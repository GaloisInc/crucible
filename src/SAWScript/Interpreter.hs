{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Interpreter
  ( interpret
  , interpretMain
  , interpretModuleAtEntry
  , InterpretEnv, interpretEnvValues, interpretEnvTypes, interpretEnvShared
  , buildInterpretEnv
  , Value, isVUnit
  , IsValue(..)
  )
  where

import Control.Applicative
import Control.Monad ( foldM )
import Data.Graph.SCC ( stronglyConnComp )
import Data.Graph ( SCC(..) )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Maybe ( fromMaybe )
import qualified Data.Set as S
import Data.Set ( Set )
import Data.Traversable hiding ( mapM )

import qualified SAWScript.AST as SS
import SAWScript.AST (Located(..))
import SAWScript.Builtins hiding (evaluate)
import SAWScript.CryptolBuiltins
import SAWScript.JavaBuiltins
import SAWScript.LLVMBuiltins
import qualified SAWScript.MGU as MGU
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value
import Verifier.SAW.Prelude (preludeModule, preludeStringIdent)
import Verifier.SAW.Rewriter ( Simpset, emptySimpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.Java.Codebase as JCB
import qualified Verifier.Java.SAWBackend as JavaSAW
import qualified Verifier.LLVM.Backend.SAW as LLVMSAW

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

type Expression = SS.Expr SS.ResolvedName SS.Schema
type BlockStatement = SS.BlockStmt SS.ResolvedName SS.Schema
type RNameMap = Map (Located SS.ResolvedName)
data InterpretEnv s = InterpretEnv { interpretEnvValues :: RNameMap (Value s)
                                   , interpretEnvTypes :: RNameMap SS.Schema
                                   , interpretEnvShared :: RNameMap (SharedTerm s)
                                   } deriving (Show)


-- Type matching ---------------------------------------------------------------

-- | Matches a (possibly) polymorphic type @polyty@ against a
-- monomorphic type @monoty@, which must be an instance of it. The
-- function returns a list of type variable instantiations, in the
-- same order as the variables in the outermost TypAbs of @polyty@.
typeInstantiation :: SS.Schema -> SS.Type -> [SS.Type]
typeInstantiation (SS.Forall xs t1) t2 =
  [ fromMaybe (error "unbound type variable") (M.lookup x m) | x <- xs ]
    where m = fromMaybe (error "matchType failed") (matchType t1 t2)

-- | @matchType pat ty@ returns a map of variable instantiations, if
-- @ty@ is an instance of @pat@.
matchType :: SS.Type -> SS.Type -> Maybe (Map SS.Name SS.Type)
matchType (SS.TyCon c1 ts1) (SS.TyCon c2 ts2) | c1 == c2 = matchTypes ts1 ts2
matchType (SS.TyRecord m1) (SS.TyRecord m2)
    | M.keys m1 == M.keys m2 = matchTypes (M.elems m1) (M.elems m2)
matchType (SS.TyVar (SS.BoundVar x)) t2 = Just (M.singleton x t2)
matchType t1 t2 = error $ "matchType failed: " ++ show (t1, t2)

matchTypes :: [SS.Type] -> [SS.Type] -> Maybe (Map SS.Name SS.Type)
matchTypes [] [] = Just M.empty
matchTypes [] (_ : _) = Nothing
matchTypes (_ : _) [] = Nothing
matchTypes (x : xs) (y : ys) = do
  m1 <- matchType x y
  m2 <- matchTypes xs ys
  let compatible = and (M.elems (M.intersectionWith (==) m1 m2))
  if compatible then Just (M.union m1 m2) else Nothing


-- Translation to SAWCore ------------------------------------------------------

data Kind = KStar | KSize

translateKind :: SharedContext s -> Kind -> IO (SharedTerm s)
translateKind sc KStar = scSort sc (mkSort 0)
translateKind sc KSize = scNatType sc

translatableType :: SS.Type -> Bool
translatableType ty =
    case ty of
      SS.TyRecord m               -> all translatableType (M.elems m)
      SS.TyCon (SS.TupleCon _) ts -> all translatableType ts
      SS.TyCon SS.ArrayCon [l, t] -> translatableType l && translatableType t
      SS.TyCon SS.FunCon [a, b]   -> translatableType a && translatableType b
      SS.TyCon SS.BoolCon []      -> True
      SS.TyCon SS.ZCon []         -> True
      SS.TyCon (SS.NumCon _) []   -> True
      SS.TyVar (SS.BoundVar _)    -> True
      _                           -> False

-- | Precondition: translatableType ty
translateType
    :: SharedContext s
    -> Map SS.Name (Int, Kind)
    -> SS.Type -> IO (SharedTerm s)
translateType sc tenv ty =
    case ty of
      SS.TyRecord tm              -> do tm' <- traverse (translateType sc tenv) tm
                                        scRecordType sc tm'
      SS.TyCon (SS.TupleCon _) ts -> do ts' <- traverse (translateType sc tenv) ts
                                        scTupleType sc ts'
      SS.TyCon SS.ArrayCon [n, t] -> do n' <- translateType sc tenv n
                                        t' <- translateType sc tenv t
                                        scVecType sc n' t'
      SS.TyCon SS.FunCon [a, b]   -> do a' <- translateType sc tenv a
                                        b' <- translateType sc tenv b
                                        scFun sc a' b'
      SS.TyCon SS.BoolCon []      -> scBoolType sc
      SS.TyCon SS.ZCon []         -> scNatType sc
      SS.TyCon (SS.NumCon n) []   -> scNat sc (fromInteger n)
      SS.TyCon SS.StringCon []    ->
        scFlatTermF sc (DataTypeApp preludeStringIdent [])
      SS.TyVar (SS.BoundVar x)    -> case M.lookup x tenv of
                                       Nothing -> fail $ "translateType: unbound type variable: " ++ x
                                       Just (i, _k) -> do
                                         scLocalVar sc i
      _                           -> fail $ "untranslatable type: " ++ show ty

translatableSchema :: SS.Schema -> Bool
translatableSchema (SS.Forall _ t) = translatableType t

translateSchema
    :: SharedContext s
    -> Map SS.Name (Int, Kind)
    -> SS.Schema -> IO (SharedTerm s)
translateSchema sc tenv0 (SS.Forall xs0 t) = go tenv0 xs0
  where
    go tenv [] = translateType sc tenv t
    go tenv (x : xs) = do
      let inc (i, k) = (i + 1, k)
      let k = KStar
      let tenv' = M.insert x (0, k) (fmap inc tenv)
      k' <- translateKind sc k
      t' <- go tenv' xs
      scPi sc x k' t'

translatableExpr :: Set (Located SS.ResolvedName) -> Expression -> Bool
translatableExpr env expr =
    case expr of
      SS.Bit _             _ -> True
      SS.Quote _           _ -> True
      SS.Z _               _ -> True
      SS.Array es          t -> translatableSchema t && all (translatableExpr env) es
      SS.Undefined         _ -> False
      SS.Block _           _ -> False
      SS.Tuple es          _ -> all (translatableExpr env) es
      SS.Record bs         _ -> all (translatableExpr env . snd) bs
      SS.Index e n         _ -> translatableExpr env e && translatableExpr env n
      SS.Lookup e _        _ -> translatableExpr env e
      SS.TLookup e _       _ -> translatableExpr env e
      SS.Var x             _ -> S.member x env
      SS.Function x t e    _ -> translatableSchema t && translatableExpr env' e
          where env' = S.insert (fmap SS.LocalName x) env
      SS.Application f e   _ -> translatableExpr env f && translatableExpr env e
      SS.LetBlock bs e       -> all (translatableExpr env . snd) bs && translatableExpr env' e
          where env' = foldr S.insert env [ SS.Located (SS.LocalName (SS.getVal x)) (SS.getOrig x) (SS.getPos x)
                                            | (x, _) <- bs ]

translateExpr
    :: forall s. SharedContext s
    -> RNameMap SS.Schema
    -> RNameMap (SharedTerm s)
    -> Map SS.Name (Int, Kind)
    -> Expression -> IO (SharedTerm s)
translateExpr sc tm sm km expr =
    case expr of
      SS.Bit b                  _ -> scBool sc b
      SS.Quote s                _ -> scString sc s
      SS.Z z                    _ -> scNat sc (fromInteger z)
      SS.Array es              ty -> do let (_, t) = destArrayT ty
                                        t' <- translateType sc km t
                                        es' <- traverse (translateExpr sc tm sm km) es
                                        scVector sc t' es'
      SS.Undefined              _ -> fail "translateExpr: undefined"
      SS.Block _                _ -> fail "translateExpr Block"
      SS.Tuple es               _ -> do es' <- traverse (translateExpr sc tm sm km) es
                                        scTuple sc es'
      SS.Record bs              _ -> do bs' <- traverse (translateExpr sc tm sm km) (M.fromList bs)
                                        scRecord sc bs'
      SS.Index e i              _ -> do let (l, t) = destArrayT (SS.typeOf e)
                                        l' <- translateType sc km l
                                        t' <- translateType sc km t
                                        e' <- translateExpr sc tm sm km e
                                        i' <- translateExpr sc tm sm km i
                                        i'' <- return i' -- FIXME: add coercion from Nat to Fin w
                                        scGet sc l' t' e' i''
      SS.Lookup e n             _ -> do e' <- translateExpr sc tm sm km e
                                        scRecordSelect sc e' n
      SS.TLookup e i            _ -> do e' <- translateExpr sc tm sm km e
                                        scTupleSelector sc e' (fromIntegral i)
      SS.Var x (SS.Forall [] t)   -> case M.lookup x sm of
                                       Nothing -> fail $ "Untranslatable: " ++ SS.renderResolvedName (SS.getVal x)
                                       Just e' ->
                                         case M.lookup x tm of
                                           Nothing -> return e'
                                           Just schema -> do
                                             let ts = typeInstantiation schema t
                                             ts' <- mapM (translateType sc km) ts
                                             scApplyAll sc e' ts'
      SS.Var x (SS.Forall _ _)    ->
        fail $ "Untranslatable: " ++ SS.renderResolvedName (SS.getVal x)
      SS.Function x a e _ -> do a' <- translateSchema sc km a
                                x' <- scLocalVar sc 0
                                sm' <- traverse (incVars sc 0 1) sm
                                let sm'' = M.insert (fmap SS.LocalName x) x' sm'
                                let km' = fmap (\(i, k) -> (i + 1, k)) km
                                e' <- translateExpr sc tm sm'' km' e
                                scLambda sc (takeWhile (/= '.') (SS.getVal x)) a' e'
      SS.Application f e        _ -> do f' <- translateExpr sc tm sm km f
                                        e' <- translateExpr sc tm sm km e
                                        scApply sc f' e'
      SS.LetBlock bs e            -> do let m = M.fromList [ (SS.Located (SS.LocalName $ SS.getVal x) (SS.getOrig x) (SS.getPos x), y) | (x, y) <- bs ]
                                        let tm' = fmap SS.typeOf m
                                        sm' <- traverse (translateExpr sc tm sm km) m
                                        translateExpr sc (M.union tm' tm) (M.union sm' sm) km e
    where
      destArrayT (SS.Forall [] (SS.TyCon SS.ArrayCon [l, t])) = (l, t)
      destArrayT _ = error "translateExpr: internal error"

-- | Toplevel SAWScript expressions may be polymorphic. Type
-- abstractions do not show up explicitly in the Expr datatype, but
-- they are represented in a top-level expression's type (using
-- TypAbs). If present, these must be translated into SAWCore as
-- explicit type abstractions.
translatePolyExpr
    :: forall s. SharedContext s
    -> RNameMap SS.Schema
    -> RNameMap (SharedTerm s)
    -> Expression -> IO (SharedTerm s)
translatePolyExpr sc tm sm expr
  | translatableExpr (M.keysSet sm) expr =
    case SS.typeOf expr of
      SS.Forall [] _ -> translateExpr sc tm sm M.empty expr
      SS.Forall ns _ -> do
        let km = M.fromList [ (n, (i, KStar))  | (n, i) <- zip (reverse ns) [0..] ]
        -- FIXME: we assume all have kind KStar
        s0 <- translateKind sc KStar
        t <- translateExpr sc tm sm km expr
        scLambdaList sc [ (takeWhile (/= '.') n, s0) | n <- ns ] t
  | otherwise = return (error "Untranslatable expression")

-- Type substitution -----------------------------------------------------------

toSubst :: Map SS.Name SS.Type -> MGU.Subst
toSubst m = MGU.Subst (M.mapKeysMonotonic SS.BoundVar m)

substTypeExpr :: Map SS.Name SS.Type -> Expression -> Expression
substTypeExpr m expr = MGU.appSubst (toSubst m) expr

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> InterpretEnv s -> Expression -> IO (Value s)
interpret sc env@(InterpretEnv vm tm sm) expr =
    case expr of
      SS.Bit b             _ -> return $ VBool b
      SS.Quote s           _ -> return $ VString s
      SS.Z z               _ -> return $ VInteger z
      SS.Array es          _ -> VArray <$> traverse (interpret sc env) es
      SS.Undefined         _ -> fail "interpret: undefined"
      SS.Block stmts       _ -> interpretStmts sc env stmts
      SS.Tuple es          _ -> VTuple <$> traverse (interpret sc env) es
      SS.Record bs         _ -> VRecord <$> traverse (interpret sc env) (M.fromList bs)
      SS.Index e1 e2       _ -> do a <- interpret sc env e1
                                   i <- interpret sc env e2
                                   return (indexValue a i)
      SS.Lookup e n        _ -> do a <- interpret sc env e
                                   return (lookupValue a n)
      SS.TLookup e i       _ -> do a <- interpret sc env e
                                   return (tupleLookupValue a i)
      SS.Var x (SS.Forall [] t)
                             -> case M.lookup x vm of
                                  Nothing -> evaluate sc <$> translateExpr sc tm sm M.empty expr
                                  Just v ->
                                    case M.lookup x tm of
                                      Nothing -> return v
                                      Just schema -> do
                                        let ts = typeInstantiation schema t
                                        foldM tapplyValue v ts
      SS.Var x (SS.Forall _ _) ->
        fail $ "Can't interpret: " ++ SS.renderResolvedName (SS.getVal x)
      SS.Function x _ e    _ -> do let name = fmap SS.LocalName x
                                   let f v Nothing = interpret sc (InterpretEnv (M.insert name v vm) tm sm) e
                                       f v (Just t) = do
                                         let vm' = M.insert name v vm
                                         let sm' = M.insert name t sm
                                         interpret sc (InterpretEnv vm' tm sm') e
                                   return $ VLambda f
      SS.Application e1 e2 _ -> do v1 <- interpret sc env e1
                                   -- TODO: evaluate v1 if it is a VTerm
                                   case v1 of
                                     VFun f ->
                                         do v2 <- interpret sc env e2
                                            -- TODO: evaluate v2 if it is a VTerm
                                            return (f v2)
                                     VFunTerm f ->
                                         do t2 <- translateExpr sc tm sm M.empty e2
                                            return (f t2)
                                     VLambda f ->
                                         do v2 <- interpret sc env e2
                                            t2 <- if translatableExpr (M.keysSet sm) e2
                                                  then Just <$> translateExpr sc tm sm M.empty e2
                                                  else return Nothing
                                            f v2 t2
                                     _ -> fail "interpret Application"
      SS.LetBlock bs e       -> do let m = M.fromList [ (Located (SS.LocalName $ getVal x) (getOrig x) (getPos x), y) | (x, y) <- bs ]
                                   let tm' = fmap SS.typeOf m
                                   vm' <- traverse (interpretPoly sc env) m
                                   sm' <- traverse (translatePolyExpr sc tm sm) $
                                          M.filter (translatableExpr (M.keysSet sm)) m
                                   interpret sc (InterpretEnv (M.union vm' vm) (M.union tm' tm) (M.union sm' sm)) e

interpretPoly
    :: forall s. SharedContext s
    -> InterpretEnv s -> Expression -> IO (Value s)
interpretPoly sc env expr =
    case SS.typeOf expr of
      SS.Forall ns _ ->
          let tlam x f m = return (VTLambda (\t -> f (M.insert x t m)))
          in foldr tlam (\m -> interpret sc env (substTypeExpr m expr)) ns M.empty

interpretStmts
    :: forall s. SharedContext s
    -> InterpretEnv s -> [BlockStatement] -> IO (Value s)
interpretStmts sc env@(InterpretEnv vm tm sm) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ e] -> interpret sc env e
      SS.Bind Nothing _ e : ss ->
          do v1 <- interpret sc env e
             v2 <- interpretStmts sc env ss
             return (v1 `thenValue` v2)
      SS.Bind (Just (x, _)) _ e : ss ->
          do v1 <- interpret sc env e
             let name = fmap SS.LocalName x
             let f v Nothing = interpretStmts sc (InterpretEnv (M.insert name v vm) tm sm) ss
                 f v (Just t) = do
                   let vm' = M.insert name v vm
                   let sm' = M.insert name t sm
                   interpretStmts sc (InterpretEnv vm' tm sm') ss
             return (bindValue sc v1 (VLambda f))
      SS.BlockLet bs : ss -> interpret sc env (SS.LetBlock bs (SS.Block ss undefined))
      SS.BlockTypeDecl {} : _ -> fail "BlockTypeDecl unsupported"

interpretModule
    :: forall s. SharedContext s
    -> InterpretEnv s -> SS.ValidModule -> IO (InterpretEnv s)
interpretModule sc env m =
    do let mn = SS.moduleName m
       let graph = [ ((Located rname (SS.getOrig name) (SS.getPos name), e), rname, S.toList (exprDeps e))
                   | (name, e) <- M.assocs (SS.moduleExprEnv m)
                   , let rname = SS.TopLevelName mn (SS.getVal name) ]
       let sccs = stronglyConnComp graph
       foldM (interpretSCC sc) env sccs

interpretSCC
    :: forall s. SharedContext s
    -> InterpretEnv s -> SCC (Located SS.ResolvedName, Expression) -> IO (InterpretEnv s)
interpretSCC sc env@(InterpretEnv vm tm sm) scc =
    case scc of
      CyclicSCC _nodes -> fail "Unimplemented: Recursive top level definitions"
      AcyclicSCC (x, expr)
        | translatableExpr (M.keysSet sm) expr ->
            do s <- translatePolyExpr sc tm sm expr
               let t = SS.typeOf expr
               return $ InterpretEnv vm (M.insert x t tm) (M.insert x s sm)
        | otherwise ->
            do v <- interpretPoly sc env expr
               let t = SS.typeOf expr
               return $ InterpretEnv (M.insert x v vm) (M.insert x t tm) sm

exprDeps :: Expression -> Set SS.ResolvedName
exprDeps expr =
    case expr of
      SS.Bit _             _ -> S.empty
      SS.Quote _           _ -> S.empty
      SS.Z _               _ -> S.empty
      SS.Undefined         _ -> S.empty
      SS.Array es          _ -> S.unions (map exprDeps es)
      SS.Block stmts       _ -> S.unions (map stmtDeps stmts)
      SS.Tuple es          _ -> S.unions (map exprDeps es)
      SS.Record bs         _ -> S.unions (map (exprDeps . snd) bs)
      SS.Index e1 e2       _ -> S.union (exprDeps e1) (exprDeps e2)
      SS.Lookup e _        _ -> exprDeps e
      SS.TLookup e _       _ -> exprDeps e
      SS.Var name          _ -> S.singleton (SS.getVal name)
      SS.Function _ _ e    _ -> exprDeps e
      SS.Application e1 e2 _ -> S.union (exprDeps e1) (exprDeps e2)
      SS.LetBlock bs e       -> S.unions (exprDeps e : map (exprDeps . snd) bs)

stmtDeps :: BlockStatement -> Set SS.ResolvedName
stmtDeps stmt =
    case stmt of
      SS.Bind _ _ e        -> exprDeps e
      SS.BlockTypeDecl _ _ -> S.empty
      SS.BlockLet bs       -> S.unions (map (exprDeps . snd) bs)

interpretModuleAtEntry :: SS.Name
                          -> SharedContext s
                          -> InterpretEnv s
                          -> SS.ValidModule
                          -> IO (Value s, InterpretEnv s)
interpretModuleAtEntry entryName sc env m =
  do interpretEnv@(InterpretEnv vm _tm _sm) <- interpretModule sc env m
     let mainName = Located (SS.TopLevelName (SS.moduleName m) entryName) entryName (PosInternal "entry")
     case M.lookup mainName vm of
       Just (VIO v) -> do
         -- We've been asked to execute a 'TopLevel' action, so run it.
         r <- v
         return (r, interpretEnv)
       Just v ->
         {- We've been asked to evaluate a pure value, so wrap it up in IO
         and give it back. -}
         return (v, interpretEnv)
       Nothing -> fail $ "No " ++ entryName ++ " in module " ++ show (SS.moduleName m)

-- | Interpret an expression using the default value environments.
interpretEntry :: SS.Name -> Options -> SS.ValidModule -> IO (Value SAWCtx)
interpretEntry entryName opts m =
    do (bic, interpretEnv0) <- buildInterpretEnv opts m
       let sc = biSharedContext bic
       (result, _interpretEnv) <-
         interpretModuleAtEntry entryName sc interpretEnv0 m
       return result

buildInterpretEnv:: Options -> SS.ValidModule
                 -> IO (BuiltinContext, InterpretEnv SAWCtx)
buildInterpretEnv opts m =
    do let mn = case SS.moduleName m of SS.ModuleName xs x -> mkModuleName (xs ++ [x])
       let scm = insImport preludeModule $
                 insImport JavaSAW.javaModule $
                 insImport LLVMSAW.llvmModule $
                 insImport CryptolSAW.cryptolModule $
                 emptyModule mn
       sc <- mkSharedContext scm
       ss <- basic_ss sc
       jcb <- JCB.loadCodebase (jarList opts) (classPath opts)
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biJavaCodebase = jcb
                 }
       let vm0 = M.insert (qualify "basic_ss") (toValue ss) (valueEnv opts bic)
       let tm0 = transitivePrimEnv m
       sm0 <- coreEnv sc
       return (bic, InterpretEnv vm0 tm0 sm0)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m = fromValue <$> interpretEntry "main" opts m

-- | Collects primitives from the module and all its transitive dependencies.
transitivePrimEnv :: SS.ValidModule -> RNameMap SS.Schema
transitivePrimEnv m = M.unions (env : envs)
  where
    mn = SS.moduleName m
    env = M.mapKeysMonotonic (\x-> Located (SS.TopLevelName mn (SS.getVal x)) (SS.getOrig x) (SS.getPos x)) (SS.modulePrimEnv m)
    envs = map transitivePrimEnv (M.elems (SS.moduleDependencies m))


-- Primitives ------------------------------------------------------------------

print_value :: Value SAWCtx -> IO ()
print_value (VString s) = putStrLn s
print_value v = print v

valueEnv :: Options -> BuiltinContext -> RNameMap (Value SAWCtx)
valueEnv opts bic = M.fromList
  [ (qualify "read_sbv"    , toValue $ readSBV sc)
  , (qualify "read_aig"    , toValue $ readAIGPrim sc)
  , (qualify "write_aig"   , toValue $ writeAIG sc)
  -- Cryptol stuff
  , (qualify "cryptol_module", toValue $ loadCryptol)
  , (qualify "cryptol_extract", toValue $ extractCryptol sc)
  -- Java stuff
  , (qualify "java_extract", toValue $ extractJava bic opts)
  , (qualify "java_verify" , toValue $ verifyJava bic opts)
  , (qualify "java_pure"   , toValue $ javaPure)
  , (qualify "java_var"    , toValue $ javaVar bic opts)
  , (qualify "java_may_alias", toValue $ javaMayAlias bic opts)
  , (qualify "java_assert" , toValue $ javaAssert bic opts)
  --, (qualify "java_assert_eq" , toValue $ javaAssertEq bic opts)
  , (qualify "java_ensure_eq" , toValue $ javaEnsureEq bic opts)
  , (qualify "java_modify" , toValue $ javaModify bic opts)
  , (qualify "java_return" , toValue $ javaReturn bic opts)
  , (qualify "java_verify_tactic" , toValue $ javaVerifyTactic bic opts)
  -- LLVM stuff
  , (qualify "llvm_extract", toValue $ extractLLVM sc)
  , (qualify "llvm_verify" , toValue $ verifyLLVM bic opts)
  , (qualify "llvm_pure"   , toValue $ llvmPure)
  , (qualify "llvm_ptr"    , toValue $ llvmPtr bic opts)
  , (qualify "llvm_var"    , toValue $ llvmVar bic opts)
  -- , (qualify "llvm_may_alias", toValue $ llvmMayAlias bic opts)
  , (qualify "llvm_assert" , toValue $ llvmAssert bic opts)
  --, (qualify "llvm_assert_eq" , toValue $ llvmAssertEq bic opts)
  , (qualify "llvm_ensure_eq" , toValue $ llvmEnsureEq bic opts)
  , (qualify "llvm_modify" , toValue $ llvmModify bic opts)
  , (qualify "llvm_return" , toValue $ llvmReturn bic opts)
  , (qualify "llvm_verify_tactic" , toValue $ llvmVerifyTactic bic opts)
  -- Generic stuff
  , (qualify "prove"       , toValue $ provePrim sc)
  , (qualify "prove_print" , toValue $ provePrintPrim sc)
  , (qualify "sat"         , toValue $ satPrim sc)
  , (qualify "sat_print"   , toValue $ satPrintPrim sc)
  , (qualify "empty_ss"    , toValue (emptySimpset :: Simpset (SharedTerm SAWCtx)))
  , (qualify "addsimp"     , toValue $ addsimp sc)
  , (qualify "addsimp'"    , toValue $ addsimp' sc)
  , (qualify "rewrite"     , toValue $ rewritePrim sc)
  , (qualify "assume_valid", toValue (assumeValid :: ProofScript SAWCtx (ProofResult SAWCtx)))
  , (qualify "assume_unsat", toValue (assumeUnsat :: ProofScript SAWCtx (SatResult SAWCtx)))
  , (qualify "abc"         , toValue $ satABC sc)
  , (qualify "abc2"        , toValue $ satABC' sc)
  , (qualify "yices"       , toValue $ satYices sc)
  , (qualify "offline_aig" , toValue $ satAIG sc)
  , (qualify "offline_extcore" , toValue $ satExtCore sc)
  , (qualify "offline_smtlib1" , toValue $ satSMTLib1 sc)
  , (qualify "offline_smtlib2" , toValue $ satSMTLib2 sc)
  , (qualify "unfolding"   , toValue $ unfoldGoal sc)
  , (qualify "simplify"    , toValue $ simplifyGoal sc)
  , (qualify "print_goal"  , toValue (printGoal :: ProofScript SAWCtx ()))
  , (qualify "write_smtlib1", toValue $ writeSMTLib1 sc)
  , (qualify "write_smtlib2", toValue $ writeSMTLib2 sc)
  , (qualify "write_core"   , toValue (writeCore :: FilePath -> SharedTerm SAWCtx -> IO ()))
  , (qualify "read_core"    , toValue $ readCore sc)
  , (qualify "term"         , toValue (id :: Value SAWCtx -> Value SAWCtx))
  , (qualify "term_size"    , toValue (scSharedSize :: SharedTerm SAWCtx -> Integer))
  , (qualify "term_tree_size", toValue (scTreeSize :: SharedTerm SAWCtx -> Integer))
  , (qualify "print"       , toValue print_value)
  , (qualify "print_type"  , toValue $ print_type sc)
  , (qualify "print_term"  , toValue ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
  , (qualify "show_term"   , toValue (scPrettyTerm :: SharedTerm SAWCtx -> String))
  , (qualify "return"      , toValue (return :: Value SAWCtx -> IO (Value SAWCtx))) -- FIXME: make work for other monads
    {-
  , (qualify "seq"        , toValue ((>>) :: ProofScript SAWCtx (Value SAWCtx)
                                          -> ProofScript SAWCtx (Value SAWCtx)
                                          -> ProofScript SAWCtx (Value SAWCtx))) -- FIXME: temporary
    -}
  , (qualify "define"      , toValue $ definePrim sc)
  , (qualify "caseSatResult", toValueCase sc caseSatResultPrim)
  , (qualify "caseProofResult", toValueCase sc caseProofResultPrim)
  ] where sc = biSharedContext bic

coreEnv :: SharedContext s -> IO (RNameMap (SharedTerm s))
coreEnv sc =
  traverse (scGlobalDef sc . parseIdent) $ M.fromList $
    -- Pure things
    [ (qualify "bitSequence", "Prelude.bvNat")
    , (qualify "bvAdd"      , "Prelude.bvAdd")
    , (qualify "bvSub"      , "Prelude.bvSub")
    , (qualify "bvMul"      , "Prelude.bvMul")
    , (qualify "not"        , "Prelude.not")
    , (qualify "conj"       , "Prelude.and")
    , (qualify "disj"       , "Prelude.or")
    , (qualify "ite"        , "Prelude.ite")
    , (qualify "eq"         , "Prelude.eq")
    , (qualify "bvEq"       , "Prelude.bvEq")
    , (qualify "bvNot"      , "Prelude.bvNot")
    , (qualify "bvXor"      , "Prelude.bvXor")
    , (qualify "bvOr"       , "Prelude.bvOr")
    , (qualify "bvAnd"      , "Prelude.bvAnd")
    , (qualify "bvShl"      , "Prelude.bvShl")
    , (qualify "bvShr"      , "Prelude.bvShr")
    , (qualify "bvule"      , "Prelude.bvule")
    , (qualify "bvult"      , "Prelude.bvult")
    , (qualify "bvuge"      , "Prelude.bvuge")
    , (qualify "bvugt"      , "Prelude.bvugt")
    , (qualify "bvsle"      , "Prelude.bvsle")
    , (qualify "bvslt"      , "Prelude.bvslt")
    , (qualify "bvsge"      , "Prelude.bvsge")
    , (qualify "bvsgt"      , "Prelude.bvsgt")
    , (qualify "bvAt"       , "Prelude.bvAt")
    , (qualify "bvUpd"      , "Prelude.bvUpd")
    , (qualify "reverse"    , "Prelude.reverse")
    -- Java things
    , (qualify "java_bool"  , "Java.mkBooleanType")
    , (qualify "java_byte"  , "Java.mkByteType")
    , (qualify "java_char"  , "Java.mkCharType")
    , (qualify "java_short" , "Java.mkShortType")
    , (qualify "java_int"   , "Java.mkIntType")
    , (qualify "java_long"  , "Java.mkLongType")
    , (qualify "java_float" , "Java.mkFloatType")
    , (qualify "java_double", "Java.mkDoubleType")
    , (qualify "java_array" , "Java.mkArrayType")
    , (qualify "java_class" , "Java.mkClassType")
    , (qualify "java_value" , "Java.mkValue")
    , (qualify "ec_join"    , "Java.ecJoin")
    , (qualify "ec_join768" , "Java.ecJoin768")
    , (qualify "ec_split"   , "Java.ecSplit")
    , (qualify "ec_split768", "Java.ecSplit768")
    , (qualify "ec_extend"  , "Java.ecExtend")
    , (qualify "long_extend", "Java.longExtend")
    -- LLVM things
    , (qualify "llvm_int"   , "LLVM.mkIntType")
    , (qualify "llvm_float" , "LLVM.mkFloatType")
    , (qualify "llvm_double", "LLVM.mkDoubleType")
    , (qualify "llvm_array" , "LLVM.mkArrayType")
    , (qualify "llvm_value",  "LLVM.mkValue")
    , (qualify "trunc31"    , "LLVM.trunc31")
    ]

qualify :: String -> Located SS.ResolvedName
qualify s = Located (SS.TopLevelName (SS.ModuleName [] "Prelude") s) s (PosInternal "coreEnv")
