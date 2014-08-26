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
  , InterpretEnv(..)
  , buildInterpretEnv
  , Value, isVUnit
  , IsValue(..)
  )
  where

import Control.Applicative
import Control.Monad ( foldM )
import Data.Graph.SCC ( stronglyConnComp )
import Data.Graph ( SCC(..) )
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Maybe ( fromMaybe )
import qualified Data.Set as S
import Data.Set ( Set )
import Data.Traversable hiding ( mapM )

import qualified SAWScript.AST as SS
import SAWScript.AST (Located(..))
import SAWScript.Builtins hiding (evaluate)
import SAWScript.CryptolBuiltins
import qualified SAWScript.CryptolEnv as CEnv
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

import qualified Cryptol.TypeCheck.AST as T

type Expression = SS.Expr SS.ResolvedName SS.Schema
type BlockStatement = SS.BlockStmt SS.ResolvedName SS.Schema
type RNameMap = Map (Located SS.ResolvedName)

-- Environment -----------------------------------------------------------------

data InterpretEnv s = InterpretEnv
  { ieValues  :: RNameMap (Value s)
  , ieTypes   :: RNameMap SS.Schema
  , ieCryptol :: CEnv.CryptolEnv s
  }

extendEnv :: SS.LName -> SS.Schema -> Value s -> InterpretEnv s -> InterpretEnv s
extendEnv x t v (InterpretEnv vm tm ce) = InterpretEnv vm' tm' ce'
  where
    name = fmap SS.LocalName x
    qname = T.QName Nothing (T.Name (getOrig x))
    vm' = Map.insert name v vm
    tm' = Map.insert name t tm
    ce' = case v of
            VTerm (Just schema) trm
              -> CEnv.bindTypedTerm (qname, TypedTerm schema trm) ce
            _ -> ce

-- Type matching ---------------------------------------------------------------

-- | Matches a (possibly) polymorphic type @polyty@ against a
-- monomorphic type @monoty@, which must be an instance of it. The
-- function returns a list of type variable instantiations, in the
-- same order as the variables in the outermost TypAbs of @polyty@.
typeInstantiation :: SS.Schema -> SS.Type -> [SS.Type]
typeInstantiation (SS.Forall xs t1) t2 =
  [ fromMaybe (error "unbound type variable") (Map.lookup x m) | x <- xs ]
    where m = fromMaybe (error "matchType failed") (matchType t1 t2)

-- | @matchType pat ty@ returns a map of variable instantiations, if
-- @ty@ is an instance of @pat@.
matchType :: SS.Type -> SS.Type -> Maybe (Map SS.Name SS.Type)
matchType (SS.TyCon c1 ts1) (SS.TyCon c2 ts2) | c1 == c2 = matchTypes ts1 ts2
matchType (SS.TyRecord m1) (SS.TyRecord m2)
    | Map.keys m1 == Map.keys m2 = matchTypes (Map.elems m1) (Map.elems m2)
matchType (SS.TyVar (SS.BoundVar x)) t2 = Just (Map.singleton x t2)
matchType t1 t2 = error $ "matchType failed: " ++ show (t1, t2)

matchTypes :: [SS.Type] -> [SS.Type] -> Maybe (Map SS.Name SS.Type)
matchTypes [] [] = Just Map.empty
matchTypes [] (_ : _) = Nothing
matchTypes (_ : _) [] = Nothing
matchTypes (x : xs) (y : ys) = do
  m1 <- matchType x y
  m2 <- matchTypes xs ys
  let compatible = and (Map.elems (Map.intersectionWith (==) m1 m2))
  if compatible then Just (Map.union m1 m2) else Nothing


-- Type substitution -----------------------------------------------------------

toSubst :: Map SS.Name SS.Type -> MGU.Subst
toSubst m = MGU.Subst (Map.mapKeysMonotonic SS.BoundVar m)

substTypeExpr :: Map SS.Name SS.Type -> Expression -> Expression
substTypeExpr m expr = MGU.appSubst (toSubst m) expr

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> InterpretEnv s -> Expression -> IO (Value s)
interpret sc env@(InterpretEnv vm tm ce) expr =
    case expr of
      SS.Bit b             _ -> return $ VBool b
      SS.Quote s           _ -> return $ VString s
      SS.Z z               _ -> return $ VInteger z
      SS.Undefined         _ -> fail "interpret: undefined"
      SS.Code str          _ -> toValue `fmap` CEnv.parseTypedTerm sc ce str
      SS.Array es          _ -> VArray <$> traverse (interpret sc env) es
      SS.Block stmts       _ -> interpretStmts sc env stmts
      SS.Tuple es          _ -> VTuple <$> traverse (interpret sc env) es
      SS.Record bs         _ -> VRecord <$> traverse (interpret sc env) (Map.fromList bs)
      SS.Index e1 e2       _ -> do a <- interpret sc env e1
                                   i <- interpret sc env e2
                                   return (indexValue a i)
      SS.Lookup e n        _ -> do a <- interpret sc env e
                                   return (lookupValue a n)
      SS.TLookup e i       _ -> do a <- interpret sc env e
                                   return (tupleLookupValue a i)
      SS.Var x (SS.Forall [] t)
                             -> case Map.lookup x vm of
                                  Nothing -> fail $ "unknown variable: " ++ SS.renderResolvedName (SS.getVal x)
                                  --evaluate sc <$> translateExpr sc tm sm Map.empty expr
                                  Just v ->
                                    case Map.lookup x tm of
                                      Nothing -> return v
                                      Just schema -> do
                                        let ts = typeInstantiation schema t
                                        foldM tapplyValue v ts
      SS.Var x (SS.Forall _ _) ->
        fail $ "Can't interpret: " ++ SS.renderResolvedName (SS.getVal x)
{-
      SS.Var x             _ -> case Map.lookup x vm of
                                  Nothing -> fail $ "unknown variable: " ++ SS.renderResolvedName (SS.getVal x)
                                  Just v -> return v
-}
      SS.Function x t e    _ -> do let f v = interpret sc (extendEnv x t v env) e
                                   return $ VLambda f
      SS.Application e1 e2 _ -> do v1 <- interpret sc env e1
                                   v2 <- interpret sc env e2
                                   case v1 of
                                     VLambda f -> f v2
                                     _ -> fail $ "interpret Application: " ++ show v1
      SS.LetBlock bs e       -> do let f env0 (x, rhs) = do v <- interpretPoly sc env0 rhs
                                                            let t = SS.typeOf rhs
                                                            return (extendEnv x t v env0)
                                   env' <- foldM f env bs
                                   interpret sc env' e

interpretPoly
    :: forall s. SharedContext s
    -> InterpretEnv s -> Expression -> IO (Value s)
interpretPoly sc env expr =
    case SS.typeOf expr of
      SS.Forall ns _ ->
          let tlam x f m = return (VTLambda (\t -> f (Map.insert x t m)))
          in foldr tlam (\m -> interpret sc env (substTypeExpr m expr)) ns Map.empty

interpretStmts
    :: forall s. SharedContext s
    -> InterpretEnv s -> [BlockStatement] -> IO (Value s)
interpretStmts sc env@(InterpretEnv vm tm ce) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ e] -> interpret sc env e
      SS.Bind Nothing _ e : ss ->
          do v1 <- interpret sc env e
             v2 <- interpretStmts sc env ss
             return (v1 `thenValue` v2)
      SS.Bind (Just (x, t)) _ e : ss ->
          do v1 <- interpret sc env e
             let f v = interpretStmts sc (extendEnv x t v env) ss
             return (bindValue sc v1 (VLambda f))
      SS.BlockLet bs : ss -> interpret sc env (SS.LetBlock bs (SS.Block ss undefined))
      SS.BlockTypeDecl {} : _ -> fail "BlockTypeDecl unsupported"

interpretModule
    :: forall s. SharedContext s
    -> InterpretEnv s -> SS.ValidModule -> IO (InterpretEnv s)
interpretModule sc env m =
    do let mn = SS.moduleName m
       let graph = [ ((name', e), SS.getVal name', S.toList (exprDeps e))
                   | (name, e) <- Map.assocs (SS.moduleExprEnv m)
                   , let name' = fmap (SS.TopLevelName mn) name ]
       let sccs = stronglyConnComp graph
       foldM (interpretSCC sc) env sccs

interpretSCC
    :: forall s. SharedContext s
    -> InterpretEnv s -> SCC (Located SS.ResolvedName, Expression) -> IO (InterpretEnv s)
interpretSCC sc env@(InterpretEnv vm tm ce) scc =
    case scc of
      CyclicSCC _nodes -> fail "Unimplemented: Recursive top level definitions"
      AcyclicSCC (x, expr) ->
            do v <- interpretPoly sc env expr
               let t = SS.typeOf expr
               let qname = T.QName Nothing (T.Name (getOrig x))
               let vm' = Map.insert x v vm
               let tm' = Map.insert x t tm
               ce' <- case v of
                           VTerm (Just schema) trm
                             -> do putStrLn $ "Binding top-level term: " ++ show qname
                                   return $ CEnv.bindTypedTerm (qname, TypedTerm schema trm) ce
                           _ -> return ce
               return $ InterpretEnv vm' tm' ce'

exprDeps :: Expression -> Set SS.ResolvedName
exprDeps expr =
    case expr of
      SS.Bit _             _ -> S.empty
      SS.Quote _           _ -> S.empty
      SS.Z _               _ -> S.empty
      SS.Undefined         _ -> S.empty
      SS.Code _            _ -> S.empty  -- Is this right? Or should we look for occurrences of variables?
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
  do interpretEnv@(InterpretEnv vm _tm _ce) <- interpretModule sc env m
     let mainName = Located (SS.TopLevelName (SS.moduleName m) entryName) entryName (PosInternal "entry")
     case Map.lookup mainName vm of
       Just (VIO v) -> do
         --putStrLn "We've been asked to execute a 'TopLevel' action, so run it."
         -- We've been asked to execute a 'TopLevel' action, so run it.
         r <- v
         return (r, interpretEnv)
       Just v -> do
         --putStrLn "We've been asked to evaluate a pure value, so wrap it up in IO and give it back."
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

buildInterpretEnv :: Options -> SS.ValidModule
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
       let vm0 = Map.insert (qualify "basic_ss") (toValue ss) (valueEnv opts bic)
       let tm0 = transitivePrimEnv m
       ce0 <- CEnv.initCryptolEnv sc
       return (bic, InterpretEnv vm0 tm0 ce0)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m = fromValue <$> interpretEntry "main" opts m

-- | Collects primitives from the module and all its transitive dependencies.
transitivePrimEnv :: SS.ValidModule -> RNameMap SS.Schema
transitivePrimEnv m = Map.unions (env : envs)
  where
    mn = SS.moduleName m
    env = Map.mapKeysMonotonic (fmap (SS.TopLevelName mn)) (SS.modulePrimEnv m)
    envs = map transitivePrimEnv (Map.elems (SS.moduleDependencies m))


-- Primitives ------------------------------------------------------------------

print_value :: SharedContext SAWCtx -> SS.Type -> Value SAWCtx -> IO ()
print_value _sc _t (VString s) = putStrLn s
print_value  sc _t (VTerm _ trm) = print (evaluate sc trm)
print_value _sc  t v =
  putStrLn (showsPrecValue defaultPPOpts 0 (Just t) v "")

valueEnv :: Options -> BuiltinContext -> RNameMap (Value SAWCtx)
valueEnv opts bic = Map.fromList
  [ (qualify "sbv_uninterpreted", toValue $ sbvUninterpreted sc)
  , (qualify "read_sbv"    , toValue $ readSBV sc)
  , (qualify "read_aig"    , toValue $ readAIGPrim sc)
  , (qualify "write_aig"   , toValue $ writeAIG sc)
  , (qualify "write_cnf"   , toValue $ writeCNF sc)
  -- Cryptol stuff
{-BH
  , (qualify "cryptol_module", toValue $ loadCryptol)
  , (qualify "cryptol_extract", toValue $ extractCryptol sc)
-}
  -- Java stuff
  , (qualify "java_load_class", toValue $ loadJavaClass bic)
  , (qualify "java_browse_class", toValue browseJavaClass)
  , (qualify "java_extract", toValue $ extractJava bic opts)
  , (qualify "java_verify" , toValue $ verifyJava bic opts)
  , (qualify "java_pure"   , toValue $ javaPure)
  , (qualify "java_var"    , toValue $ javaVar bic opts)
  , (qualify "java_class_var", toValue $ javaClassVar bic opts)
  , (qualify "java_may_alias", toValue $ javaMayAlias bic opts)
  , (qualify "java_assert" , toValue $ javaAssert bic opts)
  --, (qualify "java_assert_eq" , toValue $ javaAssertEq bic opts)
  , (qualify "java_ensure_eq" , toValue $ javaEnsureEq bic opts)
  , (qualify "java_modify" , toValue $ javaModify bic opts)
  , (qualify "java_return" , toValue $ javaReturn bic opts)
  , (qualify "java_verify_tactic" , toValue $ javaVerifyTactic bic opts)
  -- LLVM stuff
  , (qualify "llvm_load_module", toValue loadLLVMModule)
  , (qualify "llvm_browse_module", toValue browseLLVMModule)
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
  , (qualify "check_term"  , toValue $ check_term sc)
  , (qualify "prove"       , toValue $ provePrim sc)
  , (qualify "prove_print" , toValue $ provePrintPrim sc)
  , (qualify "sat"         , toValue $ satPrim sc)
  , (qualify "sat_print"   , toValue $ satPrintPrim sc)
  , (qualify "empty_ss"    , toValue (emptySimpset :: Simpset (SharedTerm SAWCtx)))
  , (qualify "addsimp"     , toValue $ addsimp sc)
  , (qualify "addsimp'"    , toValue $ addsimp' sc)
  , (qualify "rewrite"     , toValue $ rewritePrim sc)
  , (qualify "assume_valid", toValue (assumeValid :: ProofScript SAWCtx ProofResult))
  , (qualify "assume_unsat", toValue (assumeUnsat :: ProofScript SAWCtx SatResult))
  , (qualify "abc_old"     , toValue $ satABCold sc)
  , (qualify "abc"         , toValue $ satABC sc)
  , (qualify "yices"       , toValue $ satYices sc)
  , (qualify "external_cnf_solver", toValue $ satExternalCNF sc)
  , (qualify "boolector"   , toValue $ satBoolector sc)
  , (qualify "cvc4"        , toValue $ satCVC4 sc)
  , (qualify "mathsat"     , toValue $ satMathSAT sc)
  , (qualify "z3"          , toValue $ satZ3 sc)
  , (qualify "offline_aig" , toValue $ satAIG sc)
  , (qualify "offline_cnf" , toValue $ satCNF sc)
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
  , (qualify "print"       , toValue $ print_value sc)
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
  traverse (scGlobalDef sc . parseIdent) $ Map.fromList $
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
