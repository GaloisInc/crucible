{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Interpreter
  ( interpret
  , interpretModule
  , interpretMain
  , Value
  , IsValue(..)
  )
  where

import Control.Applicative
import Control.Monad ( foldM )
import Control.Monad.State ( StateT(..) )
import Data.Char ( isAlphaNum )
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Maybe ( fromMaybe )
import qualified Data.Set as S
import Data.Set ( Set )
import Data.Traversable hiding ( mapM )
import qualified Data.Vector as V

import qualified SAWScript.AST as SS
import SAWScript.Builtins hiding (evaluate)
import qualified SAWScript.MGU as MGU
import SAWScript.Options
import Verifier.SAW.Prelude (preludeModule)
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Rewriter ( Simpset, emptySimpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.SAW.Evaluator as SC

type Expression = SS.Expr SS.ResolvedName SS.Schema
type BlockStatement = SS.BlockStmt SS.ResolvedName SS.Schema

-- Values ----------------------------------------------------------------------

data Value s
  = VBool Bool
  | VString String
  | VInteger Integer
  | VWord Int Integer
  | VArray [Value s]
  | VTuple [Value s]
  | VRecord (Map SS.Name (Value s))
  | VFun (Value s -> Value s)
  | VFunTerm (SharedTerm s -> Value s)
  | VFunType (SS.Type -> Value s)
  | VLambda (Value s -> Maybe (SharedTerm s) -> IO (Value s))
  | VTLambda (SS.Type -> IO (Value s))
  | VTerm (SharedTerm s)
  | VIO (IO (Value s))
  | VSimpset (Simpset (SharedTerm s))
  | VTheorem (Theorem s)

instance Show (Value s) where
    showsPrec p v =
      case v of
        VBool True -> showString "True"
        VBool False -> showString "False"
        VString s -> shows s
        VInteger n -> shows n
        VWord w x -> showParen (p > 9) (shows x . showString "::[" . shows w . showString "]")
        VArray vs -> showList vs
        VTuple vs -> showParen True
                     (foldr (.) id (intersperse (showString ",") (map shows vs)))
        VRecord _ -> error "unimplemented: show VRecord" -- !(Map FieldName Value)
        VFun {} -> showString "<<fun>>"
        VFunTerm {} -> showString "<<fun-term>>"
        VFunType {} -> showString "<<fun-type>>"
        VLambda {} -> showString "<<lambda>>"
        VTLambda {} -> showString "<<polymorphic function>>"
        VTerm t -> showsPrec p t
        VIO {} -> showString "<<IO>>"
        VSimpset {} -> showString "<<simpset>>"
        VTheorem (Theorem t) -> showString "Theorem " . showParen True (showString (scPrettyTerm t))

indexValue :: Value s -> Value s -> Value s
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value s -> String -> Value s
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ name
      Just x -> x
lookupValue _ _ = error "lookupValue"

evaluate :: SharedTerm s -> Value s
evaluate t = importValue (SC.evalSharedTerm SC.preludeGlobal t)
-- FIXME: is SC.preludeGlobal always appropriate? Or should we
-- parameterize on a meaning function for globals?

applyValue :: Value s -> Value s -> IO (Value s)
applyValue (VFun f) (VTerm t) = return (f (evaluate t))
applyValue (VFun f) x = return (f x)
applyValue (VFunTerm f) (VTerm t) = return (f t)
applyValue (VLambda f) (VTerm t) = f (evaluate t) (Just t)
applyValue (VLambda f) x = f x Nothing
applyValue (VTerm t) x = applyValue (evaluate t) x
applyValue _ _ = fail "applyValue"

tapplyValue :: Value s -> SS.Type -> IO (Value s)
tapplyValue (VFunType f) t = return (f t)
tapplyValue (VTLambda f) t = f t
tapplyValue v _ = return v

thenValue :: Value s -> Value s -> Value s
thenValue (VIO m1) (VIO m2) = VIO (m1 >> m2)
thenValue _ _ = error "thenValue"

bindValue :: Value s -> Value s -> Value s
bindValue (VIO m1) v2 = VIO $ do v1 <- m1
                                 VIO m3 <- applyValue v2 v1
                                 m3
bindValue _ _ = error "bindValue"

importValue :: SC.Value -> Value s
importValue val =
    case val of
      SC.VFun f -> VFun (importValue . f . exportValue)
      SC.VTrue -> VBool True
      SC.VFalse -> VBool False
      SC.VNat n -> VInteger n
      SC.VWord w x -> VWord w x
      SC.VString s -> VString s -- FIXME: probably not needed
      SC.VTuple vs -> VTuple (V.toList (fmap importValue vs))
      SC.VRecord m -> VRecord (fmap importValue m)
      SC.VCtorApp "Prelude.False" _ -> VBool False
      SC.VCtorApp "Prelude.True" _ -> VBool True
      SC.VCtorApp {} -> error $ "VCtorApp unsupported: " ++ show val
      SC.VVector vs -> VArray (V.toList (fmap importValue vs))
      SC.VFloat {} -> error "VFloat unsupported"
      SC.VDouble {} -> error "VDouble unsupported"
      SC.VType -> error "VType unsupported"

exportValue :: Value s -> SC.Value
exportValue val =
    case val of
      VBool b -> if b then SC.VTrue else SC.VFalse
      VString s -> SC.VString s -- FIXME: probably not needed
      VInteger n -> SC.VNat n
      VWord w x -> SC.VWord w x
      VArray vs -> SC.VVector (fmap exportValue (V.fromList vs))
      VTuple vs -> SC.VTuple (fmap exportValue (V.fromList vs))
      VRecord vm -> SC.VRecord (fmap exportValue vm)
      VFun f -> SC.VFun (exportValue . f . importValue)
      VFunTerm {} -> error "exportValue VFunTerm"
      VFunType {} -> error "exportValue VFunType"
      VLambda {} -> error "exportValue VLambda"
      VTLambda {} -> error "exportValue VTLambda"
      VTerm {} -> error "VTerm unsupported"
      VIO {} -> error "VIO unsupported"
      VSimpset {} -> error "VSimpset unsupported"

-- IsValue class ---------------------------------------------------------------

-- | Used for encoding primitive operations in the Value type.
class IsValue s a where
    toValue :: a -> Value s
    fromValue :: Value s -> a
    funToValue :: (a -> Value s) -> Value s
    funToValue f = VFun (\v -> f (fromValue v))
    funFromValue :: Value s -> (a -> Value s)
    funFromValue (VFun g) = \x -> g (toValue x)
    funFromValue _        = error "fromValue (->)"

instance IsValue s (Value s) where
    toValue x = x
    fromValue x = x

instance (IsValue s a, IsValue s b) => IsValue s (a -> b) where
    toValue f = funToValue (\x -> toValue (f x))
    fromValue v = \x -> fromValue (funFromValue v x)

instance IsValue s () where
    toValue _ = VTuple []
    fromValue _ = ()

instance (IsValue s a, IsValue s b) => IsValue s (a, b) where
    toValue (x, y) = VTuple [toValue x, toValue y]
    fromValue (VTuple [x, y]) = (fromValue x, fromValue y)
    fromValue _ = error "fromValue (,)"

instance IsValue s a => IsValue s [a] where
    toValue xs = VArray (map toValue xs)
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue s a => IsValue s (IO a) where
    toValue io = VIO (fmap toValue io)
    fromValue (VIO io) = fmap fromValue io
    fromValue _ = error "fromValue IO"

instance (IsValue s t, IsValue s a) => IsValue s (StateT t IO a) where
    toValue (StateT m) = toValue m
    fromValue v = StateT (fromValue v)

instance IsValue s (SharedTerm s) where
    toValue t = VTerm t
    fromValue (VTerm t) = t
    fromValue _ = error "fromValue SharedTerm"
    funToValue f = VFunTerm f
    funFromValue (VFunTerm f) = f
    funFromValue _ = error "fromValue (->)"

instance IsValue s SS.Type where
    toValue _ = error "toValue Type"
    fromValue _ = error "fromValue Type"
    funToValue f = VFunType f
    funFromValue (VFunType f) = f
    funFromValue _ = error "fromValue (->)"

instance IsValue s String where
    toValue n = VString n
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

instance IsValue s Integer where
    toValue n = VInteger n
    fromValue (VInteger n) = n
    fromValue _ = error "fromValue Integer"

instance IsValue s Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x
    fromValue (VWord w x) = Prim.BV w x
    fromValue _ = error "fromValue BitVector"

instance IsValue s Bool where
    toValue b = VBool b
    fromValue (VBool b) = b
    fromValue _ = error "fromValue Bool"

instance IsValue s (Simpset (SharedTerm s)) where
    toValue ss = VSimpset ss
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue s (Theorem s) where
    toValue t = VTheorem t
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

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
      SS.TyVar (SS.BoundVar x)    -> case M.lookup x tenv of
                                       Nothing -> fail $ "translateType: unbound type variable: " ++ x
                                       Just (i, k) -> do
                                         k' <- translateKind sc k
                                         scLocalVar sc i k'
      _                           -> fail "untranslatable type"

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

translatableExpr :: Set SS.ResolvedName -> Expression -> Bool
translatableExpr env expr =
    case expr of
      SS.Bit _             _ -> True
      SS.Quote _           _ -> False -- We could allow strings, but I don't think we need them.
      SS.Z _               _ -> True
      SS.Array es          t -> translatableSchema t && all (translatableExpr env) es
      SS.Undefined         _ -> False
      SS.Block _           _ -> False
      SS.Tuple es          _ -> all (translatableExpr env) es
      SS.Record bs         _ -> all (translatableExpr env . snd) bs
      SS.Index e n         _ -> translatableExpr env e && translatableExpr env n
      SS.Lookup e _        _ -> translatableExpr env e
      SS.Var x             _ -> S.member x env
      SS.Function x t e    _ -> translatableSchema t && translatableExpr env' e
          where env' = S.insert (SS.LocalName x) env
      SS.Application f e   _ -> translatableExpr env f && translatableExpr env e
      SS.LetBlock bs e       -> all (translatableExpr env . snd) bs && translatableExpr env' e
          where env' = foldr S.insert env [ SS.LocalName x | (x, _) <- bs ]

translateExpr
    :: forall s. SharedContext s
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
    -> Map SS.Name (Int, Kind)
    -> Expression -> IO (SharedTerm s)
translateExpr sc tm sm km expr =
    case expr of
      SS.Bit b                  _ -> scBool sc b
      SS.Quote _                _ -> fail "translateExpr Quote"
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
      SS.Var x (SS.Forall [] t)   -> case M.lookup x sm of
                                       Nothing -> fail $ "Untranslatable: " ++ SS.renderResolvedName x
                                       Just e' ->
                                         case M.lookup x tm of
                                           Nothing -> return e'
                                           Just schema -> do
                                             let ts = typeInstantiation schema t
                                             ts' <- mapM (translateType sc km) ts
                                             scApplyAll sc e' ts'
      SS.Function x a e         _ -> do a' <- translateSchema sc km a
                                        x' <- scLocalVar sc 0 =<< incVars sc 0 1 a'
                                        sm' <- traverse (incVars sc 0 1) sm
                                        let sm'' = M.insert (SS.LocalName x) x' sm'
                                        let km' = fmap (\(i, k) -> (i + 1, k)) km
                                        e' <- translateExpr sc tm sm'' km' e
                                        scLambda sc (filter isAlphaNum x) a' e'
      SS.Application f e        _ -> do f' <- translateExpr sc tm sm km f
                                        e' <- translateExpr sc tm sm km e
                                        scApply sc f' e'
      SS.LetBlock bs e            -> do let m = M.fromList [ (SS.LocalName x, y) | (x, y) <- bs ]
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
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
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
        scLambdaList sc [ (filter isAlphaNum n, s0) | n <- ns ] t
  | otherwise = return (error "Untranslatable expression")

-- Type substitution -----------------------------------------------------------

toSubst :: Map SS.Name SS.Type -> MGU.Subst
toSubst m = MGU.Subst (M.mapKeysMonotonic SS.BoundVar m)

substTypeExpr :: Map SS.Name SS.Type -> Expression -> Expression
substTypeExpr m expr = MGU.appSubst (toSubst m) expr

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
    -> Expression -> IO (Value s)
interpret sc vm tm sm expr =
    case expr of
      SS.Bit b             _ -> return $ VBool b
      SS.Quote s           _ -> return $ VString s
      SS.Z z               _ -> return $ VInteger z
      SS.Array es          _ -> VArray <$> traverse (interpret sc vm tm sm) es
      SS.Undefined         _ -> fail "interpret: undefined"
      SS.Block stmts       _ -> interpretStmts sc vm tm sm stmts
      SS.Tuple es          _ -> VTuple <$> traverse (interpret sc vm tm sm) es
      SS.Record bs         _ -> VRecord <$> traverse (interpret sc vm tm sm) (M.fromList bs)
      SS.Index e1 e2       _ -> do a <- interpret sc vm tm sm e1
                                   i <- interpret sc vm tm sm e2
                                   return (indexValue a i)
      SS.Lookup e n        _ -> do a <- interpret sc vm tm sm e
                                   return (lookupValue a n)
      SS.Var x (SS.Forall [] t)
                             -> case M.lookup x vm of
                                  Nothing -> evaluate <$> translateExpr sc tm sm M.empty expr
                                  Just v ->
                                    case M.lookup x tm of
                                      Nothing -> return v
                                      Just schema -> do
                                        let ts = typeInstantiation schema t
                                        foldM tapplyValue v ts
      SS.Function x _ e    _ -> do let name = SS.LocalName x
                                   let f v Nothing = interpret sc (M.insert name v vm) tm sm e
                                       f v (Just t) = do
                                         let vm' = M.insert name v vm
                                         let sm' = M.insert name t sm
                                         interpret sc vm' tm sm' e
                                   return $ VLambda f
      SS.Application e1 e2 _ -> do v1 <- interpret sc vm tm sm e1
                                   -- TODO: evaluate v1 if it is a VTerm
                                   case v1 of
                                     VFun f ->
                                         do v2 <- interpret sc vm tm sm e2
                                            -- TODO: evaluate v2 if it is a VTerm
                                            return (f v2)
                                     VFunTerm f ->
                                         do t2 <- translateExpr sc tm sm M.empty e2
                                            return (f t2)
                                     VLambda f ->
                                         do v2 <- interpret sc vm tm sm e2
                                            t2 <- if translatableExpr (M.keysSet sm) e2
                                                  then Just <$> translateExpr sc tm sm M.empty e2
                                                  else return Nothing
                                            f v2 t2
                                     _ -> fail "interpret Application"
      SS.LetBlock bs e       -> do let m = M.fromList [ (SS.LocalName x, y) | (x, y) <- bs ]
                                   let tm' = fmap SS.typeOf m
                                   vm' <- traverse (interpretPoly sc vm tm sm) m
                                   sm' <- traverse (translatePolyExpr sc tm sm) $
                                          M.filter (translatableExpr (M.keysSet sm)) m
                                   interpret sc (M.union vm' vm) (M.union tm' tm) (M.union sm' sm) e

interpretPoly
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
    -> Expression -> IO (Value s)
interpretPoly sc vm tm sm expr =
    case SS.typeOf expr of
      SS.Forall ns _ ->
          let tlam x f m = return (VTLambda (\t -> f (M.insert x t m)))
          in foldr tlam (\m -> interpret sc vm tm sm (substTypeExpr m expr)) ns M.empty

interpretStmts
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
    -> [BlockStatement] -> IO (Value s)
interpretStmts sc vm tm sm stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ e] -> interpret sc vm tm sm e
      SS.Bind Nothing _ e : ss ->
          do v1 <- interpret sc vm tm sm e
             v2 <- interpretStmts sc vm tm sm ss
             return (v1 `thenValue` v2)
      SS.Bind (Just (x, _)) _ e : ss ->
          do v1 <- interpret sc vm tm sm e
             let name = SS.LocalName x
             let f v Nothing = interpretStmts sc (M.insert name v vm) tm sm ss
                 f v (Just t) = do
                   let vm' = M.insert name v vm
                   let sm' = M.insert name t sm
                   interpretStmts sc vm' tm sm' ss
             return (v1 `bindValue` VLambda f)
      SS.BlockLet bs : ss -> interpret sc vm tm sm (SS.LetBlock bs (SS.Block ss undefined))
      SS.BlockTypeDecl {} : _ -> fail "BlockTypeDecl unsupported"

-- | The initial version here simply interprets the binding for "main"
-- (assuming there is one), ignoring everything else in the module.
-- TODO: Support for multiple top-level mutually-recursive bindings.
interpretModule
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName SS.Schema
    -> Map SS.ResolvedName (SharedTerm s)
    -> SS.ValidModule -> IO (Value s)
interpretModule sc vm tm sm m = interpret sc vm tm sm main
    where main = case M.lookup "main" (SS.moduleExprEnv m) of
                   Just mn -> mn
                   Nothing -> error $ "No main in module " ++ show (SS.moduleName m)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m =
    do let mn = case SS.moduleName m of SS.ModuleName xs x -> mkModuleName (xs ++ [x])
       let scm = insImport preludeModule $
                 emptyModule mn
       sc <- mkSharedContext scm
       env <- coreEnv sc
       ss <- basic_ss sc
       let venv = M.insert (qualify "basic_ss") (toValue ss) (valueEnv opts sc)
       v <- interpretModule sc venv (transitivePrimEnv m) env m
       (fromValue v :: IO ())

-- | Collects primitives from the module and all its transitive dependencies.
transitivePrimEnv :: SS.ValidModule -> Map SS.ResolvedName SS.Schema
transitivePrimEnv m = M.unions (env : envs)
  where
    mn = SS.moduleName m
    env = M.mapKeysMonotonic (SS.TopLevelName mn) (SS.modulePrimEnv m)
    envs = map transitivePrimEnv (M.elems (SS.moduleDependencies m))


-- Primitives ------------------------------------------------------------------

valueEnv :: forall s. Options -> SharedContext s -> M.Map SS.ResolvedName (Value s)
valueEnv opts sc = M.fromList
  [ (qualify "read_sbv"    , toValue $ readSBV sc)
  , (qualify "read_aig"    , toValue $ readAIGPrim sc)
  , (qualify "write_aig"   , toValue $ writeAIG sc)
  , (qualify "java_extract", toValue $ extractJava sc opts)
  , (qualify "java_pure"   , toValue ()) -- FIXME: representing 'JavaSetup ()' as '()'
  , (qualify "llvm_extract", toValue $ extractLLVM sc)
  , (qualify "llvm_pure"   , toValue "llvm_pure") -- FIXME: representing 'LLVMSetup ()' as 'String'
  , (qualify "prove"       , toValue $ provePrim sc)
  , (qualify "sat"         , toValue $ satPrim sc)
  , (qualify "empty_ss"    , toValue (emptySimpset :: Simpset (SharedTerm s)))
  , (qualify "addsimp"     , toValue $ addsimp sc)
  , (qualify "rewrite"     , toValue $ rewritePrim sc)
  , (qualify "abc"         , toValue $ satABC sc)
  , (qualify "unfolding"   , toValue $ unfoldGoal sc)
  , (qualify "simplify"    , toValue $ simplifyGoal sc)
  , (qualify "print_goal"  , toValue (printGoal :: ProofScript s ()))
  , (qualify "write_smtlib1", toValue $ writeSMTLib1 sc)
  , (qualify "write_smtlib2", toValue $ writeSMTLib2 sc)
  , (qualify "write_core"   , toValue (writeCore :: FilePath -> SharedTerm s -> IO ()))
  , (qualify "read_core"    , toValue $ readCore sc)
  , (qualify "print"       , toValue (print :: Value s -> IO ()))
  , (qualify "print_type"  , toValue $ print_type sc)
  , (qualify "print_term"  , toValue ((putStrLn . scPrettyTerm) :: SharedTerm s -> IO ()))
  , (qualify "return"      , toValue (return :: Value s -> IO (Value s))) -- FIXME: make work for other monads
  , (qualify "seq"        , toValue ((>>) :: ProofScript s (Value s) -> ProofScript s (Value s) -> ProofScript s (Value s))) -- FIXME: temporary
  , (qualify "define"      , toValue $ definePrim sc)
  ]

coreEnv :: SharedContext s -> IO (M.Map SS.ResolvedName (SharedTerm s))
coreEnv sc =
  traverse (scGlobalDef sc . parseIdent) $ M.fromList $
    [ (qualify "bitSequence", "Prelude.bvNat")
    , (qualify "not"        , "Prelude.not")
    , (qualify "conj"       , "Prelude.and")
    , (qualify "disj"       , "Prelude.or")
    , (qualify "eq"         , "Prelude.eq")
    , (qualify "complement" , "Prelude.bvNot")
    ]

qualify :: String -> SS.ResolvedName
qualify s = SS.TopLevelName (SS.ModuleName [] "Prelude") s
