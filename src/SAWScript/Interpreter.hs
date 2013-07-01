{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Interpreter
  ( interpret
  , interpretModule
  )
  where

import Control.Applicative
import Data.Char ( isAlphaNum )
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Maybe ( fromMaybe )
import Data.Traversable hiding ( mapM )
import qualified Data.Vector as V

import qualified SAWScript.AST as SS
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.SAW.Evaluator as SC

type SC = IO -- ^ type SC indicates that IO is used only for term-building operations
type Expression = SS.Expr SS.ResolvedName SS.Type
type BlockStatement = SS.BlockStmt SS.ResolvedName SS.Type

traverseSnd :: Applicative f => (b -> f c) -> (a, b) -> f (a, c)
traverseSnd f (x, y) = (,) x <$> f y

-- Values ----------------------------------------------------------------------

data Value s
  = VBool Bool
  | VString String
  | VInteger Integer
  | VWord Int Integer
  | VArray [Value s]
  | VTuple [Value s]
  | VRecord [SS.Bind (Value s)]
  | VFun (Value s -> Value s)
  | VFunTerm (SharedTerm s -> Value s)
  | VFunBoth (Value s -> Maybe (SharedTerm s) -> SC (Value s))
  | VTerm (SharedTerm s)
  | VIO (IO (Value s))

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
        VFunBoth {} -> showString "<<fun-both>>"
        VTerm t -> showsPrec p t
        VIO {} -> showString "<<IO>>"

indexValue :: Value s -> Value s -> Value s
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value s -> String -> Value s
lookupValue (VRecord bs) name =
    case lookup name bs of
      Nothing -> error $ "no such record field: " ++ name
      Just x -> x
lookupValue _ _ = error "lookupValue"

evaluate :: SharedTerm s -> Value s
evaluate t = importValue (SC.evalSharedTerm SC.preludeGlobal t)
-- FIXME: is SC.preludeGlobal always appropriate? Or should we
-- parameterize on a meaning function for globals?

applyValue :: Value s -> Value s -> SC (Value s)
applyValue (VFun f) (VTerm t) = return (f (evaluate t))
applyValue (VFun f) x = return (f x)
applyValue (VFunTerm f) (VTerm t) = return (f t)
applyValue (VFunBoth f) (VTerm t) = f (evaluate t) (Just t)
applyValue (VFunBoth f) x = f x Nothing
applyValue (VTerm t) x = applyValue (evaluate t) x
applyValue _ _ = fail "applyValue"

thenValue :: Value s -> Value s -> Value s
thenValue (VIO m1) (VIO m2) = VIO (m1 >> m2)
thenValue _ _ = error "thenValue"

bindValue :: Value s -> Value s -> Value s
bindValue (VIO m1) v2 = VIO $ do v1 <- m1
                                 VIO m3 <- applyValue v2 v1
                                 m3
bindValue _ _ = error "bindValue"

importValue :: SC.Value s -> Value s
importValue val =
    case val of
      SC.VFun f -> VFun (importValue . f . exportValue)
      SC.VTrue -> VBool True
      SC.VFalse -> VBool False
      SC.VNat n -> VInteger n
      SC.VWord w x -> VWord w x
      SC.VString s -> VString s -- FIXME: probably not needed
      SC.VTuple vs -> VTuple (V.toList (fmap importValue vs))
      SC.VRecord m -> VRecord (M.toList (fmap importValue m))
      SC.VCtorApp {} -> error "VCtorApp unsupported"
      SC.VVector vs -> VArray (V.toList (fmap importValue vs))
      SC.VFloat {} -> error "VFloat unsupported"
      SC.VDouble {} -> error "VDouble unsupported"
      SC.VType -> error "VType unsupported"
      SC.VIO {} -> error "VIO unsupported"
      SC.VTerm {} -> error "VTerm unsupported"
      SC.VSC {} -> error "VSC unsupported"

exportValue :: Value s -> SC.Value s
exportValue val =
    case val of
      VBool b -> if b then SC.VTrue else SC.VFalse
      VString s -> SC.VString s -- FIXME: probably not needed
      VInteger n -> SC.VNat n
      VWord w x -> SC.VWord w x
      VArray vs -> SC.VVector (fmap exportValue (V.fromList vs))
      VTuple vs -> SC.VTuple (fmap exportValue (V.fromList vs))
      VRecord bs -> SC.VRecord (fmap exportValue (M.fromList bs))
      VFun f -> SC.VFun (exportValue . f . importValue)
      VFunTerm {} -> error "exportValue VFunTerm"
      VFunBoth {} -> error "exportValue VFunBoth"
      VTerm {} -> error "VTerm unsupported"
      VIO {} -> error "VIO unsupported"

-- Type matching ---------------------------------------------------------------

-- | Matches a (possibly) polymorphic type @polyty@ against a
-- monomorphic type @monoty@, which must be an instance of it. The
-- function returns a list of type variable instantiations, in the
-- same order as the variables in the outermost TypAbs of @polyty@.
typeInstantiation :: SS.Type -> SS.Type -> [SS.Type]
typeInstantiation (SS.TypAbs xs t1) t2 =
  [ fromMaybe (error "unbound type variable") (M.lookup x m) | x <- xs ]
    where m = fromMaybe (error "matchType failed") (matchType t1 t2)
typeInstantiation _ _ = []

-- | @matchType pat ty@ returns a map of variable instantiations, if
-- @ty@ is an instance of @pat@. Both types must be first-order:
-- neither may contain @TypAbs@.
matchType :: SS.Type -> SS.Type -> Maybe (Map SS.Name SS.Type)
matchType SS.BitT   SS.BitT   = Just M.empty
matchType SS.ZT     SS.ZT     = Just M.empty
matchType SS.QuoteT SS.QuoteT = Just M.empty
matchType (SS.ContextT c1) (SS.ContextT c2) | c1 == c2 = Just M.empty
matchType (SS.IntegerT n1) (SS.IntegerT n2) | n1 == n2 = Just M.empty
matchType (SS.ArrayT t1 n1) (SS.ArrayT t2 n2) = matchTypes [n1, t1] [n2, t2]
matchType (SS.BlockT c1 t1) (SS.BlockT c2 t2) = matchTypes [c1, t1] [c2, t2]
matchType (SS.TupleT ts1) (SS.TupleT ts2) = matchTypes ts1 ts2
matchType (SS.RecordT bs1) (SS.RecordT bs2)
    | map fst bs1 == map fst bs2 = matchTypes (map snd bs1) (map snd bs2)
matchType (SS.FunctionT a1 b1) (SS.FunctionT a2 b2) = matchTypes [a1, b1] [a2, b2]
matchType (SS.TypVar x)    t2 = Just (M.singleton x t2)
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

translateKind :: SharedContext s -> Kind -> SC (SharedTerm s)
translateKind sc KStar = scSort sc (mkSort 0)
translateKind sc KSize = scNatType sc

translatableType :: SS.Type -> Bool
translatableType ty =
    case ty of
      SS.BitT          -> True
      SS.ZT            -> True
      SS.QuoteT        -> False
      SS.ContextT _    -> False
      SS.IntegerT _    -> True
      SS.ArrayT t n    -> translatableType t && translatableType n
      SS.BlockT _ _    -> False
      SS.TupleT ts     -> all translatableType ts
      SS.RecordT bs    -> all (translatableType . snd) bs
      SS.FunctionT a b -> translatableType a && translatableType b
      SS.Abstract _    -> False
      SS.TypAbs _ t    -> translatableType t
      SS.TypVar _      -> True

-- | Precondition: translatableType ty
translateType
    :: SharedContext s
    -> Map SS.Name (Int, Kind)
    -> SS.Type -> SC (SharedTerm s)
translateType sc tenv ty =
    case ty of
      SS.BitT          -> scBoolType sc
      SS.ZT            -> scNatType sc
      SS.QuoteT        -> fail "translateType QuoteT"
      SS.ContextT _    -> fail "translateType ContextT"
      SS.IntegerT n    -> scNat sc n
      SS.ArrayT t n    -> do n' <- translateType sc tenv n
                             t' <- translateType sc tenv t
                             scVecType sc n' t'
      SS.BlockT _ _    -> fail "translateType BlockT"
      SS.TupleT ts     -> do ts' <- traverse (translateType sc tenv) ts
                             scTupleType sc ts'
      SS.RecordT ts    -> do ts' <- traverse (translateType sc tenv) (M.fromList ts)
                             scRecordType sc ts'
      SS.FunctionT a b -> do a' <- translateType sc tenv a
                             b' <- translateType sc tenv b
                             scFun sc a' b'
      SS.Abstract _    -> fail "translateType Abstract" -- FIXME: Should we make any exceptions?
      SS.TypAbs [] t   -> translateType sc tenv t
      SS.TypAbs (x : xs) t -> do let inc (i, k) = (i + 1, k)
                                 let k = KStar
                                 let tenv' = M.insert x (0, k) (fmap inc tenv)
                                 k' <- translateKind sc k
                                 t' <- translateType sc tenv' (SS.TypAbs xs t)
                                 scPi sc x k' t'
      SS.TypVar x      -> case M.lookup x tenv of
                            Nothing -> fail $ "ToSAWCore: unbound type variable: " ++ x
                            Just (i, k) -> do
                              k' <- translateKind sc k
                              scLocalVar sc i k'

translatableExpr :: Map SS.ResolvedName a -> Expression -> Bool
translatableExpr env expr =
    case expr of
      SS.Bit _             _ -> True
      SS.Quote _           _ -> False -- We could allow strings, but I don't think we need them.
      SS.Z _               _ -> True
      SS.Array es          t -> translatableType t && all (translatableExpr env) es
      SS.Undefined         _ -> False -- REVIEW
      SS.Block _           _ -> False
      SS.Tuple es          _ -> all (translatableExpr env) es
      SS.Record bs         _ -> all (translatableExpr env . snd) bs
      SS.Index e n         _ -> translatableExpr env e && translatableExpr env n
      SS.Lookup e _        _ -> translatableExpr env e
      SS.Var x             _ -> M.member x env
      SS.Function _ t e    _ -> translatableType t && translatableExpr env e
      SS.Application f e   _ -> translatableExpr env f && translatableExpr env e
      SS.LetBlock bs e       -> all (translatableExpr env . snd) bs && translatableExpr env e

translateExpr
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Maybe SS.Type, SharedTerm s)
    -> Map SS.Name (Int, Kind)
    -> Expression -> SC (SharedTerm s)
translateExpr sc env tenv expr =
    case expr of
      SS.Bit b                  _ -> scBool sc b
      SS.Quote _                _ -> fail "translateExpr Quote"
      SS.Z z                    _ -> scNat sc z
      SS.Array es (SS.ArrayT t _) -> do t' <- translateType sc tenv t
                                        es' <- traverse (translateExpr sc env tenv) es
                                        scVector sc t' es'
      SS.Undefined              _ -> fail "translateExpr: undefined"
      SS.Array {}                 -> fail "translateExpr: internal error"
      SS.Block _                _ -> fail "translateExpr Block"
      SS.Tuple es               _ -> do es' <- traverse (translateExpr sc env tenv) es
                                        scTuple sc es'
      SS.Record bs              _ -> do bs' <- traverse (translateExpr sc env tenv) (M.fromList bs)
                                        scRecord sc bs'
      SS.Index e i              _ -> do let SS.ArrayT t l = SS.typeOf e
                                        l' <- translateType sc tenv l
                                        t' <- translateType sc tenv t
                                        e' <- translateExpr sc env tenv e
                                        i' <- translateExpr sc env tenv i
                                        i'' <- return i' -- FIXME: add coercion from Nat to Fin w
                                        scGet sc l' t' e' i''
      SS.Lookup e n             _ -> do e' <- translateExpr sc env tenv e
                                        scRecordSelect sc e' n
      SS.Var rname              t -> case M.lookup rname env of
                                       Nothing -> fail $ "Unknown name: " ++ show rname
                                       Just (Nothing, e') -> return e'
                                       Just (Just polyty, e') ->
                                           do let ts = typeInstantiation polyty t
                                              ts' <- mapM (translateType sc tenv) ts
                                              scApplyAll sc e' ts'
      SS.Function x a e         _ -> do a' <- translateType sc tenv a
                                        x' <- scLocalVar sc 0 a'
                                        env' <- traverse (traverseSnd (incVars sc 0 1)) env
                                        let env'' = M.insert (SS.LocalName x) (Nothing, x') env'
                                        let tenv' = fmap (\(i, k) -> (i + 1, k)) tenv
                                        e' <- translateExpr sc env'' tenv' e
                                        scLambda sc (filter isAlphaNum x) a' e'
      SS.Application f e        _ -> do f' <- translateExpr sc env tenv f
                                        e' <- translateExpr sc env tenv e
                                        scApply sc f' e'
      SS.LetBlock bs e            -> do let prep (x, y) = (SS.LocalName x, (Just (SS.typeOf y), y))
                                        let m = M.fromList (map prep bs)
                                        m' <- traverse (traverseSnd (translateExpr sc env tenv)) m
                                        let env' = M.union m' env
                                        translateExpr sc env' tenv e

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName (Maybe SS.Type, SharedTerm s)
    -> Expression -> SC (Value s)
interpret sc vm tm expr =
    case expr of
      SS.Bit b             _ -> return $ VBool b
      SS.Quote s           _ -> return $ VString s
      SS.Z z               _ -> return $ VInteger z
      SS.Array es          _ -> VArray <$> traverse (interpret sc vm tm) es
      SS.Undefined         _ -> fail "interpret: undefined"
      SS.Block stmts       _ -> interpretStmts sc vm tm stmts
      SS.Tuple es          _ -> VTuple <$> traverse (interpret sc vm tm) es
      SS.Record bs         _ -> VRecord <$> traverse (traverse (interpret sc vm tm)) bs
      SS.Index e1 e2       _ -> do a <- interpret sc vm tm e1
                                   i <- interpret sc vm tm e2
                                   return (indexValue a i)
      SS.Lookup e n        _ -> do a <- interpret sc vm tm e
                                   return (lookupValue a n)
      SS.Var rname         _ -> case M.lookup rname vm of
                                  Nothing -> fail $ "unbound variable: " ++ show rname
                                  Just v -> return v
      SS.Function x _ e    _ -> do let name = SS.LocalName x
                                   let f v Nothing = interpret sc (M.insert name v vm) tm e
                                       f v (Just t) = do
                                         let vm' = M.insert name v vm
                                         let tm' = M.insert name (Nothing, t) tm
                                         interpret sc vm' tm' e
                                   return $ VFunBoth f
      SS.Application e1 e2 _ -> do v1 <- interpret sc vm tm e1
                                   -- TODO: evaluate v1 if it is a VTerm
                                   case v1 of
                                     VFun f ->
                                         do v2 <- interpret sc vm tm e2
                                            -- TODO: evaluate v2 if it is a VTerm
                                            return (f v2)
                                     VFunTerm f ->
                                         do t2 <- translateExpr sc tm M.empty e2
                                            return (f t2)
                                     VFunBoth f ->
                                         do v2 <- interpret sc vm tm e2
                                            t2 <- if translatableExpr tm e2
                                                  then Just <$> translateExpr sc tm M.empty e2
                                                  else return Nothing
                                            f v2 t2
                                     _ -> fail "interpret Application"
      SS.LetBlock bs e       -> do let prep (x, y) = (SS.LocalName x, (Just (SS.typeOf y), y))
                                   let m = M.fromList (map prep bs)
                                   vs <- traverse (interpret sc vm tm . snd) m
                                   ts <- traverse (traverseSnd (translateExpr sc tm M.empty)) m
                                   interpret sc (M.union vs vm) (M.union ts tm) e

interpretStmts
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName (Maybe SS.Type, SharedTerm s)
    -> [BlockStatement] -> SC (Value s)
interpretStmts sc vm tm stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ e] -> interpret sc vm tm e
      SS.Bind Nothing _ e : ss ->
          do v1 <- interpret sc vm tm e
             v2 <- interpretStmts sc vm tm ss
             return (v1 `thenValue` v2)
      SS.Bind (Just x) _ e : ss ->
          do v1 <- interpret sc vm tm e
             let name = SS.LocalName x
             let f v Nothing = interpretStmts sc (M.insert name v vm) tm ss
                 f v (Just t) = do
                   let vm' = M.insert name v vm
                   let tm' = M.insert name (Nothing, t) tm
                   interpretStmts sc vm' tm' ss
             return (v1 `bindValue` VFunBoth f)
      SS.BlockLet bs : ss -> interpret sc vm tm (SS.LetBlock bs (SS.Block ss undefined))
      SS.BlockTypeDecl {} : _ -> fail "BlockTypeDecl unsupported"

-- | The initial version here simply interprets the binding for "main"
-- (assuming there is one), ignoring everything else in the module.
-- TODO: Support for multiple top-level mutually-recursive bindings.
interpretModule
    :: forall s. SharedContext s
    -> Map SS.ResolvedName (Value s)
    -> Map SS.ResolvedName (Maybe SS.Type, SharedTerm s)
    -> SS.ValidModule -> SC (Value s)
interpretModule sc venv env m = interpret sc venv env main
    where main = (M.!) (SS.moduleExprEnv m) "main"
