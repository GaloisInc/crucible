{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.JavaUtils where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Array as Array
import Data.Int
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Verifier.Java.Simulator as JSS
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.JavaExpr
import SAWScript.TypedTerm
import SAWScript.Utils

type SAWBackend = SharedContext SAWCtx
type SpecPathState = Path (SharedContext SAWCtx)
type SpecJavaValue = Value (SharedTerm SAWCtx)
type SAWJavaSim = Simulator (SharedContext SAWCtx)
type LocalMap t = Map.Map LocalVariableIndex (Value t)

boolExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
boolExtend sc x = do
  n31 <- scNat sc 31
  n1 <- scNat sc 1
  scBvUExt sc n31 n1 x

boolExtend' :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
boolExtend' sc x = do
  bool <- scBoolType sc
  x' <- scSingle sc bool x
  boolExtend sc x'

byteExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
byteExtend sc x = do
  n24 <- scNat sc 24
  n8 <- scNat sc 8
  scBvSExt sc n24 n8 x

shortExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
shortExtend sc x = do
  n16 <- scNat sc 16
  scBvSExt sc n16 n16 x

extendToIValue :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
extendToIValue sc t = do
  ty <- scWhnf sc =<< scTypeOf sc t
  case ty of
    (asBoolType -> Just ()) -> boolExtend' sc t
    (asBitvectorType -> Just 1) -> boolExtend sc t
    (asBitvectorType -> Just 8) -> byteExtend sc t
    (asBitvectorType -> Just 16) -> shortExtend sc t
    (asBitvectorType -> Just 32) -> return t
    _ -> fail $ "Invalid type passed to extendToIValue: " ++ show ty

typeOfValue :: SharedContext s -> JSS.Value (SharedTerm s) -> IO JSS.Type
typeOfValue sc (IValue t) = do
  ty <- scWhnf sc =<< scTypeOf sc t
  case ty of
    (asBoolType -> Just ()) -> return JSS.BooleanType
    (asBitvectorType -> Just 1) -> return JSS.BooleanType
    (asBitvectorType -> Just 8) -> return JSS.ByteType
    (asBitvectorType -> Just 16) -> return JSS.ShortType
    (asBitvectorType -> Just 32) -> return JSS.IntType
    _ -> fail "Invalid type for IValue"
typeOfValue _ (LValue _) = return JSS.LongType
typeOfValue _ (RValue (Ref _ ty)) = return ty
typeOfValue _ (RValue NullRef) = fail "Can't get type of null reference."
typeOfValue _ (FValue _) = return JSS.FloatType
typeOfValue _ (DValue _) = return JSS.DoubleType
typeOfValue _ (AValue _) = fail "Can't get type of address value."

-- SpecPathState {{{1

-- | Add assertion for predicate to path state.
addAssertionPS :: SharedContext SAWCtx -> SharedTerm SAWCtx
               -> SpecPathState
               -> IO SpecPathState
addAssertionPS sc x p = do
  p & pathAssertions %%~ \a -> liftIO (scAnd sc a x)

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValuePS :: Ref -> Int32 -> SharedTerm SAWCtx
                -> SpecPathState
                -> SpecPathState
setArrayValuePS r n v =
  pathMemory . memScalarArrays %~ Map.insert r (n, v)

-- | Set value of bound to instance field in path state.
setInstanceFieldValuePS :: Ref -> FieldId -> SpecJavaValue
                        -> SpecPathState -> SpecPathState
setInstanceFieldValuePS r f v =
  pathMemory . memInstanceFields %~ Map.insert (r, f) v

-- | Set value of bound to static field in path state.
setStaticFieldValuePS :: FieldId -> SpecJavaValue
                      -> SpecPathState -> SpecPathState
setStaticFieldValuePS f v =
  pathMemory . memStaticFields %~ Map.insert f v

-- | Get value of bound to instance field in path state.
getInstanceFieldValuePS :: SpecPathState -> Ref -> FieldId
                        -> Maybe SpecJavaValue
getInstanceFieldValuePS ps r f =
  Map.lookup (r, f) (ps ^. pathMemory . memInstanceFields)

-- | Get value of bound to static field in path state.
getStaticFieldValuePS :: SpecPathState -> FieldId
                      -> Maybe SpecJavaValue
getStaticFieldValuePS ps f =
  Map.lookup f (ps ^. pathMemory . memStaticFields)

-- | Returns value constructor from node.
mkJSSValue :: SharedContext s -> Type -> SharedTerm s -> IO (Value (SharedTerm s))
mkJSSValue sc BooleanType n = IValue <$> extendToIValue sc n
mkJSSValue sc ByteType    n = IValue <$> extendToIValue sc n
mkJSSValue sc CharType    n = IValue <$> extendToIValue sc n
mkJSSValue sc IntType     n = IValue <$> extendToIValue sc n
mkJSSValue sc LongType    n = do
  ty <- scTypeOf sc n
  case ty of
    (asBitvectorType -> Just 64) -> return (LValue n)
    _ -> fail "internal: invalid LValue passed to mkJSSValue."
mkJSSValue sc ShortType   n = IValue <$> extendToIValue sc n
mkJSSValue _ _ _ = fail "internal: illegal type passed to mkJSSValue"


writeJavaTerm :: (MonadSim (SharedContext s) m) =>
                 SharedContext s
              -> JavaExpr
              -> TypedTerm s
              -> Simulator (SharedContext s) m ()
writeJavaTerm sc e tm = do
  -- liftIO $ putStrLn "write"
  v <- valueOfTerm sc tm
  -- TODO: get type of tm and lift to JavaActualType
  --
  -- At the moment, the types used internally are weird, so this isn't
  -- quite the right check. We should fix that.
  {-
  vty <- liftIO $ typeOfValue sc v
  let ety = exprType e
  unless (vty == ety) $ fail $
    "Writing value of type " ++ show vty ++
    " to location " ++ ppJavaExpr e ++
    " of type " ++ show ety ++ "."
  -}
  writeJavaValue e v

writeJavaValue :: (MonadSim (SharedContext s) m) =>
                  JavaExpr
               -> JSS.Value (SharedTerm s)
               -> Simulator (SharedContext s) m ()
writeJavaValue (CC.Term e) v =
  case e of
    ReturnVal _ -> fail "Can't set return value"
    Local _ idx _ -> setLocal idx v
    InstanceField rexp f -> do
      rv <- readJavaValueSim rexp
      case rv of
        RValue r -> setInstanceFieldValue r f v
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> setStaticFieldValue f v

writeJavaValuePS :: (Functor m, Monad m) =>
                    JavaExpr
                 -> SpecJavaValue
                 -> SpecPathState
                 -> m SpecPathState
writeJavaValuePS (CC.Term e) v ps =
  case e of
    ReturnVal _ -> return (ps & set pathRetVal (Just v))
    Local _ i _ ->
      case ps ^. pathStack of
        [] -> fail "no stack frames"
        (cf:cfs) -> do
          let cf' = cf & cfLocals %~ Map.insert i v
          return (ps & pathStack .~ (cf':cfs))
    InstanceField rexp f -> do
      rv <- readJavaValue ((^. cfLocals) <$> currentCallFrame ps) ps rexp
      case rv of
        RValue r -> return (setInstanceFieldValuePS r f v ps)
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> return (setStaticFieldValuePS f v ps)

readJavaTerm :: (Functor m, Monad m) =>
                Maybe (LocalMap term) -> Path' term -> JavaExpr -> m term
readJavaTerm mcf ps et =
  termOfValue ps (exprType et) =<< readJavaValue mcf ps et

readJavaTermSim :: (Functor m, Monad m) =>
                   JavaExpr
                -> Simulator sbe m (SBETerm sbe)
readJavaTermSim e = do
  ps <- getPath "readJavaTermSim"
  readJavaTerm ((^. cfLocals) <$> currentCallFrame ps) ps e

termOfValue :: (Functor m, Monad m) =>
               Path' term -> JSS.Type -> JSS.Value term -> m term
termOfValue _ tp (IValue t) =
  case tp of
    BooleanType -> return t -- TODO: shouldn't work this way
    ByteType -> return t -- TODO: shouldn't work this way
    ShortType -> return t -- TODO: shouldn't work this way
    IntType -> return t
    _ -> fail $ "Invalid Java type for IValue: " ++ show tp
termOfValue _ _ (LValue t) = return t
termOfValue ps _ (RValue r@(Ref _ (ArrayType _))) = do
  case Map.lookup r (ps ^. pathMemory . memScalarArrays) of
    Just (_, a) -> return a
    Nothing -> fail "Reference not found in arrays map"
termOfValue _ _ (RValue (Ref _ (ClassType _))) =
  fail "Translating objects to terms not yet implemented" -- TODO
termOfValue _ _ _ = fail "Can't convert term to value"

termOfValueSim :: (Functor m, Monad m) =>
                  JSS.Type -> JSS.Value (SBETerm sbe)
               -> Simulator sbe m (SBETerm sbe)
termOfValueSim tp v = do
  ps <- getPath "termOfValueSim"
  termOfValue ps tp v

valueOfTerm :: (MonadSim (SharedContext s) m) =>
               SharedContext s
            -> TypedTerm s
            -> Simulator (SharedContext s) m (JSS.Value (SharedTerm s))
valueOfTerm sc (TypedTerm _schema t) = do
  -- TODO: the following is silly since we have @schema@ in scope
  ty <- liftIO $ (scTypeOf sc t >>= scWhnf sc)
  case ty of
    (asBoolType -> Just ()) -> IValue <$> (liftIO $ boolExtend' sc t)
    (asBitvectorType -> Just 1) -> IValue <$> (liftIO $ boolExtend sc t)
    (asBitvectorType -> Just 8) -> IValue <$> (liftIO $ byteExtend sc t)
    (asBitvectorType -> Just 16) -> IValue <$> (liftIO $ shortExtend sc t)
    (asBitvectorType -> Just 32) -> return (IValue t)
    (asBitvectorType -> Just 64) -> return (LValue t)
    (asVecType -> Just (n :*: ety)) -> do
      jty <- case ety of
               (asBoolType -> Just ()) -> return BooleanType
               (asBitvectorType -> Just 1) -> return BooleanType
               (asBitvectorType -> Just 8) -> return ByteType
               (asBitvectorType -> Just 16) -> return ShortType
               (asBitvectorType -> Just 32) -> return IntType
               (asBitvectorType -> Just 64) -> return LongType
               _ -> fail $ "Unsupported array element type: " ++ show ety
      RValue <$> newSymbolicArray (ArrayType jty) (fromIntegral n) t
    _ -> fail $ "Can't translate term of type: " ++ show ty
-- If vector of other things, allocate array, translate those things, and store
-- If record, allocate appropriate object, translate fields, assign fields
-- For the last case, we need information about the desired Java type

-- NB: the CallFrame parameter allows this function to use a different
-- call frame than the one in the current state, which can be useful to
-- access parameters of a method that has returned.
readJavaValue :: (Functor m, Monad m) =>
                 Maybe (LocalMap term)
              -> Path' term
              -> JavaExpr
              -> m (JSS.Value term)
readJavaValue mlocals ps (CC.Term e) = do
  case e of
    ReturnVal _ ->
      case ps ^. pathRetVal of
        Just rv -> return rv
        Nothing -> fail "Return value not found"
    Local _ idx _ ->
      case mlocals of
        Just locals ->
          case Map.lookup idx locals of
            Just v -> return v
            Nothing -> fail $ "Local variable " ++ show idx ++ " not found"
        Nothing -> fail "Trying to read local variable with no call frame."
    InstanceField rexp f -> do
      rv <- readJavaValue mlocals ps rexp
      case rv of
        RValue ref -> do
          let ifields = ps ^. pathMemory . memInstanceFields
          case Map.lookup (ref, f) ifields of
            Just fv -> return fv
            _ -> fail $ "Instance field '" ++ fieldIdName f ++ "' not found."
        _ -> fail "Object of instance field selector evaluated to non-reference."
    StaticField f -> do
      let sfields = ps ^. pathMemory . memStaticFields
      case Map.lookup f sfields of
        Just v -> return v
        _ -> fail $ "Static field '" ++ fieldIdName f ++
                    "' not found in class '" ++ fieldIdClass f ++ "'"

readJavaValueSim :: (MonadSim sbe m) =>
                    JavaExpr
                 -> Simulator sbe m (JSS.Value (SBETerm sbe))
readJavaValueSim e = do
  ps <- getPath "readJavaValueSim"
  readJavaValue ((^. cfLocals) <$> currentCallFrame ps) ps e

logicExprToTerm :: SharedContext SAWCtx
                -> Maybe (LocalMap (SharedTerm SAWCtx))
                -> Path' (SharedTerm SAWCtx) -> LogicExpr
                -> IO (SharedTerm SAWCtx)
logicExprToTerm sc mlocals ps le = do
  let exprs = logicExprJavaExprs le
  args <- forM exprs $ \expr -> do
    t <- readJavaTerm mlocals ps expr
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) exprs
  useLogicExpr sc le argTerms

-- NB: uses call frame from path
mixedExprToTerm :: SharedContext SAWCtx
                -> Path' (SharedTerm SAWCtx) -> MixedExpr
                -> IO (SharedTerm SAWCtx)
mixedExprToTerm sc ps me = do
  let mlocals = (^. cfLocals) <$> currentCallFrame ps
  case me of
    LE le -> logicExprToTerm sc mlocals ps le
    JE je -> readJavaTerm mlocals ps je

logicExprToTermSim :: (Functor m, Monad m) =>
                      SharedContext SAWCtx
                   -> LogicExpr
                   -> Simulator SAWBackend m (SharedTerm SAWCtx)
logicExprToTermSim sc le = do
  ps <- getPath "logicExprToTermSim"
  liftIO $ logicExprToTerm sc ((^. cfLocals) <$> currentCallFrame ps) ps le

freshJavaVal :: (MonadIO m, Functor m) =>
                Maybe (IORef [SharedTerm SAWCtx])
             -> SharedContext SAWCtx
             -> JavaActualType
             -> Simulator SAWBackend m (JSS.Value (SharedTerm SAWCtx))
freshJavaVal _ _ (PrimitiveType ty) = do
  case ty of
    BooleanType -> withSBE $ \sbe -> IValue <$> freshBool sbe
    ByteType    -> withSBE $ \sbe -> IValue <$> freshByte sbe
    CharType    -> withSBE $ \sbe -> IValue <$> freshChar sbe
    ShortType   -> withSBE $ \sbe -> IValue <$> freshShort sbe
    IntType     -> withSBE $ \sbe -> IValue <$> freshInt sbe
    LongType    -> withSBE $ \sbe -> LValue <$> freshLong sbe
    _ -> fail $ "Can't create fresh primitive value of type " ++ show ty
freshJavaVal argsRef sc (ArrayInstance n ty) | isPrimitiveType ty = do
  -- TODO: should this use bvAt?
  elts <- liftIO $ do
    ety <- scBitvector sc (fromIntegral (JSS.stackWidth ty))
    ntm <- scNat sc (fromIntegral n)
    aty <- scVecType sc ntm ety
    atm <- scFreshGlobal sc "_" aty
    maybe (return ()) (\r -> modifyIORef r (atm :)) argsRef
    mapM (scAt sc ntm ety atm) =<< mapM (scNat sc) [0..(fromIntegral n) - 1]
  case ty of
    LongType -> RValue <$> newLongArray elts
    _ | isIValue ty -> RValue <$> newIntArray (ArrayType ty) elts
    _ -> fail $ "Can't create array with element type " ++ show ty
-- TODO: allow input declarations to specialize types of fields
freshJavaVal _ _ (ArrayInstance _ _) =
  fail $ "Can't create fresh array of non-scalar elements"
freshJavaVal argsRef sc (ClassInstance c) = do
  r <- createInstance (className c) Nothing
  forM_ (classFields c) $ \f -> do
    let ty = fieldType f
    v <- freshJavaVal argsRef sc (PrimitiveType ty)
    setInstanceFieldValue r (FieldId (className c) (fieldName f) ty) v
  return (RValue r)

isArrayType :: Type -> Bool
isArrayType (ArrayType _) = True
isArrayType _ = False

refInstanceFields :: (Ord f) =>
                     Map.Map (Ref, f) v
                  -> Ref
                  -> Map.Map f v
refInstanceFields m r =
  Map.fromList [ (f, v) | ((mr, f), v) <- Map.toList m, mr == r ]

pathRefInstanceFields :: Path (SharedContext SAWCtx)
                      -> Ref
                      -> Map.Map FieldId SpecJavaValue
pathRefInstanceFields ps =
  refInstanceFields (ps ^. pathMemory . memInstanceFields)

pathArrayRefs :: Path (SharedContext SAWCtx)
              -> Ref
              -> [Ref]
pathArrayRefs ps r =
  concat
  [ Array.elems a
  | (ar, a) <- Map.toList (ps ^. pathMemory . memRefArrays)
  , ar == r
  ]

pathStaticFieldRefs :: Path (SharedContext SAWCtx)
                    -> [Ref]
pathStaticFieldRefs ps =
  valueRefs $ map snd $ Map.toList (ps ^. pathMemory . memStaticFields)

reachableFromRef :: SpecPathState -> Set.Set Ref -> Ref -> Set.Set Ref
reachableFromRef _ seen r | r `Set.member` seen = Set.empty
reachableFromRef ps seen r =
  Set.unions
  [ Set.singleton r
  , Set.unions (map (reachableFromRef ps seen') refArrayRefs)
  , Set.unions (map (reachableFromRef ps seen') instFieldRefs)
  ]
  where refArrayRefs = pathArrayRefs ps r
        instFieldRefs = valueRefs $ map snd $ Map.toList $ pathRefInstanceFields ps r
        seen' = Set.insert r seen

reachableRefs :: SpecPathState -> [SpecJavaValue] -> Set.Set Ref
reachableRefs ps vs  =
  Set.unions [ reachableFromRef ps Set.empty r | r <- roots ]
  where roots = pathStaticFieldRefs ps ++ valueRefs vs

valueRefs :: [SpecJavaValue] -> [Ref]
valueRefs vs = [ r | RValue r <- vs ]

useLogicExprPS :: JSS.Path (SharedContext SAWCtx)
               -> SharedContext SAWCtx
               -> LogicExpr
               -> IO (SharedTerm SAWCtx)
useLogicExprPS ps sc le = do
  let mlocals = (^. cfLocals) <$> currentCallFrame ps
  args <- mapM (readJavaTerm mlocals ps) (logicExprJavaExprs le)
  useLogicExpr sc le args

evalAssumptions :: SharedContext SAWCtx -> SpecPathState -> [LogicExpr]
                -> IO (SharedTerm SAWCtx)
evalAssumptions sc ps as = do
  assumptionList <- mapM (useLogicExprPS ps sc) as
  true <- scBool sc True
  foldM (scAnd sc) true assumptionList
