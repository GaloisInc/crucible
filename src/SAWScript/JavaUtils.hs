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

import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe
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

byteExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
byteExtend sc x = do
  n24 <- scNat sc 24
  n8 <- scNat sc 8
  scBvUExt sc n24 n8 x

shortExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
shortExtend sc x = do
  n16 <- scNat sc 16
  scBvUExt sc n16 n16 x

typeOfValue :: JSS.Value a -> JSS.Type
typeOfValue (IValue _) = JSS.IntType
typeOfValue (LValue _) = JSS.LongType
typeOfValue (RValue (Ref _ ty)) = ty
typeOfValue (RValue NullRef) = error "Can't get type of null reference."
typeOfValue (FValue _) = JSS.FloatType
typeOfValue (DValue _) = JSS.DoubleType
typeOfValue (AValue _) = error "Can't get type of address value."

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

-- | Returns value constructor from node.
mkJSSValue :: Type -> n -> Value n
mkJSSValue BooleanType n = IValue n
mkJSSValue ByteType    n = IValue n
mkJSSValue CharType    n = IValue n
mkJSSValue IntType     n = IValue n
mkJSSValue LongType    n = LValue n
mkJSSValue ShortType   n = IValue n
mkJSSValue _ _ = error "internal: illegal type"


writeJavaTerm :: (MonadSim (SharedContext s) m) =>
                 SharedContext s
              -> JavaExpr
              -> TypedTerm s
              -> Simulator (SharedContext s) m ()
writeJavaTerm sc expr@(CC.Term e) tm = do
  liftIO $ putStrLn "write"
  v <- valueOfTerm sc tm
  let vty = typeOfValue v
      ety = exprType expr
  unless (vty == ety) $ fail $
    "Writing value of type " ++ show vty ++
    " to location of type " ++ show ety ++ "."
  case e of
    ReturnVal _ -> fail "Can't set return value"
    Local _ idx _ -> setLocal idx v
    InstanceField rexp f -> do
      rv <- readJavaValueSim rexp
      case rv of
        RValue r -> setInstanceFieldValue r f v
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> setStaticFieldValue f v

readJavaTerm :: Monad m =>
                Path' term -> JavaExpr -> m term
readJavaTerm ps et = termOfValue ps =<< readJavaValue ps et

readJavaTermSim :: Monad m =>
                   JavaExpr -> Simulator sbe m (SBETerm sbe)
readJavaTermSim e = do
  ps <- getPath "readJavaTermSim"
  readJavaTerm ps e

termOfValue :: (Monad m) =>
               Path' term -> JSS.Value term -> m term
termOfValue _ (IValue t) = return t
termOfValue _ (LValue t) = return t
termOfValue ps (RValue r@(Ref _ (ArrayType _))) = do
  case Map.lookup r (ps ^. pathMemory . memScalarArrays) of
    Just (_, a) -> return a
    Nothing -> fail "Reference not found in arrays map"
termOfValue _ (RValue (Ref _ (ClassType _))) =
  fail "Translating objects to terms not yet implemented" -- TODO
termOfValue _ _ = fail "Can't convert term to value"

termOfValueSim :: Monad m =>
                  JSS.Value (SBETerm sbe) -> Simulator sbe m (SBETerm sbe)
termOfValueSim v = do
  ps <- getPath "termOfValueSim"
  termOfValue ps v

valueOfTerm :: (MonadSim (SharedContext s) m) =>
               SharedContext s
            -> TypedTerm s
            -> Simulator (SharedContext s) m (JSS.Value (SharedTerm s))
valueOfTerm sc (TypedTerm _schema t) = do
  -- TODO: the following is silly since we have @schema@ in scope
  ty <- liftIO $ (scTypeOf sc t >>= scWhnf sc)
  case ty of
    (asBitvectorType -> Just 8) -> IValue <$> (liftIO $ byteExtend sc t)
    (asBitvectorType -> Just 16) -> IValue <$> (liftIO $ shortExtend sc t)
    (asBitvectorType -> Just 32) -> return (IValue t)
    (asBitvectorType -> Just 64) -> return (LValue t)
    (asVecType -> Just (n :*: ety)) -> do
      jty <- case ety of
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

readJavaValue :: Monad m =>
                 Path' term -> JavaExpr -> m (JSS.Value term)
readJavaValue ps (CC.Term e) = do
  case e of
    ReturnVal _ ->
      case ps ^. pathRetVal of
        Just rv -> return rv
        Nothing -> fail "Return value not found"
    Local _ idx _ -> do
      case currentCallFrame ps of
        Just cf ->
          case Map.lookup idx (cf ^. cfLocals) of
            Just v -> return v
            Nothing -> fail $ "Local variable " ++ show idx ++ " not found"
        Nothing -> fail "No current call frame"
    InstanceField rexp f -> do
      rv <- readJavaValue ps rexp
      case rv of
        RValue ref -> do
          let ifields = ps ^. pathMemory . memInstanceFields
          case Map.lookup (ref, f) ifields of
            Just fv -> return fv
            _ -> fail "Instance field not found."
        _ -> fail "Object of instance field selector evaluated to non-reference."
    StaticField f -> do
      let sfields = ps ^. pathMemory . memStaticFields
      case Map.lookup f sfields of
        Just v -> return v
        _ -> fail "Static field not found."

readJavaValueSim :: (MonadSim sbe m) =>
                    JavaExpr
                 -> Simulator sbe m (JSS.Value (SBETerm sbe))
readJavaValueSim e = do
  ps <- getPath "readJavaValueSim"
  readJavaValue ps e

logicExprToTerm :: SharedContext SAWCtx
                -> Path' (SharedTerm SAWCtx) -> LogicExpr
                -> IO (SharedTerm SAWCtx)
logicExprToTerm sc ps le = do
  let exprs = logicExprJavaExprs le
  args <- forM exprs $ \expr -> do
    t <- readJavaTerm ps expr
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) exprs
  useLogicExpr sc le argTerms

mixedExprToTerm :: SharedContext SAWCtx
                -> Path' (SharedTerm SAWCtx) -> MixedExpr
                -> IO (SharedTerm SAWCtx)
mixedExprToTerm sc ps (LE le) = logicExprToTerm sc ps le
mixedExprToTerm _sc ps (JE je) = readJavaTerm ps je

logicExprToTermSim :: (Monad m) =>
                      SharedContext SAWCtx
                   -> LogicExpr
                   -> Simulator SAWBackend m (SharedTerm SAWCtx)
logicExprToTermSim sc le = do
  ps <- getPath "logicExprToTermSim"
  liftIO $ logicExprToTerm sc ps le

addAssertion :: SBETerm sbe -> Simulator sbe m ()
addAssertion t = do
  sbe <- use backend
  modifyPathM_ "addAssertion" (addPathAssertion sbe t)

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
