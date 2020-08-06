-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.ValueConv
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Operations for translating between the protocol-buffer representations
-- and the internal Crucible representations of expressions and values.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Server.ValueConv where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Lens
import           Control.Monad
import qualified Data.Sequence as Seq
import qualified Data.HashTable.IO as HIO
import qualified Control.Monad.Catch as X
import           Data.IORef
import qualified Data.Foldable as Fold
import           Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Vector as V

import qualified Data.BitVector.Sized as BV
import           Data.HPB
import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface

import           Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Server.Encoding
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))


toByteString :: Builder -> BS.ByteString
toByteString b = LazyBS.toStrict (Builder.toLazyByteString b)

----------------------------------------------------------------------
-- Exceptions that can be thrown by functions here

data ValueException where
  InvalidUnaryOpArgCount  :: String -> Int -> ValueException
  InvalidBinaryOpArgCount :: String -> Int -> ValueException
  InvalidArgumentType :: String -> TypeRepr ty -> ValueException
  InvalidElementType :: String -> TypeRepr ty -> ValueException
  InvalidStructureIndex :: String -> Int -> Int -> ValueException
  InvalidStructureArgCount :: String -> Int -> Int -> ValueException
  InvalidResultType :: String -> TypeRepr ty -> ValueException
  BadResultWidth :: String -> NatRepr w -> ValueException
  OutOfBounds :: String -> NatRepr w_actual -> NatRepr w_limit -> ValueException
  TypeMismatch :: String -> TypeRepr ty1 -> TypeRepr ty2 -> ValueException

deriving instance Show ValueException
instance X.Exception ValueException


withOneArg :: (Show w, X.MonadThrow m, Fold.Foldable t) =>
              w -> t a -> (a -> m b) -> m b
withOneArg what args op1 =
  if Fold.length args == 1
  then let [a1] = take 1 $ Fold.toList args in op1 a1
  else X.throwM $ InvalidUnaryOpArgCount (show what) (Fold.length args)

with2Args :: (Show w, X.MonadThrow m, Fold.Foldable t) =>
             w -> t a -> (a -> a -> m b) -> m b
with2Args what args op2 =
  if Fold.length args == 2
  then let [a1, a2] = take 2 $ Fold.toList args in op2 a1 a2
  else X.throwM $ InvalidBinaryOpArgCount (show what) (Fold.length args)

with3Args :: (Show w, X.MonadThrow m, Fold.Foldable t) =>
             w -> t a -> (a -> a -> a -> m b) -> m b
with3Args what args op3 =
  if Fold.length args == 3
  then let [a1, a2, a3] = take 3 $ Fold.toList args in op3 a1 a2 a3
  else X.throwM $ InvalidBinaryOpArgCount (show what) (Fold.length args)


------------------------------------------------------------------------
-- RegEntry reference

newRegEntryRef :: Simulator p sym -> RegEntry sym tp -> IO Word64
newRegEntryRef sim a = do
  cnt <- readIORef (simValueCounter sim)
  writeIORef (simValueCounter sim) $! cnt+1
  HIO.insert (simValueCache sim) cnt (Some a)
  return cnt

parseRegEntryRef :: Simulator p sym -> Word64 -> IO (Some (RegEntry sym))
parseRegEntryRef sim w = do
  mv <- HIO.lookup (simValueCache sim) w
  case mv of
    Just v -> return v
    Nothing -> error "Could not find reg entry"

releaseRegEntryRef :: Simulator p sym -> Word64 -> IO ()
releaseRegEntryRef sim w = do
  HIO.delete (simValueCache sim) w

------------------------------------------------------------------------
-- PValue encoding/decoding.

class HasTypeRepr f where
  getTypeRepr :: f tp -> TypeRepr tp

instance HasTypeRepr (RegEntry sym) where
  getTypeRepr (RegEntry tp _) = tp

instance HasTypeRepr (R.Expr () s) where
  getTypeRepr = R.exprType

instance HasTypeRepr (R.Atom s) where
  getTypeRepr = R.typeOfAtom

checkedRegEntry :: (MonadFail m, HasTypeRepr f)
                => TypeRepr tp -> Some f -> m (f tp)
checkedRegEntry tp (Some r) =
  case testEquality tp (getTypeRepr r) of
    Just Refl -> return r
    Nothing -> fail $ unwords ["Unexpected type for protocol value. Expected", show tp, "but got", show (getTypeRepr r)]

fromProtoValue :: IsSymExprBuilder sym => Simulator p sym -> P.Value -> IO (Some (RegEntry sym))
fromProtoValue sim v = do
  sym <- getInterface sim
  case v^.P.value_code of
    P.ReferenceValue -> parseRegEntryRef sim (v^.P.value_index)
    P.TrueValue  -> return $ Some $ RegEntry BoolRepr $ truePred sym
    P.FalseValue -> return $ Some $ RegEntry BoolRepr $ falsePred sym
    P.NatValue -> do
      let i = decodeUnsigned (v^.P.value_data)
      Some . RegEntry NatRepr <$> natLit sym (fromInteger i)
    P.IntegerValue -> do
      let i = decodeSigned (v^.P.value_data)
      Some . RegEntry IntegerRepr <$> intLit sym i
    P.RationalValue -> do
      r <- decodeRational (v^.P.value_data)
      Some . RegEntry RealValRepr <$> realLit sym r
    P.BitvectorValue -> do
      let width = v^.P.value_width
      case someNat (toInteger width) of
        Just (Some n) | Just LeqProof <- isPosNat n -> do
          let i = decodeSigned (v^.P.value_data)
          Some . RegEntry (BVRepr n) <$> bvLit sym n (BV.mkBV n i)
        _ -> error "Width is too large"
    P.StringValue -> do
      let s = v^.P.value_string_lit
      Some . RegEntry (StringRepr UnicodeRepr) <$> stringLit sym (UnicodeLiteral s)
    P.UnitValue -> do
      return $ Some $ RegEntry UnitRepr ()
    P.FnHandleValue -> do
      SomeHandle h <- getHandleBinding sim (v^.P.value_index)
      return $ Some $ RegEntry (handleType h) (HandleFnVal h)

toProtoValue :: IsSymExprBuilder sym => Simulator p sym -> RegEntry sym tp -> IO P.Value
toProtoValue sim e@(RegEntry tp v) =
  case tp of
    BoolRepr
      | Just True <- asConstantPred v -> do
        return $ mempty & P.value_code .~ P.TrueValue
      | Just False <- asConstantPred v -> do
        return $ mempty & P.value_code .~ P.FalseValue

    NatRepr | Just x <- asNat v -> do
      return $ mempty & P.value_code .~ P.NatValue
                      & P.value_data .~ toByteString (encodeUnsigned (toInteger x))
    IntegerRepr | Just x <- asInteger v -> do
      return $ mempty & P.value_code .~ P.IntegerValue
                      & P.value_data .~ toByteString (encodeSigned (toInteger x))

    RealValRepr | Just r <- asRational v -> do
      return $ mempty & P.value_code .~ P.RationalValue
                      & P.value_data .~ toByteString (encodeRational r)
    BVRepr w | Just r <- BV.asSigned w <$> asBV v
             , wv <- natValue w
             , wv <= fromIntegral (maxBound :: Word64) -> do
      return $ mempty & P.value_code  .~ P.BitvectorValue
                      & P.value_width .~ fromIntegral wv
                      & P.value_data  .~ toByteString (encodeSigned r)
    StringRepr UnicodeRepr
      | Just (UnicodeLiteral txt) <- asString v -> do
          return $ mempty & P.value_code .~ P.StringValue
                          & P.value_string_lit .~ txt
    UnitRepr -> do
      return $ mempty & P.value_code .~ P.UnitValue
    FunctionHandleRepr _ _
      | HandleFnVal h <- v -> do
      return $ mempty & P.value_code .~ P.FnHandleValue
                      & P.value_index  .~ handleRef h
                      & P.value_handle_info .~ toProtoHandleInfo h
    _ -> do
      idx <- newRegEntryRef sim e
      return $ mempty & P.value_code .~ P.ReferenceValue
                      & P.value_index .~ idx


----------------------------------------------------------------------

data NatReprParseFailure where
  NatParseNegative :: Integer -> NatReprParseFailure
  NotNatValue :: P.ValueCode -> NatReprParseFailure

deriving instance Show NatReprParseFailure
instance X.Exception NatReprParseFailure


parseNatRepr :: (Monad m, X.MonadThrow m) => P.Value -> m (Some NatRepr)
parseNatRepr v =
  case v^.P.value_code of
    P.NatValue -> do
      let i = decodeUnsigned (v^.P.value_data)
      case someNat i of
        Just rep -> return rep
        Nothing -> X.throwM $ NatParseNegative i
    _ -> X.throwM $ NotNatValue (v^.P.value_code)

{-
-- | Convert a protocol buffer value to a specific RegValue.
regValueFromProto :: IsSymInterface sym
                  => Simulator sym -> P.Value -> TypeRepr tp -> IO (RegValue sym tp)
regValueFromProto sim v tp = do
  someReg <- fromProtoValue sim v
  RegEntry _ r <- checkedRegEntry tp someReg
  return r
-}

------------------------------------------------------------------------
-- convertToCrucibleApp

-- | A binary operation on bitvectores.
type BVBinOp f n r = NatRepr n -> f (BVType n) -> f (BVType n) -> App () f r

-- | A symbolic bitvector expression with some bitwidth.
data SomeBV f = forall n . (1 <= n) => SomeBV (NatRepr n) (f (BVType n))

convertToCrucibleApp :: (Applicative m, MonadFail m, HasTypeRepr f, X.MonadThrow m)
                     => (a -> m (Some f))
                     -> (a -> m (Some NatRepr))
                     -> P.PrimitiveOp
                     -> Seq a
                     -> P.CrucibleType
                     -> m (Some (App () f))
convertToCrucibleApp evalVal evalNatRepr prim_op args res_type = do
  Some res_tp <- fromProtoType res_type
  convertToCrucibleApp' evalVal evalNatRepr prim_op args res_tp

convertToCrucibleApp' :: forall a f res_tp m
                       . (Applicative m, MonadFail m, HasTypeRepr f, X.MonadThrow m)
                      => (a -> m (Some f))
                      -> (a -> m (Some NatRepr))
                         -- ^ Parse argument as a concrete nat.
                      -> P.PrimitiveOp
                      -> Seq a
                      -> TypeRepr res_tp
                      -> m (Some (App () f))
convertToCrucibleApp' evalVal evalNatRepr prim_op args result_type = do
  let evalTypedValue :: TypeRepr tp -> a -> m (f tp)
      evalTypedValue tp v = checkedRegEntry tp =<< evalVal v

  -- Gets a bitvector value.
  let evalBV :: a -> m (SomeBV f)
      evalBV v = do
        Some r <- evalVal v
        case getTypeRepr r of
          BVRepr n -> return (SomeBV n r)
          _ -> X.throwM $ InvalidArgumentType (show prim_op ++ "evalBV") $
               getTypeRepr r

  let evalCtxIndex :: a -> CtxRepr ctx -> TypeRepr tp -> m (Ctx.Index ctx tp)
      evalCtxIndex a ctx_repr ty_repr = do
          Some i <- evalNatRepr a
          case Ctx.intIndex (fromIntegral (natValue i)) (Ctx.size ctx_repr) of
             Just (Some idx) ->
                case testEquality (ctx_repr Ctx.! idx) ty_repr of
                   Just Refl -> return idx
                   Nothing -> X.throwM $ TypeMismatch
                              (show prim_op <> " structure index " <> show i)
                              (ctx_repr Ctx.! idx) ty_repr
             Nothing -> X.throwM $ InvalidStructureIndex (show prim_op)
                        (fromIntegral (natValue i))
                        (Ctx.sizeInt $ Ctx.size ctx_repr)

  let defCoerce :: KnownRepr TypeRepr tp => a -> m (f tp)
      defCoerce v = evalTypedValue knownRepr v

  let def :: m (App () f tp) -> m (Some (App () f))
      def a = Some <$> a

  let bvBinOp :: (forall n . (1 <= n) => BVBinOp f n (BVType n))
              -> m (Some (App () f))
      bvBinOp f = with2Args prim_op args $ \x y -> do
        SomeBV n xr <- evalBV x
        yr <- evalTypedValue (getTypeRepr xr) y
        return $ Some $ f n xr yr

  let bvRel :: (forall n . (1 <= n) => BVBinOp f n BoolType)
            -> m (Some (App () f))
      bvRel f = with2Args prim_op args $ \x y -> do
        SomeBV n xr <- evalBV x
        yr <- evalTypedValue (getTypeRepr xr) y
        return $ Some $ f n xr yr

  case prim_op of
    P.BoolNot -> withOneArg prim_op args $ \x ->
      def $ Not <$> defCoerce x
    P.BoolAnd -> with2Args prim_op args $ \x y -> do
      def $ And <$> defCoerce x
                  <*> defCoerce y
    P.BoolXor -> with2Args prim_op args $ \x y -> do
      def $ BoolXor <$> defCoerce x
                      <*> defCoerce y
    P.BoolIte -> with3Args prim_op args $ \c x y -> do
      def $ BoolIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y

    P.NatAdd -> with2Args prim_op args $ \x y -> do
      def $ NatAdd <$> defCoerce x
                     <*> defCoerce y
    P.NatMul -> with2Args prim_op args $ \x y -> do
      def $ NatMul <$> defCoerce x
                     <*> defCoerce y
    P.NatEq -> with2Args prim_op args $ \x y -> do
      def $ NatEq <$> defCoerce x
                    <*> defCoerce y
    P.NatLt -> with2Args prim_op args $ \x y -> do
      def $ NatLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Integers

    P.IntegerAdd -> with2Args prim_op args $ \x y -> do
      def $ IntAdd <$> defCoerce x
                     <*> defCoerce y
    P.IntegerSub -> with2Args prim_op args $ \x y -> do
      def $ IntSub <$> defCoerce x
                     <*> defCoerce y
    P.IntegerMul -> with2Args prim_op args $ \x y -> do
      def $ IntMul <$> defCoerce x
                     <*> defCoerce y
    P.IntegerEq -> with2Args prim_op args $ \x y -> do
      def $ IntEq <$> defCoerce x
                    <*> defCoerce y
    P.IntegerLt -> with2Args prim_op args $ \x y -> do
      def $ IntLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Reals

    P.RealAdd -> with2Args prim_op args $ \x y -> do
      def $ RealAdd <$> defCoerce x
                      <*> defCoerce y
    P.RealSub -> with2Args prim_op args $ \x y -> do
      def $ RealSub <$> defCoerce x
                      <*> defCoerce y
    P.RealMul -> with2Args prim_op args $ \x y -> do
      def $ RealMul <$> defCoerce x
                      <*> defCoerce y
    P.RealIte -> with3Args prim_op args $ \c x y -> do
      def $ RealIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y
    P.RealEq -> with2Args prim_op args $ \x y -> do
      def $ RealEq <$> defCoerce x
                     <*> defCoerce y
    P.RealLt -> with2Args prim_op args $ \x y -> do
      def $ RealLt <$> defCoerce x
                     <*> defCoerce y

    --------------------------------------------------------------------
    -- Bitvector operations

    P.BVAdd -> bvBinOp BVAdd
    P.BVSub -> bvBinOp BVSub
    P.BVMul -> bvBinOp BVMul
    P.BVUdiv -> bvBinOp BVUdiv
    P.BVUrem -> bvBinOp BVUrem
    P.BVSdiv -> bvBinOp BVSdiv
    P.BVSrem -> bvBinOp BVSrem
    P.BVIte -> with3Args prim_op args $ \c x y -> do
      cr <- defCoerce c :: m (f BoolType)
      SomeBV n xr <- evalBV x
      let tp = getTypeRepr xr
      yr <- evalTypedValue tp y
      return $ Some $ BVIte cr n xr yr
    P.BVEq  -> bvRel  BVEq
    P.BVUle -> bvRel  BVUle
    P.BVUlt -> bvRel  BVUlt
    P.BVSle -> bvRel BVSle
    P.BVSlt -> bvRel BVSlt
    P.BVCarry -> bvRel BVCarry
    P.BVSCarry -> bvRel BVSCarry
    P.BVSBorrow -> bvRel BVSBorrow

    P.BVShl -> bvBinOp BVShl
    P.BVLshr -> bvBinOp BVLshr
    P.BVAshr -> bvBinOp BVAshr
    P.BVNot -> withOneArg prim_op args $ \x -> do
      SomeBV n xr <- evalBV x
      return $ Some $ BVNot n xr
    P.BVAnd -> bvBinOp BVAnd
    P.BVOr  -> bvBinOp BVOr
    P.BVXor -> bvBinOp BVXor
    P.BoolToBV -> withOneArg prim_op args $ \x -> do
      rx <- evalTypedValue BoolRepr x
      case result_type of
        BVRepr result_width | Just LeqProof <- isPosNat result_width -> do
          return $ Some $ BoolToBV result_width rx
        _ -> X.throwM $ InvalidResultType "BoolToBV" result_type
    P.BVNonzero -> withOneArg prim_op args $ \x -> do
      SomeBV w xr <- evalBV x
      return $ Some $ BVNonzero w xr
    P.BVConcat -> with2Args prim_op args $ \x y -> do
      SomeBV w1 xr <- evalBV x
      SomeBV w2 yr <- evalBV y
      case isPosNat (addNat w1 w2) of
        Just LeqProof -> return $ Some $ BVConcat w1 w2 xr yr
        Nothing -> X.throwM $ BadResultWidth "BVConcat" (addNat w1 w2)
    P.BVSelect -> with3Args prim_op args $ \idx n x -> do
      Some idx_repr <- evalNatRepr idx
      Some n_repr   <- evalNatRepr n
      case isPosNat n_repr of
        Nothing -> X.throwM $ BadResultWidth "BVSelect" n_repr
        Just LeqProof -> do
          SomeBV w xr   <- evalBV x
          case (addNat idx_repr n_repr) `testLeq` w of
            Just LeqProof -> return $ Some $ BVSelect idx_repr n_repr w xr
            Nothing -> X.throwM $
                       OutOfBounds "BVSelect" (addNat idx_repr n_repr) w
    P.BVTrunc -> withOneArg prim_op args $ \x -> do
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width ->
          case isPosNat result_width of
            Just LeqProof ->
              case incNat result_width `testLeq` n of
                Just LeqProof -> return $ Some $ BVTrunc result_width n xr
                Nothing -> X.throwM $ OutOfBounds
                           "BVTrunc (larger than input)"
                           (incNat result_width) n
            Nothing -> X.throwM $ BadResultWidth "BVTrunc" result_width
        _ -> X.throwM $ InvalidResultType "BVTrunc" result_type
    P.BVZext -> withOneArg prim_op args $ \x -> do
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width ->
          case incNat n `testLeq` result_width of
            Just LeqProof -> return $ Some $ BVZext result_width n xr
            Nothing -> X.throwM $ OutOfBounds
                       "BVZext (less than input)"
                       (incNat n) result_width
        _ -> X.throwM $ InvalidResultType "BVZext" result_type
    P.BVSext -> withOneArg prim_op args $ \x -> do
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width ->
          case testLeq (incNat n) result_width of
            Just LeqProof -> return $ Some $ BVSext result_width n xr
            Nothing -> X.throwM $ OutOfBounds
                       "BVSext (less than input)"
                       (incNat n) result_width
        _ -> X.throwM $ InvalidResultType "BVSext" result_type

    --------------------------------------------------------------------
    -- Conversions

    P.NatToInteger -> withOneArg prim_op args $ \x -> do
      def $ NatToInteger <$> defCoerce x
    P.IntegerToReal -> withOneArg prim_op args $ \x -> do
      def $ IntegerToReal <$> defCoerce x

    --------------------------------------------------------------------
    -- WordMap Operations

    P.WordMapEmpty -> do
      case result_type of
        WordMapRepr w tp ->
          return $ Some $ EmptyWordMap w tp
        _ -> X.throwM $ InvalidResultType "WordMapEmpty" result_type

    P.WordMapInsert -> with3Args prim_op args $ \i v m -> do
       SomeBV w i' <- evalBV i
       Some v'     <- evalVal v
       case asBaseType (getTypeRepr v') of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Just LeqProof ->
               return $ Some $ InsertWordMap w bt i' v' m'
             Nothing -> X.throwM $ BadResultWidth "WordMapInsert word width" w
         _ -> X.throwM $ InvalidElementType "WordMapInsert" $ getTypeRepr v'

    P.WordMapLookup -> with2Args prim_op args $ \i m -> do
       SomeBV w i' <- evalBV i
       case asBaseType result_type of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Just LeqProof -> return $ Some $ LookupWordMap bt i' m'
             Nothing -> X.throwM $ BadResultWidth "WordMapLookup word width" w
         _ -> X.throwM $ InvalidElementType "WordMapLookup" result_type

    P.WordMapLookupWithDefault -> with3Args prim_op args $ \i m d -> do
       case asBaseType result_type of
         AsBaseType bt -> do
           SomeBV w i' <- evalBV i
           d'          <- evalTypedValue result_type d
           m'          <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Just LeqProof ->
               return $ Some $ LookupWordMapWithDefault bt i' m' d'
             Nothing -> X.throwM $ BadResultWidth
                        "WordMapLookupWithDefault word width" w
         _ -> X.throwM $ InvalidElementType
              "WordMapLookupWithDefault" result_type

    -----------------------------------------------------------------------
    -- Struct Operations

    P.StructLiteral -> do
      case result_type of
        StructRepr ctx_repr -> do
           let sz = Ctx.size ctx_repr
           when (Fold.length args /= Ctx.sizeInt sz) $
             X.throwM $ InvalidStructureArgCount "StructLiteral"
                        (Seq.length args) (Ctx.sizeInt sz)
           ctx <- Ctx.generateM (Ctx.size ctx_repr) $ \i -> do
                    let tp = ctx_repr Ctx.! i
                    evalTypedValue tp (Seq.index args (Ctx.indexVal i))
           return $ Some $ MkStruct ctx_repr ctx
        _ -> X.throwM $ InvalidResultType "StructLiteral" result_type

    P.StructSet -> with3Args prim_op args $ \s i x -> do
      case result_type of
        StructRepr ctx_repr -> do
           sv       <- evalTypedValue result_type s
           Some xv  <- evalVal x
           idx      <- evalCtxIndex i ctx_repr (getTypeRepr xv)
           return $ Some $ SetStruct ctx_repr sv idx xv
        _ -> X.throwM $ InvalidResultType "StructSet" result_type

    P.StructGet -> with2Args prim_op args $ \i s -> do
      Some sv <- evalVal s
      case getTypeRepr sv of
         StructRepr ctx_repr -> do
            idx <- evalCtxIndex i ctx_repr result_type
            return $ Some $ GetStruct sv idx result_type
         _ -> X.throwM $ InvalidResultType "StructGet" result_type

    --------------------------------------------------------------------
    -- Maybe Operations

    P.NothingValue -> do
      case result_type of
        MaybeRepr tp -> return $ Some $ NothingValue tp
        _ -> X.throwM $ InvalidResultType "NothingValue" result_type

    P.JustValue -> do
      case result_type of
        MaybeRepr tp -> withOneArg prim_op args $ \x -> do
          xr <- evalTypedValue tp x
          return $ Some $ JustValue tp xr
        _ -> X.throwM $ InvalidResultType "JustValue" result_type

    --------------------------------------------------------------------
    -- Debugging operations

    P.ShowValue -> do
      case result_type of
        StringRepr UnicodeRepr -> withOneArg prim_op args $ \x -> do
          Some v <- evalVal x
          case asBaseType (getTypeRepr v) of
            AsBaseType bt -> return $ Some $ ShowValue bt v
            NotBaseType -> X.throwM $ InvalidResultType
                           "ShowValue (expected base type)" $ getTypeRepr v
        _ -> X.throwM $ InvalidResultType "ShowValue" result_type

    --------------------------------------------------------------------
    -- Introspection operations

    P.IsConcrete -> do
      case result_type of
        BoolRepr -> withOneArg prim_op args $ \x -> do
          Some v <- evalVal x
          case asBaseType (getTypeRepr v) of
            AsBaseType bt -> return $ Some $ IsConcrete bt v
            NotBaseType -> X.throwM $ InvalidResultType
                           "IsConcrete (expected base type)" $ getTypeRepr v
        _ -> X.throwM $ InvalidResultType "IsConcrete" result_type

    --------------------------------------------------------------------
    -- Vector Operations

    P.VectorLit -> do
      case result_type of
        VectorRepr tp -> do
            xs <- mapM (evalTypedValue tp) (Fold.toList args)
            let v = V.fromList xs
            return $ Some $ VectorLit tp v
        _ -> X.throwM $ InvalidResultType "VectorLit" result_type

    P.VectorReplicate -> do
      case result_type of
        VectorRepr tp -> with2Args prim_op args $ \x n -> do
            nr <- defCoerce n
            xr <- evalTypedValue tp x
            return $ Some $ VectorReplicate tp nr xr
        _ -> X.throwM $ InvalidResultType "VectorRepr" result_type

    P.VectorSize -> withOneArg prim_op args $ \x -> do
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ VectorSize xr
        _ -> X.throwM $ InvalidResultType "VectorSize" result_type

    P.VectorIsEmpty -> withOneArg prim_op args $ \x -> do
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ VectorIsEmpty xr
        _ -> X.throwM $ InvalidResultType "VectorIsEmpty" result_type

    P.VectorGetEntry -> with2Args prim_op args $ \x n -> do
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      case getTypeRepr xr of
        VectorRepr tp -> return $ Some $ VectorGetEntry tp xr nr
        _ -> X.throwM $ InvalidResultType "VectorGetEntry" result_type

    P.VectorSetEntry -> with3Args prim_op args $ \x n a -> do
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      Some ar <- evalVal a
      case getTypeRepr xr of
        VectorRepr tp ->
           case testEquality tp (getTypeRepr ar) of
              Just Refl -> return $ Some $ VectorSetEntry tp xr nr ar
              _ -> X.throwM $ TypeMismatch "VectorSetEntry" tp $ getTypeRepr ar
        _ -> X.throwM $ InvalidArgumentType "VectorSetEntry" $ getTypeRepr xr
