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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Server.ValueConv where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Lens
import Control.Monad
import qualified Data.Sequence as Seq
import qualified Data.HashTable.IO as HIO
import Data.IORef
import qualified Data.Foldable as Fold
import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Vector as V


import Data.HPB
import Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx

import Lang.MATLAB.Utils.Nat (integerAsNat)

import qualified Lang.Crucible.Core as C
import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Server.Encoding
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Types
import qualified Lang.Crucible.RegCFG as R
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))


toByteString :: Builder -> BS.ByteString
toByteString b = LazyBS.toStrict (Builder.toLazyByteString b)

------------------------------------------------------------------------
-- RegEntry reference

newRegEntryRef :: Simulator sym -> RegEntry sym tp -> IO Word64
newRegEntryRef sim a = do
  cnt <- readIORef (simValueCounter sim)
  writeIORef (simValueCounter sim) $! cnt+1
  HIO.insert (simValueCache sim) cnt (Some a)
  return cnt

parseRegEntryRef :: Simulator sym -> Word64 -> IO (Some (RegEntry sym))
parseRegEntryRef sim w = do
  mv <- HIO.lookup (simValueCache sim) w
  case mv of
    Just v -> return v
    Nothing -> error "Could not find reg entry"

releaseRegEntryRef :: Simulator sym -> Word64 -> IO ()
releaseRegEntryRef sim w = do
  HIO.delete (simValueCache sim) w

------------------------------------------------------------------------
-- PValue encoding/decoding.

class HasTypeRepr f where
  getTypeRepr :: f tp -> TypeRepr tp

instance HasTypeRepr (RegEntry sym) where
  getTypeRepr (RegEntry tp _) = tp

instance HasTypeRepr (R.Expr s) where
  getTypeRepr = R.exprType

instance HasTypeRepr (R.Atom s) where
  getTypeRepr = R.typeOfAtom

checkedRegEntry :: (Monad m, HasTypeRepr f)
                => TypeRepr tp -> Some f -> m (f tp)
checkedRegEntry tp (Some r) =
  case testEquality tp (getTypeRepr r) of
    Just Refl -> return r
    Nothing -> fail "Unexpected type for protocol value."

fromProtoValue :: IsSymInterface sym => Simulator sym -> P.Value -> IO (Some (RegEntry sym))
fromProtoValue sim v = do
  sym <- getInterface sim
  case v^.P.value_code of
    P.ReferenceValue -> parseRegEntryRef sim (v^.P.value_index)
    P.TrueValue  -> return $ Some $ RegEntry BoolRepr $ truePred sym
    P.FalseValue -> return $ Some $ RegEntry BoolRepr $ falsePred sym
    P.NatValue -> do
      let i = decodeUnsigned (v^.P.value_data)
      case integerAsNat i of
        Just n -> Some . RegEntry NatRepr <$> natLit sym n
        Nothing -> fail "Integer is too large."
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
          let i = decodeUnsigned (v^.P.value_data)
          Some . RegEntry (BVRepr n) <$> bvLit sym n i
        _ -> error "Width is too large"
    P.StringValue -> do
      let s = v^.P.value_string_lit
      return $ Some $ RegEntry StringRepr s
    P.UnitValue -> do
      return $ Some $ RegEntry UnitRepr ()
    P.FnHandleValue -> do
      SomeHandle h <- getHandleBinding sim (v^.P.value_index)
      return $ Some $ RegEntry (handleType h) (HandleFnVal h)

toProtoValue :: IsSymInterface sym => Simulator sym -> RegEntry sym tp -> IO P.Value
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
    BVRepr w | Just r <- asUnsignedBV v
             , wv <- natValue w
             , wv <= toInteger (maxBound :: Word64) -> do
      return $ mempty & P.value_code  .~ P.BitvectorValue
                      & P.value_width .~ fromInteger wv
                      & P.value_data  .~ toByteString (encodeUnsigned r)
    StringRepr -> do
      return $ mempty & P.value_code .~ P.StringValue
                      & P.value_string_lit .~ v
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


parseNatRepr :: Monad m => P.Value -> m (Some NatRepr)
parseNatRepr v =
  case v^.P.value_code of
    P.NatValue -> do
      let i = decodeUnsigned (v^.P.value_data)
      case someNat i of
        Just rep -> return rep
        Nothing -> fail "improper negative Nat value in parseNatRepr"
    _ -> fail "expected Nat value in parseNatRepr"

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
type BVBinOp f n r = NatRepr n -> f (BVType n) -> f (BVType n) -> C.App f r

-- | A symbolic bitvector expression with some bitwidth.
data SomeBV f = forall n . (1 <= n) => SomeBV (NatRepr n) (f (BVType n))

-- | A symbolic signed bitvector expression with some bitwidth.
data SomeSBV f = forall n . (1 <= n) => SomeSBV (NatRepr n) (f (BVType n))

convertToCrucibleApp :: (Applicative m, Monad m, HasTypeRepr f)
                     => (a -> m (Some f))
                     -> (a -> m (Some NatRepr))
                     -> P.PrimitiveOp
                     -> Seq a
                     -> P.CrucibleType
                     -> m (Some (C.App f))
convertToCrucibleApp evalVal evalNatRepr prim_op args res_type = do
  Some res_tp <- fromProtoType res_type
  convertToCrucibleApp' evalVal evalNatRepr prim_op args res_tp

convertToCrucibleApp' :: forall a f res_tp m
                       . (Applicative m, Monad m, HasTypeRepr f)
                      => (a -> m (Some f))
                      -> (a -> m (Some NatRepr))
                         -- ^ Parse argument as a concrete nat.
                      -> P.PrimitiveOp
                      -> Seq a
                      -> TypeRepr res_tp
                      -> m (Some (C.App f))
convertToCrucibleApp' evalVal evalNatRepr prim_op args result_type = do
  let getArgs :: Monad m => Int -> m [a]
      getArgs n | Seq.length args == n = return $ Fold.toList args
                | otherwise = fail $ "Unexpected number of arguments: "
                                      ++ (show prim_op) ++ " " ++ show (Seq.length args)

  let evalTypedValue :: TypeRepr tp -> a -> m (f tp)
      evalTypedValue tp v = checkedRegEntry tp =<< evalVal v

  -- Gets a bitvector value.
  let evalBV :: a -> m (SomeBV f)
      evalBV v = do
        Some r <- evalVal v
        case getTypeRepr r of
          BVRepr n -> return (SomeBV n r)
          _ -> fail "Expected bitvector expression."
  -- Gets a bitvector value.
  let evalSBV :: a -> m (SomeSBV f)
      evalSBV v = do
        SomeBV n r <- evalBV v
        case isPosNat n of
          Nothing -> fail "Expected positive width."
          Just LeqProof -> return $ SomeSBV n r

  let evalCtxIndex :: a -> CtxRepr ctx -> TypeRepr tp -> m (Ctx.Index ctx tp)
      evalCtxIndex a ctx_repr ty_repr = do
          Some i <- evalNatRepr a
          case Ctx.intIndex (fromIntegral (natValue i)) (Ctx.size ctx_repr) of
             Just (Some idx) ->
                case testEquality (ctx_repr Ctx.! idx) ty_repr of
                   Just Refl -> return idx
                   Nothing -> fail $ "Type mismatch with structure index" ++ show i
             Nothing -> fail $ "Invalid structure index" ++ show i

  let defCoerce :: KnownRepr TypeRepr tp => a -> m (f tp)
      defCoerce v = evalTypedValue knownRepr v

  let def :: m (C.App f tp) -> m (Some (C.App f))
      def a = Some <$> a

  let bvBinOp :: (forall n . (1 <= n) => BVBinOp f n (BVType n))
              -> m (Some (C.App f))
      bvBinOp f = do
        [x, y] <- getArgs 2
        SomeSBV n xr <- evalSBV x
        let tp = getTypeRepr xr
        yr <- evalTypedValue tp y
        return $ Some $ f n xr yr

  let bvsBinOp :: (forall n . (1 <= n) => BVBinOp f n (BVType n))
               -> m (Some (C.App f))
      bvsBinOp f = do
        [x, y] <- getArgs 2
        SomeSBV n xr <- evalSBV x
        let tp = getTypeRepr xr
        yr <- checkedRegEntry tp =<< evalVal y
        return $ Some $ f n xr yr

  let bvRel :: (forall n . (1 <= n) => BVBinOp f n BoolType)
            -> m (Some (C.App f))
      bvRel f = do
        [x, y] <- getArgs 2
        SomeSBV n xr <- evalSBV x
        yr <- evalTypedValue (getTypeRepr xr) y
        return $ Some $ f n xr yr

  let bvsRel :: (forall n . (1 <= n) => BVBinOp f n BoolType)
             -> m (Some (C.App f))
      bvsRel f = do
        [x, y] <- getArgs 2
        SomeSBV n xr <- evalSBV x
        let tp = getTypeRepr xr
        yr <- checkedRegEntry tp =<< evalVal y
        return $ Some $ f n xr yr

  case prim_op of
    P.BoolNot -> do
      [x] <- getArgs 1
      def $ C.Not <$> defCoerce x
    P.BoolAnd -> do
      [x,y] <- getArgs 2
      def $ C.And <$> defCoerce x
                  <*> defCoerce y
    P.BoolXor -> do
      [x,y] <- getArgs 2
      def $ C.BoolXor <$> defCoerce x
                      <*> defCoerce y
    P.BoolIte -> do
      [c,x,y] <- getArgs 3
      def $ C.BoolIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y

    P.NatAdd -> do
      [x,y] <- getArgs 2
      def $ C.NatAdd <$> defCoerce x
                     <*> defCoerce y
    P.NatMul -> do
      [x,y] <- getArgs 2
      def $ C.NatMul <$> defCoerce x
                     <*> defCoerce y
    P.NatEq -> do
      [x,y] <- getArgs 2
      def $ C.NatEq <$> defCoerce x
                    <*> defCoerce y
    P.NatLt -> do
      [x,y] <- getArgs 2
      def $ C.NatLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Integers

    P.IntegerAdd -> do
      [x,y] <- getArgs 2
      def $ C.IntAdd <$> defCoerce x
                     <*> defCoerce y
    P.IntegerSub -> do
      [x,y] <- getArgs 2
      def $ C.IntSub <$> defCoerce x
                     <*> defCoerce y
    P.IntegerMul -> do
      [x,y] <- getArgs 2
      def $ C.IntMul <$> defCoerce x
                     <*> defCoerce y
    P.IntegerEq -> do
      [x,y] <- getArgs 2
      def $ C.IntEq <$> defCoerce x
                    <*> defCoerce y
    P.IntegerLt -> do
      [x,y] <- getArgs 2
      def $ C.IntLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Reals

    P.RealAdd -> do
      [x,y] <- getArgs 2
      def $ C.RealAdd <$> defCoerce x
                      <*> defCoerce y
    P.RealSub -> do
      [x,y] <- getArgs 2
      def $ C.RealSub <$> defCoerce x
                      <*> defCoerce y
    P.RealMul -> do
      [x,y] <- getArgs 2
      def $ C.RealMul <$> defCoerce x
                      <*> defCoerce y
    P.RealIte -> do
      [c,x,y] <- getArgs 3
      def $ C.RealIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y
    P.RealEq -> do
      [x,y] <- getArgs 2
      def $ C.RealEq <$> defCoerce x
                     <*> defCoerce y
    P.RealLt -> do
      [x,y] <- getArgs 2
      def $ C.RealLt <$> defCoerce x
                     <*> defCoerce y

    --------------------------------------------------------------------
    -- Bitvector operations

    P.BVAdd -> bvBinOp C.BVAdd
    P.BVSub -> bvBinOp C.BVSub
    P.BVMul -> bvBinOp C.BVMul
    P.BVUdiv -> bvBinOp  C.BVUdiv
    P.BVUrem -> bvBinOp  C.BVUrem
    P.BVSdiv -> bvsBinOp C.BVSdiv
    P.BVSrem -> bvsBinOp C.BVSrem
    P.BVIte -> do
      [c,x,y] <- getArgs 3
      cr <- defCoerce c :: m (f BoolType)
      SomeSBV n xr <- evalSBV x
      let tp = getTypeRepr xr
      yr <- evalTypedValue tp y
      return $ Some $ C.BVIte cr n xr yr
    P.BVEq  -> bvRel  C.BVEq
    P.BVUle -> bvRel  C.BVUle
    P.BVUlt -> bvRel  C.BVUlt
    P.BVSle -> bvsRel C.BVSle
    P.BVSlt -> bvsRel C.BVSlt
    P.BVCarry -> bvRel C.BVCarry
    P.BVSCarry -> bvsRel C.BVSCarry
    P.BVSBorrow -> bvsRel C.BVSBorrow

    P.BVShl -> bvBinOp C.BVShl
    P.BVLshr -> bvBinOp C.BVLshr
    P.BVAshr -> bvsBinOp C.BVAshr
    P.BVNot -> do
      [x] <- getArgs 1
      SomeSBV n xr <- evalSBV x
      return $ Some $ C.BVNot n xr
    P.BVAnd -> bvBinOp C.BVAnd
    P.BVOr  -> bvBinOp C.BVOr
    P.BVXor -> bvBinOp C.BVXor
    P.BoolToBV -> do
      [x] <- getArgs 1
      rx <- evalTypedValue BoolRepr x
      case result_type of
        BVRepr result_width | Just LeqProof <- isPosNat result_width -> do
          return $ Some $ C.BoolToBV result_width rx
        _ -> fail "Invalid result type"
    P.BVNonzero -> do
      [x] <- getArgs 1
      SomeSBV w xr <- evalSBV x
      return $ Some $ C.BVNonzero w xr
    P.BVConcat -> do
      [x,y] <- getArgs 2
      SomeSBV w1 xr <- evalSBV x
      SomeSBV w2 yr <- evalSBV y
      Just LeqProof <- return $ isPosNat (addNat w1 w2)
      return $ Some $ C.BVConcat w1 w2 xr yr
    P.BVSelect -> do
      [idx,n,x] <- getArgs 3
      Some idx_repr <- evalNatRepr idx
      Some n_repr   <- evalNatRepr n
      case isPosNat n_repr of
        Nothing -> fail $ "BVSelect given bad result width."
        Just LeqProof -> do
          SomeSBV w xr   <- evalSBV x
          case (addNat idx_repr n_repr) `testLeq` w of
            Just LeqProof -> return $ Some $ C.BVSelect idx_repr n_repr w xr
            Nothing -> fail $ "Invalid bitvector select: out of bounds"
    P.BVTrunc -> do
      [x] <- getArgs 1
      SomeSBV n xr <- evalSBV x
      case result_type of
        BVRepr result_width | Just LeqProof <- isPosNat result_width ->
          case incNat result_width `testLeq` n of
            Just LeqProof -> return $ Some $ C.BVTrunc result_width n xr
            Nothing -> fail $ "Result width is larger than input."
        _ -> fail "Invalid result type"
    P.BVZext -> do
      [x] <- getArgs 1
      SomeSBV n xr <- evalSBV x
      case result_type of
        BVRepr result_width ->
          case incNat n `testLeq` result_width of
            Just LeqProof -> do
              return $ Some $ C.BVZext result_width n xr
            Nothing -> fail $ "Result width is less than input."
        _ -> fail "Invalid result type"
    P.BVSext -> do
      [x] <- getArgs 1
      SomeSBV n xr <- evalSBV x
      case result_type of
        BVRepr result_width ->
          case testLeq (incNat n) result_width of
            Just LeqProof -> return $ Some $ C.BVSext result_width n xr
            Nothing -> fail $ "Result width is less than input."
        _ -> fail "Invalid result type"

    --------------------------------------------------------------------
    -- Conversions

    P.NatToInteger -> do
      [x] <- getArgs 1
      def $ C.NatToInteger <$> defCoerce x
    P.IntegerToReal -> do
      [x] <- getArgs 1
      def $ C.IntegerToReal <$> defCoerce x

    --------------------------------------------------------------------
    -- WordMap Operations

    P.WordMapEmpty -> do
      case result_type of
        WordMapRepr w tp ->
          return $ Some $ C.EmptyWordMap w tp
        _ -> fail "invalid result type"

    P.WordMapInsert -> do
       [i,v,m] <- getArgs 3
       SomeSBV w i' <- evalSBV i
       Some v'      <- evalVal v
       case asBaseType (getTypeRepr v') of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Just LeqProof ->
               return $ Some $ C.InsertWordMap w bt i' v' m'
             Nothing -> fail ("Invalid word width" ++ show w)
         _ -> fail ("Invalid word map element type: " ++ (show $ getTypeRepr v'))

    P.WordMapLookup -> do
       [i,m] <- getArgs 2
       SomeSBV w i' <- evalSBV i
       case asBaseType result_type of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Nothing -> fail ("Invalid word width" ++ show w)
             Just LeqProof ->
               return $ Some $ C.LookupWordMap bt i' m'
         _ -> fail ("Invalid word map element type: " ++ show result_type)

    P.WordMapLookupWithDefault -> do
       [i,m,d] <- getArgs 3
       case asBaseType result_type of
         AsBaseType bt -> do
           SomeSBV w i' <- evalSBV i
           d'           <- evalTypedValue result_type d
           m'           <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Nothing -> fail ("Invalid word width" ++ show w)
             Just LeqProof ->
               return $ Some $ C.LookupWordMapWithDefault bt i' m' d'
         _ -> fail ("Invalid word map element type: " ++ show result_type)

    -----------------------------------------------------------------------
    -- Struct Operations

    P.StructLiteral -> do
      case result_type of
        StructRepr ctx_repr -> do
           when (Seq.length args /= Ctx.sizeInt (Ctx.size ctx_repr))
                (fail "argument list length does not match expected structure type when building a structure literal")
           ctx <- Ctx.generateM (Ctx.size ctx_repr) $ \i -> do
                    let tp = ctx_repr Ctx.! i
                    evalTypedValue tp (Seq.index args (Ctx.indexVal i))
           return $ Some $ C.MkStruct ctx_repr ctx
        _ -> fail "Expected structure type"

    P.StructSet -> do
      [s,i,x] <- getArgs 3
      case result_type of
        StructRepr ctx_repr -> do
           sv       <- evalTypedValue result_type s
           Some xv  <- evalVal x
           idx      <- evalCtxIndex i ctx_repr (getTypeRepr xv)
           return $ Some $ C.SetStruct ctx_repr sv idx xv
        _ -> fail "Expected structure type"

    P.StructGet -> do
      [i,s] <- getArgs 2
      Some sv <- evalVal s
      case getTypeRepr sv of
         StructRepr ctx_repr -> do
            idx <- evalCtxIndex i ctx_repr result_type
            return $ Some $ C.GetStruct sv idx result_type
         _ -> fail "Expected structure type"

    --------------------------------------------------------------------
    -- Maybe Operations

    P.NothingValue -> do
      case result_type of
        MaybeRepr tp -> return $ Some $ C.NothingValue tp
        _ -> fail "invalid result type"

    P.JustValue -> do
      case result_type of
        MaybeRepr tp -> do
          [x] <- getArgs 1
          xr <- evalTypedValue tp x
          return $ Some $ C.JustValue tp xr
        _ -> fail "invalid result type"

    --------------------------------------------------------------------
    -- Debugging operations

    P.ShowValue -> do
      case result_type of
        StringRepr -> do
          [x] <- getArgs 1
          Some v <- evalVal x
          case asBaseType (getTypeRepr v) of
            AsBaseType bt -> return $ Some $ C.ShowValue bt v
            NotBaseType -> fail "Expected a base type"
        _ -> fail "invalid result type"

    --------------------------------------------------------------------
    -- Introspection operations

    P.IsConcrete -> do
      case result_type of
        BoolRepr -> do
          [x] <- getArgs 1
          Some v <- evalVal x
          case asBaseType (getTypeRepr v) of
            AsBaseType bt -> return $ Some $ C.IsConcrete bt v
            NotBaseType -> fail "Expected a base type"
        _ -> fail "invalid result type"

    --------------------------------------------------------------------
    -- Vector Operations

    P.VectorLit -> do
      case result_type of
        VectorRepr tp -> do
            xs <- sequence $ map (evalTypedValue tp) $ Fold.toList args
            let v = V.fromList xs
            return $ Some $ C.VectorLit tp v
        _ -> fail "invalid result type"

    P.VectorReplicate -> do
      case result_type of
        VectorRepr tp -> do
            [n,x] <- getArgs 2
            nr <- defCoerce n
            xr <- evalTypedValue tp x
            return $ Some $ C.VectorReplicate tp nr xr
        _ -> fail "invalid result type"

    P.VectorSize -> do
      [x] <- getArgs 1
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ C.VectorSize xr
        _ -> fail "invalid argument to VectorSize"

    P.VectorIsEmpty -> do
      [x] <- getArgs 1
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ C.VectorIsEmpty xr
        _ -> fail "invalid argument to VectorIsEmpty"

    P.VectorGetEntry -> do
      [x,n] <- getArgs 2
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      case getTypeRepr xr of
        VectorRepr tp -> return $ Some $ C.VectorGetEntry tp xr nr
        _ -> fail "invalid argument to VectorGetEntry"

    P.VectorSetEntry -> do
      [x,n,a] <- getArgs 3
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      Some ar <- evalVal a
      case getTypeRepr xr of
        VectorRepr tp ->
           case testEquality tp (getTypeRepr ar) of
              Just Refl -> return $ Some $ C.VectorSetEntry tp xr nr ar
              _ -> fail "type mismatch in VectorSetEntry"
        _ -> fail "invalid argument to VectorSetEntry"
