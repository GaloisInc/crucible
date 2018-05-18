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

checkedRegEntry :: (Monad m, HasTypeRepr f)
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
          Some . RegEntry (BVRepr n) <$> bvLit sym n i
        _ -> error "Width is too large"
    P.StringValue -> do
      let s = v^.P.value_string_lit
      Some . RegEntry StringRepr <$> stringLit sym s
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
    BVRepr w | Just r <- asSignedBV v
             , wv <- natValue w
             , wv <= toInteger (maxBound :: Word64) -> do
      return $ mempty & P.value_code  .~ P.BitvectorValue
                      & P.value_width .~ fromInteger wv
                      & P.value_data  .~ toByteString (encodeSigned r)
    StringRepr
      | Just txt <- asString v -> do
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
type BVBinOp f n r = NatRepr n -> f (BVType n) -> f (BVType n) -> App () f r

-- | A symbolic bitvector expression with some bitwidth.
data SomeBV f = forall n . (1 <= n) => SomeBV (NatRepr n) (f (BVType n))

convertToCrucibleApp :: (Applicative m, Monad m, HasTypeRepr f)
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
                       . (Applicative m, Monad m, HasTypeRepr f)
                      => (a -> m (Some f))
                      -> (a -> m (Some NatRepr))
                         -- ^ Parse argument as a concrete nat.
                      -> P.PrimitiveOp
                      -> Seq a
                      -> TypeRepr res_tp
                      -> m (Some (App () f))
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

  let def :: m (App () f tp) -> m (Some (App () f))
      def a = Some <$> a

  let bvBinOp :: (forall n . (1 <= n) => BVBinOp f n (BVType n))
              -> m (Some (App () f))
      bvBinOp f = do
        [x, y] <- getArgs 2
        SomeBV n xr <- evalBV x
        let tp = getTypeRepr xr
        yr <- evalTypedValue tp y
        return $ Some $ f n xr yr

  let bvRel :: (forall n . (1 <= n) => BVBinOp f n BoolType)
            -> m (Some (App () f))
      bvRel f = do
        [x, y] <- getArgs 2
        SomeBV n xr <- evalBV x
        yr <- evalTypedValue (getTypeRepr xr) y
        return $ Some $ f n xr yr

  case prim_op of
    P.BoolNot -> do
      [x] <- getArgs 1
      def $ Not <$> defCoerce x
    P.BoolAnd -> do
      [x,y] <- getArgs 2
      def $ And <$> defCoerce x
                  <*> defCoerce y
    P.BoolXor -> do
      [x,y] <- getArgs 2
      def $ BoolXor <$> defCoerce x
                      <*> defCoerce y
    P.BoolIte -> do
      [c,x,y] <- getArgs 3
      def $ BoolIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y

    P.NatAdd -> do
      [x,y] <- getArgs 2
      def $ NatAdd <$> defCoerce x
                     <*> defCoerce y
    P.NatMul -> do
      [x,y] <- getArgs 2
      def $ NatMul <$> defCoerce x
                     <*> defCoerce y
    P.NatEq -> do
      [x,y] <- getArgs 2
      def $ NatEq <$> defCoerce x
                    <*> defCoerce y
    P.NatLt -> do
      [x,y] <- getArgs 2
      def $ NatLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Integers

    P.IntegerAdd -> do
      [x,y] <- getArgs 2
      def $ IntAdd <$> defCoerce x
                     <*> defCoerce y
    P.IntegerSub -> do
      [x,y] <- getArgs 2
      def $ IntSub <$> defCoerce x
                     <*> defCoerce y
    P.IntegerMul -> do
      [x,y] <- getArgs 2
      def $ IntMul <$> defCoerce x
                     <*> defCoerce y
    P.IntegerEq -> do
      [x,y] <- getArgs 2
      def $ IntEq <$> defCoerce x
                    <*> defCoerce y
    P.IntegerLt -> do
      [x,y] <- getArgs 2
      def $ IntLt <$> defCoerce x
                    <*> defCoerce y

    --------------------------------------------------------------------
    -- Operations on Reals

    P.RealAdd -> do
      [x,y] <- getArgs 2
      def $ RealAdd <$> defCoerce x
                      <*> defCoerce y
    P.RealSub -> do
      [x,y] <- getArgs 2
      def $ RealSub <$> defCoerce x
                      <*> defCoerce y
    P.RealMul -> do
      [x,y] <- getArgs 2
      def $ RealMul <$> defCoerce x
                      <*> defCoerce y
    P.RealIte -> do
      [c,x,y] <- getArgs 3
      def $ RealIte <$> defCoerce c
                      <*> defCoerce x
                      <*> defCoerce y
    P.RealEq -> do
      [x,y] <- getArgs 2
      def $ RealEq <$> defCoerce x
                     <*> defCoerce y
    P.RealLt -> do
      [x,y] <- getArgs 2
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
    P.BVIte -> do
      [c,x,y] <- getArgs 3
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
    P.BVNot -> do
      [x] <- getArgs 1
      SomeBV n xr <- evalBV x
      return $ Some $ BVNot n xr
    P.BVAnd -> bvBinOp BVAnd
    P.BVOr  -> bvBinOp BVOr
    P.BVXor -> bvBinOp BVXor
    P.BoolToBV -> do
      [x] <- getArgs 1
      rx <- evalTypedValue BoolRepr x
      case result_type of
        BVRepr result_width | Just LeqProof <- isPosNat result_width -> do
          return $ Some $ BoolToBV result_width rx
        _ -> fail "Invalid result type"
    P.BVNonzero -> do
      [x] <- getArgs 1
      SomeBV w xr <- evalBV x
      return $ Some $ BVNonzero w xr
    P.BVConcat -> do
      [x,y] <- getArgs 2
      SomeBV w1 xr <- evalBV x
      SomeBV w2 yr <- evalBV y
      Just LeqProof <- return $ isPosNat (addNat w1 w2)
      return $ Some $ BVConcat w1 w2 xr yr
    P.BVSelect -> do
      [idx,n,x] <- getArgs 3
      Some idx_repr <- evalNatRepr idx
      Some n_repr   <- evalNatRepr n
      case isPosNat n_repr of
        Nothing -> fail $ "BVSelect given bad result width."
        Just LeqProof -> do
          SomeBV w xr   <- evalBV x
          case (addNat idx_repr n_repr) `testLeq` w of
            Just LeqProof -> return $ Some $ BVSelect idx_repr n_repr w xr
            Nothing -> fail $ "Invalid bitvector select: out of bounds"
    P.BVTrunc -> do
      [x] <- getArgs 1
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width | Just LeqProof <- isPosNat result_width ->
          case incNat result_width `testLeq` n of
            Just LeqProof -> return $ Some $ BVTrunc result_width n xr
            Nothing -> fail $ "Result width is larger than input."
        _ -> fail "Invalid result type"
    P.BVZext -> do
      [x] <- getArgs 1
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width ->
          case incNat n `testLeq` result_width of
            Just LeqProof -> do
              return $ Some $ BVZext result_width n xr
            Nothing -> fail $ "Result width is less than input."
        _ -> fail "Invalid result type"
    P.BVSext -> do
      [x] <- getArgs 1
      SomeBV n xr <- evalBV x
      case result_type of
        BVRepr result_width ->
          case testLeq (incNat n) result_width of
            Just LeqProof -> return $ Some $ BVSext result_width n xr
            Nothing -> fail $ "Result width is less than input."
        _ -> fail "Invalid result type"

    --------------------------------------------------------------------
    -- Conversions

    P.NatToInteger -> do
      [x] <- getArgs 1
      def $ NatToInteger <$> defCoerce x
    P.IntegerToReal -> do
      [x] <- getArgs 1
      def $ IntegerToReal <$> defCoerce x

    --------------------------------------------------------------------
    -- WordMap Operations

    P.WordMapEmpty -> do
      case result_type of
        WordMapRepr w tp ->
          return $ Some $ EmptyWordMap w tp
        _ -> fail "invalid result type"

    P.WordMapInsert -> do
       [i,v,m] <- getArgs 3
       SomeBV w i' <- evalBV i
       Some v'     <- evalVal v
       case asBaseType (getTypeRepr v') of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Just LeqProof ->
               return $ Some $ InsertWordMap w bt i' v' m'
             Nothing -> fail ("Invalid word width" ++ show w)
         _ -> fail ("Invalid word map element type: " ++ (show $ getTypeRepr v'))

    P.WordMapLookup -> do
       [i,m] <- getArgs 2
       SomeBV w i' <- evalBV i
       case asBaseType result_type of
         AsBaseType bt -> do
           m' <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Nothing -> fail ("Invalid word width" ++ show w)
             Just LeqProof ->
               return $ Some $ LookupWordMap bt i' m'
         _ -> fail ("Invalid word map element type: " ++ show result_type)

    P.WordMapLookupWithDefault -> do
       [i,m,d] <- getArgs 3
       case asBaseType result_type of
         AsBaseType bt -> do
           SomeBV w i' <- evalBV i
           d'          <- evalTypedValue result_type d
           m'          <- evalTypedValue (WordMapRepr w bt) m
           case isPosNat w of
             Nothing -> fail ("Invalid word width" ++ show w)
             Just LeqProof ->
               return $ Some $ LookupWordMapWithDefault bt i' m' d'
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
           return $ Some $ MkStruct ctx_repr ctx
        _ -> fail "Expected structure type"

    P.StructSet -> do
      [s,i,x] <- getArgs 3
      case result_type of
        StructRepr ctx_repr -> do
           sv       <- evalTypedValue result_type s
           Some xv  <- evalVal x
           idx      <- evalCtxIndex i ctx_repr (getTypeRepr xv)
           return $ Some $ SetStruct ctx_repr sv idx xv
        _ -> fail "Expected structure type"

    P.StructGet -> do
      [i,s] <- getArgs 2
      Some sv <- evalVal s
      case getTypeRepr sv of
         StructRepr ctx_repr -> do
            idx <- evalCtxIndex i ctx_repr result_type
            return $ Some $ GetStruct sv idx result_type
         _ -> fail "Expected structure type"

    --------------------------------------------------------------------
    -- Maybe Operations

    P.NothingValue -> do
      case result_type of
        MaybeRepr tp -> return $ Some $ NothingValue tp
        _ -> fail "invalid result type"

    P.JustValue -> do
      case result_type of
        MaybeRepr tp -> do
          [x] <- getArgs 1
          xr <- evalTypedValue tp x
          return $ Some $ JustValue tp xr
        _ -> fail "invalid result type"

    --------------------------------------------------------------------
    -- Debugging operations

    P.ShowValue -> do
      case result_type of
        StringRepr -> do
          [x] <- getArgs 1
          Some v <- evalVal x
          case asBaseType (getTypeRepr v) of
            AsBaseType bt -> return $ Some $ ShowValue bt v
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
            AsBaseType bt -> return $ Some $ IsConcrete bt v
            NotBaseType -> fail "Expected a base type"
        _ -> fail "invalid result type"

    --------------------------------------------------------------------
    -- Vector Operations

    P.VectorLit -> do
      case result_type of
        VectorRepr tp -> do
            xs <- sequence $ map (evalTypedValue tp) $ Fold.toList args
            let v = V.fromList xs
            return $ Some $ VectorLit tp v
        _ -> fail "invalid result type"

    P.VectorReplicate -> do
      case result_type of
        VectorRepr tp -> do
            [n,x] <- getArgs 2
            nr <- defCoerce n
            xr <- evalTypedValue tp x
            return $ Some $ VectorReplicate tp nr xr
        _ -> fail "invalid result type"

    P.VectorSize -> do
      [x] <- getArgs 1
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ VectorSize xr
        _ -> fail "invalid argument to VectorSize"

    P.VectorIsEmpty -> do
      [x] <- getArgs 1
      Some xr <- evalVal x
      case getTypeRepr xr of
        VectorRepr _tp -> return $ Some $ VectorIsEmpty xr
        _ -> fail "invalid argument to VectorIsEmpty"

    P.VectorGetEntry -> do
      [x,n] <- getArgs 2
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      case getTypeRepr xr of
        VectorRepr tp -> return $ Some $ VectorGetEntry tp xr nr
        _ -> fail "invalid argument to VectorGetEntry"

    P.VectorSetEntry -> do
      [x,n,a] <- getArgs 3
      Some xr <- evalVal x
      nr <- evalTypedValue NatRepr n
      Some ar <- evalVal a
      case getTypeRepr xr of
        VectorRepr tp ->
           case testEquality tp (getTypeRepr ar) of
              Just Refl -> return $ Some $ VectorSetEntry tp xr nr ar
              _ -> fail "type mismatch in VectorSetEntry"
        _ -> fail "invalid argument to VectorSetEntry"
