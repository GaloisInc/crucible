{-|
Module     : What4.Expr.MATLAB
Copyright  : (c) Galois, Inc, 2016
License    : BSD3
Maintainer : Joe Hendrix <jhendrix@galois.com>

This module provides an interface that a symbolic backend should
implement to support MATLAB intrinsics.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module What4.Expr.MATLAB
  ( MatlabSolverFn(..)
  , matlabSolverArgTypes
  , matlabSolverReturnType
  , ppMatlabSolverFn
  , evalMatlabSolverFn
  , testSolverFnEq
  , traverseMatlabSolverFn
  , MatlabSymbolicArrayBuilder(..)

    -- * Utilities for definition
  , clampedIntAdd
  , clampedIntSub
  , clampedIntMul
  , clampedIntNeg
  , clampedIntAbs
  , clampedUIntAdd
  , clampedUIntSub
  , clampedUIntMul
  ) where

import           Control.Monad (join)
import           Data.Kind (Type)
import           Data.Hashable
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.BaseTypes
import           What4.Interface
import           What4.Utils.Complex
import           What4.Utils.OnlyNatRepr

------------------------------------------------------------------------
-- MatlabSolverFn


clampedIntAdd :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntAdd sym x y = do
  let w = bvWidth x
  withAddPrefixLeq w (knownNat :: NatRepr 1) $ do
  -- Compute result with 1 additional bit to catch clamping
  let w' = incNat w
  x'  <- bvSext sym w' x
  y'  <- bvSext sym w' y
  -- Compute result.
  r'  <- bvAdd sym x' y'

  -- Check is result is greater than or equal to max value.
  too_high <- bvSgt sym r' =<< bvLit sym w' (maxSigned w)
  max_int <- bvLit sym w (maxSigned w)

  -- Check is result is less than min value.
  too_low <- bvSlt sym r' =<< bvLit sym w' (minSigned w)
  min_int <- bvLit sym w (minSigned w)

  -- Clamp integer range.
  r <- bvTrunc sym w r'
  r_low <- bvIte sym too_low min_int r
  bvIte sym too_high max_int r_low

clampedIntSub :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntSub sym x y = do
  let w = bvWidth x
  (ov, xy) <- subSignedOF sym x y
  ysign  <- bvIsNeg sym y
  minint <- minSignedBV sym w
  maxint <- maxSignedBV sym w
  ov_val <- bvIte sym ysign maxint minint
  bvIte sym ov ov_val xy

clampedIntMul :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntMul sym x y = do
  let w = bvWidth x
  (hi,lo) <- signedWideMultiplyBV sym x y
  zro    <- bvLit sym w 0
  ones   <- maxUnsignedBV sym w
  ok_pos <- join $ andPred sym <$> (notPred sym =<< bvIsNeg sym lo)
                              <*> bvEq sym hi zro
  ok_neg <- join $ andPred sym <$> bvIsNeg sym lo
                              <*> bvEq sym hi ones
  ov     <- notPred sym =<< orPred sym ok_pos ok_neg

  minint <- minSignedBV sym w
  maxint <- maxSignedBV sym w
  hisign <- bvIsNeg sym hi
  ov_val <- bvIte sym hisign minint maxint
  bvIte sym ov ov_val lo


-- | Compute the clamped negation of a signed bitvector.
--
--   The only difference between this operation and the usual
--   2's complement negation function is the handling of MIN_INT.
--   The usual 2's complement negation sends MIN_INT to MIN_INT;
--   however, the clamped version instead sends MIN_INT to MAX_INT.
clampedIntNeg :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntNeg sym x = do
  let w = bvWidth x
  minint <- minSignedBV sym w

  -- return maxint when x == minint, and neg(x) otherwise
  p <- bvEq sym x minint
  iteM bvIte sym p (maxSignedBV sym w) (bvNeg sym x)

-- | Compute the clamped absolute value of a signed bitvector.
--
--   The only difference between this operation and the usual 2's
--   complement operation is the handling of MIN_INT.  The usual 2's
--   complement absolute value function sends MIN_INT to MIN_INT;
--   however, the clamped version instead sends MIN_INT to MAX_INT.
clampedIntAbs :: (IsExprBuilder sym, 1 <= w)
              => sym
              -> SymBV sym w
              -> IO (SymBV sym w)
clampedIntAbs sym x = do
  isNeg  <- bvIsNeg sym x
  iteM bvIte sym isNeg (clampedIntNeg sym x) (pure x)


clampedUIntAdd :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntAdd sym x y = do
  let w = bvWidth x
  (ov, xy) <- addUnsignedOF sym x y
  maxint   <- maxUnsignedBV sym w
  bvIte sym ov maxint xy

clampedUIntSub :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntSub sym x y = do
  let w = bvWidth x
  no_underflow <- bvUge sym x y

  iteM bvIte
       sym
       no_underflow
       (bvSub sym x y) -- Perform subtraction if y >= x
       (bvLit sym w 0) -- Otherwise return min int

clampedUIntMul :: (IsExprBuilder sym, 1 <= w)
               => sym
               -> SymBV sym w
               -> SymBV sym w
               -> IO (SymBV sym w)
clampedUIntMul sym x y = do
  let w = bvWidth x
  (hi, lo) <- unsignedWideMultiplyBV sym x y
  maxint   <- maxUnsignedBV sym w
  ov       <- bvIsNonzero sym hi
  bvIte sym ov maxint lo

------------------------------------------------------------------------
-- MatlabSolverFn

-- | Builtin functions that can be used to generate symbolic functions.
--
-- These functions are expected to be total, but the value returned may not be
-- specified.  e.g. 'IntegerToNatFn' must return some natural number for every
-- integer, but for negative integers, the particular number is unspecified.
data MatlabSolverFn (f :: BaseType -> Type) args ret where

  -- Or two Boolean variables
  BoolOrFn :: MatlabSolverFn f (EmptyCtx ::> BaseBoolType ::> BaseBoolType) BaseBoolType

  -- Returns true if the real value is an integer.
  IsIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseBoolType

  -- Return true if first nat is less than or equal to second.
  NatLeFn :: MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseBoolType

  -- Return true if first value is less than or equal to second.
  IntLeFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType ::> BaseIntegerType) BaseBoolType

  -- A function for mapping a unsigned bitvector to a natural number.
  BVToNatFn :: (1 <= w)
            => !(NatRepr w)
            ->  MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseNatType
  -- A function for mapping a signed bitvector to a integer.
  SBVToIntegerFn :: (1 <= w)
                 => !(NatRepr w)
                 -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseIntegerType

  -- A function for mapping a natural number to an integer.
  NatToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseNatType) BaseIntegerType

  -- A function for mapping an integer to equivalent nat.
  --
  -- Function may return any value if input is negative.
  IntegerToNatFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType) BaseNatType

  -- A function for mapping an integer to equivalent real.
  IntegerToRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType) BaseRealType

  -- A function for mapping a real to equivalent integer.
  --
  -- Function may return any value if input is not an integer.
  RealToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseIntegerType

  -- A function that maps Booleans logical value to an integer
  -- (either 0 for false, or 1 for true)
  PredToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseBoolType) BaseIntegerType

  -- 'NatSeqFn base c' denotes the function '\i _ -> base + c*i
  NatSeqFn :: !(f BaseNatType)
           -> !(f BaseNatType)
           -> MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseNatType

  -- 'RealSeqFn base c' denotes the function '\_ i -> base + c*i
  RealSeqFn :: !(f BaseRealType)
            -> !(f BaseRealType)
            -> MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseRealType

  -- 'IndicesInRange tps upper_bounds' returns a predicate that is true if all the arguments
  -- (which must be natural numbers) are between 1 and the given upper bounds (inclusive).
  IndicesInRange :: !(Assignment OnlyNatRepr (idx ::> itp))
                 -> !(Assignment f (idx ::> itp))
                    -- Upper bounds on indices
                 -> MatlabSolverFn f (idx ::> itp) BaseBoolType

  IsEqFn :: !(BaseTypeRepr tp)
         -> MatlabSolverFn f (EmptyCtx ::> tp ::> tp) BaseBoolType

  ------------------------------------------------------------------------
  -- Bitvector functions

  -- Returns true if the bitvector is non-zero.
  BVIsNonZeroFn :: (1 <= w)
                => !(NatRepr w)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseBoolType

  -- Negate a signed bitvector
  ClampedIntNegFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) (BaseBVType w)

  -- Get absolute value of a signed bitvector
  ClampedIntAbsFn :: (1 <= w)
         => !(NatRepr w)
         -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) (BaseBVType w)

  -- Add two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntAddFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Subtract one value from another without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntSubFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Multiple two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedIntMulFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Add two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntAddFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Subtract one value from another without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntSubFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Multiple two values without wrapping but rather rounding to
  -- 0/max value when the result is out of range.
  ClampedUIntMulFn :: (1 <= w)
           => !(NatRepr w)
           -> MatlabSolverFn f
                 (EmptyCtx ::> BaseBVType w ::> BaseBVType w)
                 (BaseBVType w)

  -- Convert a signed integer to the nearest signed integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  IntSetWidthFn :: (1 <= m, 1 <= n)
                => !(NatRepr m)
                -> !(NatRepr n)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a unsigned integer to the nearest unsigned integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  UIntSetWidthFn :: (1 <= m, 1 <= n)
                 => !(NatRepr m)
                 -> !(NatRepr n)
                 -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a unsigned integer to the nearest signed integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  UIntToIntFn :: (1 <= m, 1 <= n)
                => !(NatRepr m)
                -> !(NatRepr n)
                -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  -- Convert a signed integer to the nearest unsigned integer with the
  -- given width.  This clamps the value to min-int or max int when truncated
  -- the width.
  IntToUIntFn :: (1 <= m, 1 <= n)
              => !(NatRepr m)
              -> !(NatRepr n)
              -> MatlabSolverFn f (EmptyCtx ::> BaseBVType m) (BaseBVType n)

  ------------------------------------------------------------------------
  -- Real functions

  -- Returns true if the complex number is non-zero.
  RealIsNonZeroFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseBoolType

  RealCosFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseRealType
  RealSinFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseRealType

  ------------------------------------------------------------------------
  -- Conversion functions

  RealToSBVFn :: (1 <= w)
              => !(NatRepr w)
              -> MatlabSolverFn f (EmptyCtx ::> BaseRealType) (BaseBVType w)

  RealToUBVFn :: (1 <= w)
              => !(NatRepr w)
              -> MatlabSolverFn f (EmptyCtx ::> BaseRealType) (BaseBVType w)

  -- Return 1 if the predicate is true; 0 otherwise.
  PredToBVFn :: (1 <= w)
             => !(NatRepr w)
             -> MatlabSolverFn f (EmptyCtx ::> BaseBoolType) (BaseBVType w)

  ------------------------------------------------------------------------
  -- Complex functions

  -- Returns true if the complex number is non-zero.
  CplxIsNonZeroFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseBoolType

  -- Returns true if the imaginary part of complex number is zero.
  CplxIsRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseBoolType

  -- A function for mapping a real to equivalent complex with imaginary number equals 0.
  RealToComplexFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseComplexType
  -- Returns the real component out of a complex number.
  RealPartOfCplxFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType
  -- Returns the imag component out of a complex number.
  ImagPartOfCplxFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType

  -- Return the complex number formed by negating both components.
  CplxNegFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Add two complex values.
  CplxAddFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Subtract one complex value from another.
  CplxSubFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Multiply two complex values.
  CplxMulFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType ::> BaseComplexType)
                 BaseComplexType

  -- Return the complex number formed by rounding both components.
  --
  -- Rounding is away from zero.
  CplxRoundFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType
  -- Return the complex number formed by taking floor of both components.
  CplxFloorFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType
  -- Return the complex number formed by taking ceiling of both components.
  CplxCeilFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Return magningture of complex number.
  CplxMagFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType

  -- Return the principal square root of a complex number.
  CplxSqrtFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseComplexType

  -- Returns complex exponential of input
  CplxExpFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex natural logarithm of input
  CplxLogFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex natural logarithm of input
  CplxLogBaseFn :: !Integer
                -> MatlabSolverFn f
                     (EmptyCtx ::> BaseComplexType)
                     BaseComplexType
  -- Returns complex sine of input
  CplxSinFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns complex cosine of input
  CplxCosFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType
  -- Returns tangent of input.
  --
  CplxTanFn :: MatlabSolverFn f
                 (EmptyCtx ::> BaseComplexType)
                 BaseComplexType

-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

traverseMatlabSolverFn :: Applicative m
                       => (forall tp . e tp -> m (f tp))
                       -> MatlabSolverFn e a r
                       -> m (MatlabSolverFn f a r)
traverseMatlabSolverFn f fn_id =
  case fn_id of
    BoolOrFn             -> pure $ BoolOrFn
    IsIntegerFn          -> pure $ IsIntegerFn
    NatLeFn              -> pure $ NatLeFn
    IntLeFn              -> pure $ IntLeFn
    BVToNatFn w          -> pure $ BVToNatFn w
    SBVToIntegerFn w     -> pure $ SBVToIntegerFn w
    NatToIntegerFn       -> pure $ NatToIntegerFn
    IntegerToNatFn       -> pure $ IntegerToNatFn
    IntegerToRealFn      -> pure $ IntegerToRealFn
    RealToIntegerFn      -> pure $ RealToIntegerFn
    PredToIntegerFn      -> pure $ PredToIntegerFn
    NatSeqFn  b i        -> NatSeqFn <$> f b <*> f i
    RealSeqFn b i        -> RealSeqFn <$> f b <*> f i
    IndicesInRange tps a -> IndicesInRange tps <$> traverseFC f a
    IsEqFn tp            -> pure $ IsEqFn tp

    BVIsNonZeroFn w      -> pure $ BVIsNonZeroFn w

    ClampedIntNegFn w    -> pure $ ClampedIntNegFn w
    ClampedIntAbsFn w    -> pure $ ClampedIntAbsFn w
    ClampedIntAddFn w    -> pure $ ClampedIntAddFn w
    ClampedIntSubFn w    -> pure $ ClampedIntSubFn w
    ClampedIntMulFn w    -> pure $ ClampedIntMulFn w

    ClampedUIntAddFn w   -> pure $ ClampedUIntAddFn w
    ClampedUIntSubFn w   -> pure $ ClampedUIntSubFn w
    ClampedUIntMulFn w   -> pure $ ClampedUIntMulFn w

    IntSetWidthFn i o    -> pure $ IntSetWidthFn i o
    UIntSetWidthFn i o   -> pure $ UIntSetWidthFn i o
    UIntToIntFn i o      -> pure $ UIntToIntFn i o
    IntToUIntFn i o      -> pure $ IntToUIntFn i o

    RealCosFn            -> pure $ RealCosFn
    RealSinFn            -> pure $ RealSinFn
    RealIsNonZeroFn      -> pure $ RealIsNonZeroFn

    RealToSBVFn w        -> pure $ RealToSBVFn w
    RealToUBVFn w        -> pure $ RealToUBVFn w
    PredToBVFn  w        -> pure $ PredToBVFn  w


    CplxIsNonZeroFn      -> pure $ CplxIsNonZeroFn
    CplxIsRealFn         -> pure $ CplxIsRealFn
    RealToComplexFn      -> pure $ RealToComplexFn
    RealPartOfCplxFn     -> pure $ RealPartOfCplxFn
    ImagPartOfCplxFn     -> pure $ ImagPartOfCplxFn
    CplxNegFn            -> pure $ CplxNegFn
    CplxAddFn            -> pure $ CplxAddFn
    CplxSubFn            -> pure $ CplxSubFn
    CplxMulFn            -> pure $ CplxMulFn
    CplxRoundFn          -> pure $ CplxRoundFn
    CplxFloorFn          -> pure $ CplxFloorFn
    CplxCeilFn           -> pure $ CplxCeilFn
    CplxMagFn            -> pure $ CplxMagFn
    CplxSqrtFn           -> pure $ CplxSqrtFn
    CplxExpFn            -> pure $ CplxExpFn
    CplxLogFn            -> pure $ CplxLogFn
    CplxLogBaseFn b      -> pure $ CplxLogBaseFn b
    CplxSinFn            -> pure $ CplxSinFn
    CplxCosFn            -> pure $ CplxCosFn
    CplxTanFn            -> pure $ CplxTanFn

-- | Utilities to make a pair with the same value.
binCtx :: BaseTypeRepr tp -> Ctx.Assignment BaseTypeRepr (EmptyCtx ::> tp ::> tp)
binCtx tp = Ctx.empty Ctx.:> tp Ctx.:> tp

-- | Get arg tpyes of solver fn.
matlabSolverArgTypes :: MatlabSolverFn f args ret -> Assignment BaseTypeRepr args
matlabSolverArgTypes f =
  case f of
    BoolOrFn             -> knownRepr
    IsIntegerFn          -> knownRepr
    NatLeFn              -> knownRepr
    IntLeFn              -> knownRepr
    BVToNatFn w          -> Ctx.singleton (BaseBVRepr w)
    SBVToIntegerFn w     -> Ctx.singleton (BaseBVRepr w)
    NatToIntegerFn       -> knownRepr
    IntegerToNatFn       -> knownRepr
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    PredToIntegerFn      -> knownRepr
    NatSeqFn{}           -> knownRepr
    IndicesInRange tps _ -> fmapFC toBaseTypeRepr tps
    RealSeqFn _ _        -> knownRepr
    IsEqFn tp            -> binCtx tp

    BVIsNonZeroFn w      -> Ctx.singleton (BaseBVRepr w)
    ClampedIntNegFn w    -> Ctx.singleton (BaseBVRepr w)
    ClampedIntAbsFn w    -> Ctx.singleton (BaseBVRepr w)
    ClampedIntAddFn w    -> binCtx (BaseBVRepr w)
    ClampedIntSubFn w    -> binCtx (BaseBVRepr w)
    ClampedIntMulFn w    -> binCtx (BaseBVRepr w)
    ClampedUIntAddFn w   -> binCtx (BaseBVRepr w)
    ClampedUIntSubFn w   -> binCtx (BaseBVRepr w)
    ClampedUIntMulFn w   -> binCtx (BaseBVRepr w)
    IntSetWidthFn  i _   -> Ctx.singleton (BaseBVRepr i)
    UIntSetWidthFn i _   -> Ctx.singleton (BaseBVRepr i)
    UIntToIntFn i _      -> Ctx.singleton (BaseBVRepr i)
    IntToUIntFn i _      -> Ctx.singleton (BaseBVRepr i)

    RealCosFn            -> knownRepr
    RealSinFn            -> knownRepr
    RealIsNonZeroFn      -> knownRepr

    RealToSBVFn _        -> knownRepr
    RealToUBVFn _        -> knownRepr
    PredToBVFn  _        -> knownRepr

    CplxIsNonZeroFn      -> knownRepr
    CplxIsRealFn         -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    ImagPartOfCplxFn     -> knownRepr
    CplxNegFn            -> knownRepr
    CplxAddFn            -> knownRepr
    CplxSubFn            -> knownRepr
    CplxMulFn            -> knownRepr
    CplxRoundFn          -> knownRepr
    CplxFloorFn          -> knownRepr
    CplxCeilFn           -> knownRepr
    CplxMagFn            -> knownRepr
    CplxSqrtFn           -> knownRepr
    CplxExpFn            -> knownRepr
    CplxLogFn            -> knownRepr
    CplxLogBaseFn _      -> knownRepr
    CplxSinFn            -> knownRepr
    CplxCosFn            -> knownRepr
    CplxTanFn            -> knownRepr

-- | Get return type of solver fn.
matlabSolverReturnType :: MatlabSolverFn f args ret -> BaseTypeRepr ret
matlabSolverReturnType f =
  case f of
    BoolOrFn             -> knownRepr
    IsIntegerFn          -> knownRepr
    NatLeFn              -> knownRepr
    IntLeFn              -> knownRepr
    BVToNatFn{}          -> knownRepr
    SBVToIntegerFn{}     -> knownRepr
    NatToIntegerFn       -> knownRepr
    IntegerToNatFn       -> knownRepr
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    PredToIntegerFn      -> knownRepr
    NatSeqFn{}           -> knownRepr
    IndicesInRange{}     -> knownRepr
    RealSeqFn _ _        -> knownRepr
    IsEqFn{}             -> knownRepr

    BVIsNonZeroFn _      -> knownRepr
    ClampedIntNegFn w    -> BaseBVRepr w
    ClampedIntAbsFn w    -> BaseBVRepr w
    ClampedIntAddFn w    -> BaseBVRepr w
    ClampedIntSubFn w    -> BaseBVRepr w
    ClampedIntMulFn w    -> BaseBVRepr w
    ClampedUIntAddFn w   -> BaseBVRepr w
    ClampedUIntSubFn w   -> BaseBVRepr w
    ClampedUIntMulFn w   -> BaseBVRepr w
    IntSetWidthFn  _ o   -> BaseBVRepr o
    UIntSetWidthFn _ o   -> BaseBVRepr o
    UIntToIntFn _ o      -> BaseBVRepr o
    IntToUIntFn _ o      -> BaseBVRepr o

    RealCosFn            -> knownRepr
    RealSinFn            -> knownRepr
    RealIsNonZeroFn      -> knownRepr

    RealToSBVFn w        -> BaseBVRepr w
    RealToUBVFn w        -> BaseBVRepr w
    PredToBVFn  w        -> BaseBVRepr w

    CplxIsNonZeroFn      -> knownRepr
    CplxIsRealFn         -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    ImagPartOfCplxFn     -> knownRepr
    CplxNegFn            -> knownRepr
    CplxAddFn            -> knownRepr
    CplxSubFn            -> knownRepr
    CplxMulFn            -> knownRepr
    CplxRoundFn          -> knownRepr
    CplxFloorFn          -> knownRepr
    CplxCeilFn           -> knownRepr
    CplxMagFn            -> knownRepr
    CplxSqrtFn           -> knownRepr
    CplxExpFn            -> knownRepr
    CplxLogFn            -> knownRepr
    CplxLogBaseFn _      -> knownRepr
    CplxSinFn            -> knownRepr
    CplxCosFn            -> knownRepr
    CplxTanFn            -> knownRepr

ppMatlabSolverFn ::
  (forall tp. f tp -> Doc) ->
  MatlabSolverFn f a r -> Doc
ppMatlabSolverFn printSub f =
  case f of
    BoolOrFn             -> text "bool_or"
    IsIntegerFn          -> text "is_integer"
    NatLeFn              -> text "nat_le"
    IntLeFn              -> text "int_le"
    BVToNatFn w          -> parens $ text "bv_to_nat" <+> text (show w)
    SBVToIntegerFn w     -> parens $ text "sbv_to_int" <+> text (show w)
    NatToIntegerFn       -> text "nat_to_integer"
    IntegerToNatFn       -> text "integer_to_nat"
    IntegerToRealFn      -> text "integer_to_real"
    RealToIntegerFn      -> text "real_to_integer"
    PredToIntegerFn      -> text "pred_to_integer"
    NatSeqFn  b i        -> parens $ text "nat_seq"  <+> printSub b <+> printSub i
    RealSeqFn b i        -> parens $ text "real_seq" <+> printSub b <+> printSub i
    IndicesInRange _ bnds ->
      parens (text "indices_in_range" <+> sep (toListFC printSub bnds))
    IsEqFn{}             -> text "is_eq"

    BVIsNonZeroFn w      -> parens $ text "bv_is_nonzero" <+> text (show w)
    ClampedIntNegFn w    -> parens $ text "clamped_int_neg" <+> text (show w)
    ClampedIntAbsFn w    -> parens $ text "clamped_neg_abs" <+> text (show w)
    ClampedIntAddFn w    -> parens $ text "clamped_int_add" <+> text (show w)
    ClampedIntSubFn w    -> parens $ text "clamped_int_sub" <+> text (show w)
    ClampedIntMulFn w    -> parens $ text "clamped_int_mul" <+> text (show w)
    ClampedUIntAddFn w   -> parens $ text "clamped_uint_add" <+> text (show w)
    ClampedUIntSubFn w   -> parens $ text "clamped_uint_sub" <+> text (show w)
    ClampedUIntMulFn w   -> parens $ text "clamped_uint_mul" <+> text (show w)

    IntSetWidthFn i o    -> parens $ text "int_set_width"  <+> text (show i) <+> text (show o)
    UIntSetWidthFn i o   -> parens $ text "uint_set_width" <+> text (show i) <+> text (show o)
    UIntToIntFn i o      -> parens $ text "uint_to_int"  <+> text (show i) <+> text (show o)
    IntToUIntFn i o      -> parens $ text "int_to_uint"  <+> text (show i) <+> text (show o)

    RealCosFn            -> text "real_cos"
    RealSinFn            -> text "real_sin"
    RealIsNonZeroFn      -> text "real_is_nonzero"

    RealToSBVFn w        -> parens $ text "real_to_sbv" <+> text (show w)
    RealToUBVFn w        -> parens $ text "real_to_sbv" <+> text (show w)
    PredToBVFn  w        -> parens $ text "pred_to_bv"  <+> text (show w)

    CplxIsNonZeroFn      -> text "cplx_is_nonzero"
    CplxIsRealFn         -> text "cplx_is_real"
    RealToComplexFn      -> text "real_to_complex"
    RealPartOfCplxFn     -> text "real_part_of_complex"
    ImagPartOfCplxFn     -> text "imag_part_of_complex"

    CplxNegFn            -> text "cplx_neg"
    CplxAddFn            -> text "cplx_add"
    CplxSubFn            -> text "cplx_sub"
    CplxMulFn            -> text "cplx_mul"

    CplxRoundFn          -> text "cplx_round"
    CplxFloorFn          -> text "cplx_floor"
    CplxCeilFn           -> text "cplx_ceil"
    CplxMagFn            -> text "cplx_mag"
    CplxSqrtFn           -> text "cplx_sqrt"
    CplxExpFn            -> text "cplx_exp"
    CplxLogFn            -> text "cplx_log"
    CplxLogBaseFn b      -> parens $ text "cplx_log_base" <+> text (show b)
    CplxSinFn            -> text "cplx_sin"
    CplxCosFn            -> text "cplx_cos"
    CplxTanFn            -> text "cplx_tan"

-- | Test 'MatlabSolverFn' values for equality.
testSolverFnEq :: TestEquality f
               => MatlabSolverFn f ax rx
               -> MatlabSolverFn f ay ry
               -> Maybe ((ax ::> rx) :~: (ay ::> ry))
testSolverFnEq = $(structuralTypeEquality [t|MatlabSolverFn|]
                   [ ( DataArg 0 `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|NatRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|Assignment|] `TypeApp` AnyType `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   ]
                  )

instance ( Hashable (f BaseNatType)
         , Hashable (f BaseRealType)
         , HashableF f
         )
         => Hashable (MatlabSolverFn f args tp) where
  hashWithSalt = $(structuralHashWithSalt [t|MatlabSolverFn|] [])

realIsNonZero :: IsExprBuilder sym => sym -> SymReal sym -> IO (Pred sym)
realIsNonZero sym = realNe sym (realZero sym)

evalMatlabSolverFn :: forall sym args ret
                   .  IsExprBuilder sym
                   => MatlabSolverFn (SymExpr sym) args ret
                   -> sym
                   -> Assignment (SymExpr sym) args
                   -> IO (SymExpr sym ret)
evalMatlabSolverFn f sym =
  case f of
    BoolOrFn         -> uncurryAssignment $ orPred sym

    IsIntegerFn      -> uncurryAssignment $ isInteger sym
    NatLeFn          -> uncurryAssignment $ natLe sym
    IntLeFn          -> uncurryAssignment $ intLe sym
    BVToNatFn{}      -> uncurryAssignment $ bvToNat sym
    SBVToIntegerFn{} -> uncurryAssignment $ sbvToInteger sym
    NatToIntegerFn   -> uncurryAssignment $ natToInteger sym
    IntegerToNatFn   -> uncurryAssignment $ integerToNat sym
    IntegerToRealFn  -> uncurryAssignment $ integerToReal sym
    RealToIntegerFn  -> uncurryAssignment $ realToInteger sym
    PredToIntegerFn  -> uncurryAssignment $ \p ->
      iteM intIte sym p (intLit sym 1) (intLit sym 0)
    NatSeqFn b inc   -> uncurryAssignment $ \idx _ -> do
      natAdd sym b =<< natMul sym inc idx
    RealSeqFn b inc -> uncurryAssignment $ \_ idx -> do
      realAdd sym b =<< realMul sym inc =<< natToReal sym idx
    IndicesInRange tps0 bnds0 -> \args ->
        Ctx.forIndex (Ctx.size tps0) (g tps0 bnds0 args) (pure (truePred sym))
      where g :: Assignment OnlyNatRepr ctx
              -> Assignment (SymExpr sym) ctx
              -> Assignment (SymExpr sym) ctx
              -> IO (Pred sym)
              -> Index ctx tp
              -> IO (Pred sym)
            g tps bnds args m i = do
              case tps Ctx.! i of
                OnlyNatRepr -> do
                  let v = args ! i
                  let bnd = bnds ! i
                  one <- natLit sym 1
                  p <- join $ andPred sym <$> natLe sym one v <*> natLe sym v bnd
                  andPred sym p =<< m
    IsEqFn{} -> Ctx.uncurryAssignment $ \x y -> do
      isEq sym x y

    BVIsNonZeroFn _    -> Ctx.uncurryAssignment $ bvIsNonzero sym
    ClampedIntNegFn _  -> Ctx.uncurryAssignment $ clampedIntNeg sym
    ClampedIntAbsFn _  -> Ctx.uncurryAssignment $ clampedIntAbs sym
    ClampedIntAddFn _  -> Ctx.uncurryAssignment $ clampedIntAdd sym
    ClampedIntSubFn _  -> Ctx.uncurryAssignment $ clampedIntSub sym
    ClampedIntMulFn _  -> Ctx.uncurryAssignment $ clampedIntMul sym
    ClampedUIntAddFn _ -> Ctx.uncurryAssignment $ clampedUIntAdd sym
    ClampedUIntSubFn _ -> Ctx.uncurryAssignment $ clampedUIntSub sym
    ClampedUIntMulFn _ -> Ctx.uncurryAssignment $ clampedUIntMul sym

    IntSetWidthFn  _ o -> Ctx.uncurryAssignment $ \v -> intSetWidth  sym v o
    UIntSetWidthFn _ o -> Ctx.uncurryAssignment $ \v -> uintSetWidth sym v o
    UIntToIntFn _ o    -> Ctx.uncurryAssignment $ \v -> uintToInt sym v o
    IntToUIntFn _ o    -> Ctx.uncurryAssignment $ \v -> intToUInt sym v o

    RealIsNonZeroFn    -> Ctx.uncurryAssignment $ realIsNonZero sym
    RealCosFn          -> Ctx.uncurryAssignment $ realCos sym
    RealSinFn          -> Ctx.uncurryAssignment $ realSin sym

    RealToSBVFn w      -> Ctx.uncurryAssignment $ \v -> realToSBV sym v w
    RealToUBVFn w      -> Ctx.uncurryAssignment $ \v -> realToBV  sym v w
    PredToBVFn  w      -> Ctx.uncurryAssignment $ \v -> predToBV  sym v w

    CplxIsNonZeroFn  -> Ctx.uncurryAssignment $ \x -> do
      (real_x :+ imag_x) <- cplxGetParts sym x
      join $ orPred sym <$> realIsNonZero sym real_x <*> realIsNonZero sym imag_x
    CplxIsRealFn     -> Ctx.uncurryAssignment $ isReal sym
    RealToComplexFn  -> Ctx.uncurryAssignment $ cplxFromReal sym
    RealPartOfCplxFn -> Ctx.uncurryAssignment $ getRealPart sym
    ImagPartOfCplxFn -> Ctx.uncurryAssignment $ getImagPart sym

    CplxNegFn        -> Ctx.uncurryAssignment $ cplxNeg sym
    CplxAddFn        -> Ctx.uncurryAssignment $ cplxAdd sym
    CplxSubFn        -> Ctx.uncurryAssignment $ cplxSub sym
    CplxMulFn        -> Ctx.uncurryAssignment $ cplxMul sym

    CplxRoundFn      -> Ctx.uncurryAssignment $ cplxRound sym
    CplxFloorFn      -> Ctx.uncurryAssignment $ cplxFloor sym
    CplxCeilFn       -> Ctx.uncurryAssignment $ cplxCeil  sym
    CplxMagFn        -> Ctx.uncurryAssignment $ cplxMag   sym
    CplxSqrtFn       -> Ctx.uncurryAssignment $ cplxSqrt  sym
    CplxExpFn        -> Ctx.uncurryAssignment $ cplxExp   sym
    CplxLogFn        -> Ctx.uncurryAssignment $ cplxLog   sym
    CplxLogBaseFn b  -> Ctx.uncurryAssignment $ cplxLogBase (toRational b) sym
    CplxSinFn        -> Ctx.uncurryAssignment $ cplxSin  sym
    CplxCosFn        -> Ctx.uncurryAssignment $ cplxCos  sym
    CplxTanFn        -> Ctx.uncurryAssignment $ cplxTan  sym

-- | This class is provides functions needed to implement the symbolic
-- array intrinsic functions
class IsSymExprBuilder sym => MatlabSymbolicArrayBuilder sym where

  -- | Create a Matlab solver function from its prototype.
  mkMatlabSolverFn :: sym
                   -> MatlabSolverFn (SymExpr sym) args ret
                   -> IO (SymFn sym args ret)
