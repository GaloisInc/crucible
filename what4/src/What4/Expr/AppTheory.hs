------------------------------------------------------------------------
-- |
-- Module      : What4.Expr.AppTheory
-- Description : Identifying the solver theory required by a core expression
-- Copyright   : (c) Galois, Inc 2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
module What4.Expr.AppTheory
  ( AppTheory(..)
  , quantTheory
  , appTheory
  ) where

import What4.Expr.Builder

-- | The theory that a symbol belongs to.
data AppTheory
   = BoolTheory
   | LinearArithTheory
   | NonlinearArithTheory
   | ComputableArithTheory
   | BitvectorTheory
   | QuantifierTheory
   | StringTheory
   | FloatingPointTheory
   | ArrayTheory
   | StructTheory
     -- ^ Theory attributed to structs (equivalent to records in CVC4/Z3, tuples in Yices)
   | FnTheory
     -- ^ Theory attributed application functions.
   deriving (Eq, Ord)

quantTheory :: NonceApp t (Expr t) tp -> AppTheory
quantTheory a0 =
  case a0 of
    Forall{} -> QuantifierTheory
    Exists{} -> QuantifierTheory
    ArrayFromFn{}   -> FnTheory
    MapOverArrays{} -> ArrayTheory
    ArrayTrueOnEntries{} -> ArrayTheory
    FnApp{} -> FnTheory

appTheory :: App (Expr t) tp -> AppTheory
appTheory a0 =
  case a0 of

    ----------------------------
    -- Boolean operations

    TrueBool  -> BoolTheory
    FalseBool -> BoolTheory
    NotBool{} -> BoolTheory
    AndBool{} -> BoolTheory
    XorBool{} -> BoolTheory
    IteBool{} -> BoolTheory

    RealIsInteger{} -> LinearArithTheory
    BVTestBit{} -> BitvectorTheory
    BVEq{} -> BitvectorTheory
    BVSlt{} -> BitvectorTheory
    BVUlt{} -> BitvectorTheory
    ArrayEq{} -> ArrayTheory

    ----------------------------
    -- Semiring operations
    SemiRingMul{} -> NonlinearArithTheory
    SemiRingSum{} -> LinearArithTheory
    SemiRingIte{} -> LinearArithTheory
    SemiRingEq{} -> LinearArithTheory
    SemiRingLe{} -> LinearArithTheory

    ----------------------------
    -- Nat operations

    NatDiv _ SemiRingLiteral{} -> LinearArithTheory
    NatDiv{} -> NonlinearArithTheory

    NatMod _ SemiRingLiteral{} -> LinearArithTheory
    NatMod{} -> NonlinearArithTheory

    ----------------------------
    -- Integer operations

    IntMod _ SemiRingLiteral{} -> LinearArithTheory
    IntMod{} -> NonlinearArithTheory

    IntDiv _ SemiRingLiteral{} -> LinearArithTheory
    IntDiv{} -> NonlinearArithTheory

    IntAbs{} -> LinearArithTheory
    IntDivisible{} -> LinearArithTheory

    ----------------------------
    -- Real operations

    RealDiv{} -> NonlinearArithTheory
    RealSqrt{} -> NonlinearArithTheory

    ----------------------------
    -- Computable number operations
    Pi -> ComputableArithTheory
    RealSin{}   -> ComputableArithTheory
    RealCos{}   -> ComputableArithTheory
    RealATan2{} -> ComputableArithTheory
    RealSinh{}  -> ComputableArithTheory
    RealCosh{}  -> ComputableArithTheory
    RealExp{}   -> ComputableArithTheory
    RealLog{}   -> ComputableArithTheory

    ----------------------------
    -- Bitvector operations
    PredToBV{} -> BitvectorTheory
    BVUnaryTerm{} -> BoolTheory
    BVConcat{} -> BitvectorTheory
    BVSelect{} -> BitvectorTheory
    BVNeg{}    -> BitvectorTheory
    BVAdd{}  -> BitvectorTheory
    BVMul{}  -> BitvectorTheory
    BVUdiv{} -> BitvectorTheory
    BVUrem{} -> BitvectorTheory
    BVSdiv{} -> BitvectorTheory
    BVSrem{} -> BitvectorTheory
    BVIte{}  -> BitvectorTheory
    BVShl{}   -> BitvectorTheory
    BVLshr{}  -> BitvectorTheory
    BVAshr{}  -> BitvectorTheory
    BVZext{}  -> BitvectorTheory
    BVSext{}  -> BitvectorTheory
    BVBitNot{} -> BitvectorTheory
    BVBitAnd{} -> BitvectorTheory
    BVBitOr{}  -> BitvectorTheory
    BVBitXor{} -> BitvectorTheory
    BVPopcount{} -> BitvectorTheory
    BVCountLeadingZeros{} -> BitvectorTheory
    BVCountTrailingZeros{} -> BitvectorTheory

    ----------------------------
    -- Bitvector operations
    FloatPZero{}      -> FloatingPointTheory
    FloatNZero{}      -> FloatingPointTheory
    FloatNaN{}        -> FloatingPointTheory
    FloatPInf{}       -> FloatingPointTheory
    FloatNInf{}       -> FloatingPointTheory
    FloatNeg{}        -> FloatingPointTheory
    FloatAbs{}        -> FloatingPointTheory
    FloatSqrt{}       -> FloatingPointTheory
    FloatAdd{}        -> FloatingPointTheory
    FloatSub{}        -> FloatingPointTheory
    FloatMul{}        -> FloatingPointTheory
    FloatDiv{}        -> FloatingPointTheory
    FloatRem{}        -> FloatingPointTheory
    FloatMin{}        -> FloatingPointTheory
    FloatMax{}        -> FloatingPointTheory
    FloatFMA{}        -> FloatingPointTheory
    FloatEq{}         -> FloatingPointTheory
    FloatFpEq{}       -> FloatingPointTheory
    FloatFpNe{}       -> FloatingPointTheory
    FloatLe{}         -> FloatingPointTheory
    FloatLt{}         -> FloatingPointTheory
    FloatIsNaN{}      -> FloatingPointTheory
    FloatIsInf{}      -> FloatingPointTheory
    FloatIsZero{}     -> FloatingPointTheory
    FloatIsPos{}      -> FloatingPointTheory
    FloatIsNeg{}      -> FloatingPointTheory
    FloatIsSubnorm{}  -> FloatingPointTheory
    FloatIsNorm{}     -> FloatingPointTheory
    FloatIte{}        -> FloatingPointTheory
    FloatCast{}       -> FloatingPointTheory
    FloatRound{}      -> FloatingPointTheory
    FloatFromBinary{} -> FloatingPointTheory
    FloatToBinary{}   -> FloatingPointTheory
    BVToFloat{}       -> FloatingPointTheory
    SBVToFloat{}      -> FloatingPointTheory
    RealToFloat{}     -> FloatingPointTheory
    FloatToBV{}       -> FloatingPointTheory
    FloatToSBV{}      -> FloatingPointTheory
    FloatToReal{}     -> FloatingPointTheory

    --------------------------------
    -- Conversions.

    NatToInteger{}  -> LinearArithTheory
    IntegerToReal{} -> LinearArithTheory
    BVToNat{}       -> LinearArithTheory
    BVToInteger{}   -> LinearArithTheory
    SBVToInteger{}  -> LinearArithTheory

    RoundReal{} -> LinearArithTheory
    FloorReal{} -> LinearArithTheory
    CeilReal{}  -> LinearArithTheory
    RealToInteger{} -> LinearArithTheory

    IntegerToNat{} -> LinearArithTheory
    IntegerToBV{}  -> BitvectorTheory

    ---------------------
    -- Array operations

    ArrayMap{} -> ArrayTheory
    ConstantArray{} -> ArrayTheory
    SelectArray{} -> ArrayTheory
    UpdateArray{} -> ArrayTheory
    MuxArray{} -> ArrayTheory

    ---------------------
    -- Complex operations

    Cplx{} -> LinearArithTheory
    RealPart{} -> LinearArithTheory
    ImagPart{} -> LinearArithTheory

    ---------------------
    -- Struct operations

    -- A struct with its fields.
    StructCtor{}  -> StructTheory
    StructField{} -> StructTheory
    StructIte{}   -> StructTheory
