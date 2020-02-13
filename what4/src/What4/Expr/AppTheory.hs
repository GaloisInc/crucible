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
  , typeTheory
  ) where

import           What4.BaseTypes
import           What4.Expr.Builder
import qualified What4.SemiRing as SR
import qualified What4.Expr.WeightedSum as WSum

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
    Annotation{} -> BoolTheory
    Forall{} -> QuantifierTheory
    Exists{} -> QuantifierTheory
    ArrayFromFn{}   -> FnTheory
    MapOverArrays{} -> ArrayTheory
    ArrayTrueOnEntries{} -> ArrayTheory
    FnApp{} -> FnTheory

typeTheory :: BaseTypeRepr tp -> AppTheory
typeTheory tp = case tp of
  BaseBoolRepr      -> BoolTheory
  BaseBVRepr _      -> BitvectorTheory
  BaseNatRepr       -> LinearArithTheory
  BaseIntegerRepr   -> LinearArithTheory
  BaseRealRepr      -> LinearArithTheory
  BaseFloatRepr _   -> FloatingPointTheory
  BaseStringRepr{}  -> StringTheory
  BaseComplexRepr   -> LinearArithTheory
  BaseStructRepr _  -> StructTheory
  BaseArrayRepr _ _ -> ArrayTheory

appTheory :: App (Expr t) tp -> AppTheory
appTheory a0 =
  case a0 of
    ----------------------------
    -- Boolean operations

    BaseIte tp _ _ _ _ -> typeTheory tp
    BaseEq tp _ _ -> typeTheory tp

    NotPred{} -> BoolTheory
    ConjPred{} -> BoolTheory

    RealIsInteger{} -> LinearArithTheory

    BVTestBit{} -> BitvectorTheory
    BVSlt{} -> BitvectorTheory
    BVUlt{} -> BitvectorTheory
    BVOrBits{} -> BitvectorTheory

    ----------------------------
    -- Semiring operations
    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingBVRepr _ _ -> BitvectorTheory
        SR.SemiRingNatRepr -> NonlinearArithTheory
        SR.SemiRingIntegerRepr -> NonlinearArithTheory
        SR.SemiRingRealRepr -> NonlinearArithTheory

    SemiRingSum sm ->
      case WSum.sumRepr sm of
        SR.SemiRingBVRepr _ _ -> BitvectorTheory
        SR.SemiRingNatRepr -> LinearArithTheory
        SR.SemiRingIntegerRepr -> LinearArithTheory
        SR.SemiRingRealRepr -> LinearArithTheory

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
    BVUnaryTerm{} -> BoolTheory
    BVConcat{} -> BitvectorTheory
    BVSelect{} -> BitvectorTheory
    BVUdiv{} -> BitvectorTheory
    BVUrem{} -> BitvectorTheory
    BVSdiv{} -> BitvectorTheory
    BVSrem{} -> BitvectorTheory
    BVShl{}   -> BitvectorTheory
    BVLshr{}  -> BitvectorTheory
    BVRol{}   -> BitvectorTheory
    BVRor{}   -> BitvectorTheory
    BVAshr{}  -> BitvectorTheory
    BVZext{}  -> BitvectorTheory
    BVSext{}  -> BitvectorTheory
    BVPopcount{} -> BitvectorTheory
    BVCountLeadingZeros{} -> BitvectorTheory
    BVCountTrailingZeros{} -> BitvectorTheory
    BVFill{} -> BitvectorTheory

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

    ---------------------
    -- String operations
    StringAppend{} -> StringTheory
    StringLength{} -> StringTheory
    StringContains{} -> StringTheory
    StringIndexOf{} -> StringTheory
    StringIsPrefixOf{} -> StringTheory
    StringIsSuffixOf{} -> StringTheory
    StringSubstring{} -> StringTheory

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
