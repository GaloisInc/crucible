{-# LANGUAGE GADTs #-}
module Lang.Crucible.Solver.SimpleBackend.AppTheory
  ( AppTheory(..)
  , quantTheory
  , appTheory
  ) where

import Lang.Crucible.Solver.SimpleBuilder

-- | The theory that a symbol belongs to.
data AppTheory
   = BoolTheory
   | LinearArithTheory
   | NonlinearArithTheory
   | ComputableArithTheory
   | BitvectorTheory
   | QuantifierTheory
   | ArrayTheory
   | StructTheory
     -- ^ Theory attributes to structs (equivalent to records in CVC4/Z3, tuples in Yices)
   | FnTheory
     -- ^ Theory attributed application functions.
   deriving (Eq, Ord)

quantTheory :: NonceApp t (Elt t) tp -> AppTheory
quantTheory a0 =
  case a0 of
    Forall{} -> QuantifierTheory
    Exists{} -> QuantifierTheory
    ArrayFromFn{}   -> FnTheory
    MapOverArrays{} -> ArrayTheory
    ArrayTrueOnEntries{} -> ArrayTheory
    FnApp{} -> FnTheory

appTheory :: App (Elt t) tp -> AppTheory
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

    RealEq{} -> LinearArithTheory
    RealLe{} -> LinearArithTheory
    RealIsInteger{} -> LinearArithTheory
    BVTestBit{} -> BitvectorTheory
    BVEq{} -> BitvectorTheory
    BVSlt{} -> BitvectorTheory
    BVUlt{} -> BitvectorTheory
    ArrayEq{} -> ArrayTheory

    ----------------------------
    -- Nat operations

    NatDiv _ NatElt{} -> LinearArithTheory
    NatDiv{} -> NonlinearArithTheory

    ----------------------------
    -- Integer operations

    IntMod _ NatElt{} -> LinearArithTheory
    IntMod{} -> NonlinearArithTheory

    ----------------------------
    -- Real operations

    RealMul RatElt{} _ -> LinearArithTheory
    RealMul _ RatElt{} -> LinearArithTheory
    RealMul _ _ -> NonlinearArithTheory
    RealSum{} -> LinearArithTheory
    RealIte{} -> LinearArithTheory
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
    BVTrunc{} -> BitvectorTheory
    BVBitNot{} -> BitvectorTheory
    BVBitAnd{} -> BitvectorTheory
    BVBitOr{}  -> BitvectorTheory
    BVBitXor{} -> BitvectorTheory

    --------------------------------
    -- Conversions.

    NatToInteger{}  -> LinearArithTheory
    IntegerToReal{} -> LinearArithTheory
    BVToInteger{}   -> LinearArithTheory
    SBVToInteger{}  -> LinearArithTheory

    RoundReal{} -> LinearArithTheory
    FloorReal{} -> LinearArithTheory
    CeilReal{}  -> LinearArithTheory
    RealToInteger{} -> LinearArithTheory

    IntegerToNat{} -> LinearArithTheory
    IntegerToSBV{} -> BitvectorTheory
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
