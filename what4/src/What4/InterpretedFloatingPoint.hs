{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module What4.InterpretedFloatingPoint
  ( -- * FloatInfo data kind
    type FloatInfo
    -- ** Constructors for kind FloatInfo
  , HalfFloat
  , SingleFloat
  , DoubleFloat
  , QuadFloat
  , X86_80Float
  , DoubleDoubleFloat
    -- ** Representations of FloatInfo types
  , FloatInfoRepr(..)
    -- ** FloatInfo to/from FloatPrecision
  , FloatInfoToPrecision
  , FloatPrecisionToInfo
  , floatInfoToPrecisionRepr
  , floatPrecisionToInfoRepr
    -- ** Bit-width type family
  , FloatInfoToBitWidth
  , floatInfoToBVTypeRepr
    -- * Interface classes
    -- ** Interpretation type family
  , SymInterpretedFloatType
    -- ** Type alias
  , SymInterpretedFloat
    -- ** IsInterpretedFloatExprBuilder
  , IsInterpretedFloatExprBuilder(..)
  , IsInterpretedFloatSymExprBuilder(..)
  ) where

import           Data.Hashable
import           Data.Kind
import           Data.Parameterized.Classes
import           Data.Parameterized.TH.GADT
import           GHC.TypeNats
import           Text.PrettyPrint.ANSI.Leijen

import           What4.BaseTypes
import           What4.Interface

-- | This data kind describes the types of floating-point formats.
-- This consist of the standard IEEE 754-2008 binary floating point formats,
-- as well as the X86 extended 80-bit format and the double-double format.
data FloatInfo where
  HalfFloat         :: FloatInfo  --  16 bit binary IEEE754
  SingleFloat       :: FloatInfo  --  32 bit binary IEEE754
  DoubleFloat       :: FloatInfo  --  64 bit binary IEEE754
  QuadFloat         :: FloatInfo  -- 128 bit binary IEEE754
  X86_80Float       :: FloatInfo  -- X86 80-bit extended floats
  DoubleDoubleFloat :: FloatInfo  -- two 64-bit floats fused in the "double-double" style

type HalfFloat         = 'HalfFloat         -- ^  16 bit binary IEEE754.
type SingleFloat       = 'SingleFloat       -- ^  32 bit binary IEEE754.
type DoubleFloat       = 'DoubleFloat       -- ^  64 bit binary IEEE754.
type QuadFloat         = 'QuadFloat         -- ^ 128 bit binary IEEE754.
type X86_80Float       = 'X86_80Float       -- ^ X86 80-bit extended floats.
type DoubleDoubleFloat = 'DoubleDoubleFloat -- ^ Two 64-bit floats fused in the "double-double" style.

-- | A family of value-level representatives for floating-point types.
data FloatInfoRepr (fi :: FloatInfo) where
  HalfFloatRepr         :: FloatInfoRepr HalfFloat
  SingleFloatRepr       :: FloatInfoRepr SingleFloat
  DoubleFloatRepr       :: FloatInfoRepr DoubleFloat
  QuadFloatRepr         :: FloatInfoRepr QuadFloat
  X86_80FloatRepr       :: FloatInfoRepr X86_80Float
  DoubleDoubleFloatRepr :: FloatInfoRepr DoubleDoubleFloat

instance KnownRepr FloatInfoRepr HalfFloat         where knownRepr = HalfFloatRepr
instance KnownRepr FloatInfoRepr SingleFloat       where knownRepr = SingleFloatRepr
instance KnownRepr FloatInfoRepr DoubleFloat       where knownRepr = DoubleFloatRepr
instance KnownRepr FloatInfoRepr QuadFloat         where knownRepr = QuadFloatRepr
instance KnownRepr FloatInfoRepr X86_80Float       where knownRepr = X86_80FloatRepr
instance KnownRepr FloatInfoRepr DoubleDoubleFloat where knownRepr = DoubleDoubleFloatRepr

$(return [])

instance HashableF FloatInfoRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (FloatInfoRepr fi) where
  hashWithSalt = $(structuralHash [t|FloatInfoRepr|])

instance Pretty (FloatInfoRepr fi) where
  pretty = text . show
instance Show (FloatInfoRepr fi) where
  showsPrec = $(structuralShowsPrec [t|FloatInfoRepr|])
instance ShowF FloatInfoRepr

instance TestEquality FloatInfoRepr where
  testEquality = $(structuralTypeEquality [t|FloatInfoRepr|] [])
instance OrdF FloatInfoRepr where
  compareF = $(structuralTypeOrd [t|FloatInfoRepr|] [])


type family FloatInfoToPrecision (fi :: FloatInfo) :: FloatPrecision where
  FloatInfoToPrecision HalfFloat   = Prec16
  FloatInfoToPrecision SingleFloat = Prec32
  FloatInfoToPrecision DoubleFloat = Prec64
  FloatInfoToPrecision QuadFloat   = Prec128

type family FloatPrecisionToInfo (fpp :: FloatPrecision) :: FloatInfo where
  FloatPrecisionToInfo Prec16  = HalfFloat
  FloatPrecisionToInfo Prec32  = SingleFloat
  FloatPrecisionToInfo Prec64  = DoubleFloat
  FloatPrecisionToInfo Prec128 = QuadFloat

type family FloatInfoToBitWidth (fi :: FloatInfo) :: GHC.TypeNats.Nat where
  FloatInfoToBitWidth HalfFloat         = 16
  FloatInfoToBitWidth SingleFloat       = 32
  FloatInfoToBitWidth DoubleFloat       = 64
  FloatInfoToBitWidth QuadFloat         = 128
  FloatInfoToBitWidth X86_80Float       = 80
  FloatInfoToBitWidth DoubleDoubleFloat = 128

floatInfoToPrecisionRepr
  :: FloatInfoRepr fi -> FloatPrecisionRepr (FloatInfoToPrecision fi)
floatInfoToPrecisionRepr = \case
  HalfFloatRepr         -> knownRepr
  SingleFloatRepr       -> knownRepr
  DoubleFloatRepr       -> knownRepr
  QuadFloatRepr         -> knownRepr
  X86_80FloatRepr       -> error "x86_80 is not an IEEE-754 format."
  DoubleDoubleFloatRepr -> error "double-double is not an IEEE-754 format."

floatPrecisionToInfoRepr
  :: FloatPrecisionRepr fpp -> FloatInfoRepr (FloatPrecisionToInfo fpp)
floatPrecisionToInfoRepr fpp
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec16)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec32)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec64)
  = knownRepr
  | Just Refl <- testEquality fpp (knownRepr :: FloatPrecisionRepr Prec128)
  = knownRepr
  | otherwise
  = error $ "unexpected IEEE-754 precision: " ++ show fpp

floatInfoToBVTypeRepr
  :: FloatInfoRepr fi -> BaseTypeRepr (BaseBVType (FloatInfoToBitWidth fi))
floatInfoToBVTypeRepr = \case
  HalfFloatRepr         -> knownRepr
  SingleFloatRepr       -> knownRepr
  DoubleFloatRepr       -> knownRepr
  QuadFloatRepr         -> knownRepr
  X86_80FloatRepr       -> knownRepr
  DoubleDoubleFloatRepr -> knownRepr


-- | Interpretation of the floating point type.
type family SymInterpretedFloatType (sym :: Type) (fi :: FloatInfo) :: BaseType

-- | Symbolic floating point numbers.
type SymInterpretedFloat sym fi = SymExpr sym (SymInterpretedFloatType sym fi)

-- | Abstact floating point operations.
class IsExprBuilder sym => IsInterpretedFloatExprBuilder sym where
  -- | Return floating point number @+0@.
  iFloatPZero :: sym -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fi)

  -- | Return floating point number @-0@.
  iFloatNZero :: sym -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fi)

  -- |  Return floating point NaN.
  iFloatNaN :: sym -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fi)

  -- | Return floating point @+infinity@.
  iFloatPInf :: sym -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fi)

  -- | Return floating point @-infinity@.
  iFloatNInf :: sym -> FloatInfoRepr fi -> IO (SymInterpretedFloat sym fi)

  -- | Create a floating point literal from a rational literal.
  iFloatLit
    :: sym -> FloatInfoRepr fi -> Rational -> IO (SymInterpretedFloat sym fi)

  -- | Create a (single precision) floating point literal.
  iFloatLitSingle :: sym -> Float -> IO (SymInterpretedFloat sym SingleFloat)
  -- | Create a (double precision) floating point literal.
  iFloatLitDouble :: sym -> Double -> IO (SymInterpretedFloat sym DoubleFloat)

  -- | Negate a floating point number.
  iFloatNeg
    :: sym
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Return the absolute value of a floating point number.
  iFloatAbs
    :: sym
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Compute the square root of a floating point number.
  iFloatSqrt
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Add two floating point numbers.
  iFloatAdd
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Subtract two floating point numbers.
  iFloatSub
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Multiply two floating point numbers.
  iFloatMul
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Divide two floating point numbers.
  iFloatDiv
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Compute the reminder: @x - y * n@, where @n@ in Z is nearest to @x / y@.
  iFloatRem
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Return the min of two floating point numbers.
  iFloatMin
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Return the max of two floating point numbers.
  iFloatMax
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Compute the fused multiplication and addition: @(x * y) + z@.
  iFloatFMA
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Check logical equality of two floating point numbers.
  iFloatEq
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check logical non-equality of two floating point numbers.
  iFloatNe
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check IEEE equality of two floating point numbers.
  iFloatFpEq
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check IEEE non-equality of two floating point numbers.
  iFloatFpNe
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check @<=@ on two floating point numbers.
  iFloatLe
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check @<@ on two floating point numbers.
  iFloatLt
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check @>=@ on two floating point numbers.
  iFloatGe
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  -- | Check @>@ on two floating point numbers.
  iFloatGt
    :: sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (Pred sym)

  iFloatIsNaN :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsInf :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsZero :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsPos :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsNeg :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsSubnorm :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)
  iFloatIsNorm :: sym -> SymInterpretedFloat sym fi -> IO (Pred sym)

  -- | If-then-else on floating point numbers.
  iFloatIte
    :: sym
    -> Pred sym
    -> SymInterpretedFloat sym fi
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)

  -- | Change the precision of a floating point number.
  iFloatCast
    :: sym
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymInterpretedFloat sym fi'
    -> IO (SymInterpretedFloat sym fi)
  -- | Round a floating point number to an integral value.
  iFloatRound
    :: sym
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> IO (SymInterpretedFloat sym fi)
  -- | Convert from binary representation in IEEE 754-2008 format to
  --   floating point.
  iFloatFromBinary
    :: sym
    -> FloatInfoRepr fi
    -> SymBV sym (FloatInfoToBitWidth fi)
    -> IO (SymInterpretedFloat sym fi)
  -- | Convert from floating point from to the binary representation in
  --   IEEE 754-2008 format.
  iFloatToBinary
    :: sym
    -> FloatInfoRepr fi
    -> SymInterpretedFloat sym fi
    -> IO (SymBV sym (FloatInfoToBitWidth fi))
  -- | Convert a unsigned bitvector to a floating point number.
  iBVToFloat
    :: (1 <= w)
    => sym
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymInterpretedFloat sym fi)
  -- | Convert a signed bitvector to a floating point number.
  iSBVToFloat
    :: (1 <= w) => sym
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymInterpretedFloat sym fi)
  -- | Convert a real number to a floating point number.
  iRealToFloat
    :: sym
    -> FloatInfoRepr fi
    -> RoundingMode
    -> SymReal sym
    -> IO (SymInterpretedFloat sym fi)
  -- | Convert a floating point number to a unsigned bitvector.
  iFloatToBV
    :: (1 <= w)
    => sym
    -> NatRepr w
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a signed bitvector.
  iFloatToSBV
    :: (1 <= w)
    => sym
    -> NatRepr w
    -> RoundingMode
    -> SymInterpretedFloat sym fi
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a real number.
  iFloatToReal :: sym -> SymInterpretedFloat sym fi -> IO (SymReal sym)

  -- | The associated BaseType representative of the floating point
  -- interpretation for each format.
  iFloatBaseTypeRepr
    :: sym
    -> FloatInfoRepr fi
    -> BaseTypeRepr (SymInterpretedFloatType sym fi)

-- | Helper interface for creating new symbolic floating-point constants and
--   variables.
class (IsSymExprBuilder sym, IsInterpretedFloatExprBuilder sym) => IsInterpretedFloatSymExprBuilder sym where
  -- | Create a fresh top-level floating-point uninterpreted constant.
  freshFloatConstant
    :: sym
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (SymExpr sym (SymInterpretedFloatType sym fi))
  freshFloatConstant sym nm fi = freshConstant sym nm $ iFloatBaseTypeRepr sym fi

  -- | Create a fresh floating-point latch variable.
  freshFloatLatch
    :: sym
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (SymExpr sym (SymInterpretedFloatType sym fi))
  freshFloatLatch sym nm fi = freshLatch sym nm $ iFloatBaseTypeRepr sym fi

  -- | Creates a floating-point bound variable.
  freshFloatBoundVar
    :: sym
    -> SolverSymbol
    -> FloatInfoRepr fi
    -> IO (BoundVar sym (SymInterpretedFloatType sym fi))
  freshFloatBoundVar sym nm fi = freshBoundVar sym nm $ iFloatBaseTypeRepr sym fi
