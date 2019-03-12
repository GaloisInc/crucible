{-|
[Module      : What4.SemiRing
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com

Definitions related to semi-ring structures over base types
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.SemiRing
  ( type SemiRing
  , type SemiRingNat
  , type SemiRingInteger
  , type SemiRingReal
  , type SemiRingBV
  , type BVFlavor
  , type BVBits
  , type BVArith
  , SemiRingRepr(..)
  , OrderedSemiRingRepr(..)
  , BVFlavorRepr(..)
  , SemiRingBase
  , Coefficient
  , semiRingBase
  , orderedSemiRing
  , zero
  , one
  , add
  , mul
  , eq
  , le
  , lt
  , sr_compare
  , sr_hashWithSalt
  ) where

import GHC.TypeNats
import Data.Bits
import Data.Kind
import Data.Hashable
import Data.Parameterized.Classes
import Data.Parameterized.TH.GADT
import Data.Parameterized.NatRepr
import Numeric.Natural

import What4.BaseTypes

data BVFlavor = BVArith | BVBits

data SemiRing
  = SemiRingNat
  | SemiRingInteger
  | SemiRingReal
  | SemiRingBV BVFlavor Nat

type BVArith = 'BVArith
type BVBits  = 'BVBits

type SemiRingNat = 'SemiRingNat
type SemiRingInteger = 'SemiRingInteger
type SemiRingReal = 'SemiRingReal
type SemiRingBV = 'SemiRingBV

data BVFlavorRepr (fv :: BVFlavor) where
  BVArithRepr :: BVFlavorRepr BVArith
  BVBitsRepr  :: BVFlavorRepr BVBits

data SemiRingRepr (sr :: SemiRing) where
  SemiRingNatRepr     :: SemiRingRepr SemiRingNat
  SemiRingIntegerRepr :: SemiRingRepr SemiRingInteger
  SemiRingRealRepr    :: SemiRingRepr SemiRingReal
  SemiRingBVRepr      :: (1 <= w) => !(BVFlavorRepr fv) -> !(NatRepr w) -> SemiRingRepr (SemiRingBV fv w)

data OrderedSemiRingRepr (sr :: SemiRing) where
  OrderedSemiRingNatRepr     :: OrderedSemiRingRepr SemiRingNat
  OrderedSemiRingIntegerRepr :: OrderedSemiRingRepr SemiRingInteger
  OrderedSemiRingRealRepr    :: OrderedSemiRingRepr SemiRingReal

semiRingBase :: SemiRingRepr sr -> BaseTypeRepr (SemiRingBase sr)
semiRingBase SemiRingNatRepr     = BaseNatRepr
semiRingBase SemiRingIntegerRepr = BaseIntegerRepr
semiRingBase SemiRingRealRepr    = BaseRealRepr
semiRingBase (SemiRingBVRepr _fv w)  = BaseBVRepr w

orderedSemiRing :: OrderedSemiRingRepr sr -> SemiRingRepr sr
orderedSemiRing OrderedSemiRingNatRepr     = SemiRingNatRepr
orderedSemiRing OrderedSemiRingIntegerRepr = SemiRingIntegerRepr
orderedSemiRing OrderedSemiRingRealRepr    = SemiRingRealRepr

type family SemiRingBase (sr :: SemiRing) :: BaseType where
  SemiRingBase SemiRingNat       = BaseNatType
  SemiRingBase SemiRingInteger   = BaseIntegerType
  SemiRingBase SemiRingReal      = BaseRealType
  SemiRingBase (SemiRingBV fv w) = BaseBVType w

type family Coefficient (sr :: SemiRing) :: Type where
  Coefficient SemiRingNat        = Natural
  Coefficient SemiRingInteger    = Integer
  Coefficient SemiRingReal       = Rational
  Coefficient (SemiRingBV fv w)  = Integer

sr_compare :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Ordering
sr_compare SemiRingNatRepr      = compare
sr_compare SemiRingIntegerRepr  = compare
sr_compare SemiRingRealRepr     = compare
sr_compare (SemiRingBVRepr _ _) = compare


sr_hashWithSalt :: SemiRingRepr sr -> Int -> Coefficient sr -> Int
sr_hashWithSalt SemiRingNatRepr      = hashWithSalt
sr_hashWithSalt SemiRingIntegerRepr  = hashWithSalt
sr_hashWithSalt SemiRingRealRepr     = hashWithSalt
sr_hashWithSalt (SemiRingBVRepr _ _) = hashWithSalt


zero :: SemiRingRepr sr -> Coefficient sr
zero SemiRingNatRepr          = 0 :: Natural
zero SemiRingIntegerRepr      = 0 :: Integer
zero SemiRingRealRepr         = 0 :: Rational
zero (SemiRingBVRepr BVArithRepr _) = 0 :: Integer
zero (SemiRingBVRepr BVBitsRepr _)  = 0 :: Integer

one :: SemiRingRepr sr -> Coefficient sr
one SemiRingNatRepr              = 1 :: Natural
one SemiRingIntegerRepr          = 1 :: Integer
one SemiRingRealRepr             = 1 :: Rational
one (SemiRingBVRepr BVArithRepr _) = 1 :: Integer
one (SemiRingBVRepr BVBitsRepr w)  = maxUnsigned w :: Integer

add :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Coefficient sr
add SemiRingNatRepr          = (+)
add SemiRingIntegerRepr      = (+)
add SemiRingRealRepr         = (+)
add (SemiRingBVRepr BVArithRepr w) = \x y -> toUnsigned w (x + y)
add (SemiRingBVRepr BVBitsRepr _)  = xor

mul :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Coefficient sr
mul SemiRingNatRepr          = (*)
mul SemiRingIntegerRepr      = (*)
mul SemiRingRealRepr         = (*)
mul (SemiRingBVRepr BVArithRepr w) = \x y -> toUnsigned w (x * y)
mul (SemiRingBVRepr BVBitsRepr _)  = (.&.)

eq :: SemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
eq SemiRingNatRepr          = (==)
eq SemiRingIntegerRepr      = (==)
eq SemiRingRealRepr         = (==)
eq (SemiRingBVRepr _ _)     = (==)

le :: OrderedSemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
le OrderedSemiRingNatRepr     = (<=)
le OrderedSemiRingIntegerRepr = (<=)
le OrderedSemiRingRealRepr    = (<=)

lt :: OrderedSemiRingRepr sr -> Coefficient sr -> Coefficient sr -> Bool
lt OrderedSemiRingNatRepr     = (<)
lt OrderedSemiRingIntegerRepr = (<)
lt OrderedSemiRingRealRepr    = (<)

$(return [])

instance TestEquality BVFlavorRepr where
  testEquality = $(structuralTypeEquality [t|BVFlavorRepr|] [])

instance TestEquality OrderedSemiRingRepr where
  testEquality = $(structuralTypeEquality [t|OrderedSemiRingRepr|] [])

instance TestEquality SemiRingRepr where
  testEquality =
    $(structuralTypeEquality [t|SemiRingRepr|]
      [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|testEquality|])
      , (ConType [t|BVFlavorRepr|] `TypeApp` AnyType, [|testEquality|])
      ])

instance OrdF BVFlavorRepr where
  compareF = $(structuralTypeOrd [t|BVFlavorRepr|] [])

instance OrdF OrderedSemiRingRepr where
  compareF = $(structuralTypeOrd [t|OrderedSemiRingRepr|] [])

instance OrdF SemiRingRepr where
  compareF =
    $(structuralTypeOrd [t|SemiRingRepr|]
      [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|compareF|])
      , (ConType [t|BVFlavorRepr|] `TypeApp` AnyType, [|compareF|])
      ])

instance HashableF BVFlavorRepr where
  hashWithSaltF = $(structuralHash [t|BVFlavorRepr|])
instance Hashable (BVFlavorRepr fv) where
  hashWithSalt = hashWithSaltF

instance HashableF OrderedSemiRingRepr where
  hashWithSaltF = $(structuralHash [t|OrderedSemiRingRepr|])
instance Hashable (OrderedSemiRingRepr sr) where
  hashWithSalt = hashWithSaltF

instance HashableF SemiRingRepr where
  hashWithSaltF = $(structuralHash [t|SemiRingRepr|])
instance Hashable (SemiRingRepr sr) where
  hashWithSalt = hashWithSaltF
