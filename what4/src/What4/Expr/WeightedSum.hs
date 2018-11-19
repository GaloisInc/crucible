{-|
Module      : What4.Expr.WeightedSum
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

Declares a weighted sum type used for representing sums over variables and an offset.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wwarn #-}
module What4.Expr.WeightedSum
  ( SemiRingCoefficient(..)
  , SemiRing
  , semiRingBase
  , SemiRingRepr(..)
  , semiringCompare
  , WrapF(..)

  , WeightedSum
  , constant
  , var
  , scaledVar
  , asConstant
  , asVar
  , isZero
  , traverseVars
  , add
  , addVar
  , addConstant
  , addVars
  , scale
  , eval
  , extractCommon
  , reduceIntSumMod
  ) where

import           Control.Lens
import           Data.Bits
import           Data.Hashable
import           Data.Kind
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import           Numeric.Natural

import           What4.BaseTypes


newtype WrapF (f:: k -> Type) (i :: k) = WrapF (f i)

instance OrdF f => Ord (WrapF f i) where
  compare (WrapF x) (WrapF y) = toOrdering $ compareF x y
instance TestEquality f => Eq (WrapF f i) where
  (WrapF x) == (WrapF y) = isJust $ testEquality x y
instance HashableF f => Hashable (WrapF f i) where
  hashWithSalt s (WrapF x) = hashWithSaltF s x

traverseWrap :: Functor m => (f i -> m (g i)) -> WrapF f i -> m (WrapF g i)
traverseWrap f (WrapF x) = WrapF <$> f x

class (Eq (Coefficient tp), Num (Coefficient tp), Hashable (Coefficient tp)) => SemiRingCoefficient tp where
  type Coefficient tp :: Type

type SemiRing f tp = (OrdF f, HashableF f, SemiRingCoefficient tp)

instance SemiRingCoefficient BaseRealType where
  type Coefficient BaseRealType = Rational
instance SemiRingCoefficient BaseIntegerType where
  type Coefficient BaseIntegerType = Integer
instance SemiRingCoefficient BaseNatType where
  type Coefficient BaseNatType = Natural


data SemiRingRepr (tp :: BaseType) where
  SemiRingNat  :: SemiRingRepr BaseNatType
  SemiRingInt  :: SemiRingRepr BaseIntegerType
  SemiRingReal :: SemiRingRepr BaseRealType

instance KnownRepr SemiRingRepr BaseNatType
  where knownRepr = SemiRingNat
instance KnownRepr SemiRingRepr BaseIntegerType
  where knownRepr = SemiRingInt
instance KnownRepr SemiRingRepr BaseRealType
  where knownRepr = SemiRingReal

instance TestEquality SemiRingRepr where
  testEquality SemiRingNat  SemiRingNat  = Just Refl
  testEquality SemiRingInt  SemiRingInt  = Just Refl
  testEquality SemiRingReal SemiRingReal = Just Refl
  testEquality _            _            = Nothing

instance OrdF SemiRingRepr where
  compareF SemiRingNat  SemiRingNat  = EQF
  compareF _            SemiRingNat  = GTF
  compareF SemiRingNat  _            = LTF

  compareF SemiRingInt  SemiRingInt  = EQF
  compareF _            SemiRingInt  = GTF
  compareF SemiRingInt  _            = LTF

  compareF SemiRingReal SemiRingReal = EQF

instance HashableF SemiRingRepr where
  hashWithSaltF s SemiRingNat  = hashWithSalt s (0 :: Int)
  hashWithSaltF s SemiRingInt  = hashWithSalt s (1 :: Int)
  hashWithSaltF s SemiRingReal = hashWithSalt s (2 :: Int)

instance Hashable (SemiRingRepr tp) where
  hashWithSalt = hashWithSaltF


semiRingBase :: SemiRingRepr tp -> BaseTypeRepr tp
semiRingBase SemiRingNat  = BaseNatRepr
semiRingBase SemiRingInt  = BaseIntegerRepr
semiRingBase SemiRingReal = BaseRealRepr

-- | A weighted sum of real values.
--
-- The type 'c' is the type for coeffiecients
data WeightedSum (f :: BaseType -> Type) tp
   = WeightedSum { _sumMap     :: !(Map (WrapF f tp) (Coefficient tp))
                 , _sumOffset  :: !(Coefficient tp)
                 , _sumHash    :: !Int -- ^ precomputed hash of the map part of the weighted sum
                 }

deriving instance (TestEquality f, Eq (Coefficient tp)) => Eq (WeightedSum f tp)
deriving instance (OrdF f, Ord (Coefficient tp)) => Ord (WeightedSum f tp)

semiringCompare :: SemiRingRepr tp -> Coefficient tp -> Coefficient tp -> Ordering
semiringCompare SemiRingNat  = compare
semiringCompare SemiRingInt  = compare
semiringCompare SemiRingReal = compare


-- | Created a weighted sum directly from a map and constant.
--
-- Note. When calling this, one should ensure map values equal to '0'
-- have been removed.
unfilteredSum :: SemiRing f tp => Map (WrapF f tp) (Coefficient tp) -> Coefficient tp -> WeightedSum f tp
unfilteredSum m c = WeightedSum m c (computeHash m)

sumMap :: SemiRing f tp => Simple Lens (WeightedSum f tp) (Map (WrapF f tp) (Coefficient tp))
sumMap = lens _sumMap (\w m -> w{ _sumMap = m, _sumHash = computeHash m })

sumOffset :: Simple Lens (WeightedSum f tp) (Coefficient tp)
sumOffset = lens _sumOffset (\s v -> s { _sumOffset = v })

instance SemiRing f tp => Hashable (WeightedSum f tp) where
  hashWithSalt s0 w =
    hashWithSalt (hashWithSalt s0 (_sumOffset w)) (_sumHash w)

computeHash :: SemiRing f tp => Map (WrapF f tp) (Coefficient tp) -> Int
computeHash m = Map.foldlWithKey' h 0 m
    where h s k v = s `xor` hashWithSalt (hash k) v

-- | Attempt to parse weighted sum as a constant
asConstant :: WeightedSum f tp -> Maybe (Coefficient tp)
asConstant w
  | Map.null (_sumMap w) = Just (_sumOffset w)
  | otherwise = Nothing

-- | Return true if weighted sum is equal to constant 0.
isZero :: SemiRing f tp => WeightedSum f tp -> Bool
isZero s = asConstant s == Just 0

-- | Attempt to parse weighted sum as a constant
asVar :: SemiRing f tp => WeightedSum f tp -> Maybe (f tp)
asVar w
  | [(WrapF r,1)] <- Map.toList (_sumMap w)
  , _sumOffset w == 0
  = Just r
asVar _ = Nothing

-- | Create a sum from a rational value.
constant :: SemiRing f tp => Coefficient tp -> WeightedSum f tp
constant = unfilteredSum Map.empty

-- | Traverse the expressions in a weighted sum.
traverseVars :: (Applicative m, SemiRing j tp, SemiRing k tp)
            => (j tp -> m (k tp))
            -> WeightedSum j tp
            -> m (WeightedSum k tp)
traverseVars f w =
  flip unfilteredSum (_sumOffset w) <$> traverseMapKey (traverseWrap f) (_sumMap w)

-- | Traverse the keys in a Map
traverseMapKey :: (Applicative m, Ord k)
                  => (j -> m k)
                  -> Map j v
                  -> m (Map k v)
traverseMapKey f m =
  Map.fromList <$> traverse (_1 f) (Map.toList m)

-- | This returns a variable times a constant.
scaledVar :: SemiRing f tp => Coefficient tp -> f tp -> WeightedSum f tp
scaledVar s t
  | s == 0 = unfilteredSum Map.empty 0
  | otherwise = unfilteredSum (Map.singleton (WrapF t) s) 0

-- | Create a weighted sum corresponding to the given variable.
var :: SemiRing f tp => f tp -> WeightedSum f tp
var t = unfilteredSum (Map.singleton (WrapF t) 1) 0

-- | Create a weighted sum equal to the sum of the two variables.
addVars :: SemiRing f tp
        => f tp -> f tp -> WeightedSum f tp
addVars x y
    | x' == y'  = scaledVar 2 x
    | otherwise = unfilteredSum zm 0
  where zm = Map.fromList [(x',1), (y',1)]
        x' = WrapF x
        y' = WrapF y

-- | Add two sums.
add :: SemiRing f tp
    => WeightedSum f tp
    -> WeightedSum f tp
    -> WeightedSum f tp
add x y = unfilteredSum zm zc
  where merge _ u v | r == 0 = Nothing
                    | otherwise = Just r
          where r = u + v
        zm = Map.mergeWithKey merge id id (_sumMap x) (_sumMap y)
        zc = x^.sumOffset + y^.sumOffset

-- | Add a variable to the sum.
addVar :: SemiRing f tp
       => WeightedSum f tp -> f tp -> WeightedSum f tp
addVar x y = x{ _sumMap  = if newval == 0 then Map.delete (WrapF y) m' else m'
              , _sumHash = _sumHash x `xor` oldHash `xor` newHash
              }
  where
   (oldv, m') = Map.insertLookupWithKey (\_ a b -> a+b) (WrapF y) 1 (_sumMap x)
   oldval     = fromMaybe 0 oldv
   newval     = oldval + 1
   oldHash    = maybe 0 (hashWithSalt (hash (WrapF y))) oldv
   newHash    = hashWithSalt (hash (WrapF y)) newval

-- | Add a rational to the sum.
addConstant :: SemiRing f tp => WeightedSum f tp -> Coefficient tp -> WeightedSum f tp
addConstant x r = x & sumOffset +~ r

-- | Multiply a sum by a rational coefficient.
scale :: SemiRing f tp
      => Coefficient tp -> WeightedSum f tp -> WeightedSum f tp
scale 0 _ = constant 0
scale c x = x & sumMap    %~ fmap (c*)
              & sumOffset %~ (c*)

-- | Evaluate a sum given interpretations of addition, scalar multiplication, and
-- a constant rational.
eval :: SemiRing f tp
     => (r -> r -> r)
        -- ^ Addition function
     -> (Coefficient tp -> f tp -> r)
        -- ^ Scalar multiply
     -> (Coefficient tp -> r)
        -- ^ Constant evaluation
     -> WeightedSum f tp
     -> r
eval addFn smul rat w
   | _sumOffset w == 0 =
     case Map.minViewWithKey (_sumMap w) of
       Nothing -> rat 0
       Just ((WrapF e,s),m') -> Map.foldrWithKey' merge (smul s e) m'
   | otherwise = Map.foldrWithKey' merge (rat (_sumOffset w)) (_sumMap w)
  where merge (WrapF e) s r = addFn (smul s e) r
{-# INLINABLE eval #-}

-- | Reduce a weighted sum of integers modulo a concrete integer.
--   This reduces each of the coefficents modulo the given integer,
--   removing any that are congruent to 0; the offset value is
--   also reduced.
reduceIntSumMod :: (OrdF f, HashableF f) =>
  WeightedSum f BaseIntegerType {- ^ The sum to reduce -} ->
  Integer {- ^ The modulus, must not be 0 -} ->
  WeightedSum f BaseIntegerType
reduceIntSumMod ws k = unfilteredSum m (ws^.sumOffset `mod` k)
  where
  m = runIdentity (Map.traverseMaybeWithKey f (ws^.sumMap))
  f _key x
    | x' == 0   = return (Nothing)
    | otherwise = return (Just x')
   where x' = x `mod` k


{-# INLINABLE extractCommon #-}

-- | Given two weighted sums x and y, this returns a triple (z,x',y')
-- where "x = z + x'" and "y = z + y'" and "z" contains the "common"
-- parts of "x" and "y".
--
-- This is primarily used to simplify if-then-else expressions over
-- reals to preserve shared subterms.
extractCommon :: SemiRing f tp
              => WeightedSum f tp
              -> WeightedSum f tp
              -> (WeightedSum f tp, WeightedSum f tp, WeightedSum f tp)
extractCommon (WeightedSum xm xc _) (WeightedSum ym yc _) = (z, x', y')

  where mergeCommon _ xv yv
          | xv == yv  = Just xv
          | otherwise = Nothing

        -- For the
        zm = Map.mergeWithKey mergeCommon (const Map.empty) (const Map.empty) xm ym

        -- We next need to figure out if we want to extract a constant from the two
        -- values.  Currently, we do not, but in principal we could change this to
        -- shift the results closer to zero.
        zc | xc == yc = xc
           | otherwise = 0
{-
        -- Old code which shifted result to zero.
        zc | signum xc * signum yc /= 1 = 0
           | abs xc < abs yc = xc
           | otherwise = yc
-}
        z = unfilteredSum zm zc

        x' = unfilteredSum (xm `Map.difference` zm) (xc - zc)
        y' = unfilteredSum (ym `Map.difference` zm) (yc - zc)
