{-|
Module      : Lang.Crucible.Solver.WeightedSum
Copyright   : (c) Galois Inc, 2015-2016
License     : AllRightsReserved
Maintainer  : jhendrix@galois.com

Declares a weighted sum type used for representing rational sums over variables
and an offset.
-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wwarn #-}
module Lang.Crucible.Solver.WeightedSum
  ( WeightedSum
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
  ) where

import           Control.Lens
import           Data.Bits
import           Data.Hashable
import           Data.Maybe
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           Data.Parameterized.Classes


-- | A weighted sum of real values.
--
-- The type 'c' is the type for coeffiecients (it is typically 'Integer' or 'Rational')
data WeightedSum c (t :: k -> *) i
   = WeightedSum { _sumMap :: !(Map.Map (t i) c)
                 , _sumHash :: !Int
                 , _sumOffset :: !c
                 }
  deriving (Eq, Ord)

-- | Created a weighted sum directly from a map and constant.
--
-- Note. When calling this, one should ensure map values equal to '0'
-- have been removed.
unfilteredSum :: (Hashable c, HashableF t) => Map.Map (t i) c -> c -> WeightedSum c t i
unfilteredSum m c = WeightedSum m (computeHash m) c

sumMap :: (Hashable c, HashableF t) => Simple Lens (WeightedSum c t i) (Map.Map (t i) c)
sumMap = lens _sumMap (\w m -> w{ _sumMap = m, _sumHash = computeHash m })

sumOffset :: Simple Lens (WeightedSum c t i) c
sumOffset = lens _sumOffset (\s v -> s { _sumOffset = v })

instance Hashable c => Hashable (WeightedSum c t i) where
  hashWithSalt s0 w =
    hashWithSalt (hashWithSalt s0 (_sumOffset w)) (_sumHash w)

computeHash :: (Hashable c, HashableF t) => Map.Map (t i) c -> Int
computeHash m = Map.foldlWithKey' h 0 m
    where h s k v = s `xor` hashWithSalt (hashF k) v


-- | Attempt to parse weighted sum as a constant
asConstant :: WeightedSum c t i -> Maybe c
asConstant w
  | Map.null (_sumMap w) = Just (_sumOffset w)
  | otherwise = Nothing

-- | Return true if weighted sum is equal to constant 0.
isZero :: (Eq c, Num c) => WeightedSum c t i -> Bool
isZero s = asConstant s == Just 0

-- | Attempt to parse weighted sum as a constant
asVar :: (Eq c, Num c) => WeightedSum c t i -> Maybe (t i)
asVar w
  | [(r,1)] <- Map.toList (_sumMap w)
  , _sumOffset w == 0
  = Just r
asVar _ = Nothing

-- | Create a sum from a rational value.
constant :: (Hashable c, HashableF t) => c -> WeightedSum c t i
constant = unfilteredSum Map.empty

-- | Traverse the expressions in a weighted sum.
traverseVars :: (Applicative m, Ord (k i), Hashable c, HashableF k)
            => (j i -> m (k i))
            -> WeightedSum c j i
            -> m (WeightedSum c k i)
traverseVars f w =
  flip unfilteredSum (_sumOffset w) <$> traverseMapKey f (_sumMap w)

-- | Traverse the keys in a Map
traverseMapKey :: (Applicative m, Ord k)
                  => (j -> m k)
                  -> Map j v
                  -> m (Map k v)
traverseMapKey f m =
  Map.fromList <$> traverse (_1 f) (Map.toList m)


-- | This returns a variable times a constant.
scaledVar :: (Eq c, Num c, Hashable c, HashableF t) => c -> t i -> WeightedSum c t i
scaledVar s t
  | s == 0 = unfilteredSum Map.empty 0
  | otherwise = unfilteredSum (Map.singleton t s) 0

-- | Create a weighted sum corresponding to the given variable.
var :: (Eq c, Num c, Hashable c, HashableF t) => t i -> WeightedSum c t i
var = scaledVar 1

-- | Create a weighted sum equal to the sum of the two variables.
addVars :: (Eq c, Num c, Ord (t i), Hashable c, HashableF t)
        => t i -> t i -> WeightedSum c t i
addVars x y
    | x == y = scaledVar 2 x
    | otherwise = unfilteredSum zm 0
  where zm = Map.fromList [(x, 1), (y,1)]

-- | Add two sums.
add :: (HashableF t, Ord (t i))
    => WeightedSum Rational t i
    -> WeightedSum Rational t i
    -> WeightedSum Rational t i
add x y = unfilteredSum zm zc
  where merge _ u v | r == 0 = Nothing
                    | otherwise = Just r
          where r = u + v
        zm = Map.mergeWithKey merge id id (_sumMap x) (_sumMap y)
        zc = x^.sumOffset + y^.sumOffset

-- | Add a variable to the sum.
addVar :: (Ord (t i), HashableF t)
       => WeightedSum Rational t i -> t i -> WeightedSum Rational t i
addVar x y = x{ _sumMap  = if newval == 0 then Map.delete y m' else m'
              , _sumHash = _sumHash x `xor` oldHash `xor` newHash
              }
  where
   (oldv, m') = Map.insertLookupWithKey (\_ a b -> a+b) y 1 (_sumMap x)
   oldval     = fromMaybe 0 oldv
   newval     = oldval + 1
   oldHash    = maybe 0 (hashWithSalt (hashF y)) oldv
   newHash    = hashWithSalt (hashF y) newval

-- | Add a rational to the sum.
addConstant :: Num c => WeightedSum c t i -> c -> WeightedSum c t i
addConstant x r = x & sumOffset +~ r

-- | Multiply a sum by a rational coefficient.
scale :: (Eq c, Num c, Hashable c, HashableF t)
      => c -> WeightedSum c t i -> WeightedSum c t i
scale 0 _ = constant 0
scale c x = x & sumMap    %~ fmap (c*)
              & sumOffset %~ (c*)

-- | Evaluate a sum given interpretations of addition, scalar multiplication, and
-- a constant rational.
eval :: (Eq c, Num c)
     => (r -> r -> r)
        -- ^ Addition function
     -> (c -> t i -> r)
        -- ^ Scalar multiply
     -> (c -> r)
        -- ^ Constant evaluation
     -> WeightedSum c t i
     -> r
eval addFn smul rat w
   | _sumOffset w == 0 =
     case Map.minViewWithKey (_sumMap w) of
       Nothing -> rat 0
       Just ((e,s),m') -> Map.foldrWithKey' merge (smul s e) m'
   | otherwise = Map.foldrWithKey' merge (rat (_sumOffset w)) (_sumMap w)
  where merge e s r = addFn (smul s e) r
{-# INLINABLE eval #-}


{-# INLINABLE extractCommon #-}

-- | Given two weighted sums x and y, this returns a triple (z,x',y')
-- where "x = z + x'" and "y = z + y'" and "z" contains the "common"
-- parts of "x" and "y".
--
-- This is primarily used to simplify if-then-else expressions over
-- reals to preserve shared subterms.
extractCommon :: (Eq c, Num c, Ord (t i), Hashable c, HashableF t)
                 => WeightedSum c t i
                 -> WeightedSum c t i
                 -> (WeightedSum c t i, WeightedSum c t i, WeightedSum c t i)
extractCommon (WeightedSum xm _ xc) (WeightedSum ym _ yc) = (z, x', y')

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
