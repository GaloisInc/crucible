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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wwarn #-}
module What4.Expr.WeightedSum
  ( WrapF(..)
  , Tm
  , WeightedSum
  , sumRepr
  , sumOffset
  , constant
  , var
  , scaledVar
  , asConstant
  , asVar
  , isZero
  , traverseVars
  , add
  , addVar
  , addVars
  , addConstant
  , scale
  , eval
  , evalM
  , extractCommon
  , fromTerms
  , transformSum
  , reduceIntSumMod
  ) where

import           Control.Lens
import           Control.Monad.State
import           Data.Bits
import           Data.Hashable
import           Data.Kind
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Parameterized.Classes

import           What4.BaseTypes
import qualified What4.SemiRing as SR

type Tm f = (HashableF f, OrdF f)

newtype WrapF (f:: BaseType -> Type) (i :: SR.SemiRing) = WrapF (f (SR.SemiRingBase i))

instance OrdF f => Ord (WrapF f i) where
  compare (WrapF x) (WrapF y) = toOrdering $ compareF x y
instance TestEquality f => Eq (WrapF f i) where
  (WrapF x) == (WrapF y) = isJust $ testEquality x y
instance HashableF f => Hashable (WrapF f i) where
  hashWithSalt s (WrapF x) = hashWithSaltF s x

traverseWrap :: Functor m => (f (SR.SemiRingBase i) -> m (g (SR.SemiRingBase i))) -> WrapF f i -> m (WrapF g i)
traverseWrap f (WrapF x) = WrapF <$> f x

-- | A weighted sum of real values.
--
-- The type 'c' is the type for coeffiecients
data WeightedSum (f :: BaseType -> Type) (sr :: SR.SemiRing)
   = WeightedSum { _sumMap     :: !(Map (WrapF f sr) (SR.Coefficient sr))
                 , _sumOffset  :: !(SR.Coefficient sr)
                 , _sumHash    :: !Int -- ^ precomputed hash of the map part of the weighted sum
                 , sumRepr     :: SR.SemiRingRepr sr
                 }


listEqBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
listEqBy _ [] [] = True
listEqBy f (x:xs) (y:ys)
  | f x y = listEqBy f xs ys
listEqBy _ _ _ = False

mapEqBy :: Ord k => (a -> a -> Bool) -> Map k a -> Map k a -> Bool
mapEqBy f x y = listEqBy (\(kx,ax) (ky,ay) -> kx == ky && f ax ay) (Map.toAscList x) (Map.toAscList y)

instance OrdF f => TestEquality (WeightedSum f) where
  testEquality x y
    | _sumHash x /= _sumHash y = Nothing
    | otherwise =
         do Refl <- testEquality (sumRepr x) (sumRepr y)
            unless (SR.eq (sumRepr x) (_sumOffset x) (_sumOffset y)) Nothing
            unless (mapEqBy (SR.eq (sumRepr x)) (_sumMap x) (_sumMap y)) Nothing
            return Refl


-- | Created a weighted sum directly from a map and constant.
--
-- Note. When calling this, one should ensure map values equal to '0'
-- have been removed.
unfilteredSum ::
  HashableF f =>
  SR.SemiRingRepr sr ->
  Map (WrapF f sr) (SR.Coefficient sr) ->
  SR.Coefficient sr ->
  WeightedSum f sr
unfilteredSum sr m c = WeightedSum m c (computeHash sr m) sr

sumMap :: HashableF f => Simple Lens (WeightedSum f sr) (Map (WrapF f sr) (SR.Coefficient sr))
sumMap = lens _sumMap (\w m -> w{ _sumMap = m, _sumHash = computeHash (sumRepr w) m })

sumOffset :: Simple Lens (WeightedSum f sr) (SR.Coefficient sr)
sumOffset = lens _sumOffset (\s v -> s { _sumOffset = v })

instance Hashable (WeightedSum f sr) where
  hashWithSalt s0 w =
    hashWithSalt (SR.sr_hashWithSalt (sumRepr w) s0 (_sumOffset w)) (_sumHash w)

computeHash :: HashableF f => SR.SemiRingRepr sr -> Map (WrapF f sr) (SR.Coefficient sr) -> Int
computeHash sr m = Map.foldlWithKey' h 0 m
    where h s k v = s `xor` SR.sr_hashWithSalt sr (hash k) v

-- | Attempt to parse weighted sum as a constant
asConstant :: WeightedSum f sr -> Maybe (SR.Coefficient sr)
asConstant w
  | Map.null (_sumMap w) = Just (_sumOffset w)
  | otherwise = Nothing

-- | Return true if weighted sum is equal to constant 0.
isZero :: SR.SemiRingRepr sr -> WeightedSum f sr -> Bool
isZero sr s =
   case asConstant s of
     Just c  -> SR.sr_compare sr (SR.zero sr) c == EQ
     Nothing -> False

-- | Attempt to parse weighted sum as a constant
asVar :: WeightedSum f sr -> Maybe (f (SR.SemiRingBase sr))
asVar w
  | [(WrapF r,c)] <- Map.toList (_sumMap w)
  , let sr = sumRepr w
  , SR.eq sr (SR.one sr) c
  , SR.eq sr (SR.zero sr) (_sumOffset w)
  = Just r

  | otherwise
  = Nothing

-- | Create a sum from a rational value.
constant :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> WeightedSum f sr
constant sr = unfilteredSum sr Map.empty

-- | Traverse the expressions in a weighted sum.
traverseVars :: forall k j m sr.
  (Applicative m, Tm k) =>
  (j (SR.SemiRingBase sr) -> m (k (SR.SemiRingBase sr))) ->
  WeightedSum j sr ->
  m (WeightedSum k sr)
traverseVars f w =
  (\m -> unfilteredSum (sumRepr w) m (_sumOffset w))
    <$> traverseMapKey (traverseWrap f) (_sumMap w)

-- | Traverse the keys in a Map
traverseMapKey :: (Applicative m, Ord k) =>
  (j -> m k) -> Map j v -> m (Map k v)
traverseMapKey f m =
  Map.fromList <$> traverse (_1 f) (Map.toList m)

-- | This returns a variable times a constant.
scaledVar :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> f (SR.SemiRingBase sr) -> WeightedSum f sr
scaledVar sr s t
  | SR.eq sr (SR.zero sr) s = unfilteredSum sr Map.empty (SR.zero sr)
  | otherwise = unfilteredSum sr (Map.singleton (WrapF t) s) (SR.zero sr)

-- | Create a weighted sum corresponding to the given variable.
var :: Tm f => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> WeightedSum f sr
var sr t = unfilteredSum sr (Map.singleton (WrapF t) (SR.one sr)) (SR.zero sr)

-- | Add two sums.
add ::
  Tm f =>
  SR.SemiRingRepr sr ->
  WeightedSum f sr ->
  WeightedSum f sr ->
  WeightedSum f sr
add sr x y = unfilteredSum sr zm zc
  where merge _ u v | SR.eq sr r (SR.zero sr) = Nothing
                    | otherwise               = Just r
          where r = SR.add sr u v
        zm = Map.mergeWithKey merge id id (_sumMap x) (_sumMap y)
        zc = SR.add sr (x^.sumOffset) (y^.sumOffset)

addVars ::
  Tm f =>
  SR.SemiRingRepr sr ->
  f (SR.SemiRingBase sr) ->
  f (SR.SemiRingBase sr) ->
  WeightedSum f sr
addVars sr x y
  | x' == y'  = scaledVar sr (SR.add sr (SR.one sr) (SR.one sr)) x
  | otherwise = unfilteredSum sr (Map.fromList [(x', SR.one sr),(y', SR.one sr)]) (SR.zero sr)
 where
 x' = WrapF x
 y' = WrapF y

-- | Add a variable to the sum.
addVar ::
  Tm f =>
  SR.SemiRingRepr sr ->
  WeightedSum f sr -> f (SR.SemiRingBase sr) -> WeightedSum f sr
addVar sr x y = x{ _sumMap  = m'
                 , _sumHash = _sumHash x `xor` hashAdjust
                 }
  where
   (m', hashAdjust) = runState (Map.alterF f y' (_sumMap x)) 0

   f Nothing  = do put (SR.sr_hashWithSalt sr (hash y') (SR.one sr))
                   return (Just (SR.one sr))
   f (Just c) = let c' = SR.add sr c (SR.one sr) in
                if SR.eq sr c' (SR.zero sr) then
                  do put (SR.sr_hashWithSalt sr (hash y') c)
                     return Nothing
                else
                  do put (SR.sr_hashWithSalt sr (hash y') c `xor` SR.sr_hashWithSalt sr (hash y') c')
                     return (Just c')
   y' = WrapF y

-- | Add a constant to the sum
addConstant :: SR.SemiRingRepr sr -> WeightedSum f sr -> SR.Coefficient sr -> WeightedSum f sr
addConstant sr x r = x & sumOffset %~ SR.add sr r

-- | Multiply a sum by a rational coefficient.
scale :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> WeightedSum f sr -> WeightedSum f sr
scale sr c x
 | SR.eq sr c (SR.zero sr) = constant sr (SR.zero sr)
 | otherwise = x & sumMap    %~ fmap (SR.mul sr c)
                 & sumOffset %~ (SR.mul sr c)

fromTerms ::
  Tm f =>
  SR.SemiRingRepr sr ->
  [(WrapF f sr, SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  WeightedSum f sr
fromTerms sr tms offset = unfilteredSum sr m offset
  where
  m = Map.filter (not . SR.eq sr (SR.zero sr)) (Map.fromListWith (SR.add sr) tms)

transformSum :: (Applicative m, Tm g) =>
  SR.SemiRingRepr sr' ->
  (SR.Coefficient sr -> m (SR.Coefficient sr')) ->
  (f (SR.SemiRingBase sr) -> m (g (SR.SemiRingBase sr'))) ->
  WeightedSum f sr ->
  m (WeightedSum g sr')
transformSum sr' transCoef transTm s = fromTerms sr' <$> tms <*> c
  where
  f (WrapF t, x) = (\t' x' -> (WrapF t', x')) <$> transTm t <*> transCoef x
  tms = traverse f (Map.toList (_sumMap s))
  c   = transCoef (_sumOffset s)


-- | Evaluate a sum given interpretations of addition, scalar multiplication, and
-- a constant.  This evaluation is threaded through a monad.
evalM :: Monad m =>
  (r -> r -> m r) {- ^ Addition function -} ->
  (SR.Coefficient sr -> f (SR.SemiRingBase sr) -> m r) {- ^ Scalar multiply -} ->
  (SR.Coefficient sr -> m r) {- ^ Constant evaluation -} ->
  WeightedSum f sr ->
  m r
evalM addFn smul cnst sm
   | SR.eq sr (_sumOffset sm) (SR.zero sr) =

     case Map.minViewWithKey (_sumMap sm) of
       Nothing ->
         cnst (SR.zero sr)

       Just ((WrapF e,s),m') ->
         go (Map.toList m') =<< smul s e

   | otherwise =
         go (Map.toList (_sumMap sm)) =<< cnst (_sumOffset sm)

  where
  sr = sumRepr sm

  go [] x = return x
  go ((WrapF e, s):xs) x = go xs =<< addFn x =<< smul s e

-- | Evaluate a sum given interpretations of addition, scalar multiplication, and
-- a constant rational.
eval ::
  (r -> r -> r) {- ^ Addition function -} ->
  (SR.Coefficient sr -> f (SR.SemiRingBase sr) -> r) {- ^ Scalar multiply -} ->
  (SR.Coefficient sr -> r) {- ^ Constant evaluation -} ->
  WeightedSum f sr ->
  r
eval addFn smul cnst w
   | SR.eq sr (_sumOffset w) (SR.zero sr) =
     case Map.minViewWithKey (_sumMap w) of
       Nothing -> cnst (SR.zero sr)
       Just ((WrapF e,s),m') -> Map.foldrWithKey' merge (smul s e) m'

   | otherwise = Map.foldrWithKey' merge (cnst (_sumOffset w)) (_sumMap w)

  where
  merge (WrapF e) s r = addFn (smul s e) r
  sr = sumRepr w


{-# INLINABLE eval #-}

-- | Reduce a weighted sum of integers modulo a concrete integer.
--   This reduces each of the coefficents modulo the given integer,
--   removing any that are congruent to 0; the offset value is
--   also reduced.
reduceIntSumMod :: (OrdF f, HashableF f) =>
  WeightedSum f SR.SemiRingInteger {- ^ The sum to reduce -} ->
  Integer {- ^ The modulus, must not be 0 -} ->
  WeightedSum f SR.SemiRingInteger
reduceIntSumMod ws k = unfilteredSum SR.SemiRingIntegerRepr m (ws^.sumOffset `mod` k)
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
extractCommon ::
  Tm f =>
  WeightedSum f sr ->
  WeightedSum f sr ->
  (WeightedSum f sr, WeightedSum f sr, WeightedSum f sr)
extractCommon (WeightedSum xm xc _ sr) (WeightedSum ym yc _ _) = (z, x', y')

  where mergeCommon _ xv yv
          | SR.eq sr xv yv  = Just xv
          | otherwise       = Nothing

        zm = Map.mergeWithKey mergeCommon (const Map.empty) (const Map.empty) xm ym

        (zc,xc',yc')
           | SR.eq sr xc yc = (xc, SR.zero sr, SR.zero sr)
           | otherwise      = (SR.zero sr, xc, yc)

        z = unfilteredSum sr zm zc

        x' = unfilteredSum sr (xm `Map.difference` zm) xc'
        y' = unfilteredSum sr (ym `Map.difference` zm) yc'
