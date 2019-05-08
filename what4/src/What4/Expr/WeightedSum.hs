{-|
Module      : What4.Expr.WeightedSum
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

Declares a weighted sum type used for representing sums over variables and an offset
in one of the supported semirings.  This module also implements a representation of
semiring products.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}

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
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}
module What4.Expr.WeightedSum
  ( -- * Utilities
    WrapF(..)
  , Tm
    -- * Weighted sums
  , WeightedSum
  , sumRepr
  , sumOffset
  , constant
  , var
  , scaledVar
  , asConstant
  , asVar
  , asWeightedVar
  , asAffineVar
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

    -- * Ring products
  , SemiRingProduct
  , traverseProdVars
  , nullProd
  , asProdVar
  , prodRepr
  , prodVar
  , prodMul
  , prodEval
  , prodEvalM
  , prodContains
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

-- | A weighted sum of semiring values.  Mathematically, this represents
--   an affine operaton on the underlying expressions.
data WeightedSum (f :: BaseType -> Type) (sr :: SR.SemiRing)
   = WeightedSum { _sumMap     :: !(Map (WrapF f sr) (SR.Coefficient sr))
                 , _sumOffset  :: !(SR.Coefficient sr)
                 , _sumHash    :: Int -- ^ precomputed hash of the map part of the weighted sum
                 , sumRepr     :: !(SR.SemiRingRepr sr)
                     -- ^ Runtime representation of the semiring for this sum
                 }

-- | A product of semiring values.
data SemiRingProduct (f :: BaseType -> Type) (sr :: SR.SemiRing)
   = SemiRingProduct { _prodMap  :: !(Map (WrapF f sr) (SR.Occurrence sr))
                     , _prodHash :: Int
                     , prodRepr  :: !(SR.SemiRingRepr sr)
                         -- ^ Runtime representation of the semiring for this product
                     }

listEqBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
listEqBy _ [] [] = True
listEqBy f (x:xs) (y:ys)
  | f x y = listEqBy f xs ys
listEqBy _ _ _ = False

mapEqBy :: Ord k => (a -> a -> Bool) -> Map k a -> Map k a -> Bool
mapEqBy f x y = listEqBy (\(kx,ax) (ky,ay) -> kx == ky && f ax ay) (Map.toAscList x) (Map.toAscList y)

instance OrdF f => TestEquality (SemiRingProduct f) where
  testEquality x y
    | _prodHash x /= _prodHash y = Nothing
    | otherwise =
        do Refl <- testEquality (prodRepr x) (prodRepr y)
           unless (mapEqBy (SR.occ_eq (prodRepr x)) (_prodMap x) (_prodMap y)) Nothing
           return Refl

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

-- | Retrieve the mapping from terms to coefficents.
sumMap :: HashableF f => Simple Lens (WeightedSum f sr) (Map (WrapF f sr) (SR.Coefficient sr))
sumMap = lens _sumMap (\w m -> w{ _sumMap = m, _sumHash = computeHash (sumRepr w) m })

-- | Retrieve the constant addend of the weighted sum.
sumOffset :: Simple Lens (WeightedSum f sr) (SR.Coefficient sr)
sumOffset = lens _sumOffset (\s v -> s { _sumOffset = v })

instance Hashable (WeightedSum f sr) where
  hashWithSalt s0 w =
    hashWithSalt (SR.sr_hashWithSalt (sumRepr w) s0 (_sumOffset w)) (_sumHash w)

instance Hashable (SemiRingProduct f sr) where
  hashWithSalt s0 w = hashWithSalt s0 (_prodHash w)

computeHash :: HashableF f => SR.SemiRingRepr sr -> Map (WrapF f sr) (SR.Coefficient sr) -> Int
computeHash sr m = Map.foldlWithKey' h 0 m
    where h s k v = s `xor` SR.sr_hashWithSalt sr (hash k) v

computeProdHash :: HashableF f => SR.SemiRingRepr sr -> Map (WrapF f sr) (SR.Occurrence sr) -> Int
computeProdHash sr m = Map.foldlWithKey' h 0 m
    where h s k v = s `xor` SR.occ_hashWithSalt sr (hash k) v

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

-- | Attempt to parse a weighted sum as a single expression with a coefficent and offset.
--   @asAffineVar w = Just (c,r,o)@ when @denotation(w) = c*r + o@.
asAffineVar :: WeightedSum f sr -> Maybe (SR.Coefficient sr, f (SR.SemiRingBase sr), SR.Coefficient sr)
asAffineVar w
  | [(WrapF r,c)] <- Map.toList (_sumMap w)
  = Just (c,r,_sumOffset w)

  | otherwise
  = Nothing

-- | Attempt to parse weighted sum as a single expression with a coefficent.
--   @asWeightedVar w = Just (c,r)@ when @denotation(w) = c*r@.
asWeightedVar :: WeightedSum f sr -> Maybe (SR.Coefficient sr, f (SR.SemiRingBase sr))
asWeightedVar w
  | [(WrapF r,c)] <- Map.toList (_sumMap w)
  , let sr = sumRepr w
  , SR.eq sr (SR.zero sr) (_sumOffset w)
  = Just (c,r)

  | otherwise
  = Nothing

-- | Attempt to parse weighted sum as a single expression.
--   @asVar w = Just r@ when @denotation(w) = r@
asVar :: WeightedSum f sr -> Maybe (f (SR.SemiRingBase sr))
asVar w
  | [(WrapF r,c)] <- Map.toList (_sumMap w)
  , let sr = sumRepr w
  , SR.eq sr (SR.one sr) c
  , SR.eq sr (SR.zero sr) (_sumOffset w)
  = Just r

  | otherwise
  = Nothing

-- | Create a sum from a constant coefficent value.
constant :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> WeightedSum f sr
constant sr = unfilteredSum sr Map.empty

-- | Traverse the expressions in a weighted sum.
traverseVars :: forall k j m sr.
  (Applicative m, Tm k) =>
  (j (SR.SemiRingBase sr) -> m (k (SR.SemiRingBase sr))) ->
  WeightedSum j sr ->
  m (WeightedSum k sr)
traverseVars f w =
  let sr = sumRepr w in
    (\m -> unfilteredSum sr m (_sumOffset w)) .
    Map.filter (not . SR.eq sr (SR.zero sr)) .
    Map.fromListWith (SR.add sr) <$>
      traverse (_1 (traverseWrap f)) (Map.toList (_sumMap w))

-- | Traverse the expressions in a product.
traverseProdVars :: forall k j m sr.
  (Applicative m, Tm k) =>
  (j (SR.SemiRingBase sr) -> m (k (SR.SemiRingBase sr))) ->
  SemiRingProduct j sr ->
  m (SemiRingProduct k sr)
traverseProdVars f pd =
  let sr = prodRepr pd in
    mkProd (prodRepr pd) .
    Map.fromListWith (SR.occ_add sr) <$>
      traverse (_1 (traverseWrap f)) (Map.toList (_prodMap pd))

-- | This returns a variable times a constant.
scaledVar :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> f (SR.SemiRingBase sr) -> WeightedSum f sr
scaledVar sr s t
  | SR.eq sr (SR.zero sr) s = unfilteredSum sr Map.empty (SR.zero sr)
  | otherwise = unfilteredSum sr (Map.singleton (WrapF t) s) (SR.zero sr)

-- | Create a weighted sum corresponding to the given variable.
var :: Tm f => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> WeightedSum f sr
var sr t = unfilteredSum sr (Map.singleton (WrapF t) (SR.one sr)) (SR.zero sr)


-- | Add two sums, collecting terms as necessary and deleting terms whose
--   coefficents sum to 0.
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

-- | Create a weighted sum that represents the sum of two terms.
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

-- | Add a constant to the sum.
addConstant :: SR.SemiRingRepr sr -> WeightedSum f sr -> SR.Coefficient sr -> WeightedSum f sr
addConstant sr x r = x & sumOffset %~ SR.add sr r

-- | Multiply a sum by a constant coefficient.
scale :: Tm f => SR.SemiRingRepr sr -> SR.Coefficient sr -> WeightedSum f sr -> WeightedSum f sr
scale sr c x
 | SR.eq sr c (SR.zero sr) = constant sr (SR.zero sr)
 | otherwise = unfilteredSum sr m' (SR.mul sr c (x^.sumOffset))
      where m' = Map.filter (not . SR.eq sr (SR.zero sr)) (fmap (SR.mul sr c) (x^.sumMap))

-- | Produce a weighted sum from a list of terms and an offset.
fromTerms ::
  Tm f =>
  SR.SemiRingRepr sr ->
  [(WrapF f sr, SR.Coefficient sr)] ->
  SR.Coefficient sr ->
  WeightedSum f sr
fromTerms sr tms offset = unfilteredSum sr m offset
  where
  m = Map.filter (not . SR.eq sr (SR.zero sr)) (Map.fromListWith (SR.add sr) tms)

-- | Apply update functions to the terms and coefficents of a weighted sum.
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

-- | Given two weighted sums @x@ and @y@, this returns a triple @(z,x',y')@
-- where @x = z + x'@ and @y = z + y'@ and @z@ contains the "common"
-- parts of @x@ and @y@.  We only extract common terms when both
-- terms occur with the same coefficent in each sum.
--
-- This is primarily used to simplify if-then-else expressions to
-- preserve shared subterms.
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


-- | Returns true if the product is trivial (contains no terms)
nullProd :: SemiRingProduct f sr -> Bool
nullProd pd = Map.null (_prodMap pd)

-- | If the product consists of exactly on term, return it.
asProdVar :: SemiRingProduct f sr -> Maybe (f (SR.SemiRingBase sr))
asProdVar pd
  | [(WrapF x, SR.occ_count sr -> 1)] <- Map.toList (_prodMap pd) = Just x
  | otherwise = Nothing
 where
 sr = prodRepr pd

-- | Returns true if the product contains at least on occurence of the given term.
prodContains :: OrdF f => SemiRingProduct f sr -> f (SR.SemiRingBase sr) -> Bool
prodContains pd x = Map.member (WrapF x) (_prodMap pd)

-- | Produce a product map from a raw map of terms to occurences.
--   PRECONDITION: the occurence value for each term should be non-zero.
mkProd :: HashableF f => SR.SemiRingRepr sr -> Map (WrapF f sr) (SR.Occurrence sr) -> SemiRingProduct f sr
mkProd sr m = SemiRingProduct m (computeProdHash sr m) sr

-- | Produce a product representing the single given term
prodVar :: Tm f => SR.SemiRingRepr sr -> f (SR.SemiRingBase sr) -> SemiRingProduct f sr
prodVar sr x = mkProd sr (Map.singleton (WrapF x) (SR.occ_one sr))

-- | Multiply two products, collecting terms and adding occurences.
prodMul :: Tm f => SemiRingProduct f sr -> SemiRingProduct f sr -> SemiRingProduct f sr
prodMul x y = mkProd sr m
  where
  sr = prodRepr x
  mergeCommon _ a b = Just (SR.occ_add sr a b)
  m = Map.mergeWithKey mergeCommon id id (_prodMap x) (_prodMap y)

-- | Evaluate a product, given a function representing multiplication
--   and a function to evaluate terms.
prodEval ::
  (r -> r -> r) {-^ multiplication evalation -} ->
  (f (SR.SemiRingBase sr) -> r) {-^ term evaluation -} ->
  SemiRingProduct f sr ->
  Maybe r
prodEval mul tm om =
  runIdentity (prodEvalM (\x y -> Identity (mul x y)) (Identity . tm) om)

-- | Evaluate a product, given a function representing multiplication
--   and a function to evaluate terms, where both functions are threaded
--   through a monad.
prodEvalM :: Monad m =>
  (r -> r -> m r) {-^ multiplication evalation -} ->
  (f (SR.SemiRingBase sr) -> m r) {-^ term evaluation -} ->
  SemiRingProduct f sr ->
  m (Maybe r)
prodEvalM mul tm om = f (Map.toList (_prodMap om))
  where
  sr = prodRepr om

  -- we have not yet encountered a term with non-zero occurences
  f [] = return Nothing
  f ((WrapF x, SR.occ_count sr -> n):xs)
    | n == 0    = f xs
    | otherwise =
        do t <- tm x
           t' <- go (n-1) t t
           g xs t'

  -- we have a partial product @z@ already computed and need to multiply
  -- in the remaining terms in the list
  g [] z = return (Just z)
  g ((WrapF x, SR.occ_count sr -> n):xs) z
    | n == 0    = g xs z
    | otherwise =
        do t <- tm x
           t' <- go n t z
           g xs t'

  -- compute: z * t^n
  go n t z
    | n > 0 = go (n-1) t =<< mul z t
    | otherwise = return z
