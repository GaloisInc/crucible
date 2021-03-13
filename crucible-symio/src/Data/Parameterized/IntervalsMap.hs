-----------------------------------------------------------------------
-- |
-- Module           : Data.IntervalsMap
-- Description      : Nested intervals
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Data.Parameterized.IntervalsMap
  ( IntervalF(..)
  , mkIntervalF
  , Intervals(..)
  , IntervalsMap
  , intersecting
  , unionWith
  , unionWithM
  , singleton
  , insertWith
  , insertWithM
  , intersectionWith
  , mapMIntersecting
  , fromList
  , toList
  , empty
  , IM.Interval(..)
  , mergeIntervalsF
  , mergeWithM
  , AsOrd(..)
  ) where


import           Data.Kind ( Type )
import           Data.Maybe (catMaybes)

import           Data.IntervalMap.Strict ( IntervalMap )
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalMap.Interval as IM
import qualified Data.IntervalMap.Generic.Strict as IMG

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

newtype AsOrd f tp where
  AsOrd :: { unAsOrd :: f tp } -> AsOrd f tp

instance TestEquality f => Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) = case testEquality a b of
    Just Refl -> True
    _ -> False

instance OrdF f => Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

newtype IntervalF f tp where
  IntervalF :: IM.Interval (AsOrd f tp) -> IntervalF f tp

mkIntervalF ::
  IM.Interval (f tp) -> IntervalF f tp
mkIntervalF ival = IntervalF $ fmap AsOrd ival

instance TestEquality f => TestEquality (IntervalF f) where
  testEquality (IntervalF i1) (IntervalF i2) = case testEquality (unAsOrd (IM.lowerBound i1)) (unAsOrd (IM.lowerBound i2)) of
    Just Refl | i1 == i2 -> Just Refl
    _ -> Nothing

deriving instance TestEquality f => Eq (IntervalF f tp)

deriving instance OrdF f => Ord (IntervalF f tp)

newtype Intervals f ctx = Intervals (Ctx.Assignment (IntervalF f) ctx)

deriving instance TestEquality f => Eq (Intervals f ctx)

instance OrdF f => Ord (Intervals f ctx) where
  compare (Intervals (rest1 Ctx.:> a1)) (Intervals (rest2 Ctx.:> a2)) =
    compare a1 a2 <> compare (Intervals rest1) (Intervals rest2)
  compare (Intervals Ctx.Empty) (Intervals Ctx.Empty) = EQ

data IntervalsMap (f :: k -> Type) (ctx :: Ctx.Ctx k) tp where
  IntervalsMapCons ::
    IntervalMap (AsOrd f idx) (IntervalsMap f ctx tp) ->
    IntervalsMap f (ctx Ctx.::> idx) tp
  IntervalsMapHead :: tp -> IntervalsMap f Ctx.EmptyCtx tp

instance Functor (IntervalsMap f ctx) where
  fmap f ims = case ims of
    IntervalsMapCons ims' -> IntervalsMapCons (fmap (fmap f) ims')
    IntervalsMapHead v -> IntervalsMapHead $ f v

instance Foldable (IntervalsMap f ctx) where
  foldMap f (IntervalsMapCons ims') = foldMap (foldMap f) ims'
  foldMap f (IntervalsMapHead v) = f v

instance Traversable (IntervalsMap f ctx) where
  traverse f (IntervalsMapCons ims') = IntervalsMapCons <$> traverse (traverse f) ims'
  traverse f (IntervalsMapHead v) = IntervalsMapHead <$> f v

intersecting ::
  OrdF f =>
  IntervalsMap f ctx tp ->
  Intervals f ctx ->
  IntervalsMap f ctx tp
intersecting (IntervalsMapCons ims) (Intervals (rest Ctx.:> IntervalF k)) =
  let
    top = IM.intersecting ims k
  in IntervalsMapCons $ fmap (\ims' -> intersecting ims' (Intervals rest)) top
intersecting v (Intervals Ctx.Empty) = v

fromList ::
  OrdF f =>
  [(Intervals f (ctx Ctx.::> a), tp)] ->
  IntervalsMap f (ctx Ctx.::> a) tp
fromList es = foldr (unionWith (\l _ -> l)) empty (map (uncurry singleton) es)

toList ::
  IntervalsMap f ctx tp ->
  [(Intervals f ctx, tp)]
toList (IntervalsMapCons ims) =
  concat $ map (\(k, es) -> addTo k (toList es)) $ (IM.toList ims)
  where
    addTo :: IM.Interval (AsOrd f a) -> [(Intervals f ctx, tp)] -> [(Intervals f (ctx Ctx.::> a), tp)]
    addTo ival = map (\(Intervals ivalf, a) -> (Intervals $ ivalf Ctx.:> IntervalF ival, a))
toList (IntervalsMapHead v) = [(Intervals Ctx.empty, v)]

unionWith ::
  OrdF f =>
  (a -> a -> a) ->
  IntervalsMap f ctx a ->
  IntervalsMap f ctx a ->
  IntervalsMap f ctx a
unionWith f (IntervalsMapCons ims1) (IntervalsMapCons ims2) =
  IntervalsMapCons $ IM.unionWith (unionWith f) ims1 ims2
unionWith f (IntervalsMapHead v1) (IntervalsMapHead v2) = IntervalsMapHead $ f v1 v2

unionWithM ::
  forall f m a ctx.
  OrdF f =>
  Monad m =>
  (a -> a -> m a) ->
  IntervalsMap f ctx a ->
  IntervalsMap f ctx a ->
  m (IntervalsMap f ctx a)
unionWithM f ims1 ims2 = sequenceA $ unionWith go (fmap return ims1) (fmap return ims2)
  where
    go :: m a -> m a -> m a
    go f1 f2 = do
      v1 <- f1
      v2 <- f2
      f v1 v2

data MergeResult a b =
    MergeLeft a
  | MergeRight b
  | MergeCombined a b

mergeWithM ::
  forall f m a b c ctx.
  OrdF f =>
  Monad m =>
  (a -> m c) ->
  (b -> m c) ->
  (a -> b -> m c) ->
  IntervalsMap f ctx a ->
  IntervalsMap f ctx b ->
  m (IntervalsMap f ctx c)
mergeWithM inLeft inRight combine ims1 ims2 = do
  traverse eval $ unionWith go (fmap MergeLeft ims1) (fmap MergeRight ims2)
  where
    eval :: MergeResult a b -> m c
    eval (MergeLeft a) = inLeft a
    eval (MergeRight b) = inRight b
    eval (MergeCombined a b) = combine a b

    go :: MergeResult a b -> MergeResult a b -> MergeResult a b
    go (MergeLeft f1) (MergeRight f2) = MergeCombined f1 f2
    go _ _ = error "mergeWithM: unexpected MergeResult"


singleton ::
  Intervals f ctx ->
  tp ->
  IntervalsMap f ctx tp
singleton (Intervals (rest Ctx.:> IntervalF k)) v = IntervalsMapCons $ IM.singleton k (singleton (Intervals rest) v)
singleton (Intervals Ctx.Empty) v = IntervalsMapHead v

empty :: IntervalsMap f (ctx Ctx.::> a) tp
empty = IntervalsMapCons IM.empty

insertWith ::
  OrdF f =>
  (tp -> tp -> tp) ->
  Intervals f ctx ->
  tp ->
  IntervalsMap f ctx tp ->
  IntervalsMap f ctx tp
insertWith f k v = unionWith f (singleton k v)


insertWithM ::
  forall m f ctx tp.
  Monad m =>
  OrdF f =>
  (tp -> tp -> m tp) ->
  Intervals f ctx ->
  tp ->
  IntervalsMap f ctx tp ->
  m (IntervalsMap f ctx tp)
insertWithM f k v ims = sequenceA $ insertWith go k (return v) (fmap return ims)
  where
    go :: m tp -> m tp -> m tp
    go f1 f2 = do
      v1 <- f1
      v2 <- f2
      f v1 v2

intersectionWith ::
  OrdF f =>
  (a -> b -> c) ->
  IntervalsMap f ctx a ->
  IntervalsMap f ctx b ->
  IntervalsMap f ctx c
intersectionWith f (IntervalsMapCons ims1) (IntervalsMapCons ims2) =
  IntervalsMapCons $ IM.intersectionWith (intersectionWith f) ims1 ims2
intersectionWith f (IntervalsMapHead v1) (IntervalsMapHead v2) = IntervalsMapHead $ f v1 v2

mapMIntersecting' ::
  Monad m =>
  OrdF f =>
  Intervals f ctx ->
  (tp -> m (Maybe tp)) ->
  IntervalsMap f ctx tp ->
  m (Maybe (IntervalsMap f ctx tp))
mapMIntersecting' (Intervals (rest Ctx.:> IntervalF k)) f (IntervalsMapCons ims) = do
  ims' <- mapMIntersectingBase k (\_ -> mapMIntersecting' (Intervals rest) f) ims
  case IM.size ims' of
    0 -> return Nothing
    _ -> return $ Just (IntervalsMapCons ims')
mapMIntersecting' (Intervals Ctx.Empty) f (IntervalsMapHead v) = fmap IntervalsMapHead <$> f v

-- | Adjust entries which intersect the given interval
mapMIntersecting ::
  Monad m =>
  OrdF f =>
  Intervals f (ctx Ctx.::> a) ->
  (tp -> m (Maybe tp)) ->
  IntervalsMap f (ctx Ctx.::> a) tp ->
  m (IntervalsMap f (ctx Ctx.::> a) tp)
mapMIntersecting i f ims = mapMIntersecting' i f ims >>= \case
  Just ims' -> return ims'
  Nothing -> return $ IntervalsMapCons IM.empty


mapMIntersectingBase ::
  forall k v e m.
  Monad m =>
  IMG.Interval k e =>
  Ord k =>
  k ->
  (k -> v -> m (Maybe v)) ->
  IMG.IntervalMap k v ->
  m (IMG.IntervalMap k v)
mapMIntersectingBase k f im = do
  let (pref, inter, suf) = IM.splitIntersecting im k
  case IM.size inter of
    0 -> return im
    _ -> do
      im' <- catMaybes <$> mapM go (IM.toAscList inter)
      return $ IM.fromDistinctAscList (IM.toAscList pref ++ im' ++ IM.toAscList suf)
  where
    go :: (k, v) -> m (Maybe (k, v))
    go (k', v) = f k' v >>= \case
      Just v' -> return $ Just (k', v')
      Nothing -> return Nothing


mergeIntervals ::
  Ord a =>
  IM.Interval a ->
  IM.Interval a ->
  IM.Interval a
mergeIntervals i1 i2 = case (leftClosed, rightClosed) of
  (True, True) -> IM.ClosedInterval lower upper
  (False, True) -> IM.IntervalOC lower upper
  (True, False) -> IM.IntervalCO lower upper
  (False, False) -> IM.OpenInterval lower upper
  where
    leftClosed = (IM.leftClosed i1 && lo1 <= lo2) || (IM.leftClosed i2 && lo2 <= lo1)
    rightClosed = (IM.rightClosed i1 && hi2 <= hi1) || (IM.rightClosed i2 && hi1 <= hi2)
    lo1 = IM.lowerBound i1
    lo2 = IM.lowerBound i2
    hi1 = IM.upperBound i1
    hi2 = IM.upperBound i2
    lower = min lo1 lo2
    upper = max hi1 hi2

mergeIntervalsF ::
  OrdF f =>
  IntervalF f a ->
  IntervalF f a ->
  IntervalF f a
mergeIntervalsF (IntervalF i1) (IntervalF i2) = IntervalF (mergeIntervals i1 i2)
