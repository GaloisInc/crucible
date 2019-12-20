{-|
Module      : What4.Utils.AnnotatedMap
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : huffman@galois.com

A finite map data structure with monoidal annotations.
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module What4.Utils.AnnotatedMap
  ( AnnotatedMap
  , null
  , empty
  , singleton
  , size
  , annotation
  , toList
  , insert
  , alter
  , union
  , unionWith
  , unionWithKeyMaybe
  , traverseMaybeWithKey
  ) where

import qualified Data.Foldable as Foldable (toList)
import           Data.Foldable (foldl')
import           Prelude hiding (null)

import qualified Data.FingerTree as FT
import           Data.FingerTree ((><), (<|))

----------------------------------------------------------------------
-- Operations on FingerTrees

traverseMaybeFingerTree ::
  (Applicative f, FT.Measured v1 a1, FT.Measured v2 a2) =>
  (a1 -> f (Maybe a2)) -> FT.FingerTree v1 a1 -> f (FT.FingerTree v2 a2)
traverseMaybeFingerTree f =
  foldl' (\m x -> (\y ys -> maybe ys (ys FT.|>) y) <$> f x <*> m) (pure FT.empty)

----------------------------------------------------------------------
-- Tags

data Tag k v = NoTag | Tag !Int k v
-- The Int is there to support the size function.

instance (Ord k, Semigroup v) => Semigroup (Tag k v) where
  (<>) = unionTag

instance (Ord k, Semigroup v) => Monoid (Tag k v) where
  mempty  = NoTag
  mappend = unionTag

unionTag :: (Ord k, Semigroup v) => Tag k v -> Tag k v -> Tag k v
unionTag x NoTag = x
unionTag NoTag y = y
unionTag (Tag ix _ vx) (Tag iy ky vy) =
  Tag (ix + iy) ky (vx <> vy)

----------------------------------------------------------------------

newtype AnnotatedMap k v a =
  AnnotatedMap (FT.FingerTree (Tag k v) (Entry k v a))
  -- Invariant: The entries in the fingertree must be sorted by key,
  -- strictly increasing from left to right.

data Entry k v a = Entry k v a

keyOf :: Entry k v a -> k
keyOf (Entry k _ _) = k

valOf :: Entry k v a -> (v, a)
valOf (Entry _ v a) = (v, a)

instance (Ord k, Semigroup v) => FT.Measured (Tag k v) (Entry k v a) where
  measure (Entry k v _) = Tag 1 k v

annotation :: (Ord k, Semigroup v) => AnnotatedMap k v a -> Maybe v
annotation (AnnotatedMap ft) =
  case FT.measure ft of
    Tag _ _ v -> Just v
    NoTag     -> Nothing

toList :: AnnotatedMap k v a -> [(k, a)]
toList (AnnotatedMap ft) =
  [ (k, a) | Entry k _ a <- Foldable.toList ft ]

null :: AnnotatedMap k v a -> Bool
null (AnnotatedMap ft) = FT.null ft

empty :: (Ord k, Semigroup v) => AnnotatedMap k v a
empty = AnnotatedMap FT.empty

singleton :: (Ord k, Semigroup v) => k -> v -> a -> AnnotatedMap k v a
singleton k v a =
  AnnotatedMap (FT.singleton (Entry k v a))

size :: (Ord k, Semigroup v) => AnnotatedMap k v a -> Int
size (AnnotatedMap ft) =
  case FT.measure ft of
    Tag i _ _ -> i
    NoTag     -> 0

splitAtKey ::
  (Ord k, Semigroup v) =>
  k -> FT.FingerTree (Tag k v) (Entry k v a) ->
  ( FT.FingerTree (Tag k v) (Entry k v a)
  , Maybe (Entry k v a)
  , FT.FingerTree (Tag k v) (Entry k v a)
  )
splitAtKey k ft =
  case FT.viewl r of
    e FT.:< r' | k == keyOf e -> (l, Just e, r')
    _ -> (l, Nothing, r)
  where
    (l, r) = FT.split found ft
    found NoTag = False
    found (Tag _ k' _) = k <= k'

insert ::
  (Ord k, Semigroup v) =>
  k -> v -> a -> AnnotatedMap k v a -> AnnotatedMap k v a
insert k v a (AnnotatedMap ft) =
  AnnotatedMap (l >< (Entry k v a <| r))
  where
    (l, _, r) = splitAtKey k ft

alter ::
  (Ord k, Semigroup v) =>
  (Maybe (v, a) -> Maybe (v, a)) -> k -> AnnotatedMap k v a -> AnnotatedMap k v a
alter f k (AnnotatedMap ft) =
  case f (fmap valOf m) of
    Nothing -> AnnotatedMap (l >< r)
    Just (v, a) -> AnnotatedMap (l >< (Entry k v a <| r))
  where
    (l, m, r) = splitAtKey k ft

union ::
  (Ord k, Semigroup v) =>
  AnnotatedMap k v a -> AnnotatedMap k v a -> AnnotatedMap k v a
union = unionGeneric (const . Just)

unionWith ::
  (Ord k, Semigroup v) =>
  ((v, a) -> (v, a) -> (v, a)) ->
  AnnotatedMap k v a -> AnnotatedMap k v a -> AnnotatedMap k v a
unionWith f = unionGeneric g
  where
    g (Entry k v1 x1) (Entry _ v2 x2) = Just (Entry k v3 x3)
      where (v3, x3) = f (v1, x1) (v2, x2)

unionWithKeyMaybe ::
  (Ord k, Semigroup v) =>
  (k -> a -> a -> Maybe (v, a)) ->
  AnnotatedMap k v a -> AnnotatedMap k v a -> AnnotatedMap k v a
unionWithKeyMaybe f = unionGeneric g
  where g (Entry k _ x) (Entry _ _ y) = fmap (\(v, z) -> Entry k v z) (f k x y)

unionGeneric ::
  (Ord k, Semigroup v) =>
  (Entry k v a -> Entry k v a -> Maybe (Entry k v a)) ->
  AnnotatedMap k v a -> AnnotatedMap k v a -> AnnotatedMap k v a
unionGeneric f (AnnotatedMap ft1) (AnnotatedMap ft2) = AnnotatedMap (merge1 ft1 ft2)
  where
    merge1 xs ys =
      case FT.viewl xs of
        FT.EmptyL -> ys
        x FT.:< xs' ->
          case ym of
            Nothing -> ys1 >< (x <| merge2 xs' ys2)
            Just y ->
              case f x y of
                Nothing -> ys1 >< merge2 xs' ys2
                Just z -> ys1 >< (z <| merge2 xs' ys2)
          where
            (ys1, ym, ys2) = splitAtKey (keyOf x) ys

    merge2 xs ys =
      case FT.viewl ys of
        FT.EmptyL -> xs
        y FT.:< ys' ->
          case xm of
            Nothing -> xs1 >< (y <| merge1 xs2 ys')
            Just x ->
              case f x y of
                Nothing -> xs1 >< merge1 xs2 ys'
                Just z -> xs1 >< (z <| merge1 xs2 ys')
          where
            (xs1, xm, xs2) = splitAtKey (keyOf y) xs

traverseMaybeWithKey ::
  (Applicative f, Ord k, Semigroup v1, Semigroup v2) =>
  (k -> v1 -> a1 -> f (Maybe (v2, a2))) ->
  AnnotatedMap k v1 a1 -> f (AnnotatedMap k v2 a2)
traverseMaybeWithKey f (AnnotatedMap ft) =
  AnnotatedMap <$> traverseMaybeFingerTree g ft
  where
    g (Entry k v1 x1) = fmap (\(v2, x2) -> Entry k v2 x2) <$> f k v1 x1
