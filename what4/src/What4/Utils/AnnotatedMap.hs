{-|
Module      : What4.Utils.AnnotatedMap
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : huffman@galois.com

A finite map data structure with monoidal annotations.
-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module What4.Utils.AnnotatedMap
  ( AnnotatedMap
  , null
  , empty
  , singleton
  , size
  , lookup
  , delete
  , annotation
  , toList
  , fromAscList
  , insert
  , alter
  , alterF
  , union
  , unionWith
  , unionWithKeyMaybe
  , filter
  , mapMaybe
  , traverseMaybeWithKey
  , difference
  , mergeWithKey
  , mergeWithKeyM
  , mergeA
  , eqBy
  ) where

import           Data.Functor.Identity
import qualified Data.Foldable as Foldable
import           Data.Foldable (foldl')
import           Prelude hiding (null, filter, lookup)

import qualified Data.FingerTree as FT
import           Data.FingerTree ((><), (<|))

----------------------------------------------------------------------
-- Operations on FingerTrees

filterFingerTree ::
  FT.Measured v a =>
  (a -> Bool) -> FT.FingerTree v a -> FT.FingerTree v a
filterFingerTree p =
  foldl' (\xs x -> if p x then xs FT.|> x else xs) FT.empty

mapMaybeFingerTree ::
  (FT.Measured v1 a1, FT.Measured v2 a2) =>
  (a1 -> Maybe a2) -> FT.FingerTree v1 a1 -> FT.FingerTree v2 a2
mapMaybeFingerTree f =
  foldl' (\xs x -> maybe xs (xs FT.|>) (f x)) FT.empty

traverseMaybeFingerTree ::
  (Applicative f, FT.Measured v1 a1, FT.Measured v2 a2) =>
  (a1 -> f (Maybe a2)) -> FT.FingerTree v1 a1 -> f (FT.FingerTree v2 a2)
traverseMaybeFingerTree f =
   foldl' (\m x -> rebuild <$> m <*> f x) (pure FT.empty)
 where
 rebuild ys Nothing  = ys
 rebuild ys (Just y) = ys FT.|> y

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
  AnnotatedMap { annotatedMap :: FT.FingerTree (Tag k v) (Entry k v a) }
  -- Invariant: The entries in the fingertree must be sorted by key,
  -- strictly increasing from left to right.

data Entry k v a = Entry k v a
  deriving (Functor, Foldable, Traversable)

keyOf :: Entry k v a -> k
keyOf (Entry k _ _) = k

valOf :: Entry k v a -> (v, a)
valOf (Entry _ v a) = (v, a)

instance (Ord k, Semigroup v) => FT.Measured (Tag k v) (Entry k v a) where
  measure (Entry k v _) = Tag 1 k v

instance (Ord k, Semigroup v) => Functor (AnnotatedMap k v) where
  fmap f (AnnotatedMap ft) =
    AnnotatedMap (FT.unsafeFmap (fmap f) ft)

instance (Ord k, Semigroup v) => Foldable.Foldable (AnnotatedMap k v) where
  foldr f z (AnnotatedMap ft) =
    foldr f z [ a | Entry _ _ a <- Foldable.toList ft ]

instance (Ord k, Semigroup v) => Traversable (AnnotatedMap k v) where
  traverse f (AnnotatedMap ft) =
    AnnotatedMap <$> FT.unsafeTraverse (traverse f) ft

annotation :: (Ord k, Semigroup v) => AnnotatedMap k v a -> Maybe v
annotation (AnnotatedMap ft) =
  case FT.measure ft of
    Tag _ _ v -> Just v
    NoTag     -> Nothing

toList :: AnnotatedMap k v a -> [(k, a)]
toList (AnnotatedMap ft) =
  [ (k, a) | Entry k _ a <- Foldable.toList ft ]

fromAscList :: (Ord k, Semigroup v) => [(k,v,a)] -> AnnotatedMap k v a
fromAscList = AnnotatedMap . FT.fromList . fmap f
 where
 f (k,v,a) = Entry k v a

listEqBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
listEqBy _ [] [] = True
listEqBy f (x:xs) (y:ys)
  | f x y = listEqBy f xs ys
listEqBy _ _ _ = False

eqBy :: Ord k => (a -> a -> Bool) -> AnnotatedMap k v a -> AnnotatedMap k v a -> Bool
eqBy f x y = listEqBy (\(kx,ax) (ky,ay) -> kx == ky && f ax ay) (toList x) (toList y)

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

lookup :: (Ord k, Semigroup v) => k -> AnnotatedMap k v a -> Maybe (v, a)
lookup k (AnnotatedMap ft) = valOf <$> m
  where
  (_, m, _) = splitAtKey k ft

delete :: (Ord k, Semigroup v) => k -> AnnotatedMap k v a -> AnnotatedMap k v a
delete k m@(AnnotatedMap ft) =
  case splitAtKey k ft of
    (_, Nothing, _) -> m
    (l, Just _, r)  -> AnnotatedMap (l >< r)

alter ::
  (Ord k, Semigroup v) =>
  (Maybe (v, a) -> Maybe (v, a)) -> k -> AnnotatedMap k v a -> AnnotatedMap k v a
alter f k (AnnotatedMap ft) =
  case f (fmap valOf m) of
    Nothing -> AnnotatedMap (l >< r)
    Just (v, a) -> AnnotatedMap (l >< (Entry k v a <| r))
  where
    (l, m, r) = splitAtKey k ft

alterF ::
  (Functor f, Ord k, Semigroup v) =>
  (Maybe (v, a) -> f (Maybe (v, a))) -> k -> AnnotatedMap k v a -> f (AnnotatedMap k v a)
alterF f k (AnnotatedMap ft) = rebuild <$> f (fmap valOf m)
  where
  (l, m, r) = splitAtKey k ft

  rebuild Nothing      = AnnotatedMap (l >< r)
  rebuild (Just (v,a)) = AnnotatedMap (l >< (Entry k v a) <| r)


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

filter ::
  (Ord k, Semigroup v) =>
  (a -> Bool) -> AnnotatedMap k v a -> AnnotatedMap k v a
filter f (AnnotatedMap ft) = AnnotatedMap (filterFingerTree g ft)
  where g (Entry _ _ a) = f a

mapMaybe ::
  (Ord k, Semigroup v) =>
  (a -> Maybe b) ->
  AnnotatedMap k v a -> AnnotatedMap k v b
mapMaybe f (AnnotatedMap ft) =
  AnnotatedMap (mapMaybeFingerTree g ft)
  where g (Entry k v a) = Entry k v <$> f a

traverseMaybeWithKey ::
  (Applicative f, Ord k, Semigroup v1, Semigroup v2) =>
  (k -> v1 -> a1 -> f (Maybe (v2, a2))) ->
  AnnotatedMap k v1 a1 -> f (AnnotatedMap k v2 a2)
traverseMaybeWithKey f (AnnotatedMap ft) =
  AnnotatedMap <$> traverseMaybeFingerTree g ft
  where
    g (Entry k v1 x1) = fmap (\(v2, x2) -> Entry k v2 x2) <$> f k v1 x1

difference ::
  (Ord k, Semigroup v, Semigroup w) =>
  AnnotatedMap k v a -> AnnotatedMap k w b -> AnnotatedMap k v a
difference a b = runIdentity $ mergeGeneric (\_ _ -> Identity Nothing) pure (const (pure empty)) a b

mergeWithKey ::
  (Ord k, Semigroup u, Semigroup v, Semigroup w) =>
  (k -> (u, a) -> (v, b) -> Maybe (w, c)) {- ^ for keys present in both maps -} ->
  (AnnotatedMap k u a -> AnnotatedMap k w c) {- ^ for subtrees only in first map -} ->
  (AnnotatedMap k v b -> AnnotatedMap k w c) {- ^ for subtrees only in second map -} ->
  AnnotatedMap k u a -> AnnotatedMap k v b -> AnnotatedMap k w c
mergeWithKey f g1 g2 m1 m2 = runIdentity $ mergeGeneric f' (pure . g1) (pure . g2) m1 m2
  where
    f' (Entry k u a) (Entry _ v b) = Identity $
      case f k (u, a) (v, b) of
        Nothing -> Nothing
        Just (w, c) -> Just (Entry k w c)

mergeA ::
  (Ord k, Semigroup v, Applicative f) =>
  (k -> (v, a) -> (v, a) -> f (v,a)) ->
  AnnotatedMap k v a -> AnnotatedMap k v a -> f (AnnotatedMap k v a)
mergeA f m1 m2 = mergeGeneric f' pure pure m1 m2
 where
 f' (Entry k v1 x1) (Entry _ v2 x2) = g k <$> f k (v1,x1) (v2,x2)
 g k (v,x) = Just (Entry k v x)

mergeWithKeyM :: (Ord k, Semigroup u, Semigroup v, Semigroup w, Applicative m) =>
  (k -> (u,a) -> (v,b) -> m (w,c)) ->
  (k -> (u,a) -> m (w,c)) ->
  (k -> (v,b) -> m (w,c)) ->
  AnnotatedMap k u a -> AnnotatedMap k v b -> m (AnnotatedMap k w c)
mergeWithKeyM both left right = mergeGeneric both' left' right'
 where
 both' (Entry k u a) (Entry _ v b) = q k <$> both k (u,a) (v,b)
 left'  m = AnnotatedMap <$> traverseMaybeFingerTree fl (annotatedMap m)
 right' m = AnnotatedMap <$> traverseMaybeFingerTree fr (annotatedMap m)

 fl (Entry k v x) = q k <$> left k (v,x)
 fr (Entry k v x) = q k <$> right k (v,x)

 q k (a,b) = Just (Entry k a b)


mergeGeneric ::
  (Ord k, Semigroup u, Semigroup v, Semigroup w, Applicative m) =>
  (Entry k u a -> Entry k v b -> m (Maybe (Entry k w c))) {- ^ for keys present in both maps -} ->
  (AnnotatedMap k u a -> m (AnnotatedMap k w c)) {- ^ for subtrees only in first map -} ->
  (AnnotatedMap k v b -> m (AnnotatedMap k w c)) {- ^ for subtrees only in second map -} ->
  AnnotatedMap k u a -> AnnotatedMap k v b -> m (AnnotatedMap k w c)
mergeGeneric f g1 g2 (AnnotatedMap ft1) (AnnotatedMap ft2) = AnnotatedMap <$> (merge1 ft1 ft2)
  where
    g1' ft = annotatedMap <$> g1 (AnnotatedMap ft)
    g2' ft = annotatedMap <$> g2 (AnnotatedMap ft)

    rebuild l Nothing r  = l >< r
    rebuild l (Just x) r = l >< (x <| r)

    merge1 xs ys =
      case FT.viewl xs of
        FT.EmptyL -> g2' ys
        x FT.:< xs' ->
          let (ys1, ym, ys2) = splitAtKey (keyOf x) ys in
          case ym of
            Nothing -> (><) <$> g2' ys1 <*> merge2 xs ys2
            Just y  -> rebuild <$> g2' ys1 <*> f x y <*> merge2 xs' ys2

    merge2 xs ys =
      case FT.viewl ys of
        FT.EmptyL -> g1' xs
        y FT.:< ys' ->
          let (xs1, xm, xs2) = splitAtKey (keyOf y) xs in
          case xm of
            Nothing -> (><) <$> g1' xs1 <*> merge1 xs2 ys
            Just x  -> rebuild <$> g1' xs1 <*> f x y <*> merge1 xs2 ys'
