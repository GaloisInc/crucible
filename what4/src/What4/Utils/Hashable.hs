{-|
Module      : What4.Utils.Hashable
Copyright   : (c) Galois Inc, 2015
License     : BSD3
Maintainer  : jhendrix@galois.com

Declares newtype wrappers around values to implement Hashable.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
#if __GLASGOW_HASKELL__ >= 802
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
#endif
module What4.Utils.Hashable
  ( Vector(..)
  , Map
  , mkMap
  , hashedMap
  , mapInsert
  , mapLookup
  , mapFilter
  , mapEmpty
  , mapNull
  , mapDelete
  , mapMinView
  , mergeMapWithM
  , traverseHashedMap
  ) where

import           Data.Bits
import           Data.Hashable
import           Data.Kind
import           Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.TraversableFC

-- | A newtype wrapper around a vector.
--
-- Solely implemented for a 'Hashable' instance.
newtype Vector e = Vector (V.Vector e)
  deriving (Eq)

instance Functor Vector where
  fmap f (Vector v) = Vector (fmap f v)

instance Foldable Vector where
  foldMap f (Vector v) = foldMap f v

instance Traversable Vector where
  traverse f (Vector v) = Vector <$> traverse f v

instance Hashable e => Hashable (Vector e) where
  hashWithSalt s (Vector v) = hashVector s v
  {-# INLINE hashWithSalt #-}

hashVector :: Hashable e => Int -> V.Vector e -> Int
hashVector = foldl' hashWithSalt

-- | A newtype wrapper around a vector.
--
-- Solely implemented for a 'Hashable' instance.
data Map (k :: k1 -> Type) (i :: Ctx.Ctx k1) (vf :: k2 -> Type) (vi :: k2) =
  HashedMap
  { hmHash :: !Int
  , hmMap  :: Map.Map (Ctx.Assignment k i) (vf vi)
  }

hashedMap :: Map k i vf vi -> Map.Map (Ctx.Assignment k i) (vf vi)
hashedMap = hmMap
{-# INLINE hashedMap #-}

instance (Eq (Ctx.Assignment k i), Eq (vf vi)) => Eq (Map k i vf vi) where
  x == y
   | hmHash x /= hmHash y = False
   | otherwise            = hmMap x == hmMap y

instance (Ord (Ctx.Assignment k i), Ord (vf vi)) => Ord (Map k i vf vi) where
  compare x y = compare (hmMap x) (hmMap y)

mkMap :: (HashableF k, HashableF vf)
      => Map.Map (Ctx.Assignment k i) (vf vi)
      -> Map k i vf vi
mkMap m = HashedMap
          { hmHash = computeMapHash m
          , hmMap  = m
          }

-- | This compute the hash of a map.  It is the exclusive or of the key/values pairs.
--
-- This allows one to update the bindings without rehashing the entire map.
computeMapHash :: ( HashableF k
                  , HashableF vf
                  )
               => Map.Map (Ctx.Assignment k i) (vf vi) -> Int
computeMapHash =
   Map.foldlWithKey' (\s k v -> s `xor` hashWithSaltF (hashF k) v) 0

instance FoldableFC (Map k i) where
  foldMapFC f m = foldMap f (hmMap m)

traverseHashedMap :: (Applicative m, HashableF k, HashableF b)
                  => (a vi -> m (b vi))
                  -> Map k i a vi -> m (Map k i b vi)
traverseHashedMap f m = mkMap <$> traverse f (hmMap m)

instance Hashable (Map k i vf vi) where
  hashWithSalt s m = hashWithSalt s (hmHash m)
  {-# INLINE hashWithSalt #-}

-- | Create an empty map.
mapEmpty :: Map k i a vi
mapEmpty =
  HashedMap
  { hmHash = 0
  , hmMap  = Map.empty
  }

mapLookup :: OrdF k => Ctx.Assignment k i -> Map k i a vi -> Maybe (a vi)
mapLookup k m = Map.lookup k (hmMap m)

mapInsert :: (OrdF k, HashableF k, HashableF a)
          => Ctx.Assignment k i
          -> a vi
          -> Map k i a vi -> Map k i a vi
mapInsert k v m =
  HashedMap
  { hmHash = hmHash m `xor` oldHash `xor` newHash
  , hmMap  = m'
  }
 where
  (oldv, m') = Map.insertLookupWithKey (\_ x _ -> x) k v (hmMap m)
  khash   = hashF k
  newHash = hashWithSaltF khash v
  oldHash = case oldv of
               Nothing   -> 0
               Just vold -> hashWithSaltF khash vold

mapDelete :: (OrdF k, HashableF k, HashableF a)
          => Ctx.Assignment k i
          -> Map k i a vi
          -> Map k i a vi
mapDelete k m =
  case Map.lookup k (hmMap m) of
    Nothing -> m
    Just v  ->
      HashedMap
      { hmHash = hmHash m `xor` hashWithSaltF (hashF k) v
      , hmMap  = Map.delete k (hmMap m)
      }

mapFilter :: (HashableF k, HashableF a)
          => (a vi -> Bool)
          -> Map k i a vi
          -> Map k i a vi
mapFilter p m = mkMap $ Map.filter p (hmMap m)

-- | Return true if map is empty.
mapNull :: Map k i a vi -> Bool
mapNull m = Map.null (hmMap m)

mapMinView :: (HashableF k, HashableF a)
           => Map k i a vi -> Maybe (a vi, Map k i a vi)
mapMinView m =
  case Map.minViewWithKey (hmMap m) of
    Nothing -> Nothing
    Just ((k,v),m') -> Just (v, hm')
      where hm' = HashedMap
                  { hmHash = hmHash m `xor` hashWithSaltF (hashF k) v
                  , hmMap  = m'
                  }

mergeMapWithM :: (OrdF k, Applicative m, HashableF k, HashableF c)
              => (Ctx.Assignment k i -> a vi -> b vi -> m (c vi))
              -> (Ctx.Assignment k i -> a vi -> m (c vi))
              -> (Ctx.Assignment k i -> b vi -> m (c vi))
              -> Map k i a vi
              -> Map k i b vi
              -> m (Map k i c vi)
mergeMapWithM b l r x y = do
  let b' k u v = Just $ b k u v
  mkMap <$> (sequenceA $ Map.mergeWithKey b'
                           (Map.mapWithKey l)
                           (Map.mapWithKey r)
                           (hmMap x)
                           (hmMap y))
