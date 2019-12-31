{-|
Module      : What4.Expr.ArrayUpdateMap
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module What4.Expr.ArrayUpdateMap
( ArrayUpdateMap
, arrayUpdateAbs
, empty
, null
, lookup
, filter
, singleton
, insert
, delete
, fromAscList
, toList
, toMap
, keysSet
, traverseArrayUpdateMap
, mergeM
) where

import           Prelude hiding (lookup, null, filter)

import           Data.Functor.Identity
import           Data.Hashable
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Map as Map
import qualified Data.Set as Set

import           What4.BaseTypes
import           What4.IndexLit
import           What4.Utils.AbstractDomains
import qualified What4.Utils.AnnotatedMap as AM
import           What4.Utils.IncrHash

------------------------------------------------------------------------
-- ArrayUpdateMap

data ArrayUpdateNote tp =
  ArrayUpdateNote
  { aunHash :: !IncrHash
  , _aunRepr :: !(BaseTypeRepr tp)
  , aunAbs  :: !(AbstractValue tp)
  }

instance Semigroup (ArrayUpdateNote tp) where
  ArrayUpdateNote hx tpr ax <> ArrayUpdateNote hy _ ay =
    ArrayUpdateNote (hx <> hy) tpr (withAbstractable tpr $ avJoin tpr ax ay)

newtype ArrayUpdateMap e ctx tp =
  ArrayUpdateMap ( AM.AnnotatedMap (Ctx.Assignment IndexLit ctx) (ArrayUpdateNote tp) (e tp) )

instance TestEquality e => Eq (ArrayUpdateMap e ctx tp) where
  ArrayUpdateMap m1 == ArrayUpdateMap m2 = AM.eqBy (\ x y -> isJust $ testEquality x y) m1 m2

instance Hashable (ArrayUpdateMap e ctx tp) where
  hashWithSalt s (ArrayUpdateMap m) =
    case AM.annotation m of
      Nothing  -> hashWithSalt s (111::Int)
      Just aun -> hashWithSalt s (aunHash aun)

mkNote :: (HashableF e, HasAbsValue e) => BaseTypeRepr tp -> Ctx.Assignment IndexLit ctx -> e tp -> ArrayUpdateNote tp
mkNote tpr idx e = ArrayUpdateNote (mkIncrHash (hashWithSaltF (hash idx) e)) tpr (getAbsValue e)

arrayUpdateAbs :: ArrayUpdateMap e ct tp -> Maybe (AbstractValue tp)
arrayUpdateAbs (ArrayUpdateMap m) = aunAbs <$> AM.annotation m

fromAscList :: (HasAbsValue e, HashableF e) =>
  BaseTypeRepr tp -> [(Ctx.Assignment IndexLit ctx, e tp)] -> ArrayUpdateMap e ctx tp
fromAscList tpr xs = ArrayUpdateMap (AM.fromAscList (fmap f xs))
 where
 f (k,e) = (k, mkNote tpr k e, e)

toList :: ArrayUpdateMap e ctx tp -> [(Ctx.Assignment IndexLit ctx, e tp)]
toList (ArrayUpdateMap m) = AM.toList m

traverseArrayUpdateMap :: Applicative m =>
  (e tp -> m (f tp)) ->
  ArrayUpdateMap e ctx tp ->
  m (ArrayUpdateMap f ctx tp)
traverseArrayUpdateMap f (ArrayUpdateMap m) = ArrayUpdateMap <$> traverse f m

null :: ArrayUpdateMap e ctx tp -> Bool
null (ArrayUpdateMap m) = AM.null m

lookup :: Ctx.Assignment IndexLit ctx -> ArrayUpdateMap e ctx tp -> Maybe (e tp)
lookup idx (ArrayUpdateMap m) = snd <$> AM.lookup idx m

delete :: Ctx.Assignment IndexLit ctx -> ArrayUpdateMap e ctx tp -> ArrayUpdateMap e ctx tp
delete idx (ArrayUpdateMap m) = ArrayUpdateMap (AM.delete idx m)

filter :: (e tp -> Bool) -> ArrayUpdateMap e ctx tp -> ArrayUpdateMap e ctx tp
filter p (ArrayUpdateMap m) = ArrayUpdateMap $ runIdentity $ AM.traverseMaybeWithKey f m
 where
 f _k v x
   | p x       = return (Just (v,x))
   | otherwise = return Nothing

singleton ::
  (HashableF e, HasAbsValue e) =>
  BaseTypeRepr tp ->
  Ctx.Assignment IndexLit ctx ->
  e tp ->
  ArrayUpdateMap e ctx tp
singleton tpr idx e = ArrayUpdateMap (AM.singleton idx (mkNote tpr idx e) e)

insert ::
  (HashableF e, HasAbsValue e) =>
  BaseTypeRepr tp ->
  Ctx.Assignment IndexLit ctx ->
  e tp ->
  ArrayUpdateMap e ctx tp ->
  ArrayUpdateMap e ctx tp
insert tpr idx e (ArrayUpdateMap m) =  ArrayUpdateMap (AM.insert idx (mkNote tpr idx e) e m)

empty :: ArrayUpdateMap e ctx tp
empty = ArrayUpdateMap AM.empty

mergeM :: (Applicative m, HashableF g, HasAbsValue g) =>
  BaseTypeRepr tp ->
  (Ctx.Assignment IndexLit ctx -> e tp -> f tp -> m (g tp)) ->
  (Ctx.Assignment IndexLit ctx -> e tp -> m (g tp)) ->
  (Ctx.Assignment IndexLit ctx -> f tp -> m (g tp)) ->
  ArrayUpdateMap e ctx tp ->
  ArrayUpdateMap f ctx tp ->
  m (ArrayUpdateMap g ctx tp)
mergeM tpr both left right (ArrayUpdateMap ml) (ArrayUpdateMap mr) =
  ArrayUpdateMap <$> AM.mergeWithKeyM both' left' right' ml mr
 where
 mk k x = (mkNote tpr k x, x)

 both' k (_,x) (_,y) = mk k <$> both k x y
 left' k (_,x) = mk k <$> left k x
 right' k (_,y) = mk k <$> right k y

keysSet :: ArrayUpdateMap e ctx tp -> Set.Set (Ctx.Assignment IndexLit ctx)
keysSet (ArrayUpdateMap m) = Set.fromAscList (fst <$> AM.toList m)

toMap :: ArrayUpdateMap e ctx tp -> Map.Map (Ctx.Assignment IndexLit ctx) (e tp)
toMap (ArrayUpdateMap m) = Map.fromAscList (AM.toList m)
