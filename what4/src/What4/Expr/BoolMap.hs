{-|
Module      : What4.Expr.BoolMap
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com

Declares a datatype for representing n-way conjunctions or disjunctions
in a way that efficently capures important algebraic
laws like commutativity, associativity and resolution.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.BoolMap
  ( BoolMap
  , var
  , addVar
  , fromVars
  , combine
  , Polarity(..)
  , negatePolarity
  , contains
  , isInconsistent
  , isNull
  , BoolMapView(..)
  , viewBoolMap
  , traverseVars
  , reversePolarities
  , removeVar
  ) where

import           Control.Lens (_1, over)
import           Data.Bits
import           Data.Hashable
import           Data.List (foldl')
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import           Data.Parameterized.Classes

import           What4.BaseTypes

-- | Describes the occurence of a variable or expression, whether it is
--   negated or not.
data Polarity = Positive | Negative
 deriving (Eq,Ord,Show)

instance Hashable Polarity where
  hashWithSalt s Positive = hashWithSalt s (0::Int)
  hashWithSalt s Negative = hashWithSalt s (1::Int)

-- | Swap a polarity value
negatePolarity :: Polarity -> Polarity
negatePolarity Positive = Negative
negatePolarity Negative = Positive

newtype Wrap (f :: k -> Type) (x :: k) = Wrap { unWrap:: f x }

instance TestEquality f => Eq (Wrap f x) where
  Wrap a == Wrap b = isJust $ testEquality a b
instance OrdF f => Ord (Wrap f x) where
  compare (Wrap a) (Wrap b) = toOrdering $ compareF a b
instance HashableF f => Hashable (Wrap f x) where
  hashWithSalt s (Wrap a) = hashWithSaltF s a

-- | This data structure keeps track of a collection of expressions
--   together with their polarities. Such a collection might represent
--   either a conjunction or a disjunction of expressions.  The
--   implementation uses a map from expression values to their
--   polarities, and thus automatically implements the associative,
--   commutative and idempotencey laws common to both conjunctions and
--   disjunctions.  Moreover, if the same expression occurs in the
--   collection with opposite polarities, the entire collection
--   collapses via a resolution step to an \"inconsistent\" map.  For
--   conjunctions this corresponds to a contradiction and
--   represents false; for disjunction, this corresponds to the law of
--   the excluded middle and represents true.
data BoolMap (f :: BaseType -> Type)
  = InconsistentMap
  | BoolMap !(Map (Wrap f BaseBoolType) Polarity)
 deriving (Eq, Ord)

-- | Traverse the expressions in a bool map, and rebuild the map.
traverseVars :: (Applicative m, OrdF g) =>
  (f BaseBoolType -> m (g (BaseBoolType))) ->
  BoolMap f -> m (BoolMap g)
traverseVars _ InconsistentMap = pure InconsistentMap
traverseVars f (BoolMap m) =
  fromVars <$> traverse (_1 (f . unWrap)) (Map.toList m)

instance HashableF f => Hashable (BoolMap f) where
  hashWithSalt s InconsistentMap = hashWithSalt s (0::Int)
  hashWithSalt s (BoolMap m) =
    foldr (\(x,p) y -> hashWithSalt (hash p) x `xor` y) (hashWithSalt s (1::Int)) (Map.toList m)

-- | Represents the state of a bool map
data BoolMapView f
  = BoolMapUnit
       -- ^ A bool map with no expressions, represents the unit of the corresponding operation
  | BoolMapDualUnit
       -- ^ An inconsistent bool map, represents the dual of the operation unit
  | BoolMapTerms (NonEmpty (f BaseBoolType, Polarity))
       -- ^ The terms appearing in the bool map, of which there is at least one

-- | Deconstruct the given bool map for later processing
viewBoolMap :: BoolMap f -> BoolMapView f
viewBoolMap InconsistentMap = BoolMapDualUnit
viewBoolMap (BoolMap m) =
  case Map.toList m of
    []  -> BoolMapUnit
    (Wrap x,p):xs -> BoolMapTerms ((x,p):|(map (over _1 unWrap) xs))

-- | Returns true for an inconsistent bool map
isInconsistent :: BoolMap f -> Bool
isInconsistent InconsistentMap = True
isInconsistent _ = False

-- | Returns true for a \"null\" bool map with no terms
isNull :: BoolMap f -> Bool
isNull InconsistentMap = False
isNull (BoolMap m) = Map.null m

-- | Produce a singleton bool map, consisting of just the given term
var :: OrdF f => f BaseBoolType -> Polarity -> BoolMap f
var x p = BoolMap (Map.singleton (Wrap x) p)

-- | Add a variable to a bool map, performing a resolution step if possible
addVar :: OrdF f => f BaseBoolType -> Polarity -> BoolMap f -> BoolMap f
addVar _ _ InconsistentMap = InconsistentMap
addVar x p1 (BoolMap bm) = maybe InconsistentMap BoolMap $ Map.alterF f (Wrap x) bm
 where
 f Nothing = return (Just p1)
 f (Just p2) | p1 == p2  = return (Just p1)
             | otherwise = Nothing

-- | Generate a bool map from a list of terms and polarities by repeatedly
--   calling @addVar@.
fromVars :: OrdF f => [(f BaseBoolType, Polarity)] -> BoolMap f
fromVars = foldl' (\m (x,p) -> addVar x p m) (BoolMap Map.empty)

-- | Merge two bool maps, performing resolution as necessary.
combine :: OrdF f => BoolMap f -> BoolMap f -> BoolMap f
combine InconsistentMap _ = InconsistentMap
combine _ InconsistentMap = InconsistentMap
combine (BoolMap m1) (BoolMap m2) =
    maybe InconsistentMap BoolMap $
      Map.mergeA Map.preserveMissing Map.preserveMissing (Map.zipWithAMatched f) m1 m2

  where f _k p1 p2 | p1 == p2  = Just p1
                   | otherwise = Nothing

-- | Test if the bool map contains the given term, and return the polarity
--   of that term if so.
contains :: OrdF f => BoolMap f -> f BaseBoolType -> Maybe Polarity
contains InconsistentMap _ = Nothing
contains (BoolMap m) x = Map.lookup (Wrap x) m

-- | Swap the polarities of the terms in the given bool map.
reversePolarities :: BoolMap f -> BoolMap f
reversePolarities InconsistentMap = InconsistentMap
reversePolarities (BoolMap m) = BoolMap $! fmap negatePolarity m

-- | Remove the given term from the bool map.  The map is unchanged
--   if inconsistent or if the term does not occur.
removeVar :: OrdF f => BoolMap f -> f BaseBoolType -> BoolMap f
removeVar InconsistentMap _ = InconsistentMap
removeVar (BoolMap m) x = BoolMap (Map.delete (Wrap x) m)
