{-|
Module      : What4.Expr.BoolMap
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com

Declares a datatype for representing n-way conjunctions (or negated
conjunctions) in a way that efficently capures important algebraic
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
  ) where

import           Control.Lens (_1, over)
import           Data.Bits
import           Data.Hashable
import           Data.List (foldl')
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import           Data.Parameterized.Classes

import           What4.BaseTypes

data Polarity = Positive | Negative
 deriving (Eq,Ord,Show)

instance Hashable Polarity where
  hashWithSalt s Positive = hashWithSalt s (0::Int)
  hashWithSalt s Negative = hashWithSalt s (1::Int)

negatePolarity :: Polarity -> Polarity
negatePolarity Positive = Negative
negatePolarity Negative = Positive

newtype Wrap (f :: k -> *) (x :: k) = Wrap { unWrap:: f x }

instance TestEquality f => Eq (Wrap f x) where
  Wrap a == Wrap b = isJust $ testEquality a b
instance OrdF f => Ord (Wrap f x) where
  compare (Wrap a) (Wrap b) = toOrdering $ compareF a b
instance HashableF f => Hashable (Wrap f x) where
  hashWithSalt s (Wrap a) = hashWithSaltF s a

data BoolMap f
  = InconsistentMap
  | BoolMap !(Map (Wrap f BaseBoolType) Polarity)
 deriving (Eq, Ord)

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

data BoolMapView f
  = BoolMapConst !Bool
  | BoolMapTerms (NonEmpty (f BaseBoolType, Polarity))

viewBoolMap :: BoolMap f -> BoolMapView f
viewBoolMap InconsistentMap = BoolMapConst False
viewBoolMap (BoolMap m) =
  case Map.toList m of
    []  -> BoolMapConst True
    (Wrap x,p):xs -> BoolMapTerms ((x,p):|(map (over _1 unWrap) xs))

isInconsistent :: BoolMap f -> Bool
isInconsistent InconsistentMap = True
isInconsistent _ = False

isNull :: BoolMap f -> Bool
isNull InconsistentMap = False
isNull (BoolMap m) = Map.null m

var :: OrdF f => f BaseBoolType -> Polarity -> BoolMap f
var x p = BoolMap (Map.singleton (Wrap x) p)

addVar :: OrdF f => f BaseBoolType -> Polarity -> BoolMap f -> BoolMap f
addVar _ _ InconsistentMap = InconsistentMap
addVar x p1 (BoolMap bm) = maybe InconsistentMap BoolMap $ Map.alterF f (Wrap x) bm
 where
 f Nothing = return (Just p1)
 f (Just p2) | p1 == p2  = return (Just p1)
             | otherwise = Nothing

fromVars :: OrdF f => [(f BaseBoolType, Polarity)] -> BoolMap f
fromVars = foldl' (\m (x,p) -> addVar x p m) (BoolMap Map.empty)

combine :: OrdF f => BoolMap f -> BoolMap f -> BoolMap f
combine InconsistentMap _ = InconsistentMap
combine _ InconsistentMap = InconsistentMap
combine (BoolMap m1) (BoolMap m2) =
    maybe InconsistentMap BoolMap $
      Map.mergeA Map.preserveMissing Map.preserveMissing (Map.zipWithAMatched f) m1 m2

  where f _k p1 p2 | p1 == p2  = Just p1
                   | otherwise = Nothing

contains :: OrdF f => BoolMap f -> f BaseBoolType -> Maybe Polarity
contains InconsistentMap _ = Nothing
contains (BoolMap m) x = Map.lookup (Wrap x) m

reversePolarities :: BoolMap f -> BoolMap f
reversePolarities InconsistentMap = InconsistentMap
reversePolarities (BoolMap m) = BoolMap $! fmap negatePolarity m
