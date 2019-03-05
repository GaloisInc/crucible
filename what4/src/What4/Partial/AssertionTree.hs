{-|
Module           : What4.Partial.AssertionTree
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

We might want to track the provenance of the expression's partiality, and ask:
What assertion(s) does the predicate represent? The 'AssertionTree' datatype
allows for an uninterpreted tree of predicates, each with an attached
explanation.

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

module What4.Partial.AssertionTree
 ( AssertionTree(..)
 , addCondition
 , binaryAnd
 , binaryOr
 , cataAT
 , tagAT
 , cataMAT
 , asConstAT_
 , asConstAT
 , collapseAT
 , absurdAT
 ) where

import           GHC.Generics (Generic, Generic1)
import           Data.Data (Data)

import           Data.Maybe (catMaybes)
import           Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import           Data.Eq.Deriving (deriveEq1, deriveEq2)
import           Data.Ord.Deriving (deriveOrd1, deriveOrd2)
import           Text.Show.Deriving (deriveShow1, deriveShow2)
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Void (Void, absurd)
import           Control.Monad (foldM)

import           What4.Interface

------------------------------------------------------------------------
-- ** AssertionTree

-- See also "Lang.Crucible.CFG.Extension.Safety"

-- | A type representing an AST consisting of
--  * "atomic" predicates with labels
--  * a list of predicates 'And'-ed together
--  * a list of predicates 'Or'-ed together
--  * the if-then-else of two predicates
--
-- Often, the type parameter 'a' will be some combination of a 'BaseBoolType'
-- with some information about it, whereas 'c' will just be the 'BaseBoolType'.
-- This tree can be used as the predicate in a 'PartExpr'.
data AssertionTree c a =
    Leaf a
  | And  (NonEmpty (AssertionTree c a))
  | Or   (NonEmpty (AssertionTree c a))
  | Ite  c (AssertionTree c a) (AssertionTree c a)
  deriving (Data, Eq, Functor, Generic, Generic1, Foldable, Traversable, Ord, Show)

$(deriveBifunctor     ''AssertionTree)
$(deriveBifoldable    ''AssertionTree)
$(deriveBitraversable ''AssertionTree)
$(deriveEq1           ''AssertionTree)
$(deriveEq2           ''AssertionTree)
$(deriveOrd1          ''AssertionTree)
$(deriveOrd2          ''AssertionTree)
$(deriveShow1         ''AssertionTree)
$(deriveShow2         ''AssertionTree)

binaryAnd :: AssertionTree c a -> AssertionTree c a -> AssertionTree c a
binaryAnd t1 t2 = And (t1 :| [t2])

binaryOr :: AssertionTree c a -> AssertionTree c a -> AssertionTree c a
binaryOr t1 t2 = Or (t1 :| [t2])

-- | 'And' a condition onto an assertion tree
addCondition :: AssertionTree c a
             -> a
             -> AssertionTree c a
addCondition tree cond = binaryAnd (Leaf cond) tree

-- | Catamorphisms for the 'AssertionTree' type
cataAT :: (a -> b)           -- ^ 'Leaf' case
       -> (NonEmpty b -> b)  -- ^ 'And' case
       -> (NonEmpty b -> b)  -- ^ 'Or' case
       -> (c -> b -> b -> b) -- ^ 'Ite' case
       -> AssertionTree c a
       -> b
cataAT leaf and_ or_ ite val =
  case val of
    Leaf a      -> leaf a
    And  l      -> and_ (NonEmpty.map r l)
    Or   l      -> or_  (NonEmpty.map r l)
    Ite c t1 t2 -> ite c (r t1) (r t2)
  where r = cataAT leaf and_ or_ ite

-- | Add an additional piece of information to an 'AndOrIte' tree
tagAT :: (a -> b)           -- ^ 'Leaf' case
      -> (NonEmpty b -> b)  -- ^ Summarize child tags ('And' case)
      -> (NonEmpty b -> b)  -- ^ Summarize child tags ('Or' case)
      -> (c -> b -> b -> b) -- ^ Summarize child tags ('Ite' case)
      -> AssertionTree c a
      -> (AssertionTree c (a, b), b)
tagAT leaf summarizeAnd summarizeOr summarizeITE =
  cataAT
    (\lf      ->
       let tag = leaf lf
       in (Leaf (lf, tag), tag))
    (\factors ->
       let tag = summarizeAnd (NonEmpty.map snd factors)
       in (And (NonEmpty.map fst factors), tag))
    (\summands ->
       let tag = summarizeOr (NonEmpty.map snd summands)
       in (Or (NonEmpty.map fst summands), tag))
    (\cond t1 t2 ->
       let tag = summarizeITE cond (snd t1) (snd t2)
       in (Ite cond (fst t1) (fst t2), tag))

-- | Monadic catamorphisms for the 'AssertionTree' type
--
-- Essentially, this function just arbitrarily picks a serialization of effects.
cataMAT :: Monad f
        => (a -> f b)           -- ^ 'Leaf' case
        -> (NonEmpty b -> f b)  -- ^ 'And' case
        -> (NonEmpty b -> f b)  -- ^ 'Or' case
        -> (c -> b -> b -> f b) -- ^ 'Ite' case
        -> AssertionTree c a
        -> f b
cataMAT leaf and_ or_ ite = cataAT
  leaf             -- Leaf
  (\l -> sequence l >>= and_)
  (\l -> sequence l >>= or_)
  (\a t1 t2 -> do
    t1' <- t1
    t2' <- t2
    ite a t1' t2') -- Ite

-- | Simplify an tree with 'Pred' in it with 'asConstantPred'
--
-- The original tree is included with a 'Maybe Bool' that might summarize it's
-- (constant) value.
asConstAT_ :: (IsExprBuilder sym)
           => sym
           -> (a -> Pred sym)
           -> AssertionTree c a
           -> (AssertionTree c (a, Maybe Bool), Maybe Bool)
asConstAT_ _sym f =
  tagAT
    (asConstantPred . f)
    (\factors    ->
       let factors' = catMaybes (NonEmpty.toList factors)
       in if any not factors'
          then Just False
          else if length factors' == length factors
               then Just True
               else Nothing)
    (\summands    ->
       let summands' = catMaybes (NonEmpty.toList summands)
       in if or summands'
          then Just True
          else if length summands' == length summands
               then Just False
               else Nothing)
    (\_ t1 t2 ->
       case (t1, t2) of
         (Just True, Just True)   -> Just True
         (Just False, Just False) -> Just False
         _                        -> Nothing)

-- | Like 'asConstPred', but for assertion trees.
asConstAT :: (IsExprBuilder sym)
          => sym
          -> (a -> Pred sym)
          -> AssertionTree c a
          -> Maybe Bool
asConstAT sym f = snd . asConstAT_ sym f

-- | A monadic catamorphism, collapsing everything to one predicate.
collapseAT :: (IsExprBuilder sym)
           => sym
           -> (a -> IO (Pred sym))   -- ^ 'Leaf' case
           -> (c -> IO (Pred sym))   -- ^ 'Ite' case
           -> AssertionTree c a
           -> IO (Pred sym)
collapseAT sym leafToPred iteToPred = cataMAT
  leafToPred
  (foldM (andPred sym) (truePred sym))
  (foldM (orPred sym) (falsePred sym))
  (\c p1 p2 -> iteToPred c >>= \p -> itePred sym p p1 p2)

-- | If the leaves are absurd, so is the whole structure.
--
-- This could be written as a catamorphism, but we only need to travel down
-- at most one branch.
absurdAT :: (a -> Void)
         -> AssertionTree c a
         -> b
absurdAT getVoid =
  \case
    Leaf a        -> absurd (getVoid a)
    Or   (t :| _) -> absurdAT getVoid t
    And  (t :| _) -> absurdAT getVoid t
    Ite  _ t _    -> absurdAT getVoid t
