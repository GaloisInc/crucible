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
 , canonicalizeAT
 , asConstAT_
 , asConstAT
 , collapseAT
 , absurdAT
 ) where

import           GHC.Generics (Generic, Generic1)
import           Data.Data (Data)

import           Data.Maybe (catMaybes)
import           Data.Bifunctor (bimap)
import           Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import           Data.Eq.Deriving (deriveEq1, deriveEq2)
import           Data.Ord.Deriving (deriveOrd1, deriveOrd2)
import           Text.Show.Deriving (deriveShow1, deriveShow2)
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import           Data.Void (Void, absurd)
import           Control.Monad (foldM, (<=<))
import           Control.Arrow ((&&&))

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

-- | Add an additional piece of information to an 'AndOrIte' tree, possibly
--   modifying the structure of the tree based on subtrees and computed tags
--   along the way.
tagAndReplace :: (a -> b)           -- ^ 'Leaf' case
              -> (c -> d)           -- ^ 'Leaf' case
              -> (NonEmpty (AssertionTree (c, d) (a, b), b) ->
                  (AssertionTree (c, d) (a, b), b))
                 -- ^ 'And' case
              -> (NonEmpty (AssertionTree (c, d) (a, b), b) ->
                  (AssertionTree (c, d) (a, b), b))
                 -- ^ 'Or' case
              -> ((c, d) ->
                   (AssertionTree (c, d) (a, b), b) ->
                   (AssertionTree (c, d) (a, b), b) ->
                   (AssertionTree (c, d) (a, b), b))
                 -- ^ 'Ite' case
              -> AssertionTree c a
              -> (AssertionTree (c, d) (a, b), b)
tagAndReplace leaf cond summarizeAnd summarizeOr summarizeITE =
  cataAT
    (\lf       -> let tag = leaf lf in (Leaf (lf, tag), tag))
    (\factors  -> summarizeAnd factors)
    (\summands -> summarizeOr summands)
    (\c t1 t2  -> summarizeITE (c, cond c) t1 t2)

-- | Add an additional piece of information to an 'AndOrIte' tree
tagAT :: (a -> b)           -- ^ 'Leaf' case
      -> (c -> d)           -- ^ 'Cond' case
      -> (NonEmpty b -> b)  -- ^ Summarize child tags ('And' case)
      -> (NonEmpty b -> b)  -- ^ Summarize child tags ('Or' case)
      -> (c -> d -> b -> b -> b) -- ^ Summarize child tags ('Ite' case)
      -> AssertionTree c a
      -> (AssertionTree (c, d) (a, b), b)
tagAT leaf cond summarizeAnd summarizeOr summarizeITE =
  tagAndReplace
    leaf
    cond
    (And &&&& summarizeAnd)
    (Or  &&&& summarizeOr)
    (\c@(c1, c2) (thenTree, thenTag) (elseTree, elseTag) ->
      (Ite c thenTree elseTree, summarizeITE c1 c2 thenTag elseTag))
  where (&&&&) :: Functor f => (f a -> c) -> (f b -> d) -> f (a, b) -> (c, d)
        f &&&& g = (f . fmap fst) &&& (g . fmap snd)

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

-- | Simplify an assertion tree by removing singleton 'And' and 'Or' applications.
simplifyAT :: AssertionTree c a
           -> AssertionTree c a
simplifyAT = cataAT Leaf (simplifyNonEmpty And) (simplifyNonEmpty Or) Ite
  where simplifyNonEmpty _ (x :| []) = x
        simplifyNonEmpty f xs = f xs

-- | Apply some constant folding: figure out of trees are constantly true or
--   constantly false, and apply some transformation to them if so.
--   Generally, the transformation will be just replacing them with a constant
--   value.
constantFoldAT_ :: (IsExprBuilder sym)
                => proxy sym
                -> (a -> Maybe (Pred sym))
                -> (c -> Maybe (Pred sym))
                -> (Maybe Bool ->
                      AssertionTree (c, Maybe Bool) (a, Maybe Bool) ->
                      AssertionTree (c, Maybe Bool) (a, Maybe Bool))
                   -- ^ Apply to subtrees
                -> AssertionTree c a
                -> (AssertionTree (c, Maybe Bool) (a, Maybe Bool), Maybe Bool)
constantFoldAT_ _proxy f g transform at =
  tagAndReplace
    (asConstantPred <=< f)
    (asConstantPred <=< g)
    (\factors ->
      let factors' = catMaybes (NonEmpty.toList (fmap snd factors))
          t = And (fmap fst factors)
          transform' b = (transform b t, b)
      in if any not factors'
         then transform' (Just False)
         else if length factors' == length factors
              then transform' (Just True)
              else transform' Nothing)
    (\summands ->
      let summands' = catMaybes (NonEmpty.toList (fmap snd summands))
          t = Or (fmap fst summands)
          transform' b = (transform b t, b)
      in if or summands'
         then transform' (Just True)
         else if length summands' == length summands
              then transform' (Just False)
              else transform' Nothing)
    (\(c, c') t1@(tree1, tag1) t2@(tree2, tag2) ->
       let t = Ite (c, c') tree1 tree2
           transform' b = (transform b t, b)
       in
        case c' of
          Just True  -> t1
          Just False -> t2
          Nothing ->
            case (tag1, tag2) of
              (Just True, Just True)   -> transform' (Just True)
              (Just False, Just False) -> transform' (Just False)
              _                        -> transform' Nothing)
    at

-- | Do all possible constant folding, replacing trivially true or false subtrees
constantFoldAT :: (IsExprBuilder sym)
               => proxy sym
               -> (a -> Maybe (Pred sym))
               -> (c -> Maybe (Pred sym))
               -> AssertionTree c a -- ^ \"Trivially true\" tree
               -> AssertionTree c a -- ^ \"Trivially false\" tree
               -> AssertionTree c a
               -> AssertionTree c a
constantFoldAT proxy f g true false =
  let addb b z = (z, Just b)
      true'  = bimap (addb True) (addb True) true
      false' = bimap (addb False) (addb False) false
  in bimap fst fst . fst . constantFoldAT_ proxy f g
       (\case
          Just True  -> const true'
          Just False -> const false'
          Nothing    -> id)

-- | Put an assertion tree in \"canonical form\": simplify and constant fold it.
canonicalizeAT :: (IsExprBuilder sym)
               => proxy sym
               -> (a -> Maybe (Pred sym))
               -> (c -> Maybe (Pred sym))
               -> AssertionTree c a -- ^ \"Trivially true\" tree
               -> AssertionTree c a -- ^ \"Trivially false\" tree
               -> AssertionTree c a
               -> AssertionTree c a
canonicalizeAT proxy f g true false =
  simplifyAT . constantFoldAT proxy f g true false

-- | Simplify an tree with 'Pred' in it with 'asConstantPred'
--
-- The original tree is included with a 'Maybe Bool' that might summarize it's
-- (constant) value.
asConstAT_ :: (IsExprBuilder sym)
           => proxy sym
           -> (a -> Maybe (Pred sym))
           -> (c -> Maybe (Pred sym))
           -> AssertionTree c a
           -> (AssertionTree (c, Maybe Bool) (a, Maybe Bool), Maybe Bool)
asConstAT_ proxy f g = constantFoldAT_ proxy f g (const id)

-- | Like 'asConstPred', but for assertion trees.
asConstAT :: (IsExprBuilder sym)
          => proxy sym
          -> (a -> Maybe (Pred sym))
          -> (c -> Maybe (Pred sym))
          -> AssertionTree c a
          -> Maybe Bool
asConstAT proxy f g = snd . asConstAT_ proxy f g

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
