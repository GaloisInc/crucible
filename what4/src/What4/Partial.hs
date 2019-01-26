{-|
Module           : What4.Solver.Partial
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Often, various operations on values are only partially defined (in the case of
Crucible expressions, consider loading a value from a pointer - this is only
defined in the case that the pointer is valid and non-null). The 'PartExpr'
type allows for packaging values together with predicates that express their
partiality: the value is only valid if the predicate is true.

Taking this idea one step further, we might want to track the provenance of
the expression's partiality, and ask: What assertion(s) does the predicate
represent? The 'AssertionTree' datatype allows for an uninterpreted tree of
predicates, each with an attached explanation.

The 'PartExpr' data type is essentially a generalization of 'Maybe' as a
datatype, and the 'PartialT' monad transformer is a symbolic generalization of
the 'Maybe' monad.

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.Partial
 ( -- * PartExpr
   PartExpr(..)
 , mkPE
 , justPartExpr
 , maybePartExpr
 , joinMaybePE
   -- * AssertionTree
 , AssertionTree(..)
 , binaryAnd
 , binaryOr
 , cataAT
 , tagAT
 , cataMAT
 , asConstAT_
 , asConstAT
 , collapseAT
   -- * PartialT
 , PartialT(..)
 , runPartialT
 , returnUnassigned
 , returnMaybe
 , returnPartial
 , addCondition
 , mergePartial
 , mergePartials
 ) where

import           GHC.Generics (Generic, Generic1)
import           Data.Data (Data)

import           Data.Maybe (catMaybes)
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import           Control.Monad (foldM)
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class

import           What4.BaseTypes
import           What4.Interface

------------------------------------------------------------------------
-- ** PartExpr

-- | A partial value represents a value that may or may not be assigned.
data PartExpr p v
   = PE { _pePred :: !p
        , _peValue :: !v
        }
   | Unassigned -- TODO(langston): Add a 'Text' (explanation) argument
  deriving (Data, Eq, Functor, Generic, Generic1, Foldable, Traversable, Ord, Show)

mkPE :: IsExpr p => p BaseBoolType -> a -> PartExpr (p BaseBoolType) a
mkPE p v =
  case asConstantPred p of
    Just False -> Unassigned
    _ -> PE p v

-- | Create a part expression from a value that is always defined.
justPartExpr :: IsExprBuilder sym
             => sym -> v -> PartExpr (Pred sym) v
justPartExpr sym = PE (truePred sym)

-- | Create a part expression from a maybe value.
maybePartExpr :: IsExprBuilder sym
              => sym -> Maybe a -> PartExpr (Pred sym) a
maybePartExpr _ Nothing = Unassigned
maybePartExpr sym (Just r) = justPartExpr sym r

-- | @'joinMaybePE' = 'Data.Maybe.fromMaybe' 'Unassigned'@.
joinMaybePE :: Maybe (PartExpr p v) -> PartExpr p v
joinMaybePE Nothing = Unassigned
joinMaybePE (Just pe) = pe

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
           -> (a -> Pred sym) -- ^ 'Leaf' case
           -> (c -> Pred sym) -- ^ 'Ite' case
           -> AssertionTree c a
           -> IO (Pred sym)
collapseAT sym leafToPred iteToPred = cataMAT
  (pure . leafToPred)
  (foldM (andPred sym) (truePred sym))
  (foldM (orPred sym) (falsePred sym))
  (\c -> itePred sym (iteToPred c))

{-
ppAssertionTree :: (IsExprBuilder sym) => sym -> AssertionTree sym -> Doc
ppAssertionTree sym tree =
  let (tree', _) = asConstAOI_ sym _pred tree
  in
    cataAOI
      (\(lf, mb) -> text' (_explanation lf) <+> mbToText mb) -- TODO(langston): UB
      (\factors ->
         text' "All of "
         <$$> indent 2 (vcat factors))
      (\summands ->
         text' "Any of "
         <$$> indent 2 (vcat summands))
      (\(cond, mb) doc1 doc2 ->
         text' "If " <+> text' (_explanation cond) <+> mbToText mb <$$>
         indent 2 (vcat [ "then " <+> doc1
                        , "else " <+> doc2
                        ]))
      tree'
  where mbToText (Just True)  = text "(known-true)"
        mbToText (Just False) = text "(known-false)"
        mbToText Nothing      = mempty
        text' = text . unpack
-}

------------------------------------------------------------------------
-- Merge

-- | If-then-else on partial expressions.
mergePartial :: (IsExprBuilder sym, MonadIO m) =>
  sym ->
  (Pred sym -> a -> a -> PartialT sym m a)
    {- ^ Operation to combine inner values. The 'Pred' parameter is the
         if-then-else condition. -} ->
  Pred sym {- ^ condition to merge on -} ->
  PartExpr (Pred sym) a {- ^ 'if' value -}  ->
  PartExpr (Pred sym) a {- ^ 'then' value -} ->
  m (PartExpr (Pred sym) a)

{-# SPECIALIZE mergePartial ::
      IsExprBuilder sym =>
      sym ->
      (Pred sym -> a -> a -> PartialT sym IO a) ->
      Pred sym ->
      PartExpr (Pred sym) a ->
      PartExpr (Pred sym) a ->
      IO (PartExpr (Pred sym) a)   #-}

mergePartial _ _ _ Unassigned Unassigned =
     return Unassigned
mergePartial sym _ c (PE px x) Unassigned =
     do p <- liftIO $ andPred sym px c
        return $! mkPE p x
mergePartial sym _ c Unassigned (PE py y) =
     do p <- liftIO (andPred sym py =<< notPred sym c)
        return $! mkPE p y
mergePartial sym f c (PE px x) (PE py y) =
    do p <- liftIO (itePred sym c px py)
       runPartialT sym p (f c x y)

-- | Merge a collection of partial values in an if-then-else tree.
--   For example, if we merge a list like @[(xp,x),(yp,y),(zp,z)]@,
--   we get a value that is morally equivalent to:
--   @if xp then x else (if yp then y else (if zp then z else undefined))@.
mergePartials :: (IsExprBuilder sym, MonadIO m) =>
  sym ->
  (Pred sym -> a -> a -> PartialT sym m a)
    {- ^ Operation to combine inner values.
         The 'Pred' parameter is the if-then-else condition.
     -} ->
  [(Pred sym, PartExpr (Pred sym) a)]      {- ^ values to merge -} ->
  m (PartExpr (Pred sym) a)
mergePartials sym f = go
  where
  go [] = return Unassigned
  go ((c,x):xs) =
    do y <- go xs
       mergePartial sym f c x y

------------------------------------------------------------------------
-- PartialT

-- | A monad transformer which enables symbolic partial computations to run by
-- maintaining a predicate on the value.
newtype PartialT sym m a =
  PartialT { unPartial :: sym -> Pred sym -> m (PartExpr (Pred sym) a) }

-- | Run a partial computation.
runPartialT :: sym -- ^ Solver interface
            -> Pred sym -- ^ Initial condition
            -> PartialT sym m a -- ^ Computation to run.
            -> m (PartExpr (Pred sym) a)
runPartialT sym p f = unPartial f sym p

instance Functor m => Functor (PartialT sym m) where
  fmap f mx = PartialT $ \sym p -> fmap resolve (unPartial mx sym p)
    where resolve Unassigned = Unassigned
          resolve (PE q x) = PE q (f x)

-- We depend on the monad transformer as partialT explicitly orders
-- the calls to the functions in (<*>).  This ordering allows us to
-- avoid having any requirements that sym implement a partial interface.
instance (IsExpr (SymExpr sym), Monad m) => Applicative (PartialT sym m) where
  pure a = PartialT $ \_ p -> pure $! mkPE p a
  mf <*> mx = mf >>= \f -> mx >>= \x -> pure (f x)

instance (IsExpr (SymExpr sym), Monad m) => Monad (PartialT sym m) where
  return = pure
  m >>= h =
    PartialT $ \sym p -> do
      pr <- unPartial m sym p
      case pr of
        Unassigned -> pure Unassigned
        PE q r -> unPartial (h r) sym q
  fail msg = PartialT $ \_ _ -> fail msg

instance MonadTrans (PartialT sym) where
  lift m = PartialT $ \_ p -> PE p <$> m

instance (IsExpr (SymExpr sym), MonadIO m) => MonadIO (PartialT sym m) where
  liftIO = lift . liftIO

-- | End the partial computation and just return the unassigned value.
returnUnassigned :: Applicative m => PartialT sym m a
returnUnassigned = PartialT $ \_ _ -> pure Unassigned

-- | Lift a 'Maybe' value to a partial expression.
returnMaybe :: (IsExpr (SymExpr sym), Applicative m) =>  Maybe a -> PartialT sym m a
returnMaybe Nothing  = returnUnassigned
returnMaybe (Just a) = PartialT $ \_ p -> pure (mkPE p a)

-- | Return a partial expression.
--
-- This joins the partial expression with the current constraints on the
-- current computation.
returnPartial :: (IsExprBuilder sym, MonadIO m)
              => PartExpr (Pred sym) a
              -> PartialT sym m a
returnPartial Unassigned = returnUnassigned
returnPartial (PE q a) = PartialT $ \sym p -> liftIO (mkPE <$> andPred sym p q <*> pure a)

-- | Add an extra condition to the current partial computation.
addCondition_ :: (IsExprBuilder sym, MonadIO m)
              => Pred sym
              -> PartialT sym m ()
addCondition_ q = returnPartial (mkPE q ())
