{-# LANGUAGE UndecidableInstances #-}
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

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Partial
 ( -- ** Partial
   Partial(..)
 , partialPred
 , partialValue

   -- ** PartialWithErr
 , PartialWithErr(..)

   -- ** PartExpr
 , PartExpr
 , pattern PE
 , pattern Unassigned
 , mkPE
 , justPartExpr
 , maybePartExpr
 , joinMaybePE

   -- ** PartialT
 , PartialT(..)
 , runPartialT
 , returnUnassigned
 , returnMaybe
 , returnPartial
 , addCondition
 , mergePartial
 , mergePartials
 ) where

import GHC.Generics (Generic, Generic1)
import Data.Data (Data)
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

import What4.BaseTypes
import What4.Interface (IsExprBuilder, SymExpr, IsExpr, Pred)
import What4.Interface (truePred, andPred, notPred, itePred, asConstantPred)

import Control.Lens.TH (makeLenses)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Eq.Deriving (deriveEq1, deriveEq2)
import Data.Ord.Deriving (deriveOrd1, deriveOrd2)
import Text.Show.Deriving (deriveShow1, deriveShow2)

------------------------------------------------------------------------
-- ** Partial

-- | A partial value represents a value that may or may not be valid.
--
-- The '_partialPred' field represents a predicate (optionally with additional
-- provenance information) embodying the value's partiality.
data Partial p v =
  Partial { _partialPred  :: !p
          , _partialValue :: !v
          }
  deriving (Data, Eq, Functor, Generic, Generic1, Foldable, Traversable, Ord, Show)

makeLenses ''Partial

$(deriveBifunctor     ''Partial)
$(deriveBifoldable    ''Partial)
$(deriveBitraversable ''Partial)
$(deriveEq1           ''Partial)
$(deriveEq2           ''Partial)
$(deriveOrd1          ''Partial)
$(deriveOrd2          ''Partial)
$(deriveShow1         ''Partial)
$(deriveShow2         ''Partial)

-- | Create a 'Partial' expression from a value that is always defined.
total :: IsExprBuilder sym
      => sym
      -> v
      -> Partial (Pred sym) v
total sym = Partial (truePred sym)

------------------------------------------------------------------------
-- ** PartialWithErr

-- | Either a partial value, or a straight-up error.
data PartialWithErr e p v =
    NoErr (Partial p v)
  | Err e
  deriving (Data, Eq, Functor, Generic, Generic1, Foldable, Traversable, Ord, Show)

$(deriveBifunctor     ''PartialWithErr)
$(deriveBifoldable    ''PartialWithErr)
$(deriveBitraversable ''PartialWithErr)
$(deriveEq1           ''PartialWithErr)
$(deriveEq2           ''PartialWithErr)
$(deriveOrd1          ''PartialWithErr)
$(deriveOrd2          ''PartialWithErr)
$(deriveShow1         ''PartialWithErr)
$(deriveShow2         ''PartialWithErr)

------------------------------------------------------------------------
-- ** PartExpr

-- | A 'PartExpr' is a 'PartialWithErr' that provides no information about what
-- went wrong. Its name is historic.
type PartExpr p v = PartialWithErr () p v

pattern Unassigned :: PartExpr p v
pattern Unassigned = Err ()

pattern PE :: p -> v -> PartExpr p v
pattern PE p v = NoErr (Partial p v)

-- Claim that the above two patterns are exhaustive for @PartExpr p v@
{-# COMPLETE Unassigned, PE #-}

mkPE :: IsExpr p => p BaseBoolType -> a -> PartExpr (p BaseBoolType) a
mkPE p v =
  case asConstantPred p of
    Just False -> Unassigned
    _ -> PE p v

-- | Create a part expression from a value that is always defined.
justPartExpr :: IsExprBuilder sym => sym -> v -> PartExpr (Pred sym) v
justPartExpr sym = NoErr . total sym

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
-- *** Merge

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
-- *** PartialT

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
addCondition :: (IsExprBuilder sym, MonadIO m)
             => Pred sym
             -> PartialT sym m ()
addCondition q = returnPartial (mkPE q ())
