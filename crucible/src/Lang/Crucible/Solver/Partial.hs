{-|
Module           : Lang.Crucible.Solver.Partial
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines a partial expression data type 'PartExpr' which is essentially a
generalization of 'Maybe' as a datatype, and a monad transformer 'PartialT'
which is a symbolic generalizion of the 'Maybe' monad.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Lang.Crucible.Solver.Partial
 ( -- * PartExpr
   PartExpr(..)
 , justPartExpr
 , maybePartExpr
 , joinMaybePE
 , readPartExpr
   -- * PartialT
 , PartialT
 , runPartialT
 , returnUnassigned
 , returnMaybe
 , returnPartial
 , addCondition
 ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class

import Lang.Crucible.BaseTypes
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Solver.BoolInterface

-- | A partial value represents a value that may or may not be assigned.
data PartExpr p v
   = PE { _pePred :: !p
        , _peValue :: !v
        }
   | Unassigned
 deriving ( Functor, Foldable, Traversable )

-- | Create a part expression from a value that is always defined.
justPartExpr :: IsBoolExprBuilder sym
             => sym -> v -> PartExpr (SymExpr sym BaseBoolType) v
justPartExpr sym = PE (truePred sym)

-- | Create a part expression from a maybe value.
maybePartExpr :: IsBoolExprBuilder sym
              => sym -> Maybe a -> PartExpr (SymExpr sym BaseBoolType) a
maybePartExpr _ Nothing = Unassigned
maybePartExpr sym (Just r) = justPartExpr sym r

joinMaybePE :: Maybe (PartExpr p v) -> PartExpr p v
joinMaybePE Nothing = Unassigned
joinMaybePE (Just pe) = pe

readPartExpr :: IsBoolSolver sym
             => sym
             -> PartExpr (Pred sym) v
             -> SimErrorReason
             -> IO v
readPartExpr sym Unassigned msg = do
  addFailedAssertion sym msg
readPartExpr sym (PE p v) msg = do
  addAssertion sym p msg
  return v

------------------------------------------------------------------------
-- PartialT

-- | A monad transformer which enables symbolic partial computations to run by
-- maintaining a predicate on the value.
newtype PartialT sym m a =
  PartialT { unPartial :: sym -> Pred sym -> m (PartExpr (Pred sym) a) }

-- | Run a partial computation.
runPartialT :: IsBoolExprBuilder sym
            => sym -- ^ Solver interface
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
instance Monad m => Applicative (PartialT sym m) where
  pure a = PartialT $ \_ p -> pure $! PE p a
  mf <*> mx = mf >>= \f -> mx >>= \x -> pure (f x)

instance Monad m => Monad (PartialT sym m) where
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

instance MonadIO m => MonadIO (PartialT sym m) where
  liftIO = lift . liftIO

-- | End the partial computation and just return the unassigned value.
returnUnassigned :: Applicative m => PartialT sym m a
returnUnassigned = PartialT $ \_ _ -> pure Unassigned

-- | Lift a 'Maybe' value to a partial expression.
returnMaybe :: Applicative m =>  Maybe a -> PartialT sym m a
returnMaybe Nothing  = returnUnassigned
returnMaybe (Just a) = PartialT $ \_ p -> pure (PE p a)

-- | Return a partial expression.
--
-- This joins the partial expression with the current constraints on the
-- current computation.
returnPartial :: (IsPred (Pred sym), IsBoolExprBuilder sym, MonadIO m)
              => PartExpr (Pred sym) a
              -> PartialT sym m a
returnPartial Unassigned = returnUnassigned
returnPartial (PE q a) =
    case asConstantPred q of
      Just False -> returnUnassigned
      _ -> PartialT $ \sym p -> liftIO $ resolve <$> andPred sym p q
  where resolve r = case asConstantPred r of
                      Just False -> Unassigned
                      _ -> PE r a




-- | Add an extra condition to the current partial computation.
addCondition :: (IsPred (Pred sym), IsBoolExprBuilder sym, MonadIO m)
              => Pred sym
              -> PartialT sym m ()
addCondition q = returnPartial (PE q ())
