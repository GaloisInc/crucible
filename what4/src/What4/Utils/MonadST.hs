------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.MonadST
-- Description      : Typeclass for monads generalizing ST
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines the MonadST class, which contains the ST
-- and IO monads and a small collection of moand transformers over them.
------------------------------------------------------------------------


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module What4.Utils.MonadST
  ( MonadST(..)
  , Control.Monad.ST.ST
  , RealWorld
  ) where

import Control.Monad.ST
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.State as L
import Control.Monad.State.Strict as S
import Control.Monad.Writer as L
import Control.Monad.Writer.Strict as S

class Monad m => MonadST s m | m -> s where
  liftST :: ST s a -> m a

instance MonadST RealWorld IO where
  liftST = stToIO

instance MonadST s (ST s) where
  liftST = id

instance MonadST s m => MonadST s (ContT r m) where
  liftST m = lift $ liftST m

instance MonadST s m => MonadST s (ReaderT r m) where
  liftST m = lift $ liftST m

instance MonadST s m => MonadST s (L.StateT u m) where
  liftST m = lift $ liftST m

instance MonadST s m => MonadST s (S.StateT u m) where
  liftST m = lift $ liftST m

instance (MonadST s m, Monoid w) => MonadST s (L.WriterT w m) where
  liftST m = lift $ liftST m

instance (MonadST s m, Monoid w) => MonadST s (S.WriterT w m) where
  liftST m = lift $ liftST m
