------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.StateContT
-- Description      : A monad providing continuations and state.
-- Copyright        : (c) Galois, Inc 2013-2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines a monad with continuations and state.  By using this
-- instead of a MTL StateT and ContT transformer stack, one can have a
-- continuation that implements MonadCont and MonadState, yet never
-- returns the final state.  This also wraps MonadST.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.Utils.StateContT
  ( StateContT(..)
    -- * Re-exports
  , Control.Monad.Cont.Class.MonadCont(..)
  , Control.Monad.State.Class.MonadState(..)
  ) where

import Control.Monad.Cont.Class   (MonadCont(..))
import Control.Monad.IO.Class     (MonadIO(..))
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.State.Class  (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
import qualified Control.Monad.Fail
#endif

import What4.Utils.MonadST

-- | A monad transformer that provides @MonadCont@ and @MonadState@.
newtype StateContT s r m a
      = StateContT { runStateContT :: (a -> s -> m r)
                                   -> s
                                   -> m r
                   }

fmapStateContT :: (a -> b) -> StateContT s r m a -> StateContT s r m b
fmapStateContT = \f m -> StateContT $ \c -> runStateContT m (\v s -> (c $! f v) s)
{-# INLINE fmapStateContT #-}

applyStateContT :: StateContT s r m (a -> b) -> StateContT s r m a -> StateContT s r m b
applyStateContT = \mf mv ->
  StateContT $ \c ->
    runStateContT mf (\f -> runStateContT mv (\v s -> (c $! f v) s))
{-# INLINE applyStateContT #-}

returnStateContT :: a -> StateContT s r m a
returnStateContT = \v -> seq v $ StateContT $ \c -> c v
{-# INLINE returnStateContT #-}

bindStateContT :: StateContT s r m a -> (a -> StateContT s r m b) -> StateContT s r m b
bindStateContT = \m n -> StateContT $ \c -> runStateContT m (\a -> runStateContT (n a) c)
{-# INLINE bindStateContT #-}

instance Functor (StateContT s r m) where
  fmap = fmapStateContT

instance Applicative (StateContT s r m) where
  pure  = returnStateContT
  (<*>) = applyStateContT

instance Monad (StateContT s r m) where
  (>>=) = bindStateContT
  return = returnStateContT

instance MonadFail m => MonadFail (StateContT s r m) where
  fail = \msg -> StateContT $ \_ _ -> fail msg

instance MonadCont (StateContT s r m) where
  callCC f = StateContT $ \c -> runStateContT (f (\a -> seq a $ StateContT $ \_ s -> c a s)) c

instance MonadState s (StateContT s r m) where
  get = StateContT $ \c s -> c s s
  put = \s -> seq s $ StateContT $ \c _ -> c () s
  state f = StateContT $ \c s -> let (r,s') = f s in (c $! r) $! s'

instance MonadTrans (StateContT s r) where
  lift = \m -> StateContT $ \c s -> m >>= \v -> seq v (c v s)

instance MonadIO m => MonadIO (StateContT s r m) where
  liftIO = lift . liftIO

instance MonadST s m => MonadST s (StateContT t r m) where
  liftST = lift . liftST

instance MonadReader v m => MonadReader v (StateContT s r m) where
  ask = lift ask
  local f m = StateContT $ \c s -> local f (runStateContT m c s)
