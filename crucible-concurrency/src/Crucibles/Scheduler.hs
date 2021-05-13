{- |
Module           : Scheduler
Description      : Representation of a process scheduler
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

A Scheduler is principally a vector of threads with some additional bookkeeping.

Here, we track the value returned by the main thread (if it has returned), the
active thread, and the number of context switches that have been observed.

Most of the functions here are just for convenience, as the Lens interface makes
updating the record simple enough.
-}
{-# LANGUAGE RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
module Crucibles.Scheduler where

import           Control.Lens
import           Control.Monad.State
import qualified Data.Vector as V
import           Data.Vector.Lens
import qualified Lang.Crucible.Types as C
import           Lang.Crucible.Simulator

-- | The scheduler state, which is parameterized by the thread state as well as
-- the top level return type. This is dependent on Crucible types, but that
-- might not be necessary or desirable.
data Scheduler p sym ext th ret =
  Scheduler
  { _threads      :: !(V.Vector th) -- ^ The actual thread states
  , _retRepr      :: !(C.TypeRepr ret) -- ^ Typerepr of the top level return type
  -- , _mainResult   :: Maybe (RegEntry sym ret) -- ^ If the main thread has returned a value, it is stored here.
  , mainCont      :: !(forall rtp. OverrideSim p sym ext rtp C.EmptyCtx ret (RegValue sym ret))
  , _activeThread :: !Int -- ^ In the domain of @_threads@, which thread is currently active
  , _numSwitches  :: !Int -- ^ Bookkeeping -- this can probably be anything and should be refactored?
  }
makeLenses ''Scheduler

type ASchedSetter s p sym ext th ret =
  ASetter s s (Scheduler p sym ext th ret) (Scheduler p sym ext th ret)

-- | Add a new thread to the scheduler as a monadic action.
-- This appends the thread to the end of the scheduler.
addThread :: MonadState s m
          => ASchedSetter s p sym ext th ret -> th -> m ()
addThread atSched th = atSched.threads %= flip V.snoc th

-- | Replace the state of thread @i@ as a monadic action.
setThreadState :: MonadState s m
               => ASchedSetter s p sym ext th ret -> Int -> th -> m ()
setThreadState atSched i th = atSched.threads.ordinals [i] .= th

getThreadState :: MonadState s m
               => Lens' s (Scheduler p sym ext th ret) -> Int -> m th
getThreadState atSched thId =
  do ts <- use $ atSched.threads
     return $! ts V.! thId

-- | Replace the state of the active thread as a monadic action.
setActiveThreadState :: MonadState s m
                     => Lens' s (Scheduler p sym ext th ret)  -> th -> m ()
setActiveThreadState atSched th =
  do i <- use (atSched.activeThread)
     setThreadState atSched i th

-- | Make thread @i@ the active thread a monadic action
switchThread :: MonadState s m
             => Lens' s (Scheduler p sym ext th ret) -> Int -> m ()
switchThread atSched i = atSched.activeThread .= i

-- | Return a list of (thread index, thread state) pairs that satisfy some
-- predicate.
selectThreads :: MonadState s m
              => Lens' s (Scheduler p sym ext th ret) -> (V.Vector th -> Int -> th -> Bool) -> m [(Int, th)]
selectThreads atSched p =
  do ts <- use (atSched.threads)
     return $ V.ifoldl' (pick ts) [] ts
  where
    pick ts selected i th
      | p ts i th    = (i,th) : selected
      | otherwise = selected
