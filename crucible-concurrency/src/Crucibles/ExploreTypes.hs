{- |
Module           : Crucibles.ExploreTypes
Description      : Types and Lenses used by thread exploration
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Crucibles.ExploreTypes where

import Control.Lens
import Control.Monad.State
import Data.Text
import Data.Map.Strict
import Data.Parameterized (Some(..))

import Lang.Crucible.Simulator

import Crucibles.Scheduler
import Crucibles.Execution
import Crucibles.Common
import Crucibles.SchedulingAlgorithm (SchedAlgM, runSchedAlg)

type ThreadEvent             = ScheduleEvent EventInfo
type ThreadResource          = Text
type ThreadSched p alg sym ext ret = Scheduler p sym ext (ThreadState p sym ext ret) ret
type ThreadExec p alg sym ext ret = Exploration p alg ext ret sym -- TODO: Rename me
type ThreadExecutions        = Executions ThreadEvent
type ThreadExecM p sym ext r f a =
  StateT (SimState p sym ext r f a) IO
type ThreadState p sym ext ret = ThreadStateP p sym ext ret

evalTEWithState ::
  SimState p sym ext r f a ->
  ThreadExecM p sym ext r f a b ->
  IO b
evalTEWithState s exec = evalStateT exec s

-- | The state managed across multiple executions
data Exploration p alg ext ret sym = Exploration
  { _exec      :: !(Executions ThreadEvent)
    -- ^ The current execution graph
  , _scheduler :: !(ThreadSched p alg sym ext ret)
    -- ^ State of each thread
  , _schedAlg  :: !alg
    -- ^ State required by the scheduling algorithm
  , _num       :: !Int
    -- ^ Number of executions explored
  , _gVars     :: !(Map Text (Some GlobalVar))
    -- ^ Map from name to GlobalVars that the exploration has invented. Typically these are locks.
  }
makeLenses ''Exploration

-- | A class for Crucible personality types @p@ which contain a
-- 'Exploration'.
class HasExploration p q alg ext ret sym | p -> q alg ext ret sym where
  exploration :: Lens' p (Exploration q alg ext ret sym)

instance HasExploration (Exploration p alg ext ret sym) p alg ext ret sym where
  exploration = id
  {-# INLINE exploration #-}

-- | A Crucible personality type
-- ( see 'Lang.Crucible.Simulator.ExecutionTree.cruciblePersonality')
-- suitable for use with @crucible-concurrency@.
newtype Personality alg ext ret sym
  = Personality { _personality :: Exploration (Personality alg ext ret sym) alg ext ret sym }
makeLenses ''Personality

instance HasExploration (Personality alg ext ret sym) (Personality alg ext ret sym) alg ext ret sym where
  exploration = personality
  {-# INLINE exploration #-}

stateExpl ::
  HasExploration p p alg ext ret sym =>
  Lens' (SimState p sym ext r f a) (ThreadExec p alg sym ext ret)
stateExpl = stateContext.cruciblePersonality.exploration

stateExplAlg ::
  HasExploration p p alg ext ret sym =>
  Lens' (SimState p sym ext r f a) alg
stateExplAlg = stateExpl.schedAlg

stateExec ::
  HasExploration p p alg ext ret sym =>
  Lens' (SimState p sym ext r f a) ThreadExecutions
stateExec = stateExpl.exec

runUpdateSchedAlg ::
  ( MonadState (SimState p sym ext r f a) m
  , HasExploration p p alg ext ret sym
  ) =>
  SchedAlgM alg b ->
  m b
runUpdateSchedAlg alg =
  do exe <- use stateExec
     dpor <- use stateExplAlg
     let (a, dpor') = runSchedAlg exe dpor alg
     stateExplAlg .= dpor'
     return a
