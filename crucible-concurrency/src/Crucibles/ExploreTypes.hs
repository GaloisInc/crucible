{- |
Module           : Crucibles.ExploreTypes
Description      : Types and Lenses used by thread exploration
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
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
type ThreadSched p alg sym ext ret = Scheduler (Exploration p alg ext ret sym) sym ext (ThreadState p alg sym ext ret) ret
type ThreadExec p alg sym ext ret = Exploration p alg ext ret sym -- TODO: Rename me
type ThreadExecutions        = Executions ThreadEvent
type ThreadExecM p alg sym ext ret r f a =
  StateT (SimState (ThreadExec p alg sym ext ret) sym ext r f a) IO
type ThreadState p alg sym ext ret = ThreadStateP (ThreadExec p alg sym ext ret) sym ext ret

evalTEWithState ::
  SimState (ThreadExec p alg sym ext ret) sym ext r f a ->
  ThreadExecM p alg sym ext ret r f a b ->
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
  , _personality :: p
    -- ^ Custom user state
  , _num       :: !Int
    -- ^ Number of executions explored
  , _gVars     :: !(Map Text (Some GlobalVar))
    -- ^ Map from name to GlobalVars that the exploration has invented. Typically these are locks.
  }
makeLenses ''Exploration

stateExpl :: Simple Lens (SimState (ThreadExec p alg sym ext ret) sym ext r f a) (ThreadExec p alg sym ext ret)
stateExpl = stateContext.cruciblePersonality

stateExplAlg :: Lens' (SimState (ThreadExec p alg sym ext ret) sym ext r f a) alg
stateExplAlg = stateExpl.schedAlg

stateExec :: Lens' (SimState (ThreadExec p alg sym ext ret) sym ext r f a) ThreadExecutions
stateExec = stateExpl.exec

runUpdateSchedAlg ::
  (MonadState (SimState (ThreadExec p alg sym ext ret) sym ext r f a) m) =>
  SchedAlgM alg b ->
  m b
runUpdateSchedAlg alg =
  do exe <- use stateExec
     dpor <- use stateExplAlg
     let (a, dpor') = runSchedAlg exe dpor alg
     stateExplAlg .= dpor'
     return a
