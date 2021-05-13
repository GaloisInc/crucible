{- |
Module           : Crucibles.SchedulingAlgorithm
Description      : Interface to scheduling decisions
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

Defines the typeclass that serves as the interface between the exploration
feature and the algorithm for picking threads to run.
-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
module Crucibles.SchedulingAlgorithm where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.State

import Crucibles.Common
import Crucibles.Execution

data SchedRO = SchedRO
  { _exec :: Executions (ScheduleEvent EventInfo)
  }
makeLenses ''SchedRO

-- | The algorithm gets RO access to the execution graph
type SchedAlgM alg a =
  ReaderT SchedRO (State alg) a

class SchedulingAlgorithm alg where
  -- | Initialize the algorithm
  initialAlgState :: alg

  -- | Do any initialization required before a new execution
  prepareNewExecution :: SchedAlgM alg ()

  -- | Given a terminated run, do any post-processing
  processExecution :: Executions (ScheduleEvent EventInfo) -> alg -> alg

  -- | Determine if we have explored enough executions
  fullyExplored :: Executions (ScheduleEvent EventInfo) -> alg -> Bool

  -- | Perform any updates pertaining to adding new events to the execution graph
  notifyNewEvents :: ThreadID -> Direction -> [ScheduleEvent EventInfo] -> SchedAlgM alg ()

  -- | Indicate that the current event results in a branch state.
  -- The algorithm will typically need to record the fact that there are
  -- two paths to explore (the true and false branches)
  notifyBranch :: ThreadID -> EventID -> SchedAlgM alg ()

  -- | Given a thread and the list of runnable threadID/thread pairs, pick a new
  -- thread to run
  pickNextThread :: ThreadID -> [(Int, ThreadStateP p sym ext ret)] -> SchedAlgM alg (Maybe (ThreadID, Direction))

  -- | Debugging: print out the current execution graph/algorithm state.
  ppExecutions :: Executions (ScheduleEvent EventInfo) -> alg -> String

-- | Run the scheduler action
runSchedAlg :: Executions (ScheduleEvent EventInfo) -> alg -> SchedAlgM alg a -> (a, alg)
runSchedAlg ex dpor alg =
  runState (runReaderT alg (SchedRO { _exec = ex })) dpor
