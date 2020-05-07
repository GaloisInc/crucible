-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.PathSplitting
-- Description      : Support for implementing path splitting
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an execution feature that converts symbolic
-- branches into path splitting by pushing unexplored paths onto a
-- worklist instead of performing eager path merging (the default
-- behavior).
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.PathSplitting
  ( WorkItem(..)
  , WorkList
  , queueWorkItem
  , dequeueWorkItem
  , restoreWorkItem
  , pathSplittingFeature
  , executeCrucibleDFSPaths
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad.Reader
import           Data.IORef
import           Data.Sequence( Seq )
import qualified Data.Sequence as Seq
import           Data.Word

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.Operations


-- | A `WorkItem` represents a suspended symbolic execution path that
--   can later be resumed.  It captures all the relevant context that
--   is required to recreate the simulator state at the point when
--   the path was suspended.
data WorkItem p sym ext rtp =
  forall f args.
  WorkItem
  { -- | The predicate we branched on to generate this work item
    workItemPred  :: Pred sym
    -- | The location of the symbolic branch
  , workItemLoc   :: ProgramLoc
    -- | The paused execution frame
  , workItemFrame :: PausedFrame p sym ext rtp f
    -- | The overall execution state of this path
  , workItemState :: SimState p sym ext rtp f ('Just args)
    -- | The assumption state of the symbolic backend when we suspended this work item
  , workItemAssumes :: AssumptionState sym
  }

-- | A `WorkList` represents a sequence of `WorkItems` that still
--   need to be explored.
type WorkList p sym ext rtp = IORef (Seq (WorkItem p sym ext rtp))

-- | Put a work item onto the front of the work list.
queueWorkItem :: WorkItem p sym ext rtp -> WorkList p sym ext rtp -> IO ()
queueWorkItem i wl = atomicModifyIORef' wl (\xs -> (i Seq.<| xs, ()))

-- | Pull a work item off the front of the work list, if there are any left.
--   When used with `queueWorkItem`, this function uses the work list as a stack
--   and will explore paths in a depth-first manner.
dequeueWorkItem :: WorkList p sym ext rtp -> IO (Maybe (WorkItem p sym ext rtp))
dequeueWorkItem wl =
  atomicModifyIORef' wl $ \xs ->
     case Seq.viewl xs of
       Seq.EmptyL   -> (xs,  Nothing)
       i Seq.:< xs' -> (xs', Just i)

-- | Given a work item, restore the simulator state so that it is ready to resume
--   exploring the path that it represents.
restoreWorkItem ::
  IsSymInterface sym =>
  WorkItem p sym ext rtp ->
  IO (ExecState p sym ext rtp)
restoreWorkItem (WorkItem branchPred loc frm st assumes) =
  do let sym = st ^. stateSymInterface
     setCurrentProgramLoc sym loc
     restoreAssumptionState sym assumes
     addAssumption sym (LabeledPred branchPred (ExploringAPath loc (pausedLoc frm)))
     let ctx = st ^. stateTree . actContext
     runReaderT (resumeFrame frm ctx) st

-- | The path splitting execution feature always selects the \"true\" branch
--   of a symbolic branch to explore first, and pushes the \"false\" branch
--   onto the front of the given work list.  With this feature enabled,
--   a single path will be explored with no symbolic branching until it is finished,
--   and all remaining unexplored paths will be suspended in the work list, where
--   they can be later resumed.
pathSplittingFeature ::
  IsSymInterface sym =>
  WorkList p sym ext rtp ->
  ExecutionFeature p sym ext rtp
pathSplittingFeature wl = ExecutionFeature $ \case
  SymbolicBranchState p trueFrame falseFrame _bt st ->

    do let sym = st ^. stateSymInterface
       pnot <- notPred sym p
       assumes <- saveAssumptionState sym
       loc <- getCurrentProgramLoc sym

       let wi = WorkItem
                { workItemPred  = pnot
                , workItemLoc   = loc
                , workItemFrame = forgetPostdomFrame falseFrame
                , workItemState = st
                , workItemAssumes = assumes
                }
       queueWorkItem wi wl

       addAssumption sym (LabeledPred p (ExploringAPath loc (pausedLoc trueFrame)))

       let ctx = st ^. stateTree . actContext
       ExecutionFeatureNewState <$> runReaderT (resumeFrame (forgetPostdomFrame trueFrame) ctx) st

  _ -> return ExecutionFeatureNoChange


-- | This function executes a state using the path splitting execution
--   feature.  Each time a path is completed, the given result
--   continuation is executed on it. If the continuation returns
--   'True', additional paths will be executed; otherwise, we exit early
--   and exploration stops.
--
--   If exploration continues, the next work item will be
--   popped of the front of the work list and will be executed in turn.
--   If a timeout result is encountered, we instead stop executing paths early.
--   The return value of this function is the number of paths that were
--   completed, and a list of remaining paths (if any) that were not
--   explored due to timeout or early exit.
executeCrucibleDFSPaths :: forall p sym ext rtp.
  ( IsSymInterface sym
  , IsSyntaxExtension ext
  ) =>
  FloatModeRepr (CrucibleFloatMode sym) ->
  [ ExecutionFeature p sym ext rtp ] {- ^ Execution features to install -} ->
  ExecState p sym ext rtp   {- ^ Execution state to begin executing -} ->
  (ExecResult p sym ext rtp -> IO Bool)
    {- ^ Path result continuation, return 'True' to explore more paths -} ->
  IO (Word64, Seq (WorkItem p sym ext rtp))
executeCrucibleDFSPaths fm execFeatures exst0 cont =
  do wl <- newIORef Seq.empty
     cnt <- newIORef (1::Word64)
     let feats = execFeatures ++ [pathSplittingFeature wl]
     go wl cnt feats exst0

 where
 go wl cnt feats exst =
   do res <- executeCrucible fm feats exst
      goOn <- cont res
      case res of
        TimeoutResult _ ->
           do xs <- readIORef wl
              i  <- readIORef cnt
              return (i,xs)

        _ | not goOn ->
           do xs <- readIORef wl
              i  <- readIORef cnt
              return (i,xs)

          | otherwise ->
             dequeueWorkItem wl >>= \case
               Nothing ->
                 do i <- readIORef cnt
                    return (i, mempty)

               Just wi ->
                 do modifyIORef' cnt succ
                    restoreWorkItem wi >>= go wl cnt feats
