-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.PathSplitting
-- Description      : Support for implementing path splitting
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
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

import           What4.Interface
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.Operations


data WorkItem p sym ext rtp =
  forall f args.
  WorkItem
  { workItemPred  :: Pred sym
  , workItemLoc   :: ProgramLoc
  , workItemFrame :: PausedFrame p sym ext rtp f
  , workItemState :: SimState p sym ext rtp f ('Just args)
  , workItemAssumes :: AssumptionState sym
  }

type WorkList p sym ext rtp = IORef (Seq (WorkItem p sym ext rtp))

queueWorkItem :: WorkItem p sym ext rtp -> WorkList p sym ext rtp -> IO ()
queueWorkItem i wl = atomicModifyIORef' wl (\xs -> (i Seq.<| xs, ()))

dequeueWorkItem :: WorkList p sym ext rtp -> IO (Maybe (WorkItem p sym ext rtp))
dequeueWorkItem wl =
  atomicModifyIORef' wl $ \xs ->
     case Seq.viewl xs of
       Seq.EmptyL   -> (xs,  Nothing)
       i Seq.:< xs' -> (xs', Just i)

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

{-
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
                , workItemFrame = falseFrame
                , workItemState = st
                , workItemAssumes = assumes
                }
       queueWorkItem wi wl

       addAssumption sym (LabeledPred p (ExploringAPath loc (pausedLoc trueFrame)))

       let ctx = st ^. stateTree . actContext
       Just <$> runReaderT (resumeFrame trueFrame ctx) st

  _ -> return Nothing
-}
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
                { workItemPred  = p
                , workItemLoc   = loc
                , workItemFrame = trueFrame
                , workItemState = st
                , workItemAssumes = assumes
                }
       queueWorkItem wi wl

       addAssumption sym (LabeledPred pnot (ExploringAPath loc (pausedLoc falseFrame)))

       let ctx = st ^. stateTree . actContext
       Just <$> runReaderT (resumeFrame falseFrame ctx) st

  _ -> return Nothing


executeCrucibleDFSPaths :: forall p sym ext rtp.
  ( IsSymInterface sym
  , IsSyntaxExtension ext
  ) =>
  [ ExecutionFeature p sym ext rtp ] {- ^ Execution features to install -} ->
  ExecState p sym ext rtp   {- ^ Execution state to begin executing -} ->
  IO ()
executeCrucibleDFSPaths execFeatures exst0 =
  do wl <- newIORef Seq.empty
     let feats = execFeatures ++ [pathSplittingFeature wl]
     go wl feats exst0

 where
 go wl feats exst =
   do _ <- executeCrucible feats exst
      dequeueWorkItem wl >>= \case
        Nothing -> return ()
        Just wi -> restoreWorkItem wi >>= go wl feats
