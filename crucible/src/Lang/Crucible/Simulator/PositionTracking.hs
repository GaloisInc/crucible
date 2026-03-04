-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.PositionTracking
-- Description      : Execution feature for tracking program positions
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.PositionTracking
  ( positionTrackingFeature
  ) where

import Control.Lens ((^.), to)
import Control.Monad.IO.Class

import Lang.Crucible.Backend
import Lang.Crucible.Simulator.CallFrame
import Lang.Crucible.Simulator.EvalStmt
import Lang.Crucible.Simulator.ExecutionTree


-- | This execution feature adds a @LocationReachedEvent@ to
--   the backend assumption tracking whenever execution reaches the
--   head of a basic block.
positionTrackingFeature ::
  IsSymInterface sym =>
  sym ->
  IO (GenericExecutionFeature sym)
positionTrackingFeature _sym = return $ GenericExecutionFeature onStep
 where
   onStep ::
     ExecState p sym ext rtp ->
     IO (ExecutionFeatureResult p sym ext rtp)
   onStep exst@(RunningState (RunBlockStart _bid) st) =
     do let loc = st ^. (stateCrucibleFrame.to frameProgramLoc)
        liftIO $ withStateBackend st $ \bak ->
          addAssumptions bak (singleEvent (LocationReachedEvent loc))
        return (ExecutionFeatureModifiedState exst)

   onStep _ = return ExecutionFeatureNoChange
