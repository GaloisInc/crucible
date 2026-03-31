-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Cut
-- Description      : Support for symbolic execution cuts
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Andrei Stefanescu <andrei@galois.com>
-- Stability        : provisional
--
-- This module provides execution features for changing the state on
-- cutpoints.
-----------------------------------------------------------------------
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Lang.Crucible.Simulator.Cut
  ( cutAndReturn
  ) where

import           Control.Lens
import           Control.Monad.Reader
import qualified Data.Bimap as Bimap
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.Simulator.CallFrame as C
import qualified Lang.Crucible.Simulator.EvalStmt as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.Operations as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegValue as C
import qualified What4.FunctionName as W

-- | This execution feature registers an override for a cutpoint.
--   The override summarizes the execution from the cutpoint
--   to the return from the function (similar to a tail call).
--   This feature requires a map from each function handle
--   to the list of cutpoints in the respective function with this
--   execution feature.
cutAndReturn ::
  (C.IsSymInterface sym, C.IsSyntaxExtension ext) =>
  C.CFG ext blocks init ret ->
  C.CutpointName ->
  Ctx.Assignment C.TypeRepr args ->
  C.TypeRepr ret ->
  C.OverrideSim p sym ext rtp args ret (C.RegValue sym ret) ->
  HashMap C.SomeHandle [C.CutpointName] ->
  IO (C.ExecutionFeature p sym ext rtp)
cutAndReturn C.CFG{..} cutpoint_name arg_types ret_type override all_cutpoints =
  case Bimap.lookup cutpoint_name cfgCutpoints of
    Just (Some cutpoint_block_id)
      | cutpoint_block <- C.getBlock cutpoint_block_id cfgBlockMap
      , Just Refl <- testEquality (C.blockInputs cutpoint_block) arg_types ->
        return $ C.ExecutionFeature $ \case
          C.RunningState (C.RunPostBranchMerge block_id) state
            | frame <- state ^. C.stateCrucibleFrame
            , C.SomeHandle cfgHandle == C.frameHandle frame
            , Just Refl <- testEquality
                (fmapFC C.blockInputs cfgBlockMap)
                (fmapFC C.blockInputs $ C.frameBlockMap frame)
            , Just Refl <- testEquality cutpoint_block_id block_id
            , Just Refl <- testEquality ret_type (C.frameReturnType frame) -> do
              let override_frame = C.OF $ C.OverrideFrame
                    { _override = W.functionNameFromText $
                        C.cutpointNameText cutpoint_name
                    , _overrideHandle = C.frameHandle frame
                    , _overrideRegMap = state ^.
                        C.stateCrucibleFrame . C.frameRegs
                    }
              result_state <- runReaderT (C.runOverrideSim ret_type override) $
                state & C.stateTree %~
                  C.pushCallFrame C.TailReturnToCrucible override_frame
              return $ C.ExecutionFeatureNewState result_state
          C.CallState return_handler (C.CrucibleCall block_id frame) state
            | Just cutpoints <- HashMap.lookup
                (C.frameHandle frame)
                all_cutpoints -> do
              let result_frame = C.setFrameCutpointPostdomInfo
                    cutpoints
                    frame
              result_state <- runReaderT
                (C.performFunctionCall
                  return_handler
                  (C.CrucibleCall block_id result_frame))
                state
              return $ C.ExecutionFeatureNewState result_state
          C.TailCallState value_from_value (C.CrucibleCall block_id frame) state
            | Just cutpoints <- HashMap.lookup
                (C.frameHandle frame)
                all_cutpoints -> do
              let result_frame = C.setFrameCutpointPostdomInfo
                    cutpoints
                    frame
              result_state <- runReaderT
                (C.performTailCall
                  value_from_value
                  (C.CrucibleCall block_id result_frame))
                state
              return $ C.ExecutionFeatureNewState result_state
          _ -> return C.ExecutionFeatureNoChange
    _ -> fail $ "unexpected cutpoint: " ++ show cutpoint_name
