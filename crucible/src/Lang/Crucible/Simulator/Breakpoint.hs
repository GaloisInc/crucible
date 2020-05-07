-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Breakpoint
-- Description      : Support for symbolic execution breakpoints
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Andrei Stefanescu <andrei@galois.com>
-- Stability        : provisional
--
-- This module provides execution features for changing the state on
-- breakpoints.
-----------------------------------------------------------------------
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Lang.Crucible.Simulator.Breakpoint
  ( breakAndReturn
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

-- | This execution feature registers an override for a breakpoint.
--   The override summarizes the execution from the breakpoint
--   to the return from the function (similar to a tail call).
--   This feature requires a map from each function handle
--   to the list of breakpoints in the respective function with this
--   execution feature.
breakAndReturn ::
  (C.IsSymInterface sym, C.IsSyntaxExtension ext) =>
  C.CFG ext blocks init ret ->
  C.BreakpointName ->
  Ctx.Assignment C.TypeRepr args ->
  C.TypeRepr ret ->
  C.OverrideSim p sym ext rtp args ret (C.RegValue sym ret) ->
  HashMap C.SomeHandle [C.BreakpointName] ->
  IO (C.ExecutionFeature p sym ext rtp)
breakAndReturn C.CFG{..} breakpoint_name arg_types ret_type override all_breakpoints =
  case Bimap.lookup breakpoint_name cfgBreakpoints of
    Just (Some breakpoint_block_id)
      | breakpoint_block <- C.getBlock breakpoint_block_id cfgBlockMap
      , Just Refl <- testEquality (C.blockInputs breakpoint_block) arg_types ->
        return $ C.ExecutionFeature $ \case
          C.RunningState (C.RunPostBranchMerge block_id) state
            | frame <- state ^. C.stateCrucibleFrame
            , C.SomeHandle cfgHandle == C.frameHandle frame
            , Just Refl <- testEquality
                (fmapFC C.blockInputs cfgBlockMap)
                (fmapFC C.blockInputs $ C.frameBlockMap frame)
            , Just Refl <- testEquality breakpoint_block_id block_id
            , Just Refl <- testEquality ret_type (C.frameReturnType frame) -> do
              let override_frame = C.OF $ C.OverrideFrame
                    { _override = W.functionNameFromText $
                        C.breakpointNameText breakpoint_name
                    , _overrideHandle = C.frameHandle frame
                    , _overrideRegMap = state ^.
                        C.stateCrucibleFrame . C.frameRegs
                    }
              result_state <- runReaderT (C.runOverrideSim ret_type override) $
                state & C.stateTree %~
                  C.pushCallFrame C.TailReturnToCrucible override_frame
              return $ C.ExecutionFeatureNewState result_state
          C.CallState return_handler (C.CrucibleCall block_id frame) state
            | Just breakpoints <- HashMap.lookup
                (C.frameHandle frame)
                all_breakpoints -> do
              let result_frame = C.setFrameBreakpointPostdomInfo
                    breakpoints
                    frame
              result_state <- runReaderT
                (C.performFunctionCall
                  return_handler
                  (C.CrucibleCall block_id result_frame))
                state
              return $ C.ExecutionFeatureNewState result_state
          C.TailCallState value_from_value (C.CrucibleCall block_id frame) state
            | Just breakpoints <- HashMap.lookup
                (C.frameHandle frame)
                all_breakpoints -> do
              let result_frame = C.setFrameBreakpointPostdomInfo
                    breakpoints
                    frame
              result_state <- runReaderT
                (C.performTailCall
                  value_from_value
                  (C.CrucibleCall block_id result_frame))
                state
              return $ C.ExecutionFeatureNewState result_state
          _ -> return C.ExecutionFeatureNoChange
    _ -> fail $ "unexpected breakpoint: " ++ show breakpoint_name
