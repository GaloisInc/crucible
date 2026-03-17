{-|
Module      : Lang.Crucible.Simulator.EagerProving
Description : Eagerly prove goals during symbolic execution
Copyright   : (c) Galois, Inc 2026
License     : BSD3

This module provides an 'ExecutionFeature' that eagerly proves proof obligations
during symbolic execution. See 'eagerProvingFeature' for the main entry point.
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Simulator.EagerProving
  ( -- * Triggers
    EagerProvingTrigger(..)
  , proveEveryStep
  , proveAtBranches
    -- * Feature
  , eagerProvingFeature
    -- * Consumers
  , EagerProofConsumer(..)
  , abortOnFailure
  , abortResult
  ) where

import           Control.Lens ((^.))

import qualified What4.Expr as WE
import qualified What4.Interface as W4

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Prove as CBP
import qualified Lang.Crucible.Simulator.EvalStmt as ES
import qualified Lang.Crucible.Simulator.ExecutionTree as ET

-- | Controls which execution states trigger eager proving.
newtype EagerProvingTrigger p sym ext rtp =
  EagerProvingTrigger
  { shouldProve :: ET.ExecState p sym ext rtp -> Bool
  }

-- | Trigger proving on every step except 'ResultState'.
proveEveryStep :: EagerProvingTrigger p sym ext rtp
proveEveryStep = EagerProvingTrigger $ \exst ->
  case exst of
    ET.ResultState {} -> False
    _ -> True

-- | Trigger proving on symbolic branch and merge states.
proveAtBranches :: EagerProvingTrigger p sym ext rtp
proveAtBranches = EagerProvingTrigger $ \exst ->
  case exst of
    ET.SymbolicBranchState {} -> True
    ET.BranchMergeState {} -> True
    _ -> False

-- | A function that, given the current 'ET.ExecState', produces a
-- 'CBP.ProofConsumer' to handle each proof result.
--
-- Parameterizing over 'ET.ExecState' allows the consumer to
-- construct 'ET.AbortState' values, see e.g., 'abortOnFailure'.
newtype EagerProofConsumer p sym ext rtp t =
  EagerProofConsumer
  { getEagerProofConsumer ::
      ET.ExecState p sym ext rtp ->
      CBP.ProofConsumer sym t (ES.ExecutionFeatureResult p sym ext rtp)
  }

-- | A default 'EagerProofConsumer' that aborts execution on disproof or
-- unknown results.
--
-- On 'CBP.Proved', returns 'ES.ExecutionFeatureNoChange'. On 'CBP.Disproved'
-- or 'CBP.Unknown', returns an 'ExecutionFeatureNewState' wrapping an
-- 'ET.AbortState' with the 'CB.AssertionFailure' from the obligation's
-- assertion.
abortOnFailure :: EagerProofConsumer p sym ext rtp t
abortOnFailure = EagerProofConsumer $ \exst -> CBP.ProofConsumer $ \obl res ->
  case res of
    CBP.Proved -> pure ES.ExecutionFeatureNoChange
    CBP.Disproved {} -> pure (abortResult obl exst)
    CBP.Unknown -> pure (abortResult obl exst)

-- | Construct an 'ET.AbortState' from an 'ET.ExecState' and a failed
-- 'CB.ProofObligation'.
abortResult ::
  CB.ProofObligation sym ->
  ET.ExecState p sym ext rtp ->
  ES.ExecutionFeatureResult p sym ext rtp
abortResult obl exst =
  let err = CB.proofGoal obl ^. CB.labeledPredMsg
  in case ET.execStateSimState exst of
       Just (ET.SomeSimState st) ->
         ES.ExecutionFeatureNewState (ET.AbortState (CB.AssertionFailure err) st)
       Nothing ->
         -- ResultState or InitialState: no SimState available, cannot abort
         ES.ExecutionFeatureNoChange

-- | An 'ExecutionFeature' that eagerly proves proof obligations.
--
-- Proved obligations are removed from the active set.
eagerProvingFeature ::
  forall p sym ext rtp t st fs.
  (sym ~ WE.ExprBuilder t st fs, W4.IsSymExprBuilder sym) =>
  -- | How to prove results
  CBP.ProofStrategy sym IO t (ES.ExecutionFeatureResult p sym ext rtp) ->
  -- | Consumer, see e.g. 'abortOnFailure'.
  EagerProofConsumer p sym ext rtp t ->
  -- | When to prove results, see e.g. 'proveEveryStep' or 'proveAtBranches'.
  EagerProvingTrigger p sym ext rtp ->
  ES.ExecutionFeature p sym ext rtp
eagerProvingFeature strategy consumer trigger =
  ES.ExecutionFeature $ \exst ->
    if not (shouldProve trigger exst)
    then pure ES.ExecutionFeatureNoChange
    else
      ET.withBackend (ET.execStateContext exst) $ \bak -> do
        obligations <- CB.getProofObligations bak
        case obligations of
          Nothing -> pure ES.ExecutionFeatureNoChange
          Just _goals -> do
            CB.clearProofObligations bak
            let k = getEagerProofConsumer consumer exst
            CBP.proveObligations strategy obligations k
