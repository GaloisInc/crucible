{-|
Module      : Lang.Crucible.Backend.Prove
Description : Proving goals under assumptions
Copyright   : (c) Galois, Inc 2024
License     : BSD3
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Backend.Prove
  ( proveGoal
  , proveProofGoal
  ) where

import           Control.Lens ((^.))

import qualified What4.Interface as W4
import qualified What4.Expr as WE
import qualified What4.Solver.Adapter as WSA
import qualified What4.SatResult as W4R

import qualified Lang.Crucible.Backend as CB
import           Lang.Crucible.Backend.Assumptions (Assumptions)

proveGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  (W4R.SatResult (WE.GroundEvalFn t, Maybe (WE.ExprRangeBindings t)) () -> IO r) ->
  IO r
proveGoal sym ld adapter asms goal k = do
  let goalPred = goal ^. CB.labeledPred
  asmsPred <- CB.assumptionsPred sym asms
  notGoal <- W4.notPred sym goalPred
  WSA.solver_adapter_check_sat adapter sym ld [asmsPred, notGoal] k

proveProofGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.ProofGoal (CB.Assumptions sym) (CB.Assertion sym) ->
  (W4R.SatResult (WE.GroundEvalFn t, Maybe (WE.ExprRangeBindings t)) () -> IO r) ->
  IO r
proveProofGoal sym ld adapter (CB.ProofGoal asms goal) =
  proveGoal sym ld adapter asms goal
