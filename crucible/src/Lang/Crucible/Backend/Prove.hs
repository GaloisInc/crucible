{-|
Module      : Lang.Crucible.Backend.Prove
Description : Proving goals under assumptions
Copyright   : (c) Galois, Inc 2024
License     : BSD3
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

data ProofResult sym t
   = Proved
   | Disproved (WE.GroundEvalFn t) (Maybe (WE.ExprRangeBindings t))
   | Unknown

proveGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  (ProofResult sym t -> IO r) ->
  IO r
proveGoal sym ld adapter asms goal k = do
  let goalPred = goal ^. CB.labeledPred
  asmsPred <- CB.assumptionsPred sym asms
  notGoal <- W4.notPred sym goalPred
  WSA.solver_adapter_check_sat adapter sym ld [asmsPred, notGoal] $
    k .
      \case
        W4R.Sat (gfn, binds) -> Disproved gfn binds
        W4R.Unsat () -> Proved
        W4R.Unknown -> Unknown

proveProofGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.ProofGoal (CB.Assumptions sym) (CB.Assertion sym) ->
  (ProofResult sym t -> IO r) ->
  IO r
proveProofGoal sym ld adapter (CB.ProofGoal asms goal) =
  proveGoal sym ld adapter asms goal
