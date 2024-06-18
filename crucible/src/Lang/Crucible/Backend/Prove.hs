{-|
Module      : Lang.Crucible.Backend.Prove
Description : Proving goals under assumptions
Copyright   : (c) Galois, Inc 2024
License     : BSD3
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Backend.Prove
  ( ProofResult(..)
  , proveGoal
  , proveProofGoal
  , proveGoals
  , proveObligations
  , proveCurrentObligations
  ) where

import           Control.Lens ((^.))
import           Data.Functor.Const (Const(Const, getConst))

import qualified What4.Interface as W4
import qualified What4.Expr as WE
import qualified What4.Solver.Adapter as WSA
import qualified What4.SatResult as W4R

import qualified Lang.Crucible.Backend as CB
import           Lang.Crucible.Backend.Assumptions (Assumptions)
import           Lang.Crucible.Backend.ProofGoals (traverseGoalsWithAssumptions)

type Goal sym = CB.ProofGoal (CB.Assumptions sym) (CB.Assertion sym)

data ProofResult sym t
   = Proved (Goal sym)
   | Disproved (Goal sym) (WE.GroundEvalFn t) (Maybe (WE.ExprRangeBindings t))
   | Unknown (Goal sym)

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
  let goal' = CB.ProofGoal asms goal
  WSA.solver_adapter_check_sat adapter sym ld [asmsPred, notGoal] $
    k .
      \case
        W4R.Sat (gfn, binds) -> Disproved goal' gfn binds
        W4R.Unsat () -> Proved goal'
        W4R.Unknown -> Unknown goal'

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

proveGoals ::
  (Monoid m, sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.Goals (CB.Assumptions sym) (CB.Assertion sym) ->
  (ProofResult sym t -> IO m) ->
  IO m
proveGoals sym ld adapter goals k =
  getConst $
    traverseGoalsWithAssumptions
      (\as g -> Const (proveGoal sym ld adapter as g k))
      goals

proveObligations ::
  (Monoid m, sym ~ WE.ExprBuilder t st fs) =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.ProofObligations sym ->
  (ProofResult sym t -> IO m) ->
  IO m
proveObligations sym ld adapter obligations k =
  case obligations of
    Nothing -> pure mempty
    Just goals -> proveGoals sym ld adapter goals k

proveCurrentObligations ::
  (Monoid m, CB.IsSymBackend sym bak, sym ~ WE.ExprBuilder t st fs) =>
  bak ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  (ProofResult sym t -> IO m) ->
  IO m
proveCurrentObligations bak ld adapter k = do
  obligations <- CB.getProofObligations bak
  let sym = CB.backendGetSym bak
  proveObligations sym ld adapter obligations k
