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

-- | The result of attempting to prove a goal with an SMT solver.
--
-- The constructors of this type correspond to those of 'W4R.SatResult'.
data ProofResult sym t
   = -- | The goal was proved.
     --
     -- Corresponds to 'W4R.Unsat'.
     Proved
     -- | The goal was disproved, and a model that falsifies it is available.
     --
     -- Corresponds to 'W4R.Sat'.
   | Disproved (WE.GroundEvalFn t) (Maybe (WE.ExprRangeBindings t))
     -- | The SMT solver returned \"unknown\".
     --
     -- Corresponds to 'W4R.Unknown'.
   | Unknown

-- | Prove a single goal ('CB.Assertion') under the supplied 'Assumptions'.
--
-- The overall approach is:
--
-- * Gather all of the assumptions ('Assumptions') currently in scope (e.g.,
--   from branch conditions).
-- * Negate the goal ('CB.Assertion') that were are trying to prove.
-- * Attempt to prove the conjunction of the assumptions and the negated goal.
--
-- If this goal is satisfiable ('W4R.Sat'), then there exists a counterexample
-- that makes the original goal false, so we have disproven the goal. If the
-- negated goal is unsatisfiable ('W4R.Unsat'), on the other hand, then the
-- original goal is proven.
--
-- Another way to think of this is as the negated material conditional
-- (implication) @not (assumptions -> assertion)@. This formula is equivalent
-- to @not ((not assumptions) and assertion)@, i.e., @assumptions and (not
-- assertion)@.
proveGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  -- | Continuation to process the 'ProofResult'.
  (CB.ProofObligation sym -> ProofResult sym t -> IO r) ->
  IO r
proveGoal sym ld adapter asms goal k = do
  let goalPred = goal ^. CB.labeledPred
  asmsPred <- CB.assumptionsPred sym asms
  notGoal <- W4.notPred sym goalPred
  WSA.solver_adapter_check_sat adapter sym ld [asmsPred, notGoal] $
    k (CB.ProofGoal asms goal) .
      \case
        W4R.Sat (gfn, binds) -> Disproved gfn binds
        W4R.Unsat () -> Proved
        W4R.Unknown -> Unknown

-- | Prove a single 'CB.ProofGoal'.
proveProofGoal ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.ProofGoal (CB.Assumptions sym) (CB.Assertion sym) ->
  -- | Continuation to process the 'ProofResult'.
  (CB.ProofObligation sym -> ProofResult sym t -> IO r) ->
  IO r
proveProofGoal sym ld adapter (CB.ProofGoal asms goal) =
  proveGoal sym ld adapter asms goal

-- | Prove a collection of 'CB.Goals'.
proveGoals ::
  (Monoid m, sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.Goals (CB.Assumptions sym) (CB.Assertion sym) ->
  -- | Continuation to process each 'ProofResult'.
  (CB.ProofObligation sym -> ProofResult sym t -> IO m) ->
  IO m
proveGoals sym ld adapter goals k =
  getConst $
    traverseGoalsWithAssumptions
      (\as g -> Const (proveGoal sym ld adapter as g k))
      goals

-- | Prove a collection of 'CB.ProofObligations'.
proveObligations ::
  (Monoid m, sym ~ WE.ExprBuilder t st fs) =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  CB.ProofObligations sym ->
  -- | Continuation to process each 'ProofResult'.
  (CB.ProofObligation sym -> ProofResult sym t -> IO m) ->
  IO m
proveObligations sym ld adapter obligations k =
  case obligations of
    Nothing -> pure mempty
    Just goals -> proveGoals sym ld adapter goals k

-- | Prove a the current collection of 'CB.ProofObligations' associated with the
-- symbolic backend (retrieved via 'CB.getProofObligations').
proveCurrentObligations ::
  (Monoid m, CB.IsSymBackend sym bak, sym ~ WE.ExprBuilder t st fs) =>
  bak ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  -- | Continuation to process each 'ProofResult'.
  (CB.ProofObligation sym -> ProofResult sym t -> IO m) ->
  IO m
proveCurrentObligations bak ld adapter k = do
  obligations <- CB.getProofObligations bak
  let sym = CB.backendGetSym bak
  proveObligations sym ld adapter obligations k
