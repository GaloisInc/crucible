{-|
Module      : Lang.Crucible.Backend.Prove
Description : Proving goals under assumptions
Copyright   : (c) Galois, Inc 2024
License     : BSD3

This module contains helpers to dispatch the proof obligations arising from
symbolic execution using SMT solvers. There are several dimensions of
configurability, encapsulated in a 'ProofStrategy':

* Offline vs. online: Offline solvers ('offlineProver') are simpler to manage
  and more easily parallelized, but starting processes adds overhead, and online
  solvers ('onlineProver') can share state as assumptions are added. See the
  top-level README for What4 for further discussion of this choice.
* Failing fast ('failFast') vs. keeping going ('keepGoing')
* Parallelism and timeouts: Not yet available via helpers in this module, but
  may be added to a 'ProofStrategy' by clients.

Once an appropriate strategy has been selected, it can be passed to entrypoints
such as 'proveObligations' to dispatch proof obligations.

When proving a single goal, the overall approach is:

* Gather all of the assumptions ('Assumptions') currently in scope (e.g.,
  from branch conditions).
* Negate the goal ('CB.Assertion') that we are trying to prove.
* Attempt to prove the conjunction of the assumptions and the negated goal.

If this goal is satisfiable ('W4R.Sat'), then there exists a counterexample
that makes the original goal false, so we have disproven the goal. If the
negated goal is unsatisfiable ('W4R.Unsat'), on the other hand, then the
original goal is proven.

Another way to think of this is as the negated material conditional
(implication) @not (assumptions -> assertion)@. This formula is equivalent
to @not ((not assumptions) and assertion)@, i.e., @assumptions and (not
assertion)@.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Backend.Prove
  ( -- * Strategy
    ProofResult(..)
  , ProofConsumer(..)
  , ProofStrategy(..)
    -- ** Combiner
  , SubgoalResult(..)
  , Combiner(..)
  , keepGoing
  , failFast
    -- ** Prover
  , Prover(..)
    -- *** Offline
  , offlineProve
  , offlineProveWithTimeout
  , offlineProver
    -- *** Online
  , onlineProve
  , onlineProver
    -- * Proving goals
  , proveGoals
  , proveObligations
  , proveCurrentObligations
  ) where

import           Control.Lens ((^.))
import           Control.Monad.Catch (MonadMask)
import           Control.Monad.Error.Class (MonadError, liftEither)
import           Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Control.Monad.Reader as Reader

import qualified What4.Interface as W4
import qualified What4.Expr as WE
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as W4SMT
import qualified What4.SatResult as W4R
import qualified What4.Solver.Adapter as WSA

import qualified Lang.Crucible.Backend as CB
import           Lang.Crucible.Backend.Assumptions (Assumptions)
import           Lang.Crucible.Utils.Timeout (Timeout, TimeoutError)
import qualified Lang.Crucible.Utils.Timeout as CTO

-- | Local helper
consumeGoals ::
  -- | Consume an 'Assuming'
  (asmp -> a -> a) ->
  -- | Consume a 'Prove'
  (goal -> a) ->
  -- | Consume a 'ProveConj'
  (a -> a -> a) ->
  CB.Goals asmp goal ->
  a
consumeGoals onAssumption onGoal onConj = go
  where
  go (CB.Prove gl) = onGoal gl
  go (CB.Assuming as gl) = onAssumption as (go gl)
  go (CB.ProveConj g1 g2) = onConj (go g1) (go g2)

-- | Local helper
consumeGoalsWithAssumptions ::
  Monoid asmp =>
  -- | Consume a 'Prove'
  (asmp -> goal -> a) ->
  -- | Consume a 'ProveConj'
  (a -> a -> a) ->
  CB.Goals asmp goal ->
  a
consumeGoalsWithAssumptions onGoal onConj goals =
  Reader.runReader (go goals) mempty
  where
  go =
    consumeGoals
      (\asmp gl -> Reader.local (<> asmp) gl)
      (\gl -> Reader.asks (\asmps -> onGoal asmps gl))
      (\g1 g2 -> onConj <$> g1 <*> g2)

---------------------------------------------------------------------
-- * Strategy

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
     -- The 'WE.GroundEvalFn' is only available for use during the execution of
     -- a 'ProofConsumer'. See 'WSA.SolverAdapter'.
     --
     -- Corresponds to 'W4R.Sat'.
   | Disproved (WE.GroundEvalFn t) (Maybe (WE.ExprRangeBindings t))
     -- | The SMT solver returned \"unknown\".
     --
     -- Corresponds to 'W4R.Unknown'.
   | Unknown

-- | A 'ProofStrategy' dictates how results are proved.
data ProofStrategy sym m t r
  = ProofStrategy
    { -- | Generally 'offlineProver' or 'onlineProver'
      stratProver :: {-# UNPACK #-} !(Prover sym m t r)
    , stratCombine :: Combiner m r
    }

-- | A callback used to consume a 'ProofResult'.
--
-- If the result is 'Disproved', then this function must consume the
-- 'WE.GroundEvalFn' before returning. See 'WSA.SolverAdapter'.
newtype ProofConsumer sym t r
  = ProofConsumer (CB.ProofObligation sym -> ProofResult sym t -> IO r)

---------------------------------------------------------------------
-- *** Combiner

data SubgoalResult r
  = SubgoalResult
    { subgoalWasProved :: !Bool
    , subgoalResult :: !r
    }

newtype Combiner m r
  = Combiner
    { getCombiner ::
        m (SubgoalResult r) -> m (SubgoalResult r) -> m (SubgoalResult r)
    }

keepGoing :: Monad m => Semigroup r => Combiner m r
keepGoing = Combiner $ \a1 a2 -> subgoalAnd <$> a1 <*> a2
  where
  subgoalAnd ::
    Semigroup r =>
    SubgoalResult r ->
    SubgoalResult r ->
    SubgoalResult r
  subgoalAnd (SubgoalResult ok1 r1) (SubgoalResult ok2 r2) =
    SubgoalResult (ok1 && ok2) (r1 <> r2)

failFast :: Monad m => Semigroup r => Combiner m r
failFast = Combiner $ \sr1 sr2 -> do
  SubgoalResult ok1 r1 <- sr1
  if ok1
  then do
    SubgoalResult ok2 r2 <- sr2
    pure (SubgoalResult ok2 (r1 <> r2))
  else pure (SubgoalResult False r1)

isProved :: ProofResult sym t -> Bool
isProved =
  \case
    Proved {} -> True
    Disproved {} -> False
    Unknown {} -> False

---------------------------------------------------------------------
-- ** Prover

data Prover sym m t r
  = Prover
    { proverProve ::
        Assumptions sym ->
        CB.Assertion sym ->
        ProofConsumer sym t r ->
        m (SubgoalResult r)
    , proverAssume ::
        Assumptions sym ->
        m (SubgoalResult r) ->
        m (SubgoalResult r)
    }

---------------------------------------------------------------------
-- *** Offline

-- Not exported
offlineProveIO ::
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  ProofConsumer sym t r ->
  IO (SubgoalResult r)
offlineProveIO sym ld adapter asmps goal (ProofConsumer k) = do
  let goalPred = goal ^. CB.labeledPred
  asmsPred <- CB.assumptionsPred sym asmps
  notGoal <- W4.notPred sym goalPred
  WSA.solver_adapter_check_sat adapter sym ld [asmsPred, notGoal] $ \r ->
    let r' =
          case r of
            W4R.Sat (gfn, binds) -> Disproved gfn binds
            W4R.Unsat () -> Proved
            W4R.Unknown -> Unknown
    in SubgoalResult (isProved r') <$> k (CB.ProofGoal asmps goal) r'

offlineProve ::
  MonadIO m =>
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  ProofConsumer sym t r ->
  m (SubgoalResult r)
offlineProve sym ld adapter asmps goal k =
  liftIO (offlineProveIO sym ld adapter asmps goal k)

offlineProveWithTimeout ::
  MonadError TimeoutError m =>
  MonadIO m =>
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  Timeout ->
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Assumptions sym ->
  CB.Assertion sym ->
  ProofConsumer sym t r ->
  m (SubgoalResult r)
offlineProveWithTimeout to sym ld adapter asmps goal k = do
  r <- liftIO (CTO.withTimeout to (offlineProveIO sym ld adapter asmps goal k))
  liftEither r

offlineProver ::
  MonadError TimeoutError m =>
  MonadIO m =>
  (sym ~ WE.ExprBuilder t st fs) =>
  Timeout ->
  W4.IsSymExprBuilder sym =>
  sym ->
  WSA.LogData ->
  WSA.SolverAdapter st ->
  Prover sym m t r
offlineProver to sym ld adapter =
  Prover
  { proverProve = offlineProveWithTimeout to sym ld adapter
  , proverAssume = \_asmps a -> a
  }

---------------------------------------------------------------------
-- *** Online

onlineProve ::
  MonadIO m =>
  W4SMT.SMTReadWriter solver =>
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  WPO.SolverProcess t solver ->
  Assumptions sym ->
  CB.Assertion sym ->
  ProofConsumer sym t r ->
  m (SubgoalResult r)
onlineProve sProc asmps goal (ProofConsumer k) =
  liftIO $ WPO.checkSatisfiableWithModel sProc "prove" (goal ^. CB.labeledPred) $ \r ->
    let r' =
          case r of
            W4R.Sat gfn -> Disproved gfn Nothing
            W4R.Unsat () -> Proved
            W4R.Unknown -> Unknown
    in SubgoalResult (isProved r') <$> k (CB.ProofGoal asmps goal) r'

onlineAssume :: 
  MonadIO m =>
  MonadMask m =>
  W4SMT.SMTReadWriter solver =>
  W4.IsSymExprBuilder sym =>
  (W4.SymExpr sym ~ WE.Expr t) =>
  sym ->
  WPO.SolverProcess t solver ->
  Assumptions sym ->
  m r ->
  m r
onlineAssume sym sProc asmps a =
  WPO.inNewFrame sProc $ do
    liftIO $ do
      let conn = WPO.solverConn sProc
      asmpsPred <- CB.assumptionsPred sym asmps
      term <- W4SMT.mkFormula conn asmpsPred
      W4SMT.assumeFormula conn term
      pure ()
    a

onlineProver ::
  MonadIO m =>
  MonadMask m =>
  W4SMT.SMTReadWriter solver =>
  (sym ~ WE.ExprBuilder t st fs) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  WPO.SolverProcess t solver ->
  Prover sym m t r
onlineProver sym sProc =
  Prover
  { proverProve = onlineProve sProc
  , proverAssume = onlineAssume sym sProc
  }

---------------------------------------------------------------------
-- * Proving goals

proveGoals ::
  Functor m =>
  ProofStrategy sym m t r ->
  CB.Goals (CB.Assumptions sym) (CB.Assertion sym) ->
  ProofConsumer sym t r ->
  m r
proveGoals (ProofStrategy prover (Combiner comb)) goals k =
  fmap subgoalResult $
    consumeGoalsWithAssumptions
      (\asmps gl -> proverProve prover asmps gl k)
      comb
      goals

proveObligations ::
  Applicative m =>
  Monoid r =>
  (sym ~ WE.ExprBuilder t st fs) =>
  ProofStrategy sym m t r ->
  CB.ProofObligations sym ->
  ProofConsumer sym t r ->
  m r
proveObligations strat obligations k =
  case obligations of
    Nothing -> pure mempty
    Just goals -> proveGoals strat goals k

-- | Prove a the current collection of 'CB.ProofObligations' associated with the
-- symbolic backend (retrieved via 'CB.getProofObligations').
proveCurrentObligations ::
  MonadIO m =>
  Monoid r =>
  (sym ~ WE.ExprBuilder t st fs) =>
  CB.IsSymBackend sym bak =>
  bak ->
  ProofStrategy sym m t r ->
  ProofConsumer sym t r ->
  m r
proveCurrentObligations bak strat k = do
  obligations <- liftIO (CB.getProofObligations bak)
  proveObligations strat obligations k
