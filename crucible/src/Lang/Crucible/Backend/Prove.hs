{-|
Module      : Lang.Crucible.Backend.Prove
Description : Proving goals under assumptions
Copyright   : (c) Galois, Inc 2024
License     : BSD3

== Overview

The functions in this module dispatch proof obligations arising from symbolic
execution using SMT solvers. There are several dimensions of configurability,
encapsulated in a 'ProofStrategy':

* Offline vs. online: Offline solvers ('offlineProver') are simpler to manage
  and more easily parallelized, but starting processes adds overhead; online
  solvers ('onlineProver') can share state as assumptions are added. See the
  top-level README for What4 for further discussion of this choice.
* Failing fast ('failFast') vs. keeping going ('keepGoing')
* Timeouts: Proving with timeouts ('offlineProveWithTimeout') vs. without
  ('offlineProve')

Once an appropriate strategy has been selected, it can be passed to entrypoints
such as 'proveObligations' to dispatch proof obligations.

== Parallelism

Parallel proving is available via a separate set of entrypoints, e.g,
'proveGoalsInParallel'. It only makes sense to use these with offline 'Prover's.
Furthermore, these can only be used with 'ProofStrategy's that operate in the
'IO' monad.

== Proving goals

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

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

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
  , offlineProveWithTimeoutIO
  , offlineProver
    -- *** Online
  , onlineProve
  , onlineProver
    -- * Proving goals
  , proveGoals
  , proveObligations
  , proveCurrentObligations
    -- * Proving goals in parallel
  , proveGoalsInParallel
  , proveObligationsInParallel
  , proveCurrentObligationsInParallel
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import qualified Control.Concurrent.QSem as CCQ
import qualified Control.Exception as X
import           Control.Lens ((^.))
import           Control.Monad (foldM)
import           Control.Monad.Catch (MonadMask)
import           Control.Monad.Error.Class (MonadError, liftEither)
import           Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Control.Monad.Reader as Reader
import qualified Data.IORef as IORef

import qualified What4.Interface as W4
import qualified What4.Expr as WE
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as W4SMT
import qualified What4.SatResult as W4R
import qualified What4.Solver.Adapter as WSA

import qualified Lang.Crucible.Backend as CB
import           Lang.Crucible.Backend.Assumptions (Assumptions)
import           Lang.Crucible.Utils.Timeout (Timeout, TimedOut)
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

-- | Not exported, but see 'proveGoalsInParallel'
consumeGoalsParallel ::
  Monoid asmp =>
  -- | Consume a 'Prove'
  (asmp -> goal -> IO r) ->
  -- | Consume a 'ProveConj'
  (r -> r -> IO r) ->
  CB.Goals asmp goal ->
  IO r
consumeGoalsParallel onGoal onConj goals = do
  caps <- CC.getNumCapabilities
  sem <- liftIO $ CCQ.newQSem caps
  workers <- liftIO $ IORef.newIORef []
  let onGoal' asmps goal = do
        let withQSem = X.bracket_ (CCQ.waitQSem sem) (CCQ.signalQSem sem) 
        task' <- CCA.async (withQSem (onGoal asmps goal))
        IORef.modifyIORef' workers (task':)
        pure ()
  consumeGoalsWithAssumptions onGoal' (>>) goals
  go onConj =<< IORef.readIORef workers
  where
    go :: (r -> r -> IO r) -> [CCA.Async r] -> IO r
    go combine tasks =
      partitionPoll tasks >>=
        \case
          -- Note that `rest` can't be empty (and thus this cant loop
          -- indefinitely), because `tasks` can't be empty, because `Goal`
          -- is the only leaf of `Goals` (so there must be at least one).
          ([], rest) -> delay >> go combine rest
          ((r:rs), rest) -> do
            accum <- foldM combine r rs
            foldMReady combine accum rest
  
    -- Pause for 0.1 s = 1 * 10^5 microsecs
    delay = do
      let pointOneSecond = 100000
      CC.threadDelay pointOneSecond

    -- Like foldl', but processes the inputs whenever they're ready, rather than
    -- in the order in which they're supplied in the list. Polls repeatedly, but
    -- with a delay.
    foldMReady :: (b -> a -> IO b) -> b -> [CCA.Async a] -> IO b
    foldMReady f accum as = do
      (ready, rest) <- partitionPoll as
      result <- foldM f accum ready
      if null rest
      then pure result
      else do
        delay
        foldMReady f result rest

    -- Partition a list of tasks into those that are ready (in which case,
    -- extract their results), and those that are still in progress.
    partitionPoll :: [CCA.Async r] -> IO ([r], [CCA.Async r])
    partitionPoll [] = pure ([], [])
    partitionPoll (x:xs) = do
      (ready, waiting) <- partitionPoll xs
      CCA.poll x >>=
        \case
          Just (Left exn) -> X.throwIO exn
          Just (Right r) -> pure (r:ready, waiting)
          Nothing -> pure (ready, x:waiting)

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

-- | Whether or not a subgoal was proved, together with the result from a
-- 'ProofConsumer'.
data SubgoalResult r
  = SubgoalResult
    { subgoalWasProved :: !Bool
    , subgoalResult :: !r
    }
  deriving Functor

-- | How to combine results of proofs, used as part of a 'ProofStrategy'.
newtype Combiner m r
  = Combiner
    { getCombiner ::
        m (SubgoalResult r) -> m (SubgoalResult r) -> m (SubgoalResult r)
    }

-- | Combine 'SubgoalResult's using the '<>' operator. Keep going when subgoals
-- fail.
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

-- | Combine 'SubgoalResult's using the '<>' operator. After the first subgoal
-- fails, stop trying to prove further goals.
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

-- | A collection of functions used to prove goals as part of a 'ProofStrategy'.
data Prover sym m t r
  = Prover
    { -- | Prove a single goal under some 'Assumptions'.
      proverProve ::
        Assumptions sym ->
        CB.Assertion sym ->
        ProofConsumer sym t r ->
        m (SubgoalResult r)
      -- | Assume some 'Assumptions' in the scope of a subgoal.
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

-- | Prove a goal using an \"offline\" solver (i.e., one process per goal).
--
-- See 'offlineProveWithTimeout' for a version that integrates 'Timeout's.
--
-- See the module-level documentation for further discussion of offline vs.
-- online solving.
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

-- | Prove a goal using an \"offline\" solver, with a timeout.
--
-- See 'offlineProve' for a version without 'Timeout's.
--
-- See the module-level documentation for further discussion of offline vs.
-- online solving.
offlineProveWithTimeout ::
  MonadError TimedOut m =>
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

-- | Like 'offlineProverWithTimeout', but throws timeouts as exceptions using
-- 'X.throwIO' instead of requiring 'MonadError'.
offlineProveWithTimeoutIO ::
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
offlineProveWithTimeoutIO to sym ld adapter asmps goal k = do
  r <- liftIO (CTO.withTimeout to (offlineProveIO sym ld adapter asmps goal k))
  case r of
    Left CTO.TimedOut -> liftIO (X.throwIO CTO.TimedOut)
    Right r' -> pure r'

-- | Prove goals using 'offlineProveWithTimeoutIO'.
--
-- See the module-level documentation for further discussion of offline vs.
-- online solving.
offlineProver ::
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
  { proverProve = offlineProveWithTimeoutIO to sym ld adapter
  , proverAssume = \_asmps a -> a
  }

---------------------------------------------------------------------
-- *** Online

-- | Prove a goal using an \"online\" solver (i.e., one process for all goals).
--
-- See the module-level documentation for further discussion of offline vs.
-- online solving.
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

-- | Add an assumption by @push@ing a new frame ('WPO.inNewFrame').
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

-- | Prove goals using 'onlineProve' and 'onlineAssume'.
--
-- See the module-level documentation for further discussion of offline vs.
-- online solving.
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

-- | Prove a collection of 'CB.Goals' using the specified 'ProofStrategy'.
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

-- | Prove a collection of 'CB.ProofObligations' using a 'ProofStrategy'.
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

---------------------------------------------------------------------
-- * Proving goals in parallel

-- | Prove a collection of 'CB.Goals' using the specified offline
-- 'ProofStrategy'.
--
-- This function ensures that at most 'CC.getNumCapabilities' solvers are
-- running at once. It first creates async tasks (with 'CCA.async') for proving
-- each goal, then repeatedly polls them (with a delay of 0.1s), combining
-- results (with the 'Combiner') as they become available. It does not support
-- \"failing fast\", it always waits for all solvers to complete before
-- returning.
proveGoalsInParallel ::
  Semigroup r =>
  -- | Strategy with offline prover (e.g., 'offlineProver')
  ProofStrategy sym IO t r ->
  CB.Goals (CB.Assumptions sym) (CB.Assertion sym) ->
  ProofConsumer sym t r ->
  IO r
proveGoalsInParallel strat goals k =
  subgoalResult <$>
    consumeGoalsParallel
      (\asmps gl -> proverProve (stratProver strat) asmps gl k)
      (\r1 r2 -> getCombiner (stratCombine strat) (pure r1) (pure r2))
      goals

-- | Prove a collection of 'CB.ProofObligations' in parallel using an offline
-- 'ProofStrategy'.
--
-- For more details, see 'proveGoalsInParallel'.
proveObligationsInParallel ::
  Monoid r =>
  -- | Strategy with offline prover (e.g., 'offlineProver')
  ProofStrategy sym IO t r ->
  CB.ProofObligations sym ->
  ProofConsumer sym t r ->
  IO r
proveObligationsInParallel strat obligations k =
  case obligations of
    Nothing -> pure mempty
    Just goals -> proveGoalsInParallel strat goals k

-- | Prove a the current collection of 'CB.ProofObligations' associated with the
-- symbolic backend (retrieved via 'CB.getProofObligations') in parallel using
-- an offline 'ProofStrategy'.
--
-- For more details, see 'proveGoalsInParallel'.
proveCurrentObligationsInParallel ::
  Monoid r =>
  (sym ~ WE.ExprBuilder t st fs) =>
  CB.IsSymBackend sym bak =>
  bak ->
  -- | Strategy with offline prover (e.g., 'offlineProver')
  ProofStrategy sym IO t r ->
  ProofConsumer sym t r ->
  IO r
proveCurrentObligationsInParallel bak strat k = do
  obligations <- liftIO (CB.getProofObligations bak)
  proveObligationsInParallel strat obligations k
