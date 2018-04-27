{-|
Module      : Lang.Crucible.Solver.BoolInterface
Copyright   : (c) Galois, Inc 2014-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides a minimalistic interface for manipulating Boolean formulas
and execution contexts in the symbolic simulator.

  [@instance 'IsBoolSolver' sym@]
  Functions for managing path conditions and assertions.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Solver.BoolInterface
  ( BranchResult(..)
  , IsBoolSolver(..)
  , Assertion(..)
  , assertPred
  , IsSymInterface
    -- * Utilities
  , addAssertionM
  , assertIsInteger
  , readPartExpr
  ) where

import Data.Sequence (Seq)

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Solver.Interface
import Lang.Crucible.Solver.AssumptionStack
import Lang.Crucible.Utils.Complex

-- | Result of attempting to branch on a predicate.
data BranchResult sym
     -- | Branch is symbolic.
     --
     -- The Boolean value indicates whether the backend suggests that the active
     -- path should be the case where the condition is true or false.
   = SymbolicBranch !Bool

     -- | No branch is needed, and the predicate is evaluated to the
     -- given value.
   | NoBranch !Bool

     -- | In branching, the simulator detected that the current path
     -- is infeasible.
   | InfeasibleBranch

type IsSymInterface sym = (IsBoolSolver sym, IsSymExprBuilder sym)

-- | A Boolean solver has function for building up terms, and operating
-- within an assertion context.
class IsBoolSolver sym where

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Given a Boolean predicate that the simulator wishes to branch on,
  -- this decides what the next course of action should be for the branch.
  evalBranch :: sym
             -> Pred sym -- Predicate to branch on.
             -> IO (BranchResult sym)

  -- | Push a new assumption frame onto the stack.  Assumptions and assertions
  --   made will now be associated with this frame on the stack until a new
  --   frame is pushed onto the stack, or until this one is popped.
  pushAssumptionFrame :: sym -> IO FrameIdentifier

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.  Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrame :: sym -> FrameIdentifier -> IO (Seq (Pred sym))

  ----------------------------------------------------------------------
  -- Assertions

  -- | Add an assertion to the current state.
  --
  -- This may throw the given SimError if the assertion is unsatisfiable.
  --
  -- Every assertion added to the system produces a proof obligation. These
  -- proof obligations can be retrieved via the 'getProofObligations' call.
  addAssertion :: sym -> Pred sym -> SimErrorReason -> IO ()

  -- | Add an assumption to the current state.  Like assertions, assumptions
  --   add logical facts to the current path condition.  However, assumptions
  --   cannot lead to path failures.  Moreover, they do not produce proof
  --   obligations the way assertions do.
  addAssumption :: sym -> Pred sym -> IO ()

  addAssumptions :: sym -> Seq (Pred sym) -> IO ()

  -- | This will cause the current path to fail
  addFailedAssertion :: sym -> SimErrorReason -> IO a

  -- | Get the current path condition as a predicate.
  getPathCondition :: sym -> IO (Pred sym)

  -- | Get the collection of proof obligations.
  getProofObligations :: sym -> IO (Seq (ProofGoal (Pred sym) SimErrorReason))

  -- | Set the collection of proof obligations to the given sequence.  Typically, this is used
  --   to remove proof obligations that have been successfully proved by resetting the list
  --   of obligations to be only those not proved.
  setProofObligations :: sym -> Seq (ProofGoal (Pred sym) SimErrorReason) -> IO ()

  cloneAssumptionState :: sym -> IO (AssumptionStack (Pred sym) SimErrorReason)

  restoreAssumptionState :: sym -> AssumptionStack (Pred sym) SimErrorReason -> IO ()


addAssertionM :: IsBoolSolver sym
              => sym
              -> IO (Pred sym)
              -> SimErrorReason
              -> IO ()
addAssertionM sym pf msg = do
  p <- pf
  addAssertion sym p msg

assertIsInteger :: (IsBoolSolver sym, IsExprBuilder sym)
                => sym
                -> SymReal sym
                -> SimErrorReason
                -> IO ()
assertIsInteger sym v msg = do
  addAssertionM sym (isInteger sym v) msg

readPartExpr :: IsBoolSolver sym
             => sym
             -> PartExpr (Pred sym) v
             -> SimErrorReason
             -> IO v
readPartExpr sym Unassigned msg = do
  addFailedAssertion sym msg
readPartExpr sym (PE p v) msg = do
  addAssertion sym p msg
  return v
