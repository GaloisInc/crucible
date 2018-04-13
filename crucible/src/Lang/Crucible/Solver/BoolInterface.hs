{-|
Module      : Lang.Crucible.Solver.BoolInterface
Copyright   : (c) Galois, Inc 2014-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides a minimalistic interface for manipulating Boolean formulas
and execution contexts in the symbolic simulator.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Solver.BoolInterface
  ( IsPred(..)
  , SymExpr
  , Pred
  , SymPathState
  , BranchResult(..)
  , IsBoolExprBuilder(..)
  , IsBoolSolver(..)
  , Assertion(..)
  , assertPred
  , itePredM
  ) where

import Control.Exception (throwIO)
import Control.Lens
import Control.Monad.IO.Class

import Lang.Crucible.BaseTypes
import Lang.Crucible.Config
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator.SimError

-- | The class for expressions.
type family SymExpr (sym :: *) :: BaseType -> *

type Pred sym = SymExpr sym BaseBoolType

------------------------------------------------------------------------
-- IsPred

class IsPred v where
  -- | Evaluate if predicate is constant.
  asConstantPred :: v -> Maybe Bool
  asConstantPred _ = Nothing

------------------------------------------------------------------------
-- IsBoolSolver

-- | @IsBoolExprBuilder@ has methods for constructing
--   symbolic expressions of boolean type.
class IsBoolExprBuilder sym where
  truePred  :: sym -> Pred sym
  falsePred :: sym -> Pred sym

  notPred :: sym -> Pred sym -> IO (Pred sym)

  andPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  orPred  :: sym -> Pred sym -> Pred sym -> IO (Pred sym)
  orPred sym x y = do
    xn <- notPred sym x
    yn <- notPred sym y
    notPred sym =<< andPred sym xn yn

  impliesPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)
  impliesPred sym x y = do
    nx <- notPred sym x
    orPred sym y nx

  xorPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  eqPred  :: sym -> Pred sym -> Pred sym -> IO (Pred sym)
  eqPred sym x y = notPred sym =<< xorPred sym x y

  -- | Perform ite on a predicate.
  itePred :: sym -> Pred sym -> Pred sym -> Pred sym -> IO (Pred sym)


-- | Perform an ite on a predicate lazily.
itePredM :: (IsPred (Pred sym), IsBoolExprBuilder sym, MonadIO m)
         => sym
         -> Pred sym
         -> m (Pred sym)
         -> m (Pred sym)
         -> m (Pred sym)
itePredM sym c mx my =
  case asConstantPred c of
    Just True -> mx
    Just False -> my
    Nothing -> do
      x <- mx
      y <- my
      liftIO $ itePred sym c x y

-- | State in the backend associated with a particular execution path.
-- This is useful
type family SymPathState (sym :: *) :: *

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

-- | Information about an assertion that was previously made.
data Assertion pred
   = Assertion { -- | Location of assertion
                 assertLoc :: !ProgramLoc
                 -- | Predicate that was asserted.
               , _assertPred :: !pred
                 -- | Message added when assertion was made.
               , assertMsg :: !(Maybe SimErrorReason)
               }

-- | Predicate that was asserted.
assertPred :: Simple Lens (Assertion pred) pred
assertPred = lens _assertPred (\s v -> s { _assertPred = v })

-- | A Boolean solver has function for building up terms, and operating
-- within an assertion context.
class ( HasProgramLoc (SymPathState sym)
      ) => IsBoolSolver sym where

  -- | Retrieve the configuration object corresponding to this solver interface.
  getConfiguration :: sym -> Config

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Given a Boolean predicate that the simulator wishes to branch on,
  -- this decides what the next course of action should be for the branch.
  evalBranch :: sym
             -> Pred sym -- Predicate to branch on.
             -> IO (BranchResult sym)

  -- | Get current state information.
  getCurrentState :: sym -> IO (SymPathState sym)

  -- | Reset simulator back to previous state.
  resetCurrentState :: sym -> SymPathState sym -> IO ()

  -- | @switchPathState sym old new@
  --
  -- This switch the path state from the current one to new.
  -- old is guaranteed to be a predecessor of both states
  switchCurrentState :: sym -> SymPathState sym -> SymPathState sym -> IO ()

  -- | Push a branch predicate and add new assertion level.
  pushBranchPred :: sym -> Pred sym -> IO ()

  -- | @mergeState sym p true_state false_state@ updates the current state info to
  -- correspond to add assertions in true_state when p is assumed true and assertions
  -- in false state when p is assumed false.
  mergeState :: sym
             -> Pred sym
             -> SymPathState sym
             -> SymPathState sym
             -> IO ()

  ----------------------------------------------------------------------
  -- Program location operations

  -- | Get current location of program for term creation purposes.
  getCurrentProgramLoc :: sym -> IO ProgramLoc

  -- | Set current location of program for term creation purposes.
  setCurrentProgramLoc :: sym -> ProgramLoc -> IO ()

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

  -- | This will cause the current path to fail
  addFailedAssertion :: sym -> SimErrorReason -> IO a
  addFailedAssertion sym msg = do
    loc <- getCurrentProgramLoc sym
    throwIO (SimError loc msg)

  -- | Get the current path condition as a predicate.
  getAssertionPred :: sym -> IO (Pred sym)

  -- | Get the collection of proof obligations.
  getProofObligations :: sym -> IO [([Pred sym], Assertion (Pred sym))]

  -- | Set the collection of proof obligations to the given list.  Typically, this is used
  --   to remove proof obligations that have been successfully proved by resetting the list
  --   of obligations to be only those not proved.
  setProofObligations :: sym -> [([Pred sym], Assertion (Pred sym))] -> IO ()

  -- | Return assertions that were added between the two path states.
  --
  -- The second path state must be a successor of the first.
  -- The assertions will be returned in reverse order from how they were
  -- added.
  getAssertionsBetween :: sym
                       -> SymPathState sym
                       -> SymPathState sym
                       -> IO [Assertion (Pred sym)]

  getAssertionsSince :: sym -> SymPathState sym -> IO [Assertion (Pred sym)]
  getAssertionsSince sym old = do
    cur <- getCurrentState sym
    getAssertionsBetween sym old cur
