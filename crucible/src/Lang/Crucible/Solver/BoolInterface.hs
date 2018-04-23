{-|
Module      : Lang.Crucible.Solver.BoolInterface
Copyright   : (c) Galois, Inc 2014-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides a minimalistic interface for manipulating Boolean formulas
and execution contexts in the symbolic simulator.
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
  ( SymPathState
  , BranchResult(..)
  , IsBoolExprBuilder(..)
  , IsBoolSolver(..)
  , Assertion(..)
  , assertPred
  , IsSymInterface
    -- * Utilities
  , addAssertionM
  , assertIsInteger
  , cplxDiv
  , cplxLog
  , cplxLogBase
  , readPartExpr
  ) where

import Control.Exception (throwIO)
import Control.Lens

import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Solver.Interface
import Lang.Crucible.Utils.Complex

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

type IsSymInterface sym = (IsBoolSolver sym, IsSymbolicExprBuilder sym)

-- | A Boolean solver has function for building up terms, and operating
-- within an assertion context.
class ( HasProgramLoc (SymPathState sym)
      ) => IsBoolSolver sym where

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


addAssertionM :: IsBoolSolver sym
              => sym
              -> IO (Pred sym)
              -> SimErrorReason
              -> IO ()
addAssertionM sym pf msg = do
  p <- pf
  addAssertion sym p msg

-- | Divide one number by another.
--
-- Adds assertion on divide by zero.
cplxDiv :: (IsExprBuilder sym, IsBoolSolver sym)
        => sym
        -> SymCplx sym
        -> SymCplx sym
        -> IO (SymCplx sym)
cplxDiv sym x y = do
  addAssertionM sym (isNonZero sym y) (GenericSimError "Divide by zero")
  xr :+ xi <- cplxGetParts sym x
  yc@(yr :+ yi) <- cplxGetParts sym y
  case asRational <$> yc of
    (_ :+ Just 0) -> do
      zc <- (:+) <$> realDiv sym xr yr <*> realDiv sym xi yr
      mkComplex sym zc
    (Just 0 :+ _) -> do
      zc <- (:+) <$> realDiv sym xi yi <*> realDiv sym xr yi
      mkComplex sym zc
    _ -> do
      yr_abs <- realMul sym yr yr
      yi_abs <- realMul sym yi yi
      y_abs <- realAdd sym yr_abs yi_abs

      zr_1 <- realMul sym xr yr
      zr_2 <- realMul sym xi yi
      zr <- realAdd sym zr_1 zr_2

      zi_1 <- realMul sym xi yr
      zi_2 <- realMul sym xr yi
      zi <- realSub sym zi_1 zi_2

      zc <- (:+) <$> realDiv sym zr y_abs <*> realDiv sym zi y_abs
      mkComplex sym zc

-- | Helper function that returns logarithm of input.
--
-- This operation adds an assertion that the input is non-zero.
cplxLog' :: (IsExprBuilder sym, IsBoolSolver sym)
         => sym -> SymCplx sym -> IO (Complex (SymReal sym))
cplxLog' sym x = do
  let err = GenericSimError "Input to log must be non-zero."
  addAssertionM sym (isNonZero sym x) err
  xr :+ xi <- cplxGetParts sym x
  -- Get the magnitude of the value.
  xm <- realHypot sym xr xi
  -- Get angle of complex number.
  xa <- realAtan2 sym xi xr
  -- Get log of magnitude
  zr <- realLog sym xm
  return $! zr :+ xa

-- | Returns logarithm of input.
--
-- This operation adds an assertion that the input is non-zero.
cplxLog :: (IsExprBuilder sym, IsBoolSolver sym)
        => sym -> SymCplx sym -> IO (SymCplx sym)
cplxLog sym x = mkComplex sym =<< cplxLog' sym x

-- | Returns logarithm of input at a given base.
--
-- This operation adds an assertion that the input is non-zero.
cplxLogBase :: (IsExprBuilder sym, IsBoolSolver sym)
            => Rational
            -> sym
            -> SymCplx sym
            -> IO (SymCplx sym)
cplxLogBase base sym x = do
  b <- realLog sym =<< realLit sym base
  z <- traverse (\r -> realDiv sym r b) =<< cplxLog' sym x
  mkComplex sym z


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
