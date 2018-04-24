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
  ( FrameIdentifier
  , BranchResult(..)
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

type family FrameIdentifier (sym :: *) :: *

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
  pushAssumptionFrame :: sym -> IO (FrameIdentifier sym)

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.  Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrame :: sym -> FrameIdentifier sym -> IO (Seq (Pred sym))

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
