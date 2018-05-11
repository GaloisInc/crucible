------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Backend.Simple
-- Description : The "simple" solver backend
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- An "offline" backend for communicating with solvers.  This backend
-- does not maintain a persistent connection to a solver, and does
-- not perform satisfiability checks at symbolic branch points.
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Backend.Simple
  ( -- * SimpleBackend
    SimpleBackend
  , newSimpleBackend
    -- * SimpleBackendState
  , SimpleBackendState
  ) where

import           Control.Exception ( throwIO )
import           Control.Lens
import           Data.IORef
import           Data.Parameterized.Nonce

import           What4.AssumptionStack as AS
import           What4.Interface
import qualified What4.Expr.Builder as B

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

type SimpleBackend t = B.ExprBuilder t SimpleBackendState

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

newtype SimpleBackendState t
      = SimpleBackendState { sbAssumptionStack :: AssumptionStack (B.BoolExpr t) AssumptionReason SimError }

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> IO (SimpleBackendState t)
initialSimpleBackendState gen = SimpleBackendState <$> initAssumptionStack gen

newSimpleBackend :: NonceGenerator IO t
                 -> IO (SimpleBackend t)
newSimpleBackend gen =
  do st <- initialSimpleBackendState gen
     B.newExprBuilder st gen

getAssumptionStack :: SimpleBackend t -> IO (AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SimpleBackend t) where
  evalBranch _sym p =
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing    -> return $! SymbolicBranch True

  addAssertion sym a =
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> throwIO (a^.labeledPredMsg)
      _ ->
        do stk <- getAssumptionStack sym
           AS.assert a stk

  addAssumption sym a =
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> addFailedAssertion sym InfeasibleBranchError
      _ ->
        do stk <- getAssumptionStack sym
           AS.assume a stk

  addFailedAssertion sym msg = do
    loc <- getCurrentProgramLoc sym
    throwIO (SimError loc msg)

  addAssumptions sym ps = do
    stk <- getAssumptionStack sym
    appendAssumptions ps stk

  getPathCondition sym = do
    stk <- getAssumptionStack sym
    ps <- collectAssumptions stk
    andAllOf sym (folded.labeledPred) ps

  getProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  setProofObligations sym obligs = do
    stk <- getAssumptionStack sym
    AS.setProofObligations obligs stk

  pushAssumptionFrame sym = do
    stk <- getAssumptionStack sym
    pushFrame stk

  popAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    frm <- popFrame ident stk
    readIORef (assumeFrameCond frm)

  cloneAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.cloneAssumptionStack stk

  restoreAssumptionState sym stk = do
    writeIORef (B.sbStateManager sym) (SimpleBackendState stk)
