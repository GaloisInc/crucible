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

import           Control.Lens
import           Data.IORef
import           Data.Parameterized.Nonce

import           What4.Interface
import qualified What4.Expr.Builder as B

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

type SimpleBackend t fs = B.ExprBuilder t SimpleBackendState fs

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

newtype SimpleBackendState t
      = SimpleBackendState { sbAssumptionStack :: AssumptionStack (B.BoolExpr t) AssumptionReason SimError }

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> IO (SimpleBackendState t)
initialSimpleBackendState gen = SimpleBackendState <$> AS.initAssumptionStack gen


newSimpleBackend :: NonceGenerator IO t
                 -> IO (SimpleBackend t fs)
newSimpleBackend gen =
  do st <- initialSimpleBackendState gen
     B.newExprBuilder st gen

getAssumptionStack :: SimpleBackend t fs -> IO (AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SimpleBackend t fs) where
  evalBranch _sym p =
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing    -> return $! SymbolicBranch True

  addProofObligation sym a =
    case asConstantPred (a^.labeledPred) of
      Just True -> return ()    -- no trivialities
      _         -> AS.addProofObligation a =<< getAssumptionStack sym

  addAssumption sym a =
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> abortExecBecause (AssumedFalse (a ^. labeledPredMsg))
      _          -> AS.assume a =<< getAssumptionStack sym

  addAssumptions sym ps = do
    stk <- getAssumptionStack sym
    AS.appendAssumptions ps stk

  getPathCondition sym = do
    stk <- getAssumptionStack sym
    ps <- AS.collectAssumptions stk
    andAllOf sym (folded.labeledPred) ps

  getProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  clearProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.clearProofObligations stk

  pushAssumptionFrame sym = do
    stk <- getAssumptionStack sym
    AS.pushFrame stk

  popAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    frm <- AS.popFrame ident stk
    readIORef (AS.assumeFrameCond frm)

  cloneAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.cloneAssumptionStack stk

  restoreAssumptionState sym stk = do
    writeIORef (B.sbStateManager sym) (SimpleBackendState stk)
