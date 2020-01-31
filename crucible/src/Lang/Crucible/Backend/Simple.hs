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
    -- * Re-exports
  , B.FloatMode
  , B.FloatModeRepr(..)
  , B.FloatIEEE
  , B.FloatUninterpreted
  , B.FloatReal
  , B.Flags
  ) where

import           Control.Lens
import           Control.Monad (void)
import           Data.IORef
import           Data.Parameterized.Nonce

import           What4.Interface
import qualified What4.Expr.Builder as B

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

type SimpleBackend = B.ExprBuilder SimpleBackendState

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

newtype SimpleBackendState t fs
      = SimpleBackendState { sbAssumptionStack :: AssumptionStack (B.BoolExpr t fs) AssumptionReason SimError }

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> IO (SimpleBackendState t fs)
initialSimpleBackendState gen = SimpleBackendState <$> AS.initAssumptionStack gen


newSimpleBackend ::
  B.FloatModeRepr fm
  -- ^ Float interpretation mode (i.e., how are floats translated for the solver).
  -> NonceGenerator IO t
  -> IO (SimpleBackend t (B.Flags fm))
newSimpleBackend floatMode gen =
  do st <- initialSimpleBackendState gen
     B.newExprBuilder floatMode st gen

getAssumptionStack :: SimpleBackend t fs -> IO (AssumptionStack (B.BoolExpr t fs) AssumptionReason SimError)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SimpleBackend t fs) where

  addDurableProofObligation sym a =
     AS.addProofObligation a =<< getAssumptionStack sym

  addAssumption sym a =
    case asConstantPred (a^.labeledPred) of
      Just False -> abortExecBecause (AssumedFalse (a ^. labeledPredMsg))
      _          -> AS.assume a =<< getAssumptionStack sym

  addAssumptions sym ps = do
    stk <- getAssumptionStack sym
    AS.appendAssumptions ps stk

  collectAssumptions sym =
    AS.collectAssumptions =<< getAssumptionStack sym

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
    AS.popFrame ident stk

  popAssumptionFrameAndObligations sym ident = do
    stk <- getAssumptionStack sym
    AS.popFrameAndGoals ident stk

  popUntilAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    void $ AS.popFramesUntil ident stk

  saveAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.saveAssumptionStack stk

  restoreAssumptionState sym newstk = do
    stk <- getAssumptionStack sym
    AS.restoreAssumptionStack newstk stk
