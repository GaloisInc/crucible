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
  , getFloatMode
  ) where

import           Control.Lens
import           Control.Monad (void)
import           Data.IORef
import           Data.Parameterized.Nonce

import           What4.Config
import qualified What4.Expr.Builder as B
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.ProgramLoc

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

data SimpleBackendState t =
   SimpleBackendState
   { sbAssumptionStack :: !(AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
   , sbFloatMode :: !(FloatModeRepr (CrucibleFloatMode t))
   }

type SimpleBackend t fm = B.ExprBuilder (CrucibleBackend t fm) SimpleBackendState

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> FloatModeRepr fm -> IO (SimpleBackendState (CrucibleBackend t fm))
initialSimpleBackendState gen fm = SimpleBackendState <$> AS.initAssumptionStack gen <*> pure fm

newSimpleBackend ::
  NonceGenerator IO t ->
  FloatModeRepr fm ->  
  IO (SimpleBackend t fm)
newSimpleBackend gen fm =
  do st <- initialSimpleBackendState gen fm
     sym <- B.newExprBuilder st gen initializationLoc
     extendConfig backendOptions (getConfiguration sym)
     return sym

getAssumptionStack :: SimpleBackend t fm -> IO (AssumptionStack (B.BoolExpr (CrucibleBackend t fm)) AssumptionReason SimError)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SimpleBackend t fm) where
  getFloatMode sym = sbFloatMode <$> readIORef (B.sbStateManager sym)

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
