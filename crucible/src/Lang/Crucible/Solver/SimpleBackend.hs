------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SimpleBackend
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
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Solver.SimpleBackend
  ( -- * SimpleBackend
    SimpleBackend
  , newSimpleBackend
    -- * SimpleBackendState
  , SimpleBackendState
  ) where

import           Control.Lens
import           Data.IORef
import           Data.Parameterized.Nonce

import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.AssumptionStack as AS
import           Lang.Crucible.Solver.BoolInterface
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SimpleBuilder (BoolElt)
import qualified Lang.Crucible.Solver.SimpleBuilder as SB

type SimpleBackend t = SB.SimpleBuilder t SimpleBackendState

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

newtype SimpleBackendState t
      = SimpleBackendState { sbAssumptionStack :: AssumptionStack (BoolElt t) t SimErrorReason }

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> IO (SimpleBackendState t)
initialSimpleBackendState gen = SimpleBackendState <$> initAssumptionStack gen

newSimpleBackend :: NonceGenerator IO t
                 -> IO (SimpleBackend t)
newSimpleBackend gen =
  do st <- initialSimpleBackendState gen
     SB.newSimpleBuilder st gen

getAssumptionStack :: SimpleBackend t -> IO (AssumptionStack (BoolElt t) t SimErrorReason)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (SB.sbStateManager sym)

instance SB.IsSimpleBuilderState SimpleBackendState where
  sbAddAssertion sym e m = do
    loc <- SB.curProgramLoc sym
    stk <- getAssumptionStack sym
    assert (Assertion loc e (Just m)) stk

  sbAddAssumption sym e = do
    stk <- getAssumptionStack sym
    assume e stk

  sbAddAssumptions sym ps = do
    stk <- getAssumptionStack sym
    appendAssumptions ps stk

  sbAllAssumptions sym = do
    stk <- getAssumptionStack sym
    ps <- collectAssumptions stk
    andAllOf sym folded ps

  sbEvalBranch _ _ =
    return $! SymbolicBranch True

  sbGetProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  sbSetProofObligations sym obligs = do
    stk <- getAssumptionStack sym
    AS.setProofObligations obligs stk

  sbPushAssumptionFrame sym = do
    stk <- getAssumptionStack sym
    pushFrame stk

  sbPopAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    frm <- popFrame ident stk
    readIORef (assumeFrameCond frm)
