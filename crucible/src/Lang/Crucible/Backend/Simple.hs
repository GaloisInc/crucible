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
  , B.FloatInterpretation
  , B.FloatIEEE
  , B.FloatUninterpreted
  , B.FloatReal
  , B.Flags
  ) where

import           Control.Lens
import           Control.Monad (void)
import           Data.IORef
import           Data.Parameterized.Nonce

import qualified What4.Expr.Builder as B
import           What4.Interface
import           What4.ProgramLoc

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError

type SimpleBackend t fs = B.ExprBuilder t SimpleBackendState fs

------------------------------------------------------------------------
-- SimpleBackendState

-- | This represents the state of the backend along a given execution.
-- It contains the current assertion stack.

data SimpleBackendState t
      = SimpleBackendState { sbAssumptionStack :: AssumptionStack (B.BoolExpr t) AssumptionReason SimError
                           , sbCallStack :: [ProgramLoc] -- [oldest calls to->, next call to->, latest call]
                           }

-- | Returns an initial execution state.
initialSimpleBackendState :: NonceGenerator IO t -> IO (SimpleBackendState t)
initialSimpleBackendState gen = SimpleBackendState <$> AS.initAssumptionStack gen <*> return []


newSimpleBackend :: NonceGenerator IO t
                 -> IO (SimpleBackend t fs)
newSimpleBackend gen =
  do st <- initialSimpleBackendState gen
     B.newExprBuilder st gen

getAssumptionStack :: SimpleBackend t fs -> IO (AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
getAssumptionStack sym = sbAssumptionStack <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SimpleBackend t fs) where

  addProofObligation sym a =
    case asConstantPred (a^.labeledPred) of
      Just True -> return ()    -- no trivialities
      _         -> AS.addProofObligation a =<< getAssumptionStack sym

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
    astk <- AS.saveAssumptionStack stk
    calls <- getCallStack sym
    return (astk,calls)

  restoreAssumptionState sym (newstk,calls) = do
    stk <- getAssumptionStack sym
    AS.restoreAssumptionStack newstk stk
    modifyIORef' (B.sbStateManager sym) $ \s -> s { sbCallStack = calls }

  pushCallStack sym loc =
    modifyIORef' (B.sbStateManager sym) $ \s -> s { sbCallStack = sbCallStack s <> [ loc ] }

  popCallStack sym =
    modifyIORef' (B.sbStateManager sym) $ \s ->
    let cs  = sbCallStack s
        cs' = if null cs
              then error "Internal error: more pops than pushes to CallStack!"
              else init cs
    in s { sbCallStack = cs' }

  getCallStack sym =
    reverse . sbCallStack <$> readIORef (B.sbStateManager sym)
