------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Backend.Online
-- Description : A solver backend that maintains a persistent connection
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- The online backend maintains an open connection to an SMT solver
-- that is used to prune unsatisfiable execution traces during simulation.
-- At every symbolic branch point, the SMT solver is queried to determine
-- if one or both symbolic branches are unsatisfiable.
-- Only branches with satisfiable branch conditions are explored.
--
-- The online backend also allows override definitions access to a
-- persistent SMT solver connection.  This can be useful for some
-- kinds of algorithms that benefit from quickly performing many
-- small solver queries in a tight interaction loop.
------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Lang.Crucible.Backend.Online
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
  , checkSatisfiable
  , checkSatisfiableWithModel
  , getSolverProcess
  , resetSolverProcess
    -- ** Yices
  , YicesOnlineBackend
  , withYicesOnlineBackend
    -- ** Z3
  , Z3OnlineBackend
  , withZ3OnlineBackend
    -- * OnlineBackendState
  , OnlineBackendState
    -- * Re-exports
  , B.FloatInterpretation
  , B.FloatIEEE
  , B.FloatUninterpreted
  , B.FloatReal
  , B.Flags
  ) where


import           Control.Exception
                    ( SomeException(..), throwIO, try )
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.IORef
import           Data.Parameterized.Nonce

import           What4.Config
import qualified What4.Expr.Builder as B
import           What4.Interface
import           What4.SatResult
import           What4.Protocol.Online
import           What4.Protocol.SMTWriter as SMT
import           What4.Protocol.SMTLib2 as SMT2
import qualified What4.Solver.Yices as Yices
import qualified What4.Solver.Z3 as Z3

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Simulator.SimError


-- | Get the connection for sending commands to the solver.
getSolverConn ::
  OnlineSolver scope solver =>
  OnlineBackend scope solver fs -> IO (WriterConn scope solver)
getSolverConn sym = solverConn <$> getSolverProcess sym

--------------------------------------------------------------------------------
type OnlineBackend scope solver fs =
                        B.ExprBuilder scope (OnlineBackendState solver) fs


type YicesOnlineBackend scope fs = OnlineBackend scope (Yices.Connection scope) fs

-- | Do something with a Yices online backend.
--   The backend is only valid in the continuation.
--
--   The Yices configuration options will be automatically
--   installed into the backend configuration object.
withYicesOnlineBackend ::
  NonceGenerator IO scope ->
  (YicesOnlineBackend scope fs -> IO a) ->
  IO a
withYicesOnlineBackend gen action =
  withOnlineBackend gen $ \sym ->
    do extendConfig Yices.yicesOptions (getConfiguration sym)
       action sym

type Z3OnlineBackend scope fs = OnlineBackend scope (SMT2.Writer Z3.Z3) fs

-- | Do something with a Z3 online backend.
--   The backend is only valid in the continuation.
--
--   The Z3 configuration options will be automatically
--   installed into the backend configuration object.
withZ3OnlineBackend ::
  NonceGenerator IO scope ->
  (Z3OnlineBackend scope fs -> IO a) ->
  IO a
withZ3OnlineBackend gen action =
  withOnlineBackend gen $ \sym ->
    do extendConfig Z3.z3Options (getConfiguration sym)
       action sym

------------------------------------------------------------------------
-- OnlineBackendState: implementation details.

-- | Is the solver running or not?
data SolverState scope solver =
    SolverNotStarted
  | SolverStarted (SolverProcess scope solver)

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackendState solver scope = OnlineBackendState
  { assumptionStack ::
      !(AssumptionStack (B.BoolExpr scope) AssumptionReason SimError)
      -- ^ Number of times we have pushed
  , solverProc :: !(IORef (SolverState scope solver))
    -- ^ The solver process, if any.
  }

-- | Returns an initial execution state.
initialOnlineBackendState ::
  NonceGenerator IO scope ->
  IO (OnlineBackendState solver scope)
initialOnlineBackendState gen =
  do stk <- initAssumptionStack gen
     procref <- newIORef SolverNotStarted
     return $! OnlineBackendState
                 { assumptionStack = stk
                 , solverProc = procref
                 }

getAssumptionStack ::
  OnlineBackend scope solver fs ->
  IO (AssumptionStack (B.BoolExpr scope) AssumptionReason SimError)
getAssumptionStack sym = assumptionStack <$> readIORef (B.sbStateManager sym)


-- | Shutdown any currently-active solver process.
--   A fresh solver process will be started on the
--   next call to `getSolverProcess`.
resetSolverProcess ::
  OnlineSolver scope solver =>
  OnlineBackend scope solver fs ->
  IO ()
resetSolverProcess sym = do
  do st <- readIORef (B.sbStateManager sym)
     mproc <- readIORef (solverProc st)
     case mproc of
       -- Nothing to do
       SolverNotStarted -> return ()
       SolverStarted p ->
         do shutdownSolverProcess p
            writeIORef (solverProc st) SolverNotStarted

-- | Get the solver process.
--   Starts the solver, if that hasn't happened already.
getSolverProcess ::
  OnlineSolver scope solver =>
  OnlineBackend scope solver fs ->
  IO (SolverProcess scope solver)
getSolverProcess sym = do
  st <- readIORef (B.sbStateManager sym)
  mproc <- readIORef (solverProc st)
  case mproc of
    SolverStarted p -> return p
    SolverNotStarted ->
      do p <- startSolverProcess sym
         push (solverConn p)
         writeIORef (solverProc st) (SolverStarted p)
         return p

-- | Do something with an online backend.
--   The backend is only valid in the continuation.
--
--   Configuration options are not automatically installed
--   by this operation.
withOnlineBackend ::
  OnlineSolver scope solver =>
  NonceGenerator IO scope ->
  (OnlineBackend scope solver fs -> IO a) ->
  IO a
withOnlineBackend gen action = do
  st  <- initialOnlineBackendState gen
  sym <- B.newExprBuilder st gen
  r   <- try (action sym)
  mp  <- readIORef (solverProc st)
  case mp of
    SolverNotStarted {} -> return ()
    SolverStarted p     -> shutdownSolverProcess p
  case r of
   Left e  -> throwIO (e :: SomeException)
   Right x -> return x


instance OnlineSolver scope solver => IsBoolSolver (OnlineBackend scope solver fs) where
  addProofObligation sym a =
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      _ -> AS.addProofObligation a =<< getAssumptionStack sym

  addAssumption sym a =
    let cond = asConstantPred (a^.labeledPred)
    in case cond of
         Just False -> abortExecBecause (AssumedFalse (a^.labeledPredMsg))
         _ -> do stk  <- getAssumptionStack sym
                 -- Record assumption, even if trivial.
                 -- This allows us to keep track of the full path we are on.
                 AS.assume a stk

                 -- Send assertion to the solver, unless it is trivial.
                 case cond of
                   Just True -> return ()
                   _ -> do conn <- getSolverConn sym
                           SMT.assume conn (a^.labeledPred)


  addAssumptions sym a =
    do -- Tell the solver of assertions
       conn <- getSolverConn sym
       mapM_ (SMT.assume conn . view labeledPred) (toList a)
       -- Add assertions to list
       stk <- getAssumptionStack sym
       appendAssumptions a stk

  getPathCondition sym =
    do stk <- getAssumptionStack sym
       ps <- collectAssumptions stk
       andAllOf sym (folded.labeledPred) ps

  evalBranch sym p =
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing ->
        do proc     <- getSolverProcess sym
           notP     <- notPred sym p
           p_res    <- checkSatisfiable proc p
           notp_res <- checkSatisfiable proc notP
           case (p_res, notp_res) of
             (Unsat, Unsat) -> abortExecBecause InfeasibleBranch
             (Unsat, _ )    -> return $ NoBranch False
             (_    , Unsat) -> return $ NoBranch True
             (_    , _)     -> return $ SymbolicBranch True

  pushAssumptionFrame sym =
    do conn <- getSolverConn sym
       stk  <- getAssumptionStack sym
       push conn
       pushFrame stk

  popAssumptionFrame sym ident =
    do conn <- getSolverConn sym
       stk <- getAssumptionStack sym
       frm <- popFrame ident stk
       pop conn
       return frm

  getProofObligations sym =
    do stk <- getAssumptionStack sym
       AS.getProofObligations stk

  clearProofObligations sym =
    do stk <- getAssumptionStack sym
       AS.clearProofObligations stk

  saveAssumptionState sym =
    do stk <- getAssumptionStack sym
       AS.saveAssumptionStack stk

  restoreAssumptionState sym gc =
    do conn <- getSolverConn sym
       stk  <- getAssumptionStack sym

       -- restore the previous assumption stack
       AS.restoreAssumptionStack gc stk

       -- Retrieve the assumptions from the state to restore
       (base, frms) <- AS.allAssumptionFrames stk

       -- reset the solver state
       reset conn
       -- assume the base-level assumptions
       mapM_ (SMT.assume conn . view labeledPred) (toList base)
       -- populate the pushed frames
       forM_ (map snd $ toList frms) $ \frm ->
         do push conn
            mapM_ (SMT.assume conn . view labeledPred) (toList frm)
