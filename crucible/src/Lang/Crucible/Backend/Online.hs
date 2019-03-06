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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Backend.Online
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
  , initialOnlineBackendState
  , checkSatisfiable
  , checkSatisfiableWithModel
  , getSolverProcess
  , getSolverProcess'
  , resetSolverProcess
  , UnsatFeatures(..)
  , unsatFeaturesToProblemFeatures
    -- ** Configuration options
  , solverInteractionFile
  , onlineBackendOptions
    -- ** Branch satisfiability
  , BranchResult(..)
  , considerSatisfiability
    -- ** Yices
  , YicesOnlineBackend
  , withYicesOnlineBackend
    -- ** Z3
  , Z3OnlineBackend
  , withZ3OnlineBackend
    -- ** CVC4
  , CVC4OnlineBackend
  , withCVC4OnlineBackend
    -- ** STP
  , STPOnlineBackend
  , withSTPOnlineBackend
    -- * OnlineBackendState
  , OnlineBackendState(..)
    -- * Re-exports
  , B.FloatInterpretation
  , B.FloatIEEE
  , B.FloatUninterpreted
  , B.FloatReal
  , B.Flags
  ) where


import           Control.Lens
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.IO.Class
import           Data.Bits
import           Data.Foldable
import           Data.IORef
import           Data.Parameterized.Nonce
import qualified Data.Text as Text
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config
import qualified What4.Expr.Builder as B
import           What4.Interface
import           What4.ProblemFeatures
import           What4.ProgramLoc
import           What4.Protocol.Online
import           What4.Protocol.SMTWriter as SMT
import           What4.Protocol.SMTLib2 as SMT2
import           What4.SatResult
import qualified What4.Solver.CVC4 as CVC4
import qualified What4.Solver.STP as STP
import qualified What4.Solver.Yices as Yices
import qualified What4.Solver.Z3 as Z3

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Simulator.SimError

data UnsatFeatures
  = NoUnsatFeatures
     -- ^ Do not compute unsat cores or assumptions
  | ProduceUnsatCores
     -- ^ Enable named assumptions and unsat-core computations
  | ProduceUnsatAssumptions
     -- ^ Enable check-with-assumptions commands and unsat-assumptions computations

unsatFeaturesToProblemFeatures :: UnsatFeatures -> ProblemFeatures
unsatFeaturesToProblemFeatures x =
  case x of
    NoUnsatFeatures -> noFeatures
    ProduceUnsatCores -> useUnsatCores
    ProduceUnsatAssumptions -> useUnsatAssumptions

solverInteractionFile :: ConfigOption BaseStringType
solverInteractionFile = configOption knownRepr "solverInteractionFile"

onlineBackendOptions :: [ConfigDesc]
onlineBackendOptions =
  [ mkOpt
      solverInteractionFile
      stringOptSty
      (Just (PP.text "File to echo solver commands and responses for debugging purposes"))
      Nothing
  ]


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
--
--   n.b. the explicit forall allows the fs to be expressed as the
--   first argument so that it can be dictated easily by type
--   application from the caller. Example:
--
--   > withYicesOnlineBackend @(Flags FloatReal) ng f'
withYicesOnlineBackend :: forall fs scope m a . (MonadIO m, MonadMask m) =>
                          NonceGenerator IO scope
                       -> UnsatFeatures
                       -> (YicesOnlineBackend scope fs -> m a)
                       -> m a
withYicesOnlineBackend gen unsatFeat action =
  let feat = Yices.yicesDefaultFeatures .|. unsatFeaturesToProblemFeatures unsatFeat in
  withOnlineBackend gen feat $ \sym ->
    do liftIO $ extendConfig Yices.yicesOptions (getConfiguration sym)
       action sym

type Z3OnlineBackend scope fs = OnlineBackend scope (SMT2.Writer Z3.Z3) fs

-- | Do something with a Z3 online backend.
--   The backend is only valid in the continuation.
--
--   The Z3 configuration options will be automatically
--   installed into the backend configuration object.
--
--   n.b. the explicit forall allows the fs to be expressed as the
--   first argument so that it can be dictated easily by type
--   application from the caller. Example:
--
--   > withz3OnlineBackend @(Flags FloatReal) ng f'
withZ3OnlineBackend :: forall fs scope m a . (MonadIO m, MonadMask m) =>
                       NonceGenerator IO scope
                    -> UnsatFeatures
                    -> (Z3OnlineBackend scope fs -> m a)
                    -> m a
withZ3OnlineBackend gen unsatFeat action =
  let feat = (SMT2.defaultFeatures Z3.Z3 .|. unsatFeaturesToProblemFeatures unsatFeat) in
  withOnlineBackend gen feat $ \sym ->
    do liftIO $ extendConfig Z3.z3Options (getConfiguration sym)
       action sym

type CVC4OnlineBackend scope fs = OnlineBackend scope (SMT2.Writer CVC4.CVC4) fs

-- | Do something with a CVC4 online backend.
--   The backend is only valid in the continuation.
--
--   The CVC4 configuration options will be automatically
--   installed into the backend configuration object.
--
--   n.b. the explicit forall allows the fs to be expressed as the
--   first argument so that it can be dictated easily by type
--   application from the caller. Example:
--
--   > withCVC4OnlineBackend @(Flags FloatReal) ng f'
withCVC4OnlineBackend :: forall fs scope m a . (MonadIO m, MonadMask m) =>
                         NonceGenerator IO scope
                      -> UnsatFeatures
                      -> (CVC4OnlineBackend scope fs -> m a)
                      -> m a
withCVC4OnlineBackend gen unsatFeat action =
  let feat = (SMT2.defaultFeatures CVC4.CVC4 .|. unsatFeaturesToProblemFeatures unsatFeat) in
  withOnlineBackend gen feat $ \sym -> do
    liftIO $ extendConfig CVC4.cvc4Options (getConfiguration sym)
    action sym

type STPOnlineBackend scope fs = OnlineBackend scope (SMT2.Writer STP.STP) fs

-- | Do something with a STP online backend.
--   The backend is only valid in the continuation.
--
--   The STO configuration options will be automatically
--   installed into the backend configuration object.
--
--   n.b. the explicit forall allows the fs to be expressed as the
--   first argument so that it can be dictated easily by type
--   application from the caller.  Example:
--
--   > withSTPOnlineBackend @(Flags FloatReal) ng f'
withSTPOnlineBackend :: forall fs scope m a . (MonadIO m, MonadMask m) =>
                        NonceGenerator IO scope
                     -> (STPOnlineBackend scope fs -> m a)
                     -> m a
withSTPOnlineBackend gen action =
  withOnlineBackend gen (SMT2.defaultFeatures STP.STP) $ \sym -> do
    liftIO $ extendConfig STP.stpOptions (getConfiguration sym)
    action sym

------------------------------------------------------------------------
-- OnlineBackendState: implementation details.

-- | Is the solver running or not?
data SolverState scope solver =
    SolverNotStarted
  | SolverStarted (SolverProcess scope solver) (Maybe Handle)

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackendState solver scope = OnlineBackendState
  { assumptionStack ::
      !(AssumptionStack (B.BoolExpr scope) AssumptionReason SimError)
      -- ^ Number of times we have pushed
  , solverProc :: !(IORef (SolverState scope solver))
    -- ^ The solver process, if any.
  , currentFeatures :: !(IORef ProblemFeatures)
  }

-- | Returns an initial execution state.
initialOnlineBackendState ::
  NonceGenerator IO scope ->
  ProblemFeatures ->
  IO (OnlineBackendState solver scope)
initialOnlineBackendState gen feats =
  do stk <- initAssumptionStack gen
     procref <- newIORef SolverNotStarted
     featref <- newIORef feats
     return $! OnlineBackendState
                 { assumptionStack = stk
                 , solverProc = procref
                 , currentFeatures = featref
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
       SolverStarted p auxh ->
         do _ <- shutdownSolverProcess p
            maybe (return ()) hClose auxh
            writeIORef (solverProc st) SolverNotStarted

-- | Get the solver process.
--   Starts the solver, if that hasn't happened already.
getSolverProcess' ::
  OnlineSolver scope solver =>
  (B.ExprBuilder scope s fs -> IO (OnlineBackendState solver scope)) ->
  B.ExprBuilder scope s fs ->
  IO (SolverProcess scope solver)
getSolverProcess' getSolver sym = do
  st <- getSolver sym
  mproc <- readIORef (solverProc st)
  auxOutSetting <- getOptionSetting solverInteractionFile (getConfiguration sym)
  case mproc of
    SolverStarted p _ -> return p
    SolverNotStarted ->
      do feats <- readIORef (currentFeatures st)
         auxh <-
           getMaybeOpt auxOutSetting >>= \case
             Nothing -> return Nothing
             Just fn
               | Text.null fn -> return Nothing
               | otherwise    -> Just <$> openFile (Text.unpack fn) WriteMode
         p <- startSolverProcess feats auxh sym
         push p
         writeIORef (solverProc st) (SolverStarted p auxh)
         return p

-- | Get the solver process, specialized to @OnlineBackend@.
getSolverProcess ::
  OnlineSolver scope solver =>
  OnlineBackend scope solver fs ->
  IO (SolverProcess scope solver)
getSolverProcess = getSolverProcess' (\sym -> readIORef (B.sbStateManager sym))

-- | Result of attempting to branch on a predicate.
data BranchResult
     -- | The both branches of the predicate might be satisfiable
     --   (although satisfiablility of either branch is not guaranteed).
   = IndeterminateBranchResult

     -- | Commit to the branch where the given predicate is equal to
     --   the returned boolean.  The opposite branch is unsatisfiable
     --   (although the given branch is not necessarily satisfiable).
   | NoBranch !Bool

     -- | The context before considering the given predicate was already
     --   unsatisfiable.
   | UnsatisfiableContext



considerSatisfiability ::
  (OnlineSolver scope solver) =>
  OnlineBackend scope solver fs ->
  Maybe ProgramLoc ->
  B.BoolExpr scope ->
  IO BranchResult
considerSatisfiability sym mbPloc p =
  do proc <- getSolverProcess sym
     pnot <- notPred sym p
     let locDesc = case mbPloc of
           Just ploc -> show (plSourceLoc ploc)
           Nothing -> "(unknown location)"
     let rsn = "branch sat: " ++ locDesc
     p_res <- checkSatisfiable proc rsn p
     pnot_res <- checkSatisfiable proc rsn pnot
     case (p_res, pnot_res) of
       (Unsat{}, Unsat{}) -> return UnsatisfiableContext
       (_      , Unsat{}) -> return (NoBranch True)
       (Unsat{}, _      ) -> return (NoBranch False)
       _                  -> return IndeterminateBranchResult

-- | Do something with an online backend.
--   The backend is only valid in the continuation.
--
--   Configuration options are not automatically installed
--   by this operation.
withOnlineBackend ::
  (OnlineSolver scope solver, MonadIO m, MonadMask m) =>
  NonceGenerator IO scope ->
  ProblemFeatures ->
  (OnlineBackend scope solver fs -> m a) ->
  m a
withOnlineBackend gen feats action = do
  st  <- liftIO $ initialOnlineBackendState gen feats
  sym <- liftIO $ B.newExprBuilder st gen
  liftIO $ extendConfig onlineBackendOptions (getConfiguration sym)
  liftIO $ writeIORef (B.sbStateManager sym) st

  action sym
    `finally`
    (liftIO $ readIORef (solverProc st) >>= \case
        SolverNotStarted {} -> return ()
        SolverStarted p auxh ->
         do _ <- shutdownSolverProcess p
            maybe (return ()) hClose auxh
    )


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
       ps <- AS.collectAssumptions stk
       andAllOf sym (folded.labeledPred) ps

  collectAssumptions sym =
    AS.collectAssumptions =<< getAssumptionStack sym

  pushAssumptionFrame sym =
    do proc <- getSolverProcess sym
       stk  <- getAssumptionStack sym
       push proc
       pushFrame stk

  popAssumptionFrame sym ident =
    do proc <- getSolverProcess sym
       stk <- getAssumptionStack sym
       frm <- popFrame ident stk
       pop proc
       return frm

  popUntilAssumptionFrame sym ident =
    do proc <- getSolverProcess sym
       stk <- getAssumptionStack sym
       n <- AS.popFramesUntil ident stk
       forM_ [0..(n-1)] $ \_ -> pop proc

  popAssumptionFrameAndObligations sym ident = do
    do proc <- getSolverProcess sym
       stk <- getAssumptionStack sym
       frmAndGls <- popFrameAndGoals ident stk
       pop proc
       return frmAndGls

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
    do proc <- getSolverProcess sym
       stk  <- getAssumptionStack sym

       -- restore the previous assumption stack
       AS.restoreAssumptionStack gc stk

       -- Retrieve the assumptions from the state to restore
       AssumptionFrames base frms <- AS.allAssumptionFrames stk

       -- reset the solver state
       reset proc
       -- assume the base-level assumptions
       mapM_ (SMT.assume (solverConn proc) . view labeledPred) (toList base)
       -- populate the pushed frames
       forM_ (map snd $ toList frms) $ \frm ->
         do push proc
            mapM_ (SMT.assume (solverConn proc) . view labeledPred) (toList frm)
