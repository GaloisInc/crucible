------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Backend.Online
-- Description : A solver backend that maintains a persistent connection
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Ryan Scott <rscott@galois.com>, Langston Barrett <langston@galois.com>
-- Stability   : provisional
--
-- A solver backend ('IsSymBackend') that maintains an open connection to an
-- SMT solver (in contrast to "Lang.Crucible.Backend.Simple").
--
-- The primary intended use-case is to prune unsatisfiable execution
-- traces during simulation using the execution feature provided by
-- "Lang.Crucible.Simulator.PathSatisfiability". That execution feature is
-- parameterized over a function argument that can be intantiated  with this
-- module's 'considerSatisfiability'.
--
-- The online backend also allows override definitions access to a persistent
-- SMT solver connection. This can be useful for some kinds of algorithms
-- that benefit from quickly performing many small solver queries in a tight
-- interaction loop.
--
-- The online backend is not currently used to dispatch proof obligations during
-- symbolic execution, see [GaloisInc/crucible#369, \"Interleave proof with
-- simulation\"](https://github.com/GaloisInc/crucible/issues/369).
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.Backend.Online
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
  , newOnlineBackend
  , checkSatisfiable
  , checkSatisfiableWithModel
  , withSolverProcess
  , resetSolverProcess
  , restoreSolverState
  , UnsatFeatures(..)
  , unsatFeaturesToProblemFeatures
    -- ** Configuration options
  , solverInteractionFile
  , enableOnlineBackend
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
    -- ** Bitwuzla
  , BitwuzlaOnlineBackend
  , withBitwuzlaOnlineBackend
    -- ** Boolector
  , BoolectorOnlineBackend
  , withBoolectorOnlineBackend
    -- ** CVC4
  , CVC4OnlineBackend
  , withCVC4OnlineBackend
    -- ** CVC5
  , CVC5OnlineBackend
  , withCVC5OnlineBackend
    -- ** STP
  , STPOnlineBackend
  , withSTPOnlineBackend
  ) where


import           Control.Lens ( (^.) )
import           Control.Monad
import           Control.Monad.Fix (mfix)
import           Control.Monad.Catch
import           Control.Monad.IO.Class
import           Data.Bits
import           Data.Data (Data)
import           Data.Foldable
import           Data.IORef
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           System.IO
import qualified Data.Text as Text
import qualified Prettyprinter as PP

import           What4.Config
import           What4.Concrete
import qualified What4.Expr.Builder as B
import           What4.Interface
import           What4.ProblemFeatures
import           What4.ProgramLoc
import           What4.Protocol.Online
import           What4.Protocol.SMTWriter as SMT
import           What4.Protocol.SMTLib2 as SMT2
import           What4.SatResult
import qualified What4.Solver.Bitwuzla as Bitwuzla
import qualified What4.Solver.Boolector as Boolector
import qualified What4.Solver.CVC4 as CVC4
import qualified What4.Solver.CVC5 as CVC5
import qualified What4.Solver.STP as STP
import qualified What4.Solver.Yices as Yices
import qualified What4.Solver.Z3 as Z3

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.AssumptionStack as AS
import qualified Lang.Crucible.Backend.ProofGoals as PG
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

solverInteractionFile :: ConfigOption (BaseStringType Unicode)
solverInteractionFile = configOption knownRepr "solverInteractionFile"

-- | Option for enabling online solver interactions.  Defaults to true.
--   If disabled, operations requiring solver connections will be skipped.
enableOnlineBackend :: ConfigOption BaseBoolType
enableOnlineBackend = configOption knownRepr "enableOnlineBackend"

onlineBackendOptions :: OnlineSolver solver => OnlineBackend solver scope st fs -> [ConfigDesc]
onlineBackendOptions bak =
  [ mkOpt
      solverInteractionFile
      stringOptSty
      (Just (PP.pretty "File to echo solver commands and responses for debugging purposes"))
      Nothing
  , let enableOnset _ (ConcreteBool val) =
          do when (not val) (resetSolverProcess bak)
             return optOK
     in mkOpt
          enableOnlineBackend
          boolOptSty{ opt_onset = enableOnset }
          (Just (PP.pretty "Enable online solver communications"))
          (Just (ConcreteBool True))
  ]

--------------------------------------------------------------------------------
-- OnlineBackend

-- | Is the solver running or not?
data SolverState scope solver =
    SolverNotStarted
  | SolverStarted (SolverProcess scope solver) (Maybe Handle)

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackend solver scope st fs = OnlineBackendState
  { assumptionStack ::
      !(AssumptionStack
          (CrucibleAssumptions (B.Expr scope))
          (LabeledPred (B.BoolExpr scope) SimError))

  , solverProc :: !(IORef (SolverState scope solver))
    -- ^ The solver process, if any.

  , currentFeatures :: !(IORef ProblemFeatures)

  , onlineEnabled :: IO Bool
    -- ^ action for checking if online features are currently enabled

  , onlineExprBuilder :: B.ExprBuilder scope st fs
  }

newOnlineBackend ::
  OnlineSolver solver =>
  B.ExprBuilder scope st fs ->
  ProblemFeatures ->
  IO (OnlineBackend solver scope st fs)
newOnlineBackend sym feats =
  do stk <- initAssumptionStack (sym ^. B.exprCounter)
     procref <- newIORef SolverNotStarted
     featref <- newIORef feats

     mfix $ \bak ->
       do tryExtendConfig
            (backendOptions ++ onlineBackendOptions bak)
            (getConfiguration sym)

          enableOpt <- getOptionSetting enableOnlineBackend (getConfiguration sym)

          return $ OnlineBackendState
                   { assumptionStack = stk
                   , solverProc = procref
                   , currentFeatures = featref
                   , onlineEnabled = getOpt enableOpt
                   , onlineExprBuilder = sym
                   }

-- | Do something with an online backend.
--   The backend is only valid in the continuation.
--
--   Solver specific configuration options are not automatically installed
--   by this operation.
withOnlineBackend ::
  (OnlineSolver solver, MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  ProblemFeatures ->
  (OnlineBackend solver scope st fs -> m a) ->
  m a
withOnlineBackend sym feats action = do
  bak <- liftIO (newOnlineBackend sym feats)
  action bak
    `finally`
    (liftIO $ readIORef (solverProc bak) >>= \case
        SolverNotStarted {} -> return ()
        SolverStarted p auxh ->
          ((void $ shutdownSolverProcess p) `onException` (killSolver p))
            `finally`
          (maybe (return ()) hClose auxh)
    )


type YicesOnlineBackend scope st fs = OnlineBackend Yices.Connection scope st fs

-- | Do something with a Yices online backend.
--   The backend is only valid in the continuation.
--
--   The Yices configuration options will be automatically
--   installed into the backend configuration object.
withYicesOnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  ProblemFeatures ->
  (YicesOnlineBackend scope st fs -> m a) ->
  m a
withYicesOnlineBackend sym unsatFeat extraFeatures action =
  let feat = Yices.yicesDefaultFeatures .|. unsatFeaturesToProblemFeatures unsatFeat  .|. extraFeatures in
  withOnlineBackend sym feat $ \bak ->
    do liftIO $ tryExtendConfig Yices.yicesOptions (getConfiguration sym)
       action bak

type Z3OnlineBackend scope st fs = OnlineBackend (SMT2.Writer Z3.Z3) scope st fs

-- | Do something with a Z3 online backend.
--   The backend is only valid in the continuation.
--
--   The Z3 configuration options will be automatically
--   installed into the backend configuration object.
withZ3OnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  ProblemFeatures ->
  (Z3OnlineBackend scope st fs -> m a) ->
  m a
withZ3OnlineBackend sym unsatFeat extraFeatures action =
  let feat = (SMT2.defaultFeatures Z3.Z3 .|. unsatFeaturesToProblemFeatures unsatFeat .|. extraFeatures) in
  withOnlineBackend sym feat $ \bak ->
    do liftIO $ tryExtendConfig Z3.z3Options (getConfiguration sym)
       action bak

type BitwuzlaOnlineBackend scope st fs = OnlineBackend (SMT2.Writer Bitwuzla.Bitwuzla) scope st fs

-- | Do something with a Bitwuzla online backend.
--   The backend is only valid in the continuation.
--
--   The Bitwuzla configuration options will be automatically
--   installed into the backend configuration object.
--
--   > withBitwuzlaOnineBackend FloatRealRepr ng f'
withBitwuzlaOnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  ProblemFeatures ->
  (BitwuzlaOnlineBackend scope st fs -> m a) ->
  m a
withBitwuzlaOnlineBackend sym unsatFeat extraFeatures action =
  let feat = (SMT2.defaultFeatures Bitwuzla.Bitwuzla .|. unsatFeaturesToProblemFeatures unsatFeat .|. extraFeatures) in
  withOnlineBackend sym feat $ \bak -> do
    liftIO $ tryExtendConfig Bitwuzla.bitwuzlaOptions (getConfiguration sym)
    action bak

type BoolectorOnlineBackend scope st fs = OnlineBackend (SMT2.Writer Boolector.Boolector) scope st fs

-- | Do something with a Boolector online backend.
--   The backend is only valid in the continuation.
--
--   The Boolector configuration options will be automatically
--   installed into the backend configuration object.
--
--   > withBoolectorOnineBackend FloatRealRepr ng f'
withBoolectorOnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  (BoolectorOnlineBackend scope st fs -> m a) ->
  m a
withBoolectorOnlineBackend sym unsatFeat action =
  let feat = (SMT2.defaultFeatures Boolector.Boolector .|. unsatFeaturesToProblemFeatures unsatFeat) in
  withOnlineBackend sym feat $ \bak -> do
    liftIO $ tryExtendConfig Boolector.boolectorOptions (getConfiguration sym)
    action bak

type CVC4OnlineBackend scope st fs = OnlineBackend (SMT2.Writer CVC4.CVC4) scope st fs

-- | Do something with a CVC4 online backend.
--   The backend is only valid in the continuation.
--
--   The CVC4 configuration options will be automatically
--   installed into the backend configuration object.
withCVC4OnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  ProblemFeatures ->
  (CVC4OnlineBackend scope st fs -> m a) ->
  m a
withCVC4OnlineBackend sym unsatFeat extraFeatures action =
  let feat = (SMT2.defaultFeatures CVC4.CVC4 .|. unsatFeaturesToProblemFeatures unsatFeat .|. extraFeatures) in
  withOnlineBackend sym feat $ \bak -> do
    liftIO $ tryExtendConfig CVC4.cvc4Options (getConfiguration sym)
    action bak

type CVC5OnlineBackend scope st fs = OnlineBackend (SMT2.Writer CVC5.CVC5) scope st fs

-- | Do something with a CVC5 online backend.
--   The backend is only valid in the continuation.
--
--   The CVC5 configuration options will be automatically
--   installed into the backend configuration object.
withCVC5OnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  UnsatFeatures ->
  ProblemFeatures ->
  (CVC5OnlineBackend scope st fs -> m a) ->
  m a
withCVC5OnlineBackend sym unsatFeat extraFeatures action =
  let feat = (SMT2.defaultFeatures CVC5.CVC5 .|. unsatFeaturesToProblemFeatures unsatFeat .|. extraFeatures) in
  withOnlineBackend sym feat $ \bak -> do
    liftIO $ tryExtendConfig CVC5.cvc5Options (getConfiguration sym)
    action bak

type STPOnlineBackend scope st fs = OnlineBackend (SMT2.Writer STP.STP) scope st fs

-- | Do something with a STP online backend.
--   The backend is only valid in the continuation.
--
--   The STO configuration options will be automatically
--   installed into the backend configuration object.
withSTPOnlineBackend ::
  (MonadIO m, MonadMask m) =>
  B.ExprBuilder scope st fs ->
  (STPOnlineBackend scope st fs -> m a) ->
  m a
withSTPOnlineBackend sym action =
  withOnlineBackend sym (SMT2.defaultFeatures STP.STP) $ \bak -> do
    liftIO $ tryExtendConfig STP.stpOptions (getConfiguration sym)
    action bak

-- | Shutdown any currently-active solver process.
--   A fresh solver process will be started on the
--   next call to `getSolverProcess`.
resetSolverProcess ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  IO ()
resetSolverProcess bak = do
  do mproc <- readIORef (solverProc bak)
     case mproc of
       -- Nothing to do
       SolverNotStarted -> return ()
       SolverStarted p auxh ->
         do _ <- shutdownSolverProcess p
            maybe (return ()) hClose auxh
            writeIORef (solverProc bak) SolverNotStarted


restoreSolverState ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  PG.GoalCollector (CrucibleAssumptions (B.Expr scope))
                   (LabeledPred (B.BoolExpr scope) SimError) ->
  IO ()
restoreSolverState bak gc =
  do mproc <- readIORef (solverProc bak)
     case mproc of
       -- Nothing to do, state will be restored next time we start the process
       SolverNotStarted -> return ()

       SolverStarted proc auxh ->
         (do -- reset the solver state
             reset proc
             -- restore the assumption structure
             restoreAssumptionFrames bak proc (PG.gcFrames gc))
           `onException`
          ((killSolver proc)
             `finally`
           (maybe (return ()) hClose auxh)
             `finally`
           (writeIORef (solverProc bak) SolverNotStarted))


-- | Get the solver process. Starts the solver, if that hasn't
--   happened already and apply the given action.
--   If the @enableOnlineBackend@ option is False, the action
--   is skipped instead, and the solver is not started.
withSolverProcess ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  IO a {- ^ Default value to return if online features are disabled -} ->
  (SolverProcess scope solver -> IO a) ->
  IO a
withSolverProcess bak def action = do
  let sym = onlineExprBuilder bak
  onlineEnabled bak >>= \case
    False -> def
    True ->
     do let stk = assumptionStack bak
        mproc <- readIORef (solverProc bak)
        auxOutSetting <- getOptionSetting solverInteractionFile (getConfiguration sym)
        (p, auxh) <-
             case mproc of
               SolverStarted p auxh -> return (p, auxh)
               SolverNotStarted ->
                 do feats <- readIORef (currentFeatures bak)
                    auxh <-
                      getMaybeOpt auxOutSetting >>= \case
                        Nothing -> return Nothing
                        Just fn
                          | Text.null fn -> return Nothing
                          | otherwise    -> Just <$> openFile (Text.unpack fn) WriteMode
                    p <- startSolverProcess feats auxh sym
                    -- set up the solver in the same assumption state as specified
                    -- by the current assumption stack
                    (do frms <- AS.allAssumptionFrames stk
                        restoreAssumptionFrames bak p frms
                      ) `onException`
                      (killSolver p `finally` maybe (return ()) hClose auxh)
                    writeIORef (solverProc bak) (SolverStarted p auxh)
                    return (p, auxh)

        case solverErrorBehavior p of
          ContinueOnError ->
            action p
          ImmediateExit ->
            onException
              (action p)
              ((killSolver p)
                `finally`
               (maybe (return ()) hClose auxh)
                `finally`
               (writeIORef (solverProc bak) SolverNotStarted))

-- | Get the connection for sending commands to the solver.
withSolverConn ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  (WriterConn scope solver -> IO ()) ->
  IO ()
withSolverConn bak k = withSolverProcess bak (pure ()) (k . solverConn)


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
   deriving (Data, Eq, Generic, Ord, Typeable)


restoreAssumptionFrames ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  SolverProcess scope solver ->
  AssumptionFrames (CrucibleAssumptions (B.Expr scope)) ->
  IO ()
restoreAssumptionFrames bak proc (AssumptionFrames base frms) =
  do let sym = onlineExprBuilder bak
     -- assume the base-level assumptions
     SMT.assume (solverConn proc) =<< assumptionsPred sym base

     -- populate the pushed frames
     forM_ (map snd $ toList frms) $ \frm ->
      do push proc
         SMT.assume (solverConn proc) =<< assumptionsPred sym frm

considerSatisfiability ::
  OnlineSolver solver =>
  OnlineBackend solver scope st fs ->
  Maybe ProgramLoc ->
  B.BoolExpr scope ->
  IO BranchResult
considerSatisfiability bak mbPloc p =
  let sym = onlineExprBuilder bak in
  withSolverProcess bak (pure IndeterminateBranchResult) $ \proc ->
   do pnot <- notPred sym p
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


instance HasSymInterface (B.ExprBuilder t st fs) (OnlineBackend solver t st fs) where
  backendGetSym = onlineExprBuilder

instance (IsSymInterface (B.ExprBuilder scope st fs), OnlineSolver solver) =>
  IsSymBackend (B.ExprBuilder scope st fs)
               (OnlineBackend solver scope st fs) where

  addDurableProofObligation bak a =
     AS.addProofObligation a (assumptionStack bak)

  addAssumption bak a =
    case impossibleAssumption a of
      Just rsn -> abortExecBecause rsn
      Nothing ->
        do -- Send assertion to the solver, unless it is trivial.
           let p = assumptionPred a
           unless (asConstantPred p == Just True) $
              withSolverConn bak $ \conn -> SMT.assume conn p

           -- Record assumption, even if trivial.
           -- This allows us to keep track of the full path we are on.
           AS.appendAssumptions (singleAssumption a) (assumptionStack bak)

  addAssumptions bak as =
    -- NB, don't add the assumption to the assumption stack unless
    -- the solver assumptions succeeded
    do let sym = backendGetSym bak
       p <- assumptionsPred sym as

       -- Tell the solver of assertions
       unless (asConstantPred p == Just True) $
         withSolverConn bak $ \conn -> SMT.assume conn p

       -- Add assertions to list
       appendAssumptions as (assumptionStack bak)

  collectAssumptions bak =
    AS.collectAssumptions (assumptionStack bak)

  pushAssumptionFrame bak =
    -- NB, don't push a frame in the assumption stack unless
    -- pushing to the solver succeeded
    do withSolverProcess bak (pure ()) push
       pushFrame (assumptionStack bak)

  popAssumptionFrame bak ident =
    -- NB, pop the frame whether or not the solver pop succeeds
    do frm <- popFrame ident (assumptionStack bak)
       withSolverProcess bak (pure ()) pop
       return frm

  popUntilAssumptionFrame bak ident =
    -- NB, pop the frames whether or not the solver pop succeeds
    do n <- AS.popFramesUntil ident (assumptionStack bak)
       withSolverProcess bak (pure ()) $ \proc ->
         forM_ [0..(n-1)] $ \_ -> pop proc

  popAssumptionFrameAndObligations bak ident = do
    -- NB, pop the frames whether or not the solver pop succeeds
    do frmAndGls <- popFrameAndGoals ident (assumptionStack bak)
       withSolverProcess bak (pure ()) pop
       return frmAndGls

  getProofObligations bak =
     AS.getProofObligations (assumptionStack bak)

  clearProofObligations bak =
     AS.clearProofObligations (assumptionStack bak)

  saveAssumptionState bak =
     AS.saveAssumptionStack (assumptionStack bak)

  restoreAssumptionState bak gc =
    do restoreSolverState bak gc
       -- restore the previous assumption stack
       AS.restoreAssumptionStack gc (assumptionStack bak)
