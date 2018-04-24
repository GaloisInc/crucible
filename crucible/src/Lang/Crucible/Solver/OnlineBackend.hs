------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.OnlineBackend
-- Description : A solver backend that maintains a persistent connection
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- The online backend maintains an open connection to an SMT solver
-- (Yices, currently) that is used to prune unsatisfiable execution
-- traces during simulation.  At every symbolic branch point, the SMT
-- solver is queried to determine if one or both symbolic branches are
-- unsatisfiable.  Only branches with satisfiable branch conditions
-- are explored.
--
-- The online backend also allows override definitions access to a
-- persistent SMT solver connection.  This can be useful for some
-- kinds of algorithms that benefit from quickly performing many
-- small solver queries in a tight interaction loop.
------------------------------------------------------------------------

{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.Solver.OnlineBackend
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
    -- * OnlineBackendState
  , OnlineBackendState
  , getYicesProcess
  , Yices.YicesProcess(..)
  , yicesOnlineAdapter
  ) where

import           Control.Exception ( SomeException, throwIO, try )
import           Control.Lens
import           Data.Bits
import           Data.Foldable
import           Data.IORef
import           Data.Parameterized.Nonce
import           System.Exit
import           System.IO
import           System.Process

import qualified Lang.Crucible.Config as CFG
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.AssumptionStack as AS
import           Lang.Crucible.Solver.BoolInterface
import           Lang.Crucible.Solver.Interface
import qualified Lang.Crucible.Solver.ProcessUtils as Proc
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import           Lang.Crucible.Solver.SimpleBackend.SMTWriter
  ( assumeFormula
  , mkFormula
  )
import qualified Lang.Crucible.Solver.SimpleBackend.Yices as Yices
import qualified Lang.Crucible.Solver.SimpleBuilder as SB

type OnlineBackend t = SB.SimpleBuilder t OnlineBackendState

yicesOnlineAdapter :: SolverAdapter OnlineBackendState
yicesOnlineAdapter =
   Yices.yicesAdapter
   { solver_adapter_check_sat = \sym _ p cont -> do
        yproc <- getYicesProcess sym
        let c = Yices.yicesConn yproc

        -- build the formula outside the frame to
        -- preserve intermediate cache results
        p_smtformula <- mkFormula c p

        Yices.inFreshFrame c $ do
          assumeFormula c p_smtformula
          res <- Yices.checkAndGetModel yproc
          cont (fmap (\x -> (x, Nothing)) res)
   }

------------------------------------------------------------------------
-- OnlineBackendState

data YicesOnline

startYicesProcess :: CFG.Config -> IO (Yices.YicesProcess t s)
startYicesProcess cfg = do
  yices_path <- Proc.findSolverPath Yices.yicesPath cfg
  let args = ["--mode=push-pop"]

  let create_proc
        = (proc yices_path args)
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          , cwd = Nothing
          }

  let startProcess = do
        x <- createProcess create_proc
        case x of
          (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
          _ -> fail "Internal error in startYicesProcess: Failed to create handle."

  (in_h,out_h,err_h,ph) <- startProcess

  --void $ forkIO $ logErrorStream err_stream (logLn 2)
  -- Create new connection for sending commands to yices.
  let features = useLinearArithmetic
             .|. useBitvectors
             .|. useSymbolicArrays
             .|. useComplexArithmetic
             .|. useStructs
  conn <- Yices.newConnection in_h features SB.emptySymbolVarBimap
  Yices.setYicesParams conn cfg
  err_reader <- Yices.startHandleReader err_h
  return $! Yices.YicesProcess { Yices.yicesConn   = conn
                               , Yices.yicesStdin  = in_h
                               , Yices.yicesStdout = out_h
                               , Yices.yicesStderr = err_reader
                               , Yices.yicesHandle = ph
                               }

shutdownYicesProcess :: Yices.YicesProcess t s -> IO ()
shutdownYicesProcess yices = do
  -- Close input stream.
  hClose (Yices.yicesStdin yices)
  -- Log outstream as error messages.

  --logLn 2 "Waiting for yices to terminate"
  ec <- waitForProcess (Yices.yicesHandle yices)
  case ec of
    ExitSuccess -> return () --logLn 2 "Yices terminated."
    ExitFailure x ->
       fail $ "yices exited with unexpected code: "++show x

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackendState t
   = OnlineBackendState { assumptionStack :: !(AssumptionStack (SB.BoolElt t) t SimErrorReason)
                          -- ^ Number of times we have pushed
                        , yicesProc    :: !(IORef (Maybe (Yices.YicesProcess t YicesOnline)))
                        }

-- | Returns an initial execution state.
initialOnlineBackendState :: NonceGenerator IO t -> IO (OnlineBackendState t)
initialOnlineBackendState gen = do
  stk <- initAssumptionStack gen
  procref <- newIORef Nothing
  return $! OnlineBackendState
              { assumptionStack = stk
              , yicesProc = procref
              }

getAssumptionStack :: OnlineBackend t -> IO (AssumptionStack (SB.BoolElt t) t SimErrorReason)
getAssumptionStack sym = assumptionStack <$> readIORef (SB.sbStateManager sym)

getYicesProcess :: OnlineBackend t -> IO (Yices.YicesProcess t YicesOnline)
getYicesProcess sym = do
  st <- readIORef (SB.sbStateManager sym)
  mproc <- readIORef (yicesProc st)
  case mproc of
    Just p -> do
      return p
    Nothing -> do
      let cfg = getConfiguration sym
      p <- startYicesProcess cfg
      -- set up Yices parameters
      Yices.setYicesParams (Yices.yicesConn p) cfg
      writeIORef (yicesProc st) (Just p)
      return p

withOnlineBackend :: NonceGenerator IO t
                  -> (OnlineBackend t -> IO a)
                  -> IO a
withOnlineBackend gen action = do
  st <- initialOnlineBackendState gen
  sym <- SB.newSimpleBuilder st gen
  r <- try $ action sym
  mp <- readIORef (yicesProc st)
  case mp of
   Nothing -> return ()
   Just p -> shutdownYicesProcess p
  case r of
   Left e -> throwIO (e :: SomeException)
   Right x -> return x

checkSatisfiable
    :: OnlineBackend t
    -> SB.BoolElt t
    -> IO (SatResult ())
checkSatisfiable sym p = do
   yproc <- getYicesProcess sym
   let c = Yices.yicesConn yproc

   p_smtexpr <- mkFormula c p
   Yices.inFreshFrame c $ do
     assumeFormula c p_smtexpr
     Yices.check yproc

instance SB.IsSimpleBuilderState OnlineBackendState where
  sbAddAssertion sym p m = do
    loc <- SB.curProgramLoc sym
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    -- Record assertion
    assert (Assertion loc p (Just m)) stk
    -- Send assertion to yices
    Yices.assume conn p

  sbAddAssumption sym p = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    -- Record assumption
    assume p stk
    -- Send assertion to yices
    Yices.assume conn p

  sbAddAssumptions sym a = do
    -- Tell Yices of assertions
    conn <- Yices.yicesConn <$> getYicesProcess sym
    mapM_ (Yices.assume conn) (toList a)
    -- Add assertions to list
    stk <- getAssumptionStack sym
    appendAssumptions a stk

  sbAllAssumptions sym = do
    stk <- getAssumptionStack sym
    ps <- collectAssumptions stk
    andAllOf sym folded ps

  sbEvalBranch sym p = do
    notP <- notPred sym p

    p_res    <- checkSatisfiable sym p
    notp_res <- checkSatisfiable sym notP
    case (p_res, notp_res) of
      (Unsat, Unsat) -> return InfeasibleBranch
      (Unsat, _ )    -> return $ NoBranch False
      (_    , Unsat) -> return $ NoBranch True
      (_    , _)     -> return $ SymbolicBranch True

  sbPushAssumptionFrame sym = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    Yices.push conn
    pushFrame stk

  sbPopAssumptionFrame sym ident = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    frm <- popFrame ident stk
    ps <- readIORef (assumeFrameCond frm)
    Yices.pop conn
    return ps

  sbGetProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  sbSetProofObligations sym obligs = do
    stk <- getAssumptionStack sym
    AS.setProofObligations obligs stk
