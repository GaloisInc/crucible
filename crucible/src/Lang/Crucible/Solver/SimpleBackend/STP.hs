------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SimpleBackend.STP
-- Description : Solver adapter code for STP
-- Copyright   : (c) Galois, Inc 2015
-- Maintainer  : Joe Hendrix <rdockins@galois.com>
-- Stability   : provisional
--
-- STP-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
module Lang.Crucible.Solver.SimpleBackend.STP
  ( STP
  , stpAdapter
  ) where

import           Control.Concurrent
import           System.Exit
import qualified System.IO.Streams as Streams
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.Config
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.ProcessUtils
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.GroundEval
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import qualified Lang.Crucible.Solver.SimpleBackend.SMTLib2 as SMT2
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.Streams

data STP = STP

-- | Path to stp
stpPath :: ConfigOption FilePath
stpPath = configOption "stp.path"

stpRandomSeed :: ConfigOption Int
stpRandomSeed = configOption "stp.random-seed"

intWithRangeOpt :: Monad m => ConfigOption Int -> Int -> Int -> ConfigDesc m
intWithRangeOpt nm lo hi = mkOpt nm Nothing sty PP.empty
  where sty = integralWithRangeOptSty (Inclusive lo) (Inclusive hi)

stpOptions :: MonadVerbosity m => [ConfigDesc m]
stpOptions =
  [ mkOpt stpPath (Just "stp")
          executablePathOptSty
          "Path to STP executable."
  , intWithRangeOpt stpRandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
  ]

stpAdapter :: SolverAdapter st
stpAdapter =
  SolverAdapter
  { solver_adapter_name = "stp"
  , solver_adapter_config_options = stpOptions
  , solver_adapter_check_sat  = checkSat
  , solver_adapter_write_smt2 = SMT2.writeDefaultSMT2 STP "STP" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks STP where
  smtlib2tweaks = STP

checkSat
   :: Monad m
   => SimpleBuilder t st
   -> Config m
   -> (Int -> String -> IO ())
   -> BoolElt t
   -> (SatResult (GroundEvalFn t, Maybe (EltRangeBindings t)) -> IO a)
   -> IO a
checkSat sym cfg logLn p cont = do
  solver_path <- findSolverPath =<< getConfigValue stpPath cfg
  withSTP sym solver_path (logLn 2) $ \s -> do
    -- Assume the predicate holds.
    SMT2.assume (SMT2.sessionWriter s) p
    -- Run check SAT and get the model back.
    SMT2.runCheckSat s cont

-- | Run STP in a session.  STP will be configured to produce models, buth
-- otherwise left with the default configuration.
withSTP :: SimpleBuilder t st
        -> FilePath
            -- ^ Path to STP executable
         -> (String -> IO ())
            -- ^ Function to print messages from STP to.
         -> (SMT2.Session t STP -> IO a)
            -- ^ Action to run
         -> IO a
withSTP sym stp_path logFn action = do
  withProcessHandles stp_path [] Nothing $ \(in_h, out_h, err_h, ph) -> do
    -- Log stderr to output.
    err_stream <- Streams.handleToInputStream err_h
    _ <- forkIO $ logErrorStream err_stream logFn
    -- Create stream for output from solver.
    -- Create writer and session
    bindings <- getSymbolVarBimap sym
    wtr <- SMT2.newWriter STP in_h "STP" True useIntegerArithmetic False bindings
    out_stream <- Streams.handleToInputStream out_h
    let s = SMT2.Session { SMT2.sessionWriter = wtr
                         , SMT2.sessionResponse = out_stream
                         }
    -- Tell STP to use all supported logics.
    SMT2.setLogic  wtr SMT2.all_supported
    -- Tell STP to produce models
    SMT2.setOption wtr (SMT2.produceModels True)
    -- Run action with session
    r <- action s
    -- Tell STP to exit
    SMT2.writeExit wtr
    -- Log outstream as error messages.
    _ <- forkIO $ logErrorStream out_stream logFn
    -- Check error code.
    ec <-  waitForProcess ph
    case ec of
      ExitSuccess -> return r
      ExitFailure exit_code ->
        fail $ "STP exited with unexpected code: " ++ show exit_code
