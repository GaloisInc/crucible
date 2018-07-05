------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.STP
-- Description : Solver adapter code for STP
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Joe Hendrix <rdockins@galois.com>
-- Stability   : provisional
--
-- STP-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.STP
  ( STP
  , stpAdapter
  , stpPath
  , runSTPInOverride
  , withSTP
  ) where

import           Control.Concurrent
import           System.Exit
import qualified System.IO.Streams as Streams
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Config
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Solver.Adapter
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Utils.Process
import           What4.Utils.Streams

data STP = STP

-- | Path to stp
stpPath :: ConfigOption BaseStringType
stpPath = configOption knownRepr "stp.path"

stpRandomSeed :: ConfigOption BaseIntegerType
stpRandomSeed = configOption knownRepr "stp.random-seed"

intWithRangeOpt :: ConfigOption BaseIntegerType -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi = mkOpt nm sty Nothing Nothing
  where sty = integerWithRangeOptSty (Inclusive lo) (Inclusive hi)

stpOptions :: [ConfigDesc]
stpOptions =
  [ mkOpt stpPath 
          executablePathOptSty
          (Just (PP.text "Path to STP executable."))
          (Just (ConcreteString "stp"))
  , intWithRangeOpt stpRandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
  ]

stpAdapter :: SolverAdapter st
stpAdapter =
  SolverAdapter
  { solver_adapter_name = "stp"
  , solver_adapter_config_options = stpOptions
  , solver_adapter_check_sat  = runSTPInOverride
  , solver_adapter_write_smt2 = SMT2.writeDefaultSMT2 STP "STP" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks STP where
  smtlib2tweaks = STP

runSTPInOverride
   :: ExprBuilder t st
   -> (Int -> String -> IO ())
   -> BoolExpr t
   -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) -> IO a)
   -> IO a
runSTPInOverride sym logLn p cont = do
  solver_path <- findSolverPath stpPath (getConfiguration sym)
  withSTP sym solver_path (logLn 2) $ \s -> do
    -- Assume the predicate holds.
    SMT2.assume (SMT2.sessionWriter s) p
    -- Run check SAT and get the model back.
    SMT2.runCheckSat s cont

-- | Run STP in a session.  STP will be configured to produce models, buth
-- otherwise left with the default configuration.
withSTP :: ExprBuilder t st
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
