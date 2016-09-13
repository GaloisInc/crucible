------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SimpleBackend.CVC4
-- Description : Solver adapter code for CVC4
-- Copyright   : (c) Galois, Inc 2015
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- CVC4-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
module Lang.Crucible.Solver.SimpleBackend.CVC4
  ( CVC4
  , cvc4Adapter
  ) where

import           Control.Concurrent
import           Control.Monad (void)
import           Data.String
import           System.Exit
import           System.IO
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
import           Lang.Crucible.Solver.SimpleBackend.SMTWriter
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.Streams


intWithRangeOpt :: Monad m => ConfigOption Int -> Int -> Int -> ConfigDesc m
intWithRangeOpt nm lo hi = mkOpt nm Nothing sty PP.empty
  where sty = integralWithRangeOptSty (Inclusive lo) (Inclusive hi)

data CVC4 = CVC4

-- | Path to cvc4
cvc4Path :: ConfigOption FilePath
cvc4Path = configOption "cvc4_path"

cvc4RandomSeed :: ConfigOption Int
cvc4RandomSeed = configOption "cvc4.random-seed"

cvc4Options :: MonadVerbosity m => [ConfigDesc m]
cvc4Options =
  [ mkOpt cvc4Path (Just "cvc4") executablePathOptSty "Path to CVC4 executable"
  , intWithRangeOpt cvc4RandomSeed (negate (2^(30::Int)-1)) (2^(30::Int)-1)
  ]

cvc4Adapter :: SolverAdapter st
cvc4Adapter =
  SolverAdapter
  { solver_adapter_name = "cvc4"
  , solver_adapter_config_options = cvc4Options
  , solver_adapter_check_sat = runCVC4InOverride
  , solver_adapter_write_smt2 = writeCVC4SMT2File
  }

arrayConstant1 :: SMT_Type -> SMT2.Expr CVC4 -> SMT2.Expr CVC4
arrayConstant1 idx v =
  T $ app (fromString "store-all") [ SMT2.unType CVC4 idx, renderTerm v ]

instance SMT2.SMTLib2Tweaks CVC4 where
  smtlib2tweaks = CVC4
  smtlib2arrayConstant = Just $ \idx _elts v -> foldr arrayConstant1 v idx

writeCVC4SMT2File
   :: SimpleBuilder t st
   -> Handle
   -> BoolElt t
   -> IO ()
writeCVC4SMT2File sym h p = do
  bindings <- getSymbolVarBimap sym
  c <- SMT2.newWriter CVC4 h "CVC4" True useComputableReals True bindings
  --c <- SMT2.newWriter h "CVC4" True SMT2.LinearArithmetic
  SMT2.setLogic c SMT2.all_supported
  SMT2.setOption c (SMT2.produceModels True)
  SMT2.assume c p
  SMT2.writeCheckSat c
  SMT2.writeExit c

runCVC4InOverride
   :: Monad m
   => SimpleBuilder t st
   -> Config m
   -> (Int -> String -> IO ())
   -> BoolElt t
   -> (SatResult (GroundEvalFn t, Maybe (EltRangeBindings t)) -> IO a)
   -> IO a
runCVC4InOverride sym cfg logLn p cont = do
  solver_path <- findSolverPath =<< getConfigValue cvc4Path cfg
  withCVC4 sym solver_path (logLn 2) $ \s -> do
    -- Assume the predicate holds.
    SMT2.assume (SMT2.sessionWriter s) p
    -- Run check SAT and get the model back.
    SMT2.runCheckSat s cont

-- | Run CVC4 in a session.  CVC4 will be configured to produce models, buth
-- otherwise left with the default configuration.
withCVC4 :: SimpleBuilder t st
         -> FilePath
            -- ^ Path to CVC4 executable
         -> (String -> IO ())
            -- ^ Function to print messages from CVC4 to.
         -> (SMT2.Session t CVC4 -> IO a)
            -- ^ Action to run
         -> IO a
withCVC4 sym cvc4_path logFn action = do
  withProcessHandles cvc4_path ["--lang", "smt2"] Nothing $ \(in_h, out_h, err_h, ph) -> do
    -- Log stderr to output.
    err_stream <- Streams.handleToInputStream err_h
    void $ forkIO $ logErrorStream err_stream logFn
    -- Create stream for output from solver.
    -- Create writer and session
    bindings <- getSymbolVarBimap sym
    wtr <- SMT2.newWriter CVC4 in_h "CVC4" True useIntegerArithmetic True bindings
    out_stream <- Streams.handleToInputStream out_h
    let s = SMT2.Session { SMT2.sessionWriter = wtr
                         , SMT2.sessionResponse = out_stream
                         }
    -- Tell CVC4 to use all supported logics.
    SMT2.setLogic  wtr SMT2.all_supported
    -- Tell CVC4 to produce models
    SMT2.setOption wtr (SMT2.produceModels True)
    -- Run action with session
    r <- action s
    -- Tell CVC4 to exit
    SMT2.writeExit wtr
    -- Log outstream as error messages.
    void $ forkIO $ logErrorStream out_stream logFn
    -- Check error code.
    ec <- waitForProcess ph
    case ec of
      ExitSuccess -> return r
      ExitFailure exit_code ->
        fail $ "CVC4 exited with unexpected code: " ++ show exit_code
