------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.SimpleBackend.Boolector
-- Description      : Interface for running Boolector
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides an interface for running Boolector and parsing
-- the results back.
------------------------------------------------------------------------
module Lang.Crucible.Solver.SimpleBackend.Boolector
  ( Boolector
  , boolectorPath
  , boolectorOptions
  , boolectorAdapter
  ) where

import           Control.Concurrent
import           Control.Monad
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import           System.Exit
import           System.IO
import qualified System.IO.Streams as Streams
import           System.Process

import           Lang.Crucible.Config
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.ProcessUtils
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.GroundEval
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import qualified Lang.Crucible.Solver.SimpleBackend.SMTLib2 as SMT2
import           Lang.Crucible.Solver.SimpleBackend.SMTWriter
  (smtExprGroundEvalFn, renderTerm, SMTEvalFunctions(..))
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.Streams

data Boolector = Boolector

-- | Path to boolector
boolectorPath :: ConfigOption FilePath
boolectorPath = configOption "boolector_path"

boolectorOptions :: MonadVerbosity m => [ConfigDesc m]
boolectorOptions =
  [ mkOpt boolectorPath (Just "boolector") executablePathOptSty
    "Path to boolector executable"
  ]

boolectorAdapter :: SolverAdapter st
boolectorAdapter =
  SolverAdapter
  { solver_adapter_name = "boolector"
  , solver_adapter_config_options = boolectorOptions
  , solver_adapter_check_sat = \sym cfg logLn p cont -> do
      res <- runBoolectorInOverride sym cfg logLn p
      cont (fmap (\x -> (x,Nothing)) res)
  , solver_adapter_write_smt2 =
      SMT2.writeDefaultSMT2 () "Boolector" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks Boolector where
  smtlib2tweaks = Boolector

runBoolectorInOverride :: Monad m
                       => SimpleBuilder t st
                       -> Config m
                       -> (Int -> String -> IO ())
                       -> BoolElt t
                       -> IO (SatResult (GroundEvalFn t))
runBoolectorInOverride sym cfg logLn p  = do
  -- Get boolector path.
  path <- findSolverPath =<< getConfigValue boolectorPath cfg
  withProcessHandles path ["-m"] Nothing $ \(in_h, out_h, err_h, ph) -> do
      -- Log stderr to output.
      err_stream <- Streams.handleToInputStream err_h
      void $ forkIO $ logErrorStream err_stream (logLn 2)
      -- Write SMT2 input to Boolector.
      bindings <- getSymbolVarBimap sym
      wtr <- SMT2.newWriter Boolector in_h "Boolector" False noFeatures False bindings
      SMT2.setLogic wtr SMT2.qf_bv
      SMT2.assume wtr p

      SMT2.writeCheckSat wtr
      SMT2.writeExit wtr
      -- Close input handle to tell boolector input is done.
      hClose in_h
      -- Read stdout to get output.
      out_stream <- Streams.handleToInputStream out_h
      line_stream <- Streams.map UTF8.toString =<< Streams.lines out_stream
      out_lines <- Streams.toList line_stream
      -- Check error code.
      ec <- waitForProcess ph
      case ec of
        ExitSuccess -> return ()
        ExitFailure 10 -> return () -- SAT exit
        ExitFailure 20 -> return () -- UNSAT exit
        ExitFailure exit_code  ->
          fail $ "boolector exited with unexpected code: " ++ show exit_code
      -- Parse output.
      parseBoolectorOutput wtr out_lines

parseBoolectorOutputLine :: Monad m => String -> m (Text, String)
parseBoolectorOutputLine s =
  case words s of
    [nm,v] -> return (Text.pack nm,v)
    _ -> fail $ "Could not parse Boolector output:\n  " ++ show s

boolectorBoolValue :: Monad m => String -> m Bool
boolectorBoolValue "1" = return True
boolectorBoolValue "0" = return False
boolectorBoolValue s = fail $ "Could not parse " ++ s ++ " as a Boolean."

boolectorBVValue :: Monad m => Int -> String -> m Integer
boolectorBVValue w0 s0 = go 0 0 s0
  where go w r [] = do
          when (w /= w0) $ fail "Unexpected number of bits in output."
          return r
        go w r ('1':s) = go (w+1) (2 * r + 1) s
        go w r ('0':s) = go (w+1) (2 * r) s
        go _ _ _ = fail $ "Could not parse " ++ s0 ++ " as a bitvector."

lookupBoolectorVar :: Monad m
                   => Map Text String
                      -- ^ Map from variable names to value
                   -> (String -> m r)
                      -- ^ Function for interpreting value
                   -> Text
                      -- ^ Name of variable to lookup
                   -> m r
lookupBoolectorVar m evalFn nm =
  case Map.lookup nm m of
    Just r -> evalFn r
    Nothing -> fail $ "Could not find variable "
                   ++ Text.unpack nm ++ " in Boolector output."

parseBoolectorOutput :: SMT2.WriterConn t (SMT2.Writer Boolector)
                     -> [String]
                     -> IO (SatResult (GroundEvalFn t))
parseBoolectorOutput c out_lines =
  case out_lines of
    "unsat":_ -> return Unsat
    "sat":mdl_lines0 -> do
      let mdl_lines = filter (/= "") mdl_lines0
      m <- Map.fromList <$> mapM parseBoolectorOutputLine mdl_lines
      let evalBool tm = lookupBoolectorVar m boolectorBoolValue (Builder.toLazyText (renderTerm tm))
      let evalBV w tm = lookupBoolectorVar m (boolectorBVValue w) (Builder.toLazyText (renderTerm tm))
      let evalReal _ = fail "Boolector does not support real variables."
      let evalFns = SMTEvalFunctions { smtEvalBool = evalBool
                                     , smtEvalBV = evalBV
                                     , smtEvalReal = evalReal
                                     }
      Sat <$> smtExprGroundEvalFn c evalFns
    [] -> fail "Boolector returned no output."
    h:_ -> fail $ "Could not parse boolector output: " ++ h
