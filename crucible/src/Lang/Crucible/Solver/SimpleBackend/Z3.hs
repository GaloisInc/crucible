------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SimpleBackend.Z3
-- Description : Solver adapter code for Z3
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- Z3-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module Lang.Crucible.Solver.SimpleBackend.Z3
       ( Z3
       , z3Path
       , z3Options
       , z3Adapter
       , withZ3
       ) where

import           Control.Concurrent
import           Control.Monad.State.Strict
import           Data.Bits
import           System.Exit
import           System.IO
import qualified System.IO.Streams as Streams
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Config
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.Concrete
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.ProcessUtils
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.GroundEval
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import qualified Lang.Crucible.Solver.SimpleBackend.SMTLib2 as SMT2
import           Lang.Crucible.Solver.SimpleBackend.SMTWriter
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Utils.Streams

data Z3 = Z3

-- | Path to Z3
z3Path :: ConfigOption BaseStringType
z3Path = configOption knownRepr "z3_path"

z3Options :: [ConfigDesc]
z3Options =
  [ mkOpt
      z3Path
      executablePathOptSty
      (Just (PP.text "Z3 executable path"))
      (Just (ConcreteString "z3"))
  ]

z3Adapter :: SolverAdapter st
z3Adapter =
  SolverAdapter
  { solver_adapter_name = "z3"
  , solver_adapter_config_options = z3Options
  , solver_adapter_check_sat = runZ3InOverride
  , solver_adapter_write_smt2 = writeZ3SMT2File
  }

indexType :: [SMT_Type] -> SMT_Type
indexType [i] = i
indexType il = SMT_StructType il

indexCtor :: [SMT2.Expr Z3] -> SMT2.Expr Z3
indexCtor [i] = i
indexCtor il = structCtor il

instance SMT2.SMTLib2Tweaks Z3 where
  smtlib2tweaks = Z3

  smtlib2arrayType _ il r = SMT2.arrayType1 Z3 (indexType il) (SMT2.unType Z3 r)

  smtlib2arrayConstant = Just $ \idx elts v ->
    let array_type = SMT2.smtlib2arrayType Z3 idx elts
        cast_app = builder_list [ "as" , "const" , array_type ]
     in term_app cast_app [ v ]
  smtlib2arraySelect a i   = SMT2.arraySelect1 a (indexCtor i)
  smtlib2arrayUpdate a i v = SMT2.arrayUpdate1 a (indexCtor i) v

z3Features :: ProblemFeatures
z3Features = useNonlinearArithmetic
         .|. useIntegerArithmetic
         .|. useQuantifiers
         .|. useSymbolicArrays
         .|. useStructs

writeZ3SMT2File
   :: SimpleBuilder t st
   -> Handle
   -> BoolElt t
   -> IO ()
writeZ3SMT2File = SMT2.writeDefaultSMT2 Z3 "Z3" z3Features

runZ3InOverride
   :: SimpleBuilder t st
   -> (Int -> String -> IO ())
   -> BoolElt t
   -> (SatResult (GroundEvalFn t, Maybe (EltRangeBindings t)) -> IO a)
   -> IO a
runZ3InOverride sym logLn p cont = do
  z3_path <- findSolverPath z3Path (getConfiguration sym)
  withZ3 sym z3_path (logLn 2) $ \s -> do
    -- Assume the predicate holds.
    SMT2.assume (SMT2.sessionWriter s) p
    -- Run check SAT and get the model back.
    SMT2.runCheckSat s cont

-- | Run Z3 in a session.  Z3 will be configured to produce models, buth
-- otherwise left with the default configuration.
withZ3 :: SimpleBuilder t st
       -> FilePath
          -- ^ Path to Z3
       -> (String -> IO ())
          -- ^ Command to use for writing log messages to.
       -> (SMT2.Session t Z3 -> IO a)
            -- ^ Action to run
       -> IO a
withZ3 sym z3_path logFn action = do
  let args = ["-smt2", "-in"]
  withProcessHandles z3_path args Nothing $ \(in_h, out_h, err_h, ph) -> do
    -- Log stderr to output.
    err_stream <- Streams.handleToInputStream err_h
    void $ forkIO $ logErrorStream err_stream logFn
    -- Create writer and session
    bindings <- getSymbolVarBimap sym
    let
    wtr <- SMT2.newWriter Z3 in_h "Z3" True z3Features True bindings
    out_stream <- Streams.handleToInputStream out_h
    let s = SMT2.Session { SMT2.sessionWriter = wtr
                         , SMT2.sessionResponse = out_stream
                         }
    -- Tell Z3 to produce models.
    SMT2.setOption wtr (SMT2.produceModels True)
    -- Tell Z3 to round and print algebraic reals as decimal
    SMT2.setOption wtr (SMT2.ppDecimal True)
    -- Run action with session.
    r <- action s
    -- Tell Z3 to exit
    SMT2.writeExit wtr
    -- Log outstream from now on.
    void $ forkIO $ logErrorStream out_stream logFn

    ec <- waitForProcess ph
    case ec of
      ExitSuccess ->
        return r
      ExitFailure exit_code ->
        fail $ "Z3 exited with unexpected code: " ++ show exit_code
