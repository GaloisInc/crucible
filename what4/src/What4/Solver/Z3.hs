------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.Z3
-- Description : Solver adapter code for Z3
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- Z3-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.Z3
       ( Z3
       , z3Path
       , z3Options
       , z3Adapter
       , writeZ3SMT2File
       , runZ3InOverride
       , withZ3
       ) where

import           Control.Concurrent
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.Text.Lazy as LazyText
import           System.Exit
import           System.IO
import qualified System.IO.Streams as Streams
import           System.Process
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Config
import           What4.Solver.Adapter
import           What4.Concrete
import           What4.Interface
import           What4.ProblemFeatures
import           What4.SatResult
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Protocol.SMTWriter
import           What4.Utils.HandleReader
import           What4.Utils.Process
import           What4.Utils.Streams

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
   :: ExprBuilder t st fs
   -> Handle
   -> BoolExpr t
   -> IO ()
writeZ3SMT2File = SMT2.writeDefaultSMT2 Z3 "Z3" z3Features

runZ3InOverride
   :: ExprBuilder t st fs
   -> (Int -> String -> IO ())
   -> BoolExpr t
   -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) -> IO a)
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
withZ3 :: ExprBuilder t st fs
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

instance OnlineSolver t (SMT2.Writer Z3) where
  startSolverProcess = z3StartSolver
  shutdownSolverProcess = z3ShutdownSolver

z3StartSolver :: ExprBuilder t st fs -> IO (SolverProcess t (SMT2.Writer Z3))
z3StartSolver sym =
  do let cfg = getConfiguration sym
     z3_path <- findSolverPath z3Path cfg
     let args = ["-smt2", "-in"]
     let create_proc = (proc z3_path args)
                       { std_in  = CreatePipe
                       , std_out = CreatePipe
                       , std_err = CreatePipe
                       , create_group = True
                       , cwd = Nothing
                       }
     let startProcess = do
           x <- createProcess create_proc
           case x of
             (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
             _ -> fail "Internal error in z3StartServer: Failed to create handle."

     (in_h, out_h, err_h, ph) <- startProcess

     -- Log stderr to output.
     err_reader <- startHandleReader err_h
     -- Create writer and session
     bindings <- getSymbolVarBimap sym
     wtr <- SMT2.newWriter Z3 in_h "Z3" True z3Features True bindings

     out_stream <- Streams.handleToInputStream out_h
     -- Tell Z3 to produce models.
     SMT2.setOption wtr (SMT2.produceModels True)
     -- Tell Z3 to round and print algebraic reals as decimal
     SMT2.setOption wtr (SMT2.ppDecimal True)

     return $! SolverProcess
               { solverConn = wtr
               , solverStdin = in_h
               , solverStderr = err_reader
               , solverHandle = ph
               , solverResponse = out_stream
               , solverEvalFuns = smtEvalFuns wtr out_stream
               }


z3ShutdownSolver :: SolverProcess t (SMT2.Writer Z3) -> IO ()
z3ShutdownSolver p =
  do -- Tell Z3 to exit
     SMT2.writeExit (solverConn p)

     txt <- readAllLines (solverStderr p)

     ec <- waitForProcess (solverHandle p)
     case ec of
       ExitSuccess ->
         return ()
       ExitFailure exit_code ->
         fail ("Z3 exited with unexpected code: " ++ show exit_code ++ "\n" ++ LazyText.unpack txt)
