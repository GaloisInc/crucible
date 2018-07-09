------------------------------------------------------------------------
-- |
-- Module      : What4.Solver.CVC4
-- Description : Solver adapter code for CVC4
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- CVC4-specific tweaks to the basic SMTLib2 solver interface.
------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.CVC4
  ( CVC4
  , cvc4Adapter
  , cvc4Path
  , runCVC4InOverride
  , writeCVC4SMT2File
  , writeMultiAsmpCVC4SMT2File
  , withCVC4
  ) where

import           Control.Concurrent
import           Control.Monad (void, forM_)
import           Data.Bits
import           Data.String
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
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Protocol.SMTWriter
import           What4.Utils.Process
import           What4.Utils.Streams


intWithRangeOpt :: ConfigOption BaseIntegerType -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi = mkOpt nm sty Nothing Nothing
  where sty = integerWithRangeOptSty (Inclusive lo) (Inclusive hi)

data CVC4 = CVC4

-- | Path to cvc4
cvc4Path :: ConfigOption BaseStringType
cvc4Path = configOption knownRepr "cvc4_path"

cvc4RandomSeed :: ConfigOption BaseIntegerType
cvc4RandomSeed = configOption knownRepr "cvc4.random-seed"

cvc4Options :: [ConfigDesc]
cvc4Options =
  [ mkOpt cvc4Path
          executablePathOptSty
          (Just (PP.text "Path to CVC4 executable"))
          (Just (ConcreteString "cvc4"))
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

-- | For the moment, store-all is not supported by CVC4 yet.
arrayConstant1 :: SMT_Type -> SMT2.Expr CVC4 -> SMT2.Expr CVC4
arrayConstant1 idx v =
  T $ app (fromString "store-all") [ SMT2.unType CVC4 idx, renderTerm v ]

indexType :: [SMT_Type] -> SMT_Type
indexType [i] = i
indexType il = SMT_StructType il

instance SMT2.SMTLib2Tweaks CVC4 where
  smtlib2tweaks = CVC4

  smtlib2arrayType _ il r = SMT2.arrayType1 CVC4 (indexType il) (SMT2.unType CVC4 r)

  --smtlib2arrayConstant = Just $ \idx _elts v -> foldr arrayConstant1 v idx

  -- | Adapted from the tweak of array constant for Z3.
  smtlib2arrayConstant = Just $ \idx elts v ->
    let array_type = SMT2.smtlib2arrayType CVC4 idx elts
        cast_app = builder_list [ "as" , "const" , array_type ]
     in term_app cast_app [ v ]

cvc4Features :: ProblemFeatures
cvc4Features = useComputableReals
           .|. useSymbolicArrays

writeMultiAsmpCVC4SMT2File
   :: ExprBuilder t st
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeMultiAsmpCVC4SMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  c <- SMT2.newWriter CVC4 h "CVC4" True cvc4Features True bindings
  --c <- SMT2.newWriter h "CVC4" True SMT2.LinearArithmetic
  SMT2.setLogic c SMT2.all_supported
  SMT2.setOption c (SMT2.produceModels True)
  forM_ ps $ SMT2.assume c
  SMT2.writeCheckSat c
  SMT2.writeExit c

writeCVC4SMT2File
   :: ExprBuilder t st
   -> Handle
   -> BoolExpr t
   -> IO ()
writeCVC4SMT2File sym h p = writeMultiAsmpCVC4SMT2File sym h [p]

runCVC4InOverride
   :: ExprBuilder t st
   -> (Int -> String -> IO ())
   -> BoolExpr t
   -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) -> IO a)
   -> IO a
runCVC4InOverride sym logLn p cont = do
  solver_path <- findSolverPath cvc4Path (getConfiguration sym)
  withCVC4 sym solver_path (logLn 2) $ \s -> do
    -- Assume the predicate holds.
    SMT2.assume (SMT2.sessionWriter s) p
    -- Run check SAT and get the model back.
    SMT2.runCheckSat s cont

-- | Run CVC4 in a session.  CVC4 will be configured to produce models, buth
-- otherwise left with the default configuration.
withCVC4 :: ExprBuilder t st
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
