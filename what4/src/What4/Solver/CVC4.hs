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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module What4.Solver.CVC4
  ( CVC4(..)
  , cvc4Features
  , cvc4Adapter
  , cvc4Path
  , cvc4Options
  , runCVC4InOverride
  , withCVC4
  , writeCVC4SMT2File
  , writeMultiAsmpCVC4SMT2File
  ) where

import           Control.Monad (forM_, when)
import           Data.Bits
import           System.IO
import qualified System.IO.Streams as Streams
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
import           What4.Utils.Process


intWithRangeOpt :: ConfigOption BaseIntegerType -> Integer -> Integer -> ConfigDesc
intWithRangeOpt nm lo hi = mkOpt nm sty Nothing Nothing
  where sty = integerWithRangeOptSty (Inclusive lo) (Inclusive hi)

data CVC4 = CVC4 deriving Show

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

indexType :: [SMT2.Sort] -> SMT2.Sort
indexType [i] = i
indexType il = SMT2.structSort il

instance SMT2.SMTLib2Tweaks CVC4 where
  smtlib2tweaks = CVC4

  smtlib2arrayType il r = SMT2.arraySort (indexType il) r

  -- | Adapted from the tweak of array constant for CVC4.
  smtlib2arrayConstant = Just $ \idx rtp v ->
    SMT2.arrayConst (indexType idx) rtp v

cvc4Features :: ProblemFeatures
cvc4Features = useComputableReals
           .|. useSymbolicArrays

writeMultiAsmpCVC4SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeMultiAsmpCVC4SMT2File sym h ps = do
  bindings <- getSymbolVarBimap sym
  in_str  <- Streams.encodeUtf8 =<< Streams.handleToOutputStream h
  c <- SMT2.newWriter CVC4 in_str nullAcknowledgementAction "CVC4"
         True cvc4Features True bindings
  SMT2.setLogic c SMT2.allSupported
  SMT2.setProduceModels c True
  forM_ ps $ SMT2.assume c
  SMT2.writeCheckSat c
  SMT2.writeExit c

writeCVC4SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t]
   -> IO ()
writeCVC4SMT2File sym h ps = writeMultiAsmpCVC4SMT2File sym h ps

instance SMT2.SMTLib2GenericSolver CVC4 where
  defaultSolverPath _ = findSolverPath cvc4Path . getConfiguration

  defaultSolverArgs _ _ = return ["--lang", "smt2", "--incremental"]

  defaultFeatures _ = useIntegerArithmetic

  setDefaultLogicAndOptions writer = do
    -- Tell CVC4 to use all supported logics.
    SMT2.setLogic writer SMT2.allSupported
    -- Tell CVC4 to produce models
    SMT2.setProduceModels writer True

runCVC4InOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t]
  -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
  -> IO a
runCVC4InOverride = SMT2.runSolverInOverride CVC4 nullAcknowledgementAction (SMT2.defaultFeatures CVC4)

-- | Run CVC4 in a session. CVC4 will be configured to produce models, but
-- otherwise left with the default configuration.
withCVC4
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to CVC4 executable
  -> LogData
  -> (SMT2.Session t CVC4 -> IO a)
    -- ^ Action to run
  -> IO a
withCVC4 = SMT2.withSolver CVC4 nullAcknowledgementAction (SMT2.defaultFeatures CVC4)

setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  WriterConn t (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    -- Tell CVC4 to acknowledge successful commands
    SMT2.setOption writer "print-success"  "true"
    -- Tell CVC4 to produce models
    SMT2.setOption writer "produce-models" "true"
    -- Tell CVC4 to compute UNSAT cores, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"
    -- Tell CVC4 to use all supported logics.
    SMT2.setLogic writer SMT2.allSupported

instance OnlineSolver t (SMT2.Writer CVC4) where
  startSolverProcess = SMT2.startSolver CVC4 SMT2.smtAckResult setInteractiveLogicAndOptions
  shutdownSolverProcess = SMT2.shutdownSolver CVC4
