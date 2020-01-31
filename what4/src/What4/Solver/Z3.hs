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
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE GADTs #-}
module What4.Solver.Z3
  ( Z3(..)
  , z3Adapter
  , z3Path
  , z3Timeout
  , z3Options
  , runZ3InOverride
  , withZ3
  , writeZ3SMT2File
  ) where

import           Control.Monad ( when )
import           Data.Bits
import           Data.String
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.BaseTypes
import           What4.Concrete
import           What4.Config
import           What4.Expr.Builder
import           What4.Expr.GroundEval
import           What4.Interface
import           What4.ProblemFeatures
import           What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.SMTLib2.Syntax as SMT2Syntax
import           What4.Protocol.SMTWriter
import           What4.SatResult
import           What4.Solver.Adapter
import           What4.Utils.Process

data Z3 = Z3 deriving Show

-- | Path to Z3
z3Path :: ConfigOption (BaseStringType Unicode)
z3Path = configOption knownRepr "z3_path"

-- | Per-check timeout, in milliseconds (zero is none)
z3Timeout :: ConfigOption BaseIntegerType
z3Timeout = configOption knownRepr "z3_timeout"

z3Options :: [ConfigDesc]
z3Options =
  [ mkOpt
      z3Path
      executablePathOptSty
      (Just (PP.text "Z3 executable path"))
      (Just (ConcreteString "z3"))
  , mkOpt
      z3Timeout
      integerOptSty
      (Just (PP.text "Per-check timeout in milliseconds (zero is none)"))
      (Just (ConcreteInteger 0))
  ]

z3Adapter :: SolverAdapter st
z3Adapter =
  SolverAdapter
  { solver_adapter_name = "z3"
  , solver_adapter_config_options = z3Options
  , solver_adapter_check_sat = runZ3InOverride
  , solver_adapter_write_smt2 = writeZ3SMT2File
  }

indexType :: [SMT2.Sort] -> SMT2.Sort
indexType [i] = i
indexType il = SMT2.smtlib2StructSort @Z3 il

indexCtor :: [SMT2.Term] -> SMT2.Term
indexCtor [i] = i
indexCtor il = SMT2.smtlib2StructCtor @Z3 il

instance SMT2.SMTLib2Tweaks Z3 where
  smtlib2tweaks = Z3

  smtlib2arrayType il r = SMT2.arraySort (indexType il) r

  smtlib2arrayConstant = Just $ \idx rtp v ->
    SMT2.arrayConst (indexType idx) rtp v
  smtlib2arraySelect a i = SMT2.arraySelect a (indexCtor i)
  smtlib2arrayUpdate a i = SMT2.arrayStore a (indexCtor i)

  -- Z3 uses a datatype declaration command that differs from the
  -- SMTLib 2.6 standard
  smtlib2declareStructCmd n = Just $
      let type_name i = fromString ('T' : show (i-1))
          params = builder_list $ type_name  <$> [1..n]
          n_str = fromString (show n)
          tp = "Struct" <> n_str
          ctor = "mk-struct" <> n_str
          field_def i = app field_nm [type_name i]
            where field_nm = "struct" <> n_str <> "-proj" <> fromString (show (i-1))
          fields = field_def <$> [1..n]
          decl = app tp [app ctor fields]
          decls = "(" <> decl <> ")"
       in SMT2Syntax.Cmd $ app "declare-datatypes" [ params, decls ]

z3Features :: ProblemFeatures
z3Features = useNonlinearArithmetic
         .|. useIntegerArithmetic
         .|. useQuantifiers
         .|. useSymbolicArrays
         .|. useStructs
         .|. useStrings
         .|. useFloatingPoint
         .|. useBitvectors

writeZ3SMT2File
   :: ExprBuilder t st fs
   -> Handle
   -> [BoolExpr t fs]
   -> IO ()
writeZ3SMT2File = SMT2.writeDefaultSMT2 Z3 "Z3" z3Features

instance SMT2.SMTLib2GenericSolver Z3 where
  defaultSolverPath _ = findSolverPath z3Path . getConfiguration

  defaultSolverArgs _ sym = do
    let cfg = getConfiguration sym
    timeout <- getOption =<< getOptionSetting z3Timeout cfg
    let extraOpts = case timeout of
                      Just (ConcreteInteger n) | n > 0 -> ["-t:" ++ show n]
                      _ -> []
    return $ ["-smt2", "-in"] ++ extraOpts

  defaultFeatures _ = z3Features

  setDefaultLogicAndOptions writer = do
    -- Tell Z3 to produce models.
    SMT2.setOption writer "produce-models" "true"
    -- Tell Z3 to round and print algebraic reals as decimal
    SMT2.setOption writer "pp.decimal" "true"
    -- Tell Z3 to compute UNSAT cores, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $
      SMT2.setOption writer "produce-unsat-cores" "true"

runZ3InOverride
  :: ExprBuilder t st fs
  -> LogData
  -> [BoolExpr t fs]
  -> (SatResult (GroundEvalFn t fs, Maybe (ExprRangeBindings t fs)) () -> IO a)
  -> IO a
runZ3InOverride = SMT2.runSolverInOverride Z3 nullAcknowledgementAction z3Features

-- | Run Z3 in a session. Z3 will be configured to produce models, but
-- otherwise left with the default configuration.
withZ3
  :: ExprBuilder t st fs
  -> FilePath
    -- ^ Path to CVC4 executable
  -> LogData
  -> (SMT2.Session t fs Z3 -> IO a)
    -- ^ Action to run
  -> IO a
withZ3 = SMT2.withSolver Z3 nullAcknowledgementAction z3Features


setInteractiveLogicAndOptions ::
  SMT2.SMTLib2Tweaks a =>
  WriterConn t fs (SMT2.Writer a) ->
  IO ()
setInteractiveLogicAndOptions writer = do
    -- Tell Z3 to acknowledge successful commands
    SMT2.setOption writer "print-success"  "true"
    -- Tell Z3 to produce models
    SMT2.setOption writer "produce-models" "true"
    -- Tell Z3 to round and print algebraic reals as decimal
    SMT2.setOption writer "pp.decimal" "true"
    -- Tell Z3 to make declaraions global, so they are not removed by 'pop' commands
    SMT2.setOption writer "global-declarations" "true"
    -- Tell Z3 to compute UNSAT cores, if that feature is enabled
    when (supportedFeatures writer `hasProblemFeature` useUnsatCores) $ do
      SMT2.setOption writer "produce-unsat-cores" "true"

instance OnlineSolver t (SMT2.Writer Z3) where
  startSolverProcess = SMT2.startSolver Z3 SMT2.smtAckResult setInteractiveLogicAndOptions
  shutdownSolverProcess = SMT2.shutdownSolver Z3
