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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Solver.STP
  ( STP(..)
  , stpAdapter
  , stpPath
  , stpOptions
  , runSTPInOverride
  , withSTP
  ) where

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
import           What4.Protocol.Online
import qualified What4.Protocol.SMTLib2 as SMT2
import           What4.Protocol.SMTWriter
import           What4.Utils.Process

data STP = STP deriving Show

-- | Path to stp
stpPath :: ConfigOption (BaseStringType Unicode)
stpPath = configOption knownRepr "stp_path"

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
  , solver_adapter_write_smt2 =
       SMT2.writeDefaultSMT2 STP "STP" defaultWriteSMTLIB2Features
  }

instance SMT2.SMTLib2Tweaks STP where
  smtlib2tweaks = STP

instance SMT2.SMTLib2GenericSolver STP where
  defaultSolverPath _ = findSolverPath stpPath . getConfiguration

  defaultSolverArgs _ _ = return []

  defaultFeatures _ = useIntegerArithmetic

  setDefaultLogicAndOptions writer = do
    -- Tell STP to use all supported logics
    SMT2.setLogic writer SMT2.qf_bv

  newDefaultWriter solver ack feats sym h =
    SMT2.newWriter solver h ack (show solver) True feats False
      =<< getSymbolVarBimap sym

runSTPInOverride
  :: ExprBuilder st t fs
  -> LogData
  -> [BoolExpr t fs]
  -> (SatResult (GroundEvalFn t fs, Maybe (ExprRangeBindings t fs)) () -> IO a)
  -> IO a
runSTPInOverride = SMT2.runSolverInOverride STP nullAcknowledgementAction (SMT2.defaultFeatures STP)

-- | Run STP in a session. STP will be configured to produce models, buth
-- otherwise left with the default configuration.
withSTP
  :: ExprBuilder st t fs
  -> FilePath
    -- ^ Path to STP executable
  -> LogData
  -> (SMT2.Session t fs STP -> IO a)
    -- ^ Action to run
  -> IO a
withSTP = SMT2.withSolver STP nullAcknowledgementAction (SMT2.defaultFeatures STP)

instance OnlineSolver t (SMT2.Writer STP) where
  startSolverProcess =
    SMT2.startSolver STP (\_ -> nullAcknowledgementAction) SMT2.setDefaultLogicAndOptions
  shutdownSolverProcess = SMT2.shutdownSolver STP
