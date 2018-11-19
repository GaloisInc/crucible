{-|
Module      : What4.Solver
Copyright   : (c) Galois, Inc 2015-2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

The module reexports the most commonly used types
and operations for interacting with solvers.
-}

module What4.Solver
  ( -- * Solver Adapters
    SolverAdapter(..)
  , ExprRangeBindings
  , defaultSolverAdapter
  , solverAdapterOptions
  , LogData(..)
  , logCallback
  , defaultLogData

    -- * Boolector
  , boolectorAdapter
  , boolectorPath
  , runBoolectorInOverride

    -- * CVC4
  , cvc4Adapter
  , cvc4Path
  , runCVC4InOverride
  , writeCVC4SMT2File
  , withCVC4

    -- * DReal
  , DRealBindings
  , drealAdapter
  , drealPath
  , runDRealInOverride
  , writeDRealSMT2File

    -- * STP
  , stpAdapter
  , stpPath
  , runSTPInOverride
  , withSTP

    -- * Yices
  , yicesAdapter
  , yicesPath
  , runYicesInOverride
  , writeYicesFile

    -- * Z3
  , z3Path
  , z3Adapter
  , runZ3InOverride
  , withZ3
  ) where

import What4.Solver.Adapter
import What4.Solver.Boolector
import What4.Solver.CVC4
import What4.Solver.DReal
import What4.Solver.STP
import What4.Solver.Yices
import What4.Solver.Z3
