-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.Adapter
-- Description      : Defines the low-level interface between a particular
--                    solver and the SimpleBuilder family of backends.
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.Solver.Adapter
  ( SolverAdapter(..)
  , defaultWriteSMTLIB2Features
  , defaultSolverAdapter
  ) where

import           Data.Bits
import           Data.Typeable
import           System.IO

import           Lang.Crucible.Config
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.GroundEval
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import           Lang.Crucible.Solver.SimpleBuilder

import           Lang.Crucible.Utils.MonadVerbosity

data SolverAdapter st =
  SolverAdapter
  { solver_adapter_name :: !String

    -- | Configuration options relevant to this solver adapter
  , solver_adapter_config_options
        :: !(forall m . MonadVerbosity m => [ConfigDesc m])

    -- | Operation to check the satisfiability of a formula.
    --   The second argument is a callback that calculates the ultimate result from
    --   a SatResult and operations for finding model values in the event of a SAT result.
    --   Note: the evaluation functions may cease to be avaliable after the
    --   callback completes, so any necessary information should be extracted from
    --   them before returning.
  , solver_adapter_check_sat
        :: !(forall m t a
         . Monad m
        => SimpleBuilder t st
        -> Config m
        -> (Int -> String -> IO ())
        -> BoolElt t
        -> (SatResult (GroundEvalFn t, Maybe (EltRangeBindings t)) -> IO a)
        -> IO a)

    -- | Write an SMTLib2 problem instance onto the given handle, incorporating
    --   any solver-specific tweaks appropriate to this solver
  , solver_adapter_write_smt2 :: !(forall t . SimpleBuilder t st -> Handle -> BoolElt t -> IO ())
  } deriving (Typeable)


instance Show (SolverAdapter st) where
  show = solver_adapter_name
instance Eq (SolverAdapter st) where
  x == y = solver_adapter_name x == solver_adapter_name y
instance Ord (SolverAdapter st) where
  compare x y = compare (solver_adapter_name x) (solver_adapter_name y)

-- | Default featues to use for writing SMTLIB2 files.
defaultWriteSMTLIB2Features :: ProblemFeatures
defaultWriteSMTLIB2Features
  = useComputableReals
  .|. useIntegerArithmetic
  .|. useBitvectors
  .|. useQuantifiers
  .|. useSymbolicArrays

defaultSolverAdapter :: Typeable st => ConfigOption (SolverAdapter st)
defaultSolverAdapter = configOption "default_solver"
