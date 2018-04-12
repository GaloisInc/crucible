-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.Adapter
-- Description      : Defines the low-level interface between a particular
--                    solver and the SimpleBuilder family of backends.
-- Copyright        : (c) Galois, Inc 2015
-- License          : BSD3
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
  , solverAdapterOptions
  ) where

import           Data.Bits
import           Data.IORef
import qualified Data.Map as Map
import qualified Data.Text as T
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Config
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend.GroundEval
import           Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
import           Lang.Crucible.Solver.SimpleBuilder


data SolverAdapter st =
  SolverAdapter
  { solver_adapter_name :: !String

    -- | Configuration options relevant to this solver adapter
  , solver_adapter_config_options
        :: ![ConfigDesc]

    -- | Operation to check the satisfiability of a formula.
    --   The second argument is a callback that calculates the ultimate result from
    --   a SatResult and operations for finding model values in the event of a SAT result.
    --   Note: the evaluation functions may cease to be avaliable after the
    --   callback completes, so any necessary information should be extracted from
    --   them before returning.
  , solver_adapter_check_sat
        :: !(forall t a.
           SimpleBuilder t st
        -> Config
        -> (Int -> String -> IO ())
        -> BoolElt t
        -> (SatResult (GroundEvalFn t, Maybe (EltRangeBindings t)) -> IO a)
        -> IO a)

    -- | Write an SMTLib2 problem instance onto the given handle, incorporating
    --   any solver-specific tweaks appropriate to this solver
  , solver_adapter_write_smt2 :: !(forall t . SimpleBuilder t st -> Handle -> BoolElt t -> IO ())
  }


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

defaultSolverAdapter :: ConfigOption BaseStringType
defaultSolverAdapter = configOption BaseStringRepr "default_solver"


solverAdapterOptions ::
  [SolverAdapter st] ->
  IO ([ConfigDesc], IO (SolverAdapter st))
solverAdapterOptions [] = fail "No solver adapters specified!"
solverAdapterOptions xs@(def:_) =
  do ref <- newIORef def
     let opts = lopt ref : concatMap solver_adapter_config_options xs
     return (opts, readIORef ref)

 where
 f ref x = (T.pack (solver_adapter_name x), (PP.empty, writeIORef ref x >> return optOK))
 vals ref = Map.fromList (map (f ref) xs)
 lopt ref = optList defaultSolverAdapter
                        (vals ref)
                        (Just (PP.text "Indicates which solver to use for check-sat queries"))
                        (Just (T.pack (solver_adapter_name def)))
