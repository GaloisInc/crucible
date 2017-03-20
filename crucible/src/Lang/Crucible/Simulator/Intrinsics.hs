-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Intrinsics
-- Description      : Class and type definitions for intrinsic types
-- Copyright        : (c) Galois, Inc 2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.Simulator.Intrinsics
  (     -- * Intrinsic types
    IntrinsicClass(..)
  , IntrinsicMuxFn(..)
  , IntrinsicTypes
  ) where

import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.SymbolRepr
import qualified GHC.TypeLits

import           Lang.Crucible.Solver.BoolInterface


-- | Type family for intrinsic type representations.  Intrinsic types
--   are identified by a type-level `Symbol`, and this typeclass allows
--   backends to define implementations for these types.
--
--   An instance of this class defines both an instance for the
--   `Intrinsic` type family (which defines the runtime representation
--   for this intrinsic type) and also the `muxIntrinsic` method
--   (which defines how to merge to intrinsic values when the simulator
--   reaches a merge point).
--
-- Note: Instances of this will typically end up as orphan instances.
-- This warning is normally quite important, as orphan instances allow
-- one to define multiple instances for a particular class.  However, in
-- this case, "IntrinsicClass" contains a type family, and GHC will globally
-- check consistency of all type family instances.  Consequently, there
-- can be at most one implementation of InstrinsicClass in a program.
class IntrinsicClass (sym :: *) (nm :: GHC.TypeLits.Symbol) where
  -- | The `Intrinsic` type family defines, for a given backend and symbol name,
  --   the runtime implementation of that Crucible intrisnic type.
  type Intrinsic (sym :: *) (nm :: GHC.TypeLits.Symbol) :: *

  -- | The push branch function is called when an intrinsic value is
  --   passed through a symbolic branch.  This allows it to to any
  --   necessary bookeeping to prepare for an upcomming merge.
  --   A push branch should eventually be followed by a matching
  --   abort or mux call.
  pushBranchIntrinsic
               :: sym
               -> SymbolRepr nm
               -> Intrinsic sym nm
               -> IO (Intrinsic sym nm)
  pushBranchIntrinsic _ _ = return

  -- | The abort branch function is called when an intrinsic value
  --   reaches a merge point, but the sibling branch has aborted.
  abortBranchIntrinsic
               :: sym
               -> SymbolRepr nm
               -> Intrinsic sym nm
               -> IO (Intrinsic sym nm)
  abortBranchIntrinsic _ _ = return

  -- | The `muxIntrinsic` method defines the if-then-else operation that is used
  --   when paths are merged in the simulator and intrinsic types need to be used.
  muxIntrinsic :: sym
               -> SymbolRepr nm
               -> Pred sym
               -> Intrinsic sym nm
               -> Intrinsic sym nm
               -> IO (Intrinsic sym nm)


-- | The `IntrinsicMuxFn` datatype allows an `IntrinsicClass` instance
--   to be packaged up into a value.  This allows us to get access to IntrinsicClass
--   instance methods (the `muxIntrinsic` method in particular) at runtime even
--   for symbol names that are not known statically.
--
--   By packaging up a type class instance (rather than just providing some method with the
--   same signature as `muxIntrinsic`) we get the compiler to ensure that a single
--   distinguished implementation is always used for each backend/symbol name combination.
--   This prevents any possible confusion between different parts of the system.
data IntrinsicMuxFn (sym :: *) (nm :: Symbol) where
  IntrinsicMuxFn :: IntrinsicClass sym nm => IntrinsicMuxFn sym nm


-- | `IntrinsicTypes` is a map from symbol name representatives to `IntrinsicMuxFn`
--    values.  Such a map is useful for providing access to intrinsic type implementations
--   that are not known statically at compile time.
type IntrinsicTypes sym = MapF.MapF SymbolRepr (IntrinsicMuxFn sym)
