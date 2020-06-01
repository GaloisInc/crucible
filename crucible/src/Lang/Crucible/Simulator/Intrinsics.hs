-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Intrinsics
-- Description      : Basic definitions for defining intrinsic types
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- 'Intrinsic' types can be used to extend the basic set of types available
-- to the Crucible simulator.  A new intrinsic type is defined by
-- implementing an `IntrinsicClass` instance, which binds a type-level name
-- to a particular impelementation.  To use an intrinsic type, one must
-- register the associated `IntrinsicMuxFn` value with the simulator
-- prior to starting it.  This is done by building an `IntrinsicMuxFns`
-- map to be passed to the `initSimContext` function.
-----------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.Simulator.Intrinsics
  ( -- * Intrinsic types
    IntrinsicClass(..)
  , GetIntrinsic
  , IntrinsicMuxFn(..)
  , IntrinsicTypes
  , emptyIntrinsicTypes
  , typeError
  ) where

import           Data.Kind
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.SymbolRepr
import qualified GHC.TypeLits (Symbol)
import qualified GHC.TypeLits as TL
import           GHC.Stack

import           What4.Interface
import           Lang.Crucible.Panic
import           Lang.Crucible.Types

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
-- this case, 'IntrinsicClass' contains a type family, and GHC will globally
-- check consistency of all type family instances.  Consequently, there
-- can be at most one implementation of 'IntrinsicClass' in a program.
class IntrinsicClass (sym :: Type) (nm :: GHC.TypeLits.Symbol) where
  -- | The 'Intrinsic' type family defines, for a given backend and symbol name,
  --   the runtime implementation of that Crucible intrinsic type.
  type Intrinsic (sym :: Type) (nm :: GHC.TypeLits.Symbol) (ctx :: Ctx CrucibleType) :: Type

  -- | The push branch function is called when an intrinsic value is
  --   passed through a symbolic branch.  This allows it to do any
  --   necessary bookkeeping to prepare for an upcoming merge.
  --   A push branch should eventually be followed by a matching
  --   abort or mux call.
  pushBranchIntrinsic
               :: sym
               -> IntrinsicTypes sym
               -> SymbolRepr nm
               -> CtxRepr ctx
               -> Intrinsic sym nm ctx
               -> IO (Intrinsic sym nm ctx)
  pushBranchIntrinsic _ _ _ _ = return

  -- | The abort branch function is called when an intrinsic value
  --   reaches a merge point, but the sibling branch has aborted.
  abortBranchIntrinsic
               :: sym
               -> IntrinsicTypes sym
               -> SymbolRepr nm
               -> CtxRepr ctx
               -> Intrinsic sym nm ctx
               -> IO (Intrinsic sym nm ctx)
  abortBranchIntrinsic _ _ _ _ = return

  -- | The `muxIntrinsic` method defines the if-then-else operation that is used
  --   when paths are merged in the simulator and intrinsic types need to be used.
  muxIntrinsic :: sym
               -> IntrinsicTypes sym
               -> SymbolRepr nm
               -> CtxRepr ctx
               -> Pred sym
               -> Intrinsic sym nm ctx
               -> Intrinsic sym nm ctx
               -> IO (Intrinsic sym nm ctx)

-- | Sometimes it is convenient to provide a 'CrucibleType' as the type
-- argument to 'Intrinsic', rather than the symbol and context. If you
-- accidentally supply a non-'IntrinsicType' type, this family will be stuck.
type family GetIntrinsic sym ity where
  GetIntrinsic sym (IntrinsicType nm ctx) = Intrinsic sym nm ctx
  GetIntrinsic sym x = TL.TypeError
    (        ('TL.Text "Type mismatch:")
    'TL.:$$: ('TL.Text "  Expected ‘IntrinsicType a b’")
    'TL.:$$: ('TL.Text "  Actual " 'TL.:<>: 'TL.ShowType x)
    'TL.:$$: ('TL.Text "In type family application ‘GetIntrinsic (" 'TL.:<>: 'TL.ShowType sym 'TL.:<>: 'TL.Text ") (" 'TL.:<>: 'TL.ShowType x 'TL.:<>: 'TL.Text ")’")
    )

-- | The `IntrinsicMuxFn` datatype allows an `IntrinsicClass` instance
--   to be packaged up into a value.  This allows us to get access to 'IntrinsicClass'
--   instance methods (the `muxIntrinsic` method in particular) at runtime even
--   for symbol names that are not known statically.
--
--   By packaging up a type class instance (rather than just providing some method with the
--   same signature as `muxIntrinsic`) we get the compiler to ensure that a single
--   distinguished implementation is always used for each backend/symbol name combination.
--   This prevents any possible confusion between different parts of the system.
data IntrinsicMuxFn (sym :: Type) (nm :: Symbol) where
  IntrinsicMuxFn :: IntrinsicClass sym nm => IntrinsicMuxFn sym nm


-- | `IntrinsicTypes` is a map from symbol name representatives to `IntrinsicMuxFn`
--    values.  Such a map is useful for providing access to intrinsic type implementations
--   that are not known statically at compile time.
type IntrinsicTypes sym = MapF.MapF SymbolRepr (IntrinsicMuxFn sym)

-- | An empty collection of intrinsic types, for cases where no additional types are required
emptyIntrinsicTypes :: IntrinsicTypes sym
emptyIntrinsicTypes = MapF.empty

-- | Utility function for reporting errors when improper Crucible type arguments
--   are applied to an intrinsic type symbol.
typeError :: HasCallStack => SymbolRepr nm -> CtxRepr ctx -> b
typeError nm ctx =
  panic "Crucible type error"
        [ "Named type constructor '" ++ show nm ++ "' applied to incorrect arguments:"
        , show ctx
        ]
