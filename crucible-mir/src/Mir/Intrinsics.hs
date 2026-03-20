{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Mir.Intrinsics
  ( module Mir.Intrinsics,
    module Mir.Intrinsics.Aggregate,
    module Mir.Intrinsics.Array,
    module Mir.Intrinsics.Dyn,
    module Mir.Intrinsics.Enum,
    module Mir.Intrinsics.MethodSpec,
    module Mir.Intrinsics.Reference,
    module Mir.Intrinsics.Size,
    module Mir.Intrinsics.Slice,
    module Mir.Intrinsics.Syntax,
    module Mir.Intrinsics.Vector,
  )
where

import qualified Data.Parameterized.Map as MapF

import           Lang.Crucible.Backend
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree hiding (FnState)
import           Lang.Crucible.Simulator.Intrinsics

import           Mir.Intrinsics.Aggregate
import           Mir.Intrinsics.Array
import           Mir.Intrinsics.Dyn
import           Mir.Intrinsics.Enum
import           Mir.Intrinsics.MethodSpec
import           Mir.Intrinsics.Reference
import           Mir.Intrinsics.Size
import           Mir.Intrinsics.Slice
import           Mir.Intrinsics.Syntax
import           Mir.Intrinsics.Vector


mirExtImpl :: forall sym p. IsSymInterface sym => ExtensionImpl p sym MIR
mirExtImpl = ExtensionImpl
             { extensionEval = \_sym _iTypes _log _f _state -> \case
             , extensionExec = execMirStmt
             }

-- Table of all MIR-specific intrinsic types.  Must be at the end so it can see
-- past all previous TH calls.

mirIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
mirIntrinsicTypes =
   MapF.insert (knownSymbol @MirReferenceSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MirAggregateSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MethodSpecSymbol) IntrinsicMuxFn $
   MapF.insert (knownSymbol @MethodSpecBuilderSymbol) IntrinsicMuxFn $
   MapF.empty
