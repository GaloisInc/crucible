{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug.Override
  ( debugOverride
  ) where

import Control.Lens qualified as Lens
import Data.Parameterized.Context qualified as Ctx
import Lang.Crucible.Debug.Personality qualified as Pers
import Lang.Crucible.Debug.Personality (HasContext)
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.OverrideSim qualified as C
import Lang.Crucible.Types qualified as CT

-- | An override that stops the debugger at this location
debugOverride ::
  HasContext p cExt sym ext t =>
  C.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> CT.UnitType) CT.UnitType
debugOverride =
  C.TypedOverride
  { C.typedOverrideArgs = CT.knownRepr
  , C.typedOverrideRet = CT.knownRepr
  , C.typedOverrideHandler = \_args -> C.stateContext Lens.%= Pers.stop
  }
