{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.MIR.CLI
  ( withMirHooks
  ) where

import qualified Control.Lens as Lens

import qualified Data.Parameterized.Map as MapF

import Lang.Crucible.Backend (IsSymBackend)
import Lang.Crucible.Simulator.ExecutionTree (ExtensionImpl)
import qualified Lang.Crucible.Simulator as C

import Lang.Crucible.CLI (SimulateProgramHooks(..), defaultSimulateProgramHooks)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Mir.Intrinsics (MIR)
import qualified Mir.Intrinsics as Mir

import Lang.Crucible.MIR.Syntax (emptyParserHooks, mirParserHooks)

-- | Small helper for providing MIR language-specific hooks, e.g., for use with
-- 'Lang.Crucible.CLI.execCommand'.
withMirHooks ::
  ( (?parserHooks :: ParserHooks MIR) =>
    (forall sym bak. IsSymBackend sym bak => bak -> IO (ExtensionImpl () sym MIR)) ->
    SimulateProgramHooks MIR ->
    IO a) ->
  IO a
withMirHooks k = do
  let ?parserHooks = mirParserHooks emptyParserHooks
  let simulationHooks =
        defaultSimulateProgramHooks
          { setupHook = \_bak _ha _fds -> do
              let addIntrinsicTypes types ctx =
                    ctx { C.ctxIntrinsicTypes = MapF.union (C.ctxIntrinsicTypes ctx) types }
              C.stateContext Lens.%= addIntrinsicTypes Mir.mirIntrinsicTypes
          , setupOverridesHook = setupOverrides
          }
  let ext _ = pure Mir.mirExtImpl
  k ext simulationHooks
