{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.MIR.CLI
  ( withMirHooks
  ) where

import Lang.Crucible.Backend (IsSymBackend)
import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.CLI as CLI

import Lang.Crucible.Syntax.Concrete (ParserHooks)

import Mir.Intrinsics (MIR)
import qualified Mir.Intrinsics as Mir

import Lang.Crucible.MIR.Syntax (emptyParserHooks, mirParserHooks)

-- | Small helper for providing MIR language-specific hooks, e.g., for use with
-- 'Lang.Crucible.CLI.execCommand'.
withMirHooks ::
  ( (?parserHooks :: ParserHooks MIR) =>
    (forall p sym bak. IsSymBackend sym bak => bak -> IO (CLI.ExtensionSetup p sym MIR)) ->
    CLI.SimulateProgramHooks MIR ->
    IO a) ->
  IO a
withMirHooks k = do
  let ?parserHooks = mirParserHooks emptyParserHooks
  let simulationHooks = CLI.defaultSimulateProgramHooks
  let ext _ =
        pure CLI.ExtensionSetup
          { CLI.extImpl = Mir.mirExtImpl
          , CLI.extIntrinsicTypes = Mir.mirIntrinsicTypes
          , CLI.extInitGlobals = C.emptyGlobals
          }
  k ext simulationHooks
