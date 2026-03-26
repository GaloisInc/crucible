{-# LANGUAGE ImplicitParams #-}

module Main (main) where

import Lang.Crucible.Simulator.ExecutionTree (emptyExtensionImpl)

import Lang.Crucible.Syntax.Concrete (defaultParserHooks)

import qualified Lang.Crucible.CLI as CLI
import qualified Lang.Crucible.CLI.Options as Opts

main :: IO ()
main = do
  let ?parserHooks = defaultParserHooks
  let ext = \_ -> pure (CLI.defaultExtensionSetup emptyExtensionImpl)
  Opts.main "crucible" ext CLI.defaultSimulateProgramHooks
