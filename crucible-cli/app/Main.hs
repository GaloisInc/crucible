{-# LANGUAGE ImplicitParams #-}

module Main (main) where

import Lang.Crucible.Simulator.ExecutionTree (emptyExtensionImpl)

import Lang.Crucible.Syntax.Concrete (defaultParserHooks)
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.CLI (SimulateProgramHooks(..), defaultSimulateProgramHooks)
import qualified Lang.Crucible.CLI.Options as Opts

main :: IO ()
main =
  do let ?parserHooks = defaultParserHooks
     Opts.main "crucible" (\_ -> emptyExtensionImpl) simulationHooks
  where
        simulationHooks =
          defaultSimulateProgramHooks
            { setupOverridesHook = setupOverrides
            }
