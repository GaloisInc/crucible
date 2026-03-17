{-# LANGUAGE ImplicitParams #-}

module Main (main) where

import Lang.Crucible.Simulator.ExecutionTree (emptyExtensionImpl)

import Lang.Crucible.Syntax.Concrete (defaultParserHooks)

import Lang.Crucible.CLI (defaultSimulateProgramHooks)
import qualified Lang.Crucible.CLI.Options as Opts

main :: IO ()
main =
  do let ?parserHooks = defaultParserHooks
     Opts.main "crucible" (\_ -> pure emptyExtensionImpl) defaultSimulateProgramHooks
