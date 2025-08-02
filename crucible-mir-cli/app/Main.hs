module Main (main) where

import qualified Lang.Crucible.CLI.Options as Opts

import Lang.Crucible.MIR.CLI (withMirHooks)

main :: IO ()
main = withMirHooks (Opts.main "crucible-mir")
