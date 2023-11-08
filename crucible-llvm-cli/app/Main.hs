module Main (main) where

import qualified Lang.Crucible.CLI.Options as Opts

import Lang.Crucible.LLVM.CLI (withLlvmHooks)

main :: IO ()
main = withLlvmHooks (Opts.main "crucible-llvm")
