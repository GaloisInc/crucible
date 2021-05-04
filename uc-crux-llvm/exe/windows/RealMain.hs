module RealMain (main) where

import System.Exit
import UCCrux.LLVM.Main (defaultOutputConfig, mainWithOutputConfig)

main :: IO ()
main = mainWithOutputConfig defaultOutputConfig >>= exitWith
