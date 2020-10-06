module RealMain (main) where

import System.Exit
import CruxLLVMMain (mainWithOutputConfig, defaultOutputConfig)

main :: IO ()
main = mainWithOutputConfig defaultOutputConfig >>= exitWith
