module RealMain (main) where

import System.Exit
import CruxLLVMMain (mainWithOutputConfig, defaultOutputConfig)

main :: IO ()
main =
  do ec <- mainWithOutputConfig =<< defaultOutputConfig
     exitWith ec
