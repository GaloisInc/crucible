module RealMain (main) where

import System.Exit
import UCCrux.LLVM.Main (defaultOutputConfig, mainWithOutputConfig)

main :: IO ()
main =
  do
    ec <- mainWithOutputConfig =<< defaultOutputConfig
    exitWith ec
