module RealMain (makeMain) where

import CruxLLVMMain (defaultOutputConfig, mainWithOutputConfig)
import System.Exit

makeMain ::
  ((Maybe CruxOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode) ->
  IO ()
makeMain mainWithOutputConfig =
  mainWithOutputConfig defaultOutputConfig >>= exitWith
