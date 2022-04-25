module RealMain (makeMain) where

import Crux.Log ( OutputConfig )
import Crux.Config.Common (OutputOptions)
import CruxLLVMMain ( CruxLLVMLogging, defaultOutputConfig )
import System.Exit (ExitCode, exitWith)

makeMain ::
  ((Maybe OutputOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode) ->
  IO ()
makeMain mainWithOutputConfig =
  do
    ec <- mainWithOutputConfig =<< defaultOutputConfig
    exitWith ec
