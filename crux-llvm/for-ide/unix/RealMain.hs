module RealMain (makeMain) where

import Control.Monad (void)
import Crux.Log ( OutputConfig )
import Crux.Config.Common (CruxOptions)
import CruxLLVMMain ( CruxLLVMLogging, defaultOutputConfig )
import System.Exit (ExitCode, exitWith)
import System.Posix.Process (getProcessGroupID)
import System.Posix.Signals
  ( Handler (CatchOnce),
    installHandler,
    sigTERM,
    signalProcessGroup,
  )

-- Rebroadcast SIGTERM to the entire process group.  The CatchOnce
-- handler keeps this from handling and retransmitting SIGTERM to
-- itself over and over.
installSIGTERMHandler :: IO ()
installSIGTERMHandler =
  do
    gid <- getProcessGroupID
    void $ installHandler sigTERM (CatchOnce (handler gid)) Nothing
  where
    handler gid = signalProcessGroup sigTERM gid

makeMain ::
  ((Maybe CruxOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode) ->
  IO ()
makeMain mainWithOutputConfig =
  do
    installSIGTERMHandler
    ec <- mainWithOutputConfig defaultOutputConfig
    exitWith ec
