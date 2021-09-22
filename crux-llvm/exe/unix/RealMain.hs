module RealMain (main) where

import Control.Monad
import System.Exit
import System.Posix.Signals
import System.Posix.Process

import CruxLLVMMain (mainWithOutputConfig, defaultOutputConfig)

-- Rebroadcast SIGTERM to the entire process group.  The CatchOnce
-- handler keeps this from handling and retransmitting SIGTERM to
-- itself over and over.
installSIGTERMHandler :: IO ()
installSIGTERMHandler =
  do gid <- getProcessGroupID
     void $ installHandler sigTERM (CatchOnce (handler gid)) Nothing
 where
 handler gid = signalProcessGroup sigTERM gid


main :: IO ()
main =
  do installSIGTERMHandler
     ec <- mainWithOutputConfig =<< defaultOutputConfig
     exitWith ec
