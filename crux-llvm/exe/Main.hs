module Main (main) where

import Control.Monad
import System.Exit
import System.Posix.Signals
import System.Posix.Process

import CruxLLVMMain (mainWithOutputConfig, defaultOutputConfig)

-- Convert a SIGTERM signal into a SIGINT signal for the entire process group
installSIGTERMHandler :: IO ()
installSIGTERMHandler =
  do gid <- getProcessGroupID
     void $ installHandler sigTERM (CatchOnce (handler gid)) Nothing
 where
 handler gid = signalProcessGroup sigINT gid


main :: IO ()
main =
  do installSIGTERMHandler
     ec <- mainWithOutputConfig defaultOutputConfig
     exitWith ec
