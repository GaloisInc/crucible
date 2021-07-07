{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Crux (OutputConfig)
import qualified Crux
import Crux.Config.Common (CruxOptions)
import Crux.LLVM.Config (LLVMOptions, llvmCruxConfig)
import CruxLLVMMain
  ( CruxLLVMLogging,
    mainWithOptions,
    withCruxLLVMLogging,
  )
import qualified Data.Aeson as JSON
import qualified Lumberjack as LJ
import qualified Network.WebSockets as WS
import Paths_crux_llvm (version)
import RealMain (makeMain)
import System.Exit (ExitCode)

data ForIDEOptions = ForIDEOptions
  { cruxLLVMOptions :: LLVMOptions,
    ideHost :: String,
    idePort :: Int
  }

forIDEConfig :: IO (Crux.Config ForIDEOptions)
forIDEConfig = do
  llvmOpts <- llvmCruxConfig
  return
    Crux.Config
      { Crux.cfgFile =
          ForIDEOptions
            <$> Crux.cfgFile llvmOpts
            <*> Crux.section
              "ide-host"
              Crux.stringSpec
              "127.0.0.1"
              "Host where the IDE is listening"
            <*> Crux.section
              "ide-port"
              Crux.numSpec
              0
              "Port at which the IDE is listening",
        Crux.cfgEnv = [],
        Crux.cfgCmdLineFlag = []
      }

mainWithOutputConfig ::
  (Maybe CruxOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode
mainWithOutputConfig mkOutCfg =
  CruxLLVMMain.withCruxLLVMLogging $
    do
      conf <- forIDEConfig
      Crux.loadOptions mkOutCfg "crux-llvm-for-ide" version conf $ \(cruxOpts, forIDEOpts) ->
        WS.runClient (ideHost forIDEOpts) (idePort forIDEOpts) "/" $ \conn ->
          do
            let ?outputConfig =
                  ?outputConfig
                    { Crux._logMsg =
                        Crux._logMsg ?outputConfig
                          <> LJ.LogAction (WS.sendTextData conn . JSON.encode)
                    }
            mainWithOptions (cruxOpts, cruxLLVMOptions forIDEOpts)

main :: IO ()
main = makeMain mainWithOutputConfig
