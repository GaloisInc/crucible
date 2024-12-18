{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main (main) where

import Control.Lens (makeLenses, set, view)
import Crux (OutputConfig)
import qualified Crux
import Crux.Config.Common (OutputOptions)
import Crux.LLVM.Config (LLVMOptions, llvmCruxConfig)
import CruxLLVMMain
  ( CruxLLVMLogging,
    mainWithOptions,
    withCruxLLVMLogging,
  )
import qualified Data.Aeson as JSON
import Data.Text as Text (Text, unpack)
import qualified Lumberjack as LJ
import qualified Network.WebSockets as WS
import Paths_crux_llvm (version)
import RealMain (makeMain)
import System.Exit (ExitCode)
import Text.Read (readEither)

data ForIDEOptions = ForIDEOptions
  { _cruxLLVMOptions :: LLVMOptions,
    _ideHost :: String,
    _idePort :: Int
  }

makeLenses ''ForIDEOptions

ideHostDoc :: Text
ideHostDoc = "Host where the IDE is listening"

idePortDoc :: Text
idePortDoc = "Port at which the IDE is listening"

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
              ideHostDoc
            <*> Crux.section
              "ide-port"
              Crux.numSpec
              0
              idePortDoc,
        Crux.cfgEnv = Crux.liftEnvDescr cruxLLVMOptions <$> Crux.cfgEnv llvmOpts,
        Crux.cfgCmdLineFlag =
          (Crux.liftOptDescr cruxLLVMOptions <$> Crux.cfgCmdLineFlag llvmOpts)
            ++ [ Crux.Option
                   []
                   ["ide-host"]
                   (Text.unpack ideHostDoc)
                   $ Crux.ReqArg "STR" $
                     \v opts -> Right (set ideHost v opts),
                 Crux.Option
                   []
                   ["ide-port"]
                   (Text.unpack idePortDoc)
                   $ Crux.ReqArg "INT" $
                     \v opts -> set idePort <$> readEither v <*> pure opts
               ]
      }

mainWithOutputConfig ::
  (Maybe OutputOptions -> OutputConfig CruxLLVMLogging) -> IO ExitCode
mainWithOutputConfig mkOutCfg =
  CruxLLVMMain.withCruxLLVMLogging $
    do
      conf <- forIDEConfig
      Crux.loadOptions mkOutCfg "crux-llvm-for-ide" version conf $ \(cruxOpts, forIDEOpts) ->
        WS.runClient (view ideHost forIDEOpts) (view idePort forIDEOpts) "/" $ \conn ->
          do
            let ?outputConfig =
                  ?outputConfig
                    { Crux._logMsg =
                        Crux._logMsg ?outputConfig
                          <> LJ.LogAction (WS.sendTextData conn . JSON.encode)
                    }
            mainWithOptions (cruxOpts, view cruxLLVMOptions forIDEOpts)

main :: IO ()
main = makeMain mainWithOutputConfig
