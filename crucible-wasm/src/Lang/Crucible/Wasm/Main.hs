{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.Wasm.Main where

import System.Exit
import System.FilePath (takeExtension)
import System.IO

import qualified Data.ByteString.Lazy as LBS

import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.Simulator
import Lang.Crucible.FunctionHandle

import Lang.Crucible.LLVM.MemModel

import qualified Crux
import           Crux.Config.Common (CruxOptions(..), OutputOptions)
import qualified Crux.Log as Log
import qualified Crux.Types

import qualified Language.Wasm as Wasm

import Lang.Crucible.Wasm
import Paths_crucible_wasm (version)

data WasmOptions = WasmOptions

defaultWasmOptions :: WasmOptions
defaultWasmOptions = WasmOptions

cruxWasmConfig :: Crux.Config WasmOptions
cruxWasmConfig = Crux.Config
  { Crux.cfgFile = pure defaultWasmOptions
  , Crux.cfgEnv  = []
  , Crux.cfgCmdLineFlag = []
  }

setupWasmState :: (IsSymBackend sym bak) =>
  bak -> MemOptions -> Wasm.Script -> IO (ExecState (Crux.Crux sym) sym WasmExt (RegEntry sym UnitType))
setupWasmState bak memOptions s =
  do halloc <- newHandleAllocator

     let ?recordLLVMAnnotation = \_ _ _ -> pure ()
     let ?memOpts = memOptions
     let globals = emptyGlobals
     let bindings = emptyHandleMap
     let simctx = initSimContext bak wasmIntrinsicTypes halloc stdout (FnBindings bindings) (extImpl memOptions) Crux.CruxPersonality
     let m = execScript s emptyScriptState >> pure ()

     pure (InitialState simctx globals defaultAbortHandler knownRepr (runOverrideSim knownRepr m))

simulateWasm ::
  Crux.CruxOptions ->
  WasmOptions ->
  Crux.SimulatorCallbacks msgs st Crux.Types.CruxSimulationResult
simulateWasm cruxOpts _wasmOpts =
  Crux.SimulatorCallbacks $
    return $
      Crux.SimulatorHooks
        { Crux.setupHook =
            \bak _mOnline ->
              do let files = Crux.inputFiles cruxOpts

                 fl <- case files of
                         [fl] -> return fl
                         _ -> fail "crux-wasm requires one script file"

                 script <- parseWasmFile fl
                 initSt <- setupWasmState bak defaultMemOptions script

                 return (Crux.RunnableState initSt)
        , Crux.onErrorHook = \_bak -> return (\_ _ -> return mempty)
        , Crux.resultHook = \_bak result -> return result
        }

-- | Parse the contents of a WebAssembly file according to its file extension.
parseWasmFile :: FilePath -> IO Wasm.Script
parseWasmFile fl =
  do escript <- parse <$> LBS.readFile fl
     case escript of
       Left msg -> fail msg
       Right s -> return s
  where
    ext :: String
    ext = takeExtension fl

    -- Convert a module from a .wasm or .wat file into a script, which is the
    -- format that crucible-wasm analyzes.
    moduleToScript :: Wasm.Module -> Wasm.Script
    moduleToScript m = [Wasm.ModuleDef (Wasm.RawModDef Nothing m)]

    parse :: LBS.ByteString -> Either String Wasm.Script
    parse flContents
        -- .wasm is for binary files
      | ext == ".wasm"
      = moduleToScript <$> Wasm.decodeLazy flContents

        -- .wat is for the textual syntax
      | ext == ".wat"
      = moduleToScript <$> Wasm.parse flContents

        -- For everything else (e.g., .wast), we use the WebAssembly
        -- script syntax, which is a strict superset of the textual syntax
        -- in .wasm and .wat files.
      | otherwise
      = Wasm.parseScript flContents

mainWithOptions ::
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  (CruxOptions, WasmOptions) -> IO ExitCode
mainWithOptions (cruxOpts, wasmOpts) =
  do res <- Crux.runSimulator cruxOpts (simulateWasm cruxOpts wasmOpts)
     Crux.postprocessSimResult True cruxOpts res

mainWithOutputConfig ::
  (Maybe OutputOptions -> Crux.OutputConfig Log.CruxLogMessage) ->
  IO ExitCode
mainWithOutputConfig mkOutCfg =
  Crux.withCruxLogMessage $ do
    Crux.loadOptions mkOutCfg "crucible-wasm" version cruxWasmConfig mainWithOptions

main :: IO ()
main = do
  exitWith =<<
    mainWithOutputConfig =<<
      Crux.defaultOutputConfig Crux.cruxLogMessageToSayWhat
