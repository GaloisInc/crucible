{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Exit
import System.IO

import qualified Data.ByteString.Lazy as LBS

import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.Simulator
import Lang.Crucible.FunctionHandle

import qualified Crux
import qualified Crux.Model as Crux
import qualified Crux.Types as Crux

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

setupWasmState :: IsSymInterface sym =>
  sym -> Wasm.Script -> IO (ExecState (Crux.Model sym) sym WasmExt (RegEntry sym UnitType))
setupWasmState sym s =
  do halloc <- newHandleAllocator

     let globals = emptyGlobals
     let bindings = emptyHandleMap
     let simctx = initSimContext sym wasmIntrinsicTypes halloc stdout (FnBindings bindings) extImpl Crux.emptyModel
     let m = execScript s emptyScriptState >> pure ()

     pure (InitialState simctx globals defaultAbortHandler knownRepr (runOverrideSim knownRepr m))

simulateWasm :: Crux.CruxOptions -> WasmOptions -> Crux.SimulatorCallback
simulateWasm cruxOpts _wasmOpts = Crux.SimulatorCallback $ \sym _mOnline ->
   do let files = Crux.inputFiles cruxOpts

      fl <- case files of
              [fl] -> return fl
              _ -> fail "crux-wasm requires one script file"

      script <-
        do escript <- Wasm.parseScript <$> LBS.readFile fl
           case escript of
             Left msg -> fail msg
             Right s -> return s

      initSt <- setupWasmState sym script

      return (Crux.RunnableState initSt, \_ _ -> return mempty)

main :: IO ()
main =
  Crux.loadOptions Crux.defaultOutputConfig "crux-wasm" version cruxWasmConfig
   \(cruxOpts, wasmOpts) ->
       do res <- Crux.runSimulator cruxOpts (simulateWasm cruxOpts wasmOpts)
          exitWith =<< Crux.postprocessSimResult cruxOpts res
