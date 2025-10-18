-- | Command line interface to crucible-go
{-# Language FlexibleInstances #-}
{-# Language ImplicitParams #-}
{-# Language MultiParamTypeClasses #-}
{-# Language OverloadedStrings #-}

module Main (main) where

import qualified Control.Lens as Lens
import qualified Data.ByteString.Lazy as BS
import Data.Void (Void)
import System.Exit (exitWith)

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

-- crucible/crucible
import Lang.Crucible.Simulator
import qualified Lang.Crucible.Debug as Debug
import qualified Lang.Crucible.Types as CT

-- crux
import qualified Crux
import qualified Crux.Config.Common as Crux
import qualified Crux.Types as Crux (CruxSimulationResult)

-- Go
import Language.Go.Parser
import Lang.Crucible.Go.Simulate (setupCrucibleGoCrux)
import Lang.Crucible.Go.Types
import Paths_crucible_go (version)

data GoOptions = GoOptions { }

defaultOptions :: GoOptions
defaultOptions = GoOptions { }

cruxGoConfig :: Crux.Config GoOptions
cruxGoConfig = Crux.Config
  { Crux.cfgFile = pure defaultOptions
  , Crux.cfgEnv = []
  , Crux.cfgCmdLineFlag = []
  }

-- | Personality (see
-- 'Lang.Crucible.Simulator.ExecutionTree.cruciblePersonality')
newtype Personality sym
  = Personality { getPersonality :: Debug.Context Void sym Go CT.UnitType }

instance Debug.HasContext (Personality sym) Void sym Go CT.UnitType where
  context = Lens.lens getPersonality (const Personality)
  {-# INLINE context #-}

simulateGo ::
  Crux.CruxOptions ->
  GoOptions ->
  Crux.SimulatorCallbacks msgs st Crux.CruxSimulationResult
simulateGo copts _opts =
  Crux.SimulatorCallbacks $
    return $
      Crux.SimulatorHooks
        { Crux.setupHook =
            \sym _maybeOnline -> do
              let files = Crux.inputFiles copts
              let verbosity = Crux.simVerbose (Crux.outputOptions copts)
              file <- case files of
                        [f] -> return f
                        _ -> fail "crux-go requires a single file name as an argument"

              -- Load the file
              json <- BS.readFile file
              let fwi = either error id $ parseMain json

              -- Initialize arguments to the function
              let regmap = RegMap Ctx.Empty

              let cExts = Debug.voidExts
              inps <- Debug.defaultDebuggerInputs cExts
              dbgCtx <-
                Debug.initCtx
                  cExts
                  (Debug.IntrinsicPrinters MapF.empty)
                  inps
                  Debug.defaultDebuggerOutputs
                  CT.UnitRepr
              let p = Personality dbgCtx

              -- Set up initial crucible execution state
              Crux.RunnableState <$>
                setupCrucibleGoCrux 32 fwi verbosity sym p regmap

        -- TODO add failure explanations
        , Crux.onErrorHook = \_sym -> return (\_ _ -> return mempty)
        , Crux.resultHook = \_sym result -> return result
        }


-- | Entry point, parse command line options
main :: IO ()
main = do
  mkOutCfg <- Crux.defaultOutputConfig Crux.cruxLogMessageToSayWhat
  Crux.withCruxLogMessage $
    Crux.loadOptions mkOutCfg "crux-go" version cruxGoConfig
      $ \(cruxOpts, goOpts) ->
        exitWith =<< Crux.postprocessSimResult True cruxOpts =<<
          Crux.runSimulator (cruxOpts { Crux.outDir = "report"
                                      , Crux.skipReport = False })
          (simulateGo cruxOpts goOpts)
