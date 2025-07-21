-- | Command line interface to crucible-go
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}

module Main where

import qualified Data.ByteString.Lazy as BS

import System.Exit (exitWith)

import qualified Data.Parameterized.Context as Ctx

-- crucible/crucible
import Lang.Crucible.Simulator

-- crux
import qualified Crux
import qualified Crux.Config.Common as Crux
import qualified Crux.Types as Crux (CruxSimulationResult)

-- Go
import Language.Go.Parser
import Lang.Crucible.Go.Simulate (setupCrucibleGoCrux)
import Lang.Crucible.Go.Types
import Paths_crucible_go (version)

-- | A simulator context
type SimCtxt sym = SimContext (Crux.Crux sym) sym Go

data GoOptions = GoOptions { }

defaultOptions :: GoOptions
defaultOptions = GoOptions { }

cruxGoConfig :: Crux.Config GoOptions
cruxGoConfig = Crux.Config
  { Crux.cfgFile = pure defaultOptions
  , Crux.cfgEnv = []
  , Crux.cfgCmdLineFlag = []
  }

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

              -- Set up initial crucible execution state
              Crux.RunnableState <$>
                setupCrucibleGoCrux 32 fwi verbosity sym Crux.CruxPersonality regmap

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
