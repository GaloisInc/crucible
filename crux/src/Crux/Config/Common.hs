{-# Language RecordWildCards, OverloadedStrings, ApplicativeDo #-}
module Crux.Config.Common (CruxOptions(..), PathStrategy(..), cruxOptions, postprocessOptions) where

import Data.Functor.Alt
import Data.Time(NominalDiffTime)
import Data.Maybe(fromMaybe)
import Data.Char(toLower)
import Text.Read(readMaybe)

import Crux.Config
import Crux.Log
import Config.Schema

data PathStrategy
  = AlwaysMergePaths
  | SplitAndExploreDepthFirst

pathStrategySpec :: ValueSpec PathStrategy
pathStrategySpec =
  (AlwaysMergePaths <$ atomSpec "always-merge") <!>
  (SplitAndExploreDepthFirst <$ atomSpec "split-dfs")


postprocessOptions :: Logs => CruxOptions -> IO CruxOptions
postprocessOptions =
  checkPathStrategyInteractions

checkPathStrategyInteractions :: Logs => CruxOptions -> IO CruxOptions
checkPathStrategyInteractions crux =
  case pathStrategy crux of
    AlwaysMergePaths -> return crux
    SplitAndExploreDepthFirst
     | profileCrucibleFunctions crux ->
         do sayWarn "Crux" "Path splitting strategies are incompatible with Crucible profiling. Profiling is disabled!"
            return crux{ profileCrucibleFunctions = False }
     | otherwise -> return crux


-- | Common options for Crux-based binaries.
data CruxOptions = CruxOptions
  { inputFiles              :: [FilePath]
    -- ^ the files to analyze

  , outDir                  :: FilePath
    -- ^ Write results in this location.
    -- If empty, then do not produce any analysis results.

  , checkPathSat             :: Bool
    -- ^ Should we enable path satisfiability checking?

  , profileCrucibleFunctions :: Bool
  , profileSolver            :: Bool

  , pathStrategy             :: PathStrategy

  , globalTimeout            :: Maybe NominalDiffTime
  , goalTimeout              :: Integer
  , profileOutputInterval    :: NominalDiffTime
  , loopBound                :: Maybe Int
    -- ^ Should we artifically bound the number of loop iterations

  , makeCexes                :: Bool
    -- ^ Should we construct counter-example executables

  , simVerbose               :: Int

  , solver                   :: String
    -- ^ Solver to user for the online backend

  , yicesMCSat               :: Bool
    -- ^ Should the MC-SAT Yices solver be enabled (disables unsat cores; default: no)
  }


cruxOptions :: Config CruxOptions
cruxOptions = Config
  { cfgFile =
       do inputFiles <-
            section "files" (oneOrList fileSpec) []
            "Input files to process."

          outDir <-
            section "output-directory" dirSpec ""
            "Save results in this directory."


          checkPathSat <-
            section "path-sat" yesOrNoSpec False
            "Enable path satisfiability checking (default: no)."


          profileCrucibleFunctions <-
            section "profile-crucible" yesOrNoSpec False
            "Profile crucible function entry/exit. (default: no)"

          profileSolver <-
            section "profile-solver" yesOrNoSpec False
            "Profile solver events. (default: no)"

          profileOutputInterval <-
            section "profiling-period" fractionalSpec 5
            "Time between intermediate profile data reports (default: 5 seconds)"

          globalTimeout <-
            sectionMaybe "timeout" fractionalSpec
            "Stop executing the simulator after this many seconds."

          goalTimeout <-
            section "goal-timeout" numSpec 10
            "Stop trying to prove a goal after this many seconds. (default: 10, 0 for none)"

          loopBound <-
            sectionMaybe "iteration-bound" numSpec
            "Bound all loops to at most this many iterations."

          pathStrategy <-
            section "path-strategy" pathStrategySpec AlwaysMergePaths
            "Simulator strategy for path exploration."

          makeCexes <-
            section "make-executables" yesOrNoSpec True
            "Should we generate counter-example executables. (default: yes)"


          solver <-
            section "solver" stringSpec "yices"
            "Select solver to use. (default: \"yices\")"

          simVerbose <-
            section "sim-verbose" numSpec 1
            "Verbosity of simulators. (default: 1)"

          yicesMCSat <-
            section "mcsat" yesOrNoSpec False
            "Enable the MC-SAT solver in Yices (disables unsat cores) (default: no)"

          pure CruxOptions { .. }



  , cfgEnv = []

  , cfgCmdLineFlag =

      [ Option "d" ["sim-verbose"]
        "Set simulator verbosity level."
        $ ReqArg "NUM" $ parsePosNum "NUM" $ \v opts -> opts { simVerbose = v }

      , Option [] ["path-sat"]
        "Enable path satisfiability checking"
        $ NoArg $ \opts -> Right opts { checkPathSat = True }

      , Option [] ["output-directory"]
        "Location for reports. If unset, no reports will be generated."
        $ ReqArg "DIR" $ \v opts -> Right opts { outDir = v }

      , Option [] ["profile-crucible"]
        "Enable profiling of crucible function entry/exit"
        $ NoArg $ \opts -> Right opts { profileCrucibleFunctions = True }

      , Option [] ["profile-solver"]
        "Enable profiling of solver events"
        $ NoArg $ \opts -> Right opts { profileSolver = True }

      , Option "t" ["timeout"]
        "Stop executing the simulator after this many seconds (default: 60)"
        $ OptArg "seconds"
        $ dflt "60"
        $ parseNominalDiffTime "seconds"
        $ \v opts -> opts { globalTimeout = Just v }

      , Option [] ["goal-timeout"]
        "Stop trying to prove each goal after this many seconds."
        $ ReqArg "seconds"
        $ parsePosNum "seconds"
        $ \v opts -> opts { goalTimeout = v }

      , Option "" ["path-strategy"]
        "Strategy to use for exploring paths ('always-merge' or 'split-dfs')"
        $ ReqArg "strategy"
        $ parsePathStrategy
        $ \strat opts -> opts{ pathStrategy = strat }

      , Option "p" ["profiling-period"]
        "Time between intermediate profile data reports (default: 5 seconds)"
        $ OptArg "seconds"
        $ dflt "5"
        $ parseNominalDiffTime "seconds"
        $ \v opts -> opts { profileOutputInterval = v }

      , Option "i" ["iteration-bound"]
        "Bound all loops to at most this many iterations"
        $ ReqArg "iterations"
        $ parsePosNum "iterations"
        $ \v opts -> opts { loopBound = Just v }

      , Option "x" ["no-execs"]
        "Disable generating counter-example executables"
        $ NoArg $ \opts -> Right opts { makeCexes = False }

      , Option "s" ["solver"]
        "Select solver to use"
        $ ReqArg "solver" $ \v opts -> Right opts { solver = map toLower v }

      , Option [] ["mcsat"]
        "Enable the MC-SAT solver in Yices (disables unsat cores)"
        $ NoArg $ \opts -> Right opts { yicesMCSat = True }
      ]
  }

dflt :: String -> (String -> OptSetter opts) -> (Maybe String -> OptSetter opts)
dflt x p mb = p (fromMaybe x mb)


parsePosNum :: (Read a, Num a, Ord a) =>
  String -> (a -> opts -> opts) -> String -> OptSetter opts
parsePosNum thing mk = \txt opts ->
  case readMaybe txt of
    Just a | a >= 0 -> Right (mk a opts)
    _ -> Left ("Invalid " ++ thing)


parseNominalDiffTime ::
  String -> (NominalDiffTime -> opts -> opts) -> String -> OptSetter opts
parseNominalDiffTime thing mk =
  parsePosNum thing (\a opts -> mk (cvt a) opts)
  where cvt :: Double -> NominalDiffTime
        cvt = fromRational . toRational

parsePathStrategy ::
  (PathStrategy -> opts -> opts) -> String -> OptSetter opts
parsePathStrategy mk "always-merge" opts = Right $ mk AlwaysMergePaths opts
parsePathStrategy mk "split-dfs"    opts = Right $ mk SplitAndExploreDepthFirst opts
parsePathStrategy _mk nm _opts = Left ("Unknown path strategy: " ++ show nm)
