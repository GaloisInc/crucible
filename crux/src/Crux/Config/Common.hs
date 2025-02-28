{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module Crux.Config.Common (
  OutputOptions(..),
  CruxOptions(..),
  PathStrategy(..),
  cruxOptions,
  defaultOutputOptions,
  postprocessOptions,
) where

import Control.Lens (set)
import Data.Functor.Alt
import Data.Generics.Product.Fields (field)
import Data.Time(DiffTime, NominalDiffTime)
import Data.Maybe(fromMaybe)
import Data.Char(toLower)
import Data.Word (Word64)
import Data.Text (pack)
import GHC.Generics (Generic)
import System.Directory ( createDirectoryIfMissing )

import Crux.Config
import Crux.Config.Load (ColorOptions(..))
import Crux.Log as Log
import Config.Schema

import What4.ProblemFeatures

data PathStrategy
  = AlwaysMergePaths
  | SplitAndExploreDepthFirst

pathStrategySpec :: ValueSpec PathStrategy
pathStrategySpec =
  (AlwaysMergePaths <$ atomSpec "always-merge") <!>
  (SplitAndExploreDepthFirst <$ atomSpec "split-dfs")


postprocessOptions ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions -> IO CruxOptions
postprocessOptions =
  checkPathStrategyInteractions >>
  checkPathSatInteractions >>
  checkBldDir

checkPathStrategyInteractions ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions -> IO CruxOptions
checkPathStrategyInteractions crux =
  case pathStrategy crux of
    AlwaysMergePaths -> return crux
    SplitAndExploreDepthFirst
     | profileCrucibleFunctions crux || branchCoverage crux ->
         do sayCrux Log.DisablingProfilingIncompatibleWithPathSplitting
            return crux { profileCrucibleFunctions = False, branchCoverage = False }
     | otherwise -> return crux

checkPathSatInteractions ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions -> IO CruxOptions
checkPathSatInteractions crux =
  case checkPathSat crux of
    True -> return crux
    False
      | branchCoverage crux ->
          do sayCrux Log.DisablingBranchCoverageRequiresPathSatisfiability
             return crux { branchCoverage = False }
      | otherwise -> return crux

checkBldDir :: CruxOptions -> IO CruxOptions
checkBldDir crux = do
  createDirectoryIfMissing True $ bldDir crux
  return crux


data OutputOptions = OutputOptions
  { colorOptions :: ColorOptions

  , printFailures :: Bool
    -- ^ Print errors regarding failed verification goals

  , printSymbolicVars :: Bool
    -- ^ Print values assigned to symbolic variables
    --   when printing failed verification goals

  , simVerbose :: Int
    -- ^ Level of verbosity for the symbolic simulation

  , quietMode :: Bool
    -- ^ If true, produce minimal output

  }
  deriving (Generic)


defaultOutputOptions :: ColorOptions -> OutputOptions
defaultOutputOptions copts = OutputOptions
  { colorOptions = copts
  , printFailures = False
  , printSymbolicVars = False
  , quietMode = False
  , simVerbose = 0
  }


-- | Common options for Crux-based binaries.
data CruxOptions = CruxOptions
  { inputFiles              :: [FilePath]
    -- ^ the files to analyze

  , outDir                  :: FilePath
    -- ^ Write results in this location.
    -- If empty, then do not produce any analysis results.

  , bldDir     :: FilePath
    -- ^ Directory for writing files generated from the inputFiles set
    -- (e.g. building C sources into LLVM bitcode files) for analysis.

  , checkPathSat             :: Bool
    -- ^ Should we enable path satisfiability checking?

  , profileCrucibleFunctions :: Bool
  , profileSolver            :: Bool

  , branchCoverage           :: Bool

  , pathStrategy             :: PathStrategy

  , globalTimeout            :: Maybe NominalDiffTime
  , goalTimeout              :: Maybe DiffTime
  , profileOutputInterval    :: NominalDiffTime

  , loopBound                :: Maybe Word64
    -- ^ Should we artifically bound the number of loop iterations

  , recursionBound           :: Maybe Word64
    -- ^ Should we artifically bound the number of recursive calls to functions?

  , makeCexes                :: Bool
    -- ^ Should we construct counter-example executables

  , unsatCores               :: Bool
    -- ^ Should we attempt to compute unsatisfiable cores for successful
    --   proofs?
  , getNAbducts               :: Maybe Word64
    -- ^ How many abducts should we get from the solver for sat results?
    --   Only works with cvc5
  , solver                   :: String
    -- ^ Solver to use to discharge proof obligations
  , pathSatSolver            :: Maybe String
    -- ^ A separate solver to use for path satisfiability checking if that
    -- feature is enabled and if the path satisfiability checking solver should
    -- differ from the solver used to discharge proof obligations (default: use
    -- the proof obligation solver)
  , forceOfflineGoalSolving  :: Bool
    -- ^ Force goals to be verified using an offline solver instance, even if it
    -- would have been possible to use the same solver in online mode

  , pathSatSolverOutput      :: Maybe FilePath
    -- ^ The file to store the interaction session between the path
    -- satisfiability checker and the solver (if path satisfiability checking is
    -- enabled)
  , onlineSolverOutput       :: Maybe FilePath
    -- ^ The file to store the interaction with the online goal solver (if
    -- solving is being performed online)
  , offlineSolverOutput      :: Maybe FilePath
    -- ^ A template to use for files to store interactions with offline goal
    -- solvers (if solving is being performed offline).

  , yicesMCSat               :: Bool
    -- ^ Should the MC-SAT Yices solver be enabled (disables unsat cores; default: no)

  , floatMode                :: String
    -- ^ Tells the solver which representation to use for floating point values.

  , proofGoalsFailFast       :: Bool
    -- ^ If true, stop attempting to prove goals as soon as one is disproved

  , skipReport               :: Bool
    -- ^ Don't produce the HTML reports that describe the verification task

  , skipSuccessReports       :: Bool
    -- ^ Skip reporting on successful proof obligations

  , skipIncompleteReports    :: Bool
    -- ^ Skip reporting on goals that arise from resource exhaustion

  , hashConsing              :: Bool
    -- ^ Turn on hash-consing in the symbolic expression backend

  , onlineProblemFeatures    :: ProblemFeatures
    -- ^ Problem Features to force in online solvers

  , outputOptions            :: OutputOptions
    -- ^ Output options grouped together for easy transfer to the logger

  , debug                    :: Bool
    -- ^ Drop into the Crucible debugger before simulation begins

  }
  deriving (Generic)



cruxOptions :: Config CruxOptions
cruxOptions = Config
  { cfgFile =
       do inputFiles <-
            section "files" (oneOrList fileSpec) []
            "Input files to process."

          outDir <-
            section "output-directory" dirSpec ""
            "Save results in this directory."

          bldDir <-
            section "build-dir" dirSpec "crux-build"
            "Directory in which to create files generated from the inputFiles."

          checkPathSat <-
            section "path-sat" yesOrNoSpec False
            "Enable path satisfiability checking (default: no)."

          profileCrucibleFunctions <-
            section "profile-crucible" yesOrNoSpec False
            "Profile crucible function entry/exit. (default: no)"

          profileSolver <-
            section "profile-solver" yesOrNoSpec False
            "Profile solver events. (default: no)"

          branchCoverage <-
            section "branch-coverage" yesOrNoSpec False
            "Record branch coverage information. (default: no)"

          profileOutputInterval <-
            section "profiling-period" fractionalSpec 5
            "Time between intermediate profile data reports (default: 5 seconds)"

          globalTimeout <-
            sectionMaybe "timeout" fractionalSpec
            "Stop executing the simulator after this many seconds."

          goalTimeout <-
            sectionMaybe "goal-timeout" fractionalSpec
            "Stop trying to prove a goal after this many seconds."

          loopBound <-
            sectionMaybe "iteration-bound" numSpec
            "Bound all loops to at most this many iterations."

          recursionBound <-
            sectionMaybe "recursion-bound" numSpec
            "Bound the number of recursive calls to at most this many calls."

          pathStrategy <-
            section "path-strategy" pathStrategySpec AlwaysMergePaths
            "Simulator strategy for path exploration."

          makeCexes <-
            section "make-executables" yesOrNoSpec True
            "Should we generate counter-example executables. (default: yes)"

          unsatCores <-
            section "unsat-cores" yesOrNoSpec True
            "Should we attempt to compute unsatisfiable cores for successfult proofs (default: yes)"

          getNAbducts <-
            sectionMaybe "get-abducts" numSpec
            "How many abducts should we get from the solver for sat results? Only works with cvc5, 0 otherwise."
          solver <-
            section "solver" stringSpec "yices"
            (pack $ "Select the solver to use to discharge proof obligations. " ++
             "May be a single solver, a comma-separated list of solvers, or the string \"all\". " ++
             "Specifying multiple solvers requires the --force-offline-goal-solving option. " ++
             "(default: \"yices\")")

          pathSatSolver <-
            sectionMaybe "path-sat-solver" stringSpec
            "Select the solver to use for path satisfiability checking (if different from `solver` and required by the `path-sat` option). (default: use `solver`)"

          forceOfflineGoalSolving <-
            section "force-offline-goal-solving" yesOrNoSpec False
            "Force goals to be solved using an offline solver, even if the selected solver could have been used in online mode (default: no)"

          pathSatSolverOutput <-
            sectionMaybe "path-sat-solver-output" stringSpec
            "The file to store the interaction with the path satisfiability solver (if enabled and different from the main solver) (default: none)"

          onlineSolverOutput <-
            sectionMaybe "online-solver-output" stringSpec
            "The file to store the interaction with the online goal solver (if any) (default: none)"

          offlineSolverOutput <-
            sectionMaybe "offine-solver-output" stringSpec
            (pack offlineSolverOutputHelp)

          simVerbose <-
            section "sim-verbose" numSpec 1
            "Verbosity of simulators. (default: 1)"

          yicesMCSat <-
            section "mcsat" yesOrNoSpec False
            "Enable the MC-SAT solver in Yices (disables unsat cores) (default: no)"

          floatMode <-
            section "floating-point" stringSpec "default"
            (pack $ "Select floating point representation,"
             ++ " i.e. one of [real|ieee|uninterpreted|default]. "
             ++ "Default representation is solver specific: [cvc4|yices]=>real, z3=>ieee.")

          hashConsing <-
            section "hash-consing" yesOrNoSpec False
            "Enable hash-consing in the symbolic expression backend"

          printFailures <-
            section "print-failures" yesOrNoSpec True
            "Print error messages regarding failed verification goals"

          printSymbolicVars <-
            section "print-symbolic-vars" yesOrNoSpec False
            ("Print values assigned to symbolic variables " <>
             "when printing failed verification goals")

          skipReport <-
            section "skip-report" yesOrNoSpec False
            "Skip producing the HTML report after verification"

          skipSuccessReports <-
            section "skip-success-reports" yesOrNoSpec False
            "Skip reporting on successful proof obligations"

          skipIncompleteReports <-
            section "skip-incomplete-reports" yesOrNoSpec False
            "Skip reporting on proof obligations that arise from timeouts and resource exhaustion"

          noColors <-
            section "no-colors" yesOrNoSpec False
            "Suppress color codes in both the output and the errors"

          noColorsErr <-
            section "no-colors-err" yesOrNoSpec False
            "Suppress color codes in the errors"

          noColorsOut <-
            section "no-colors-out" yesOrNoSpec False
            "Suppress color codes in the output"

          quietMode <-
            section "quiet-mode" yesOrNoSpec False
            "If true, produce minimal output"

          proofGoalsFailFast <-
            section "proof-goals-fail-fast" yesOrNoSpec False
            "If true, stop attempting to prove goals as soon as one of them is disproved"

          onlineProblemFeatures <- pure noFeatures

          debug <-
            section "debug" yesOrNoSpec False
            "Drop into the Crucible debugger before simulation begins"

          pure CruxOptions
            { outputOptions = OutputOptions
              { colorOptions = ColorOptions
                { noColorsErr = noColorsErr || noColors
                , noColorsOut = noColorsOut || noColors
                },
                ..
              },
              ..
            }


  , cfgEnv =
      [
        EnvVar "BLDDIR" "Directory for writing build files generated from the input files."
        $ \v opts -> Right opts { bldDir = v }
      ]

  , cfgCmdLineFlag =

      [ Option "d" ["sim-verbose"]
        "Set simulator verbosity level."
        $ ReqArg "NUM" $ parsePosNum "NUM" $ \v -> set (field @"outputOptions" . field @"simVerbose") v

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

      , Option [] ["branch-coverage"]
        "Record branch coverage information"
        $ NoArg $ \opts -> Right opts { branchCoverage = True }

      , Option "t" ["timeout"]
        "Stop executing the simulator after this many seconds (default: 60)"
        $ OptArg "SECS"
        $ dflt "60"
        $ parseNominalDiffTime "seconds"
        $ \v opts -> opts { globalTimeout = Just v }

      , Option [] ["goal-timeout"]
        "Stop trying to prove each goal after this many seconds (default: 10)."
        $ OptArg "SECS"
        $ dflt "10"
        $ parseDiffTime "seconds"
        $ \v opts -> opts { goalTimeout = Just v }

      , Option "" ["path-strategy"]
        "Strategy to use for exploring paths ('always-merge' or 'split-dfs')"
        $ ReqArg "strategy"
        $ parsePathStrategy
        $ \strat opts -> opts{ pathStrategy = strat }

      , Option "p" ["profiling-period"]
        "Time between intermediate profile data reports (default: 5 seconds)"
        $ OptArg "SECS"
        $ dflt "5"
        $ parseNominalDiffTime "seconds"
        $ \v opts -> opts { profileOutputInterval = v }

      , Option "i" ["iteration-bound"]
        "Bound all loops to at most this many iterations"
        $ ReqArg "ITER"
        $ parsePosNum "iterations"
        $ \v opts -> opts { loopBound = Just v }

      , Option "r" ["recursion-bound"]
        "Bound all recursive calls to at most this many calls"
        $ ReqArg "CALLS"
        $ parsePosNum "calls"
        $ \v opts -> opts { recursionBound = Just v }

      , Option "x" ["no-execs"]
        "Disable generating counter-example executables"
        $ NoArg $ \opts -> Right opts { makeCexes = False }

      , Option [] ["no-unsat-cores"]
        "Disable computing unsat cores for successful proofs"
        $ NoArg $ \opts -> Right opts { unsatCores = False }

      , Option "n" ["get-abducts"]
        "Get these many abducts. Only works with cvc5, 0 otherwise."
        $ ReqArg "ABDUCTS"
        $ parsePosNum "abducts"
        $ \v opts -> opts { getNAbducts = Just v }

      , Option "s" ["solver"]
        ("Select the solver to use to discharge proof obligations. " ++
         "May be a single solver, a comma-separated list of solvers, or the string \"all\". " ++
         "Specifying multiple solvers requires the --force-offline-goal-solving option. " ++
         "(default: \"yices\")")
        $ ReqArg "SOLVER" $ \v opts -> Right opts { solver = map toLower v }

      , Option [] ["path-sat-solver"]
        "Select the solver to use for path satisfiability checking (if different from `solver` and required by the `path-sat` option). (default: use `solver`)"
        $ OptArg "SOLVER" $ \ms opts -> Right opts { pathSatSolver = ms }

      , Option [] ["force-offline-goal-solving"]
        "Force goals to be solved using an offline solver, even if the selected solver could have been used in online mode (default: no)"
        $ NoArg $ \opts -> Right opts { forceOfflineGoalSolving = True }

      , Option [] ["path-sat-solver-output"]
        "The file to store the interaction with the path satisfiability solver (if enabled and different from the main solver) (default: none)"
        $ ReqArg "FILE" $ \f opts -> Right opts { pathSatSolverOutput = Just f }

      , Option [] ["online-solver-output"]
        "The file to store the interaction with the online goal solver (if any) (default: none)"
        $ ReqArg "FILE" $ \f opts -> Right opts { onlineSolverOutput = Just f }

      , Option [] ["offline-solver-output"]
        offlineSolverOutputHelp
        $ ReqArg "FILE" $ \f opts -> Right opts { offlineSolverOutput = Just f }

      , Option [] ["mcsat"]
        "Enable the MC-SAT solver in Yices (disables unsat cores)"
        $ NoArg $ \opts -> Right opts { yicesMCSat = True }

      , Option [] ["skip-report"]
        "Skip producing the HTML report following verificaion"
        $ NoArg $ \opts -> Right opts { skipReport = True }

      , Option [] ["skip-success-reports"]
        "Skip reporting on successful proof obligations"
        $ NoArg $ \opts -> Right opts { skipSuccessReports = True }

      , Option [] ["skip-incomplete-reports"]
        "Skip reporting on proof obligations that arise from timeouts and resource exhaustion"
        $ NoArg $ \opts -> Right opts { skipIncompleteReports = True }

      , Option [] ["hash-consing"]
        "Enable hash-consing in the symbolic expression backend"
        $ NoArg $ \opts -> Right opts{ hashConsing = True }

      , Option [] ["skip-print-failures"]
        "Skip printing messages related to failed verification goals"
        $ NoArg $ Right . set (field @"outputOptions" . field @"printFailures") False

      , Option [] ["fail-fast"]
        "Stop attempting to prove goals as soon as one of them is disproved"
        $ NoArg $ \opts -> Right opts { proofGoalsFailFast = True }

      , Option "q" ["quiet"]
        "Quiet mode; produce minimal output"
        $ NoArg $ Right . set (field @"outputOptions" . field @"quietMode") True

      , Option "f" ["floating-point"]
        ("Select floating point representation,"
         ++ " i.e. one of [real|ieee|uninterpreted|default]. "
         ++ "Default representation is solver specific: [cvc4|yices]=>real, z3=>ieee.")
        $ ReqArg "FPREP" $ \v opts -> Right opts { floatMode = map toLower v }

      , Option [] ["debug"]
        "Drop into the Crucible debugger before simulation begins"
        $ NoArg $ \opts -> Right opts { debug = True }
      ]
  }

offlineSolverOutputHelp :: String
offlineSolverOutputHelp = unlines
  [ "A template to use for files to store interactions with offline goal solvers"
  , "(if any) (default: none). For example, if the template is `offline-output.smt2`,"
  , "then each file will be named `offline-output-<goal number>-<solver name>.smt2,"
  , "where <goal number> is the number of the goal that was proven (starting at 0)"
  , "and <solver name> is the name of the solver used to dispatch that goal."
  ]

dflt :: String -> (String -> OptSetter opts) -> (Maybe String -> OptSetter opts)
dflt x p mb = p (fromMaybe x mb)

parseDiffTime ::
  String -> (DiffTime -> opts -> opts) -> String -> OptSetter opts
parseDiffTime thing mk =
  parsePosNum thing (\a opts -> mk (cvt a) opts)
  where cvt :: Double -> DiffTime
        cvt = fromRational . toRational

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
