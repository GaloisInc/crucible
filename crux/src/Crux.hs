{-# Language RankNTypes, ImplicitParams, TypeApplications, MultiWayIf #-}
{-# Language OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module Crux
  ( main
  , mainWithOutputConfig
  , runSimulator
  , CruxOptions(..)
  , module Crux.Extension
  , module Crux.Config
  , module Crux.Log
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Foldable
import Data.IORef
import Data.List(intercalate)
import qualified Data.Sequence as Seq
import Control.Exception(catch, displayException)
import Control.Monad(when)
import System.Exit(exitSuccess, ExitCode(..))
import System.Directory(createDirectoryIfMissing)
import System.FilePath((</>))

import Data.Parameterized.Nonce(withIONonceGenerator, NonceGenerator)

import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.BoundedExec
import Lang.Crucible.Simulator.BoundedRecursion
import Lang.Crucible.Simulator.Profiling
import Lang.Crucible.Simulator.PathSatisfiability

import What4.Config (Opt, ConfigOption, setOpt, getOptionSetting, verbosity)
import What4.InterpretedFloatingPoint (IsInterpretedFloatExprBuilder)
import What4.Interface (IsExprBuilder, getConfiguration)
import What4.FunctionName (FunctionName)
import What4.Protocol.Online (OnlineSolver)
import What4.Solver.Z3 (z3Timeout)
import What4.Solver.Yices (yicesEnableMCSat, yicesGoalTimeout)

import Crux.Log
import Crux.Types
import Crux.Config
import Crux.Goal
import Crux.Model
import Crux.Report
import qualified Crux.Config.Load as Cfg
import Crux.Config.Common
import Crux.Config.Doc
import Crux.Extension
import qualified Crux.Version as Crux

-- | Throws 'ConfigError' (in addition to whatever the crucible and the
-- callbacks may throw)
main :: Language opts -> IO ExitCode
main = mainWithOutputConfig defaultOutputConfig

-- | Throws 'ConfigError' (in addition to whatever the crucible and the
-- callbacks may throw)
mainWithOutputConfig :: OutputConfig -> Language opts -> IO ExitCode
mainWithOutputConfig cfg lang =
  do opts  <- loadOptions lang
     opts1@(cruxOpts,_) <- initialize lang opts

     -- Run the simulator
     let fileText = intercalate ", " (map show (inputFiles cruxOpts))
     when (simVerbose cruxOpts > 1) $
       say "Crux" ("Checking " ++ fileText)
     (cmpl, res) <- runSimulator lang opts1

     reportStatus res

     -- Generate report
     when (outDir cruxOpts /= "") $
        generateReport cruxOpts res

     -- Generate counter examples
     when (makeCexes cruxOpts) $
       makeCounterExamples lang opts res

     return $! computeExitCode cmpl res

  `catch` \(e :: Cfg.ConfigError) ->
    do sayFail "Crux" (displayException e)
       return (ExitFailure 1)

 where ?outputConfig = cfg

-- | Load the options for the given language.
-- IMPORTANT:  This processes options like @help@ and @version@, which
-- just print something and exit, so this function may never return!
loadOptions :: Logs => Language opts -> IO (Options opts)
loadOptions lang =
  do let nm      = Text.pack (name lang)
         optSpec = cfgJoin cruxOptions (configuration lang)
     opts <- Cfg.loadConfig nm optSpec
     case opts of
       Cfg.ShowHelp -> showHelp nm optSpec >> exitSuccess
       Cfg.ShowVersion -> showVersion lang >> exitSuccess
       Cfg.Options (crux,os) files ->
          do crux' <- postprocessOptions crux { inputFiles = files ++ inputFiles crux }
             pure (crux', os)

showHelp :: Logs => Text -> Config opts -> IO ()
showHelp nm cfg = outputLn (show (configDocs nm cfg))

showVersion :: Logs => Language opts -> IO ()
showVersion l = outputLn ("crux version: " ++ Crux.version ++ ", " ++
                          name l ++ " version: " ++ version l)


--------------------------------------------------------------------------------


-- Run a computation in the context of a given online solver
-- with a particular floating-point interpretation mode.
withBackend ::
  CruxOptions ->
  NonceGenerator IO scope ->
  (forall solver fs.
    ( OnlineSolver scope solver
    , IsInterpretedFloatExprBuilder (OnlineBackend scope solver fs)
    ) =>
    OnlineBackend scope solver fs -> IO a) -> IO a
withBackend cruxOpts nonceGen f =
  case floatMode cruxOpts of
    "real" -> withSolver FloatRealRepr (solver cruxOpts)
    "ieee" -> withSolver FloatIEEERepr (solver cruxOpts)
    "uninterpreted" -> withSolver FloatUninterpretedRepr (solver cruxOpts)
    "default" ->
      case (solver cruxOpts) of
        s@"cvc4" -> withSolver FloatRealRepr s
        s@"yices" -> withSolver FloatRealRepr s
        s@"z3" -> withSolver FloatIEEERepr s
        s -> fail $ "unknown solver: " ++ s ++ "; expepected of one [cvc4|yices|z3]."
    fm -> fail $ "unknown floating-point mode: " ++ fm ++ "; expepected of one [real|ieee|uninterpreted|default]."
  where
  unsatCores | yicesMCSat cruxOpts = NoUnsatFeatures
             | otherwise           = ProduceUnsatCores
  withSolver fpMode "cvc4" =
    withCVC4OnlineBackend fpMode nonceGen ProduceUnsatCores f
  withSolver fpMode "yices" =
    withYicesOnlineBackend fpMode nonceGen unsatCores $ \sym ->
      do symCfg sym yicesEnableMCSat (yicesMCSat cruxOpts)
         case goalTimeout cruxOpts of
           Just s -> symCfg sym yicesGoalTimeout (floor s)
           Nothing -> return ()
         f sym
  withSolver fpMode "z3" =
    withZ3OnlineBackend fpMode nonceGen ProduceUnsatCores $ \sym->
      do case goalTimeout cruxOpts of
           Just s -> symCfg sym z3Timeout (floor s * 1000)
           Nothing -> return ()
         f sym
  withSolver _fpMode other =
    fail $ "unknown solver: " ++ other ++ "; expepected of one [cvc4|yices|z3]."

symCfg :: (IsExprBuilder sym, Opt t a) => sym -> ConfigOption t -> a -> IO ()
symCfg sym x y =
  do opt <- getOptionSetting x (getConfiguration sym)
     _   <- setOpt opt y
     pure ()


data ProfData sym = ProfData
  { inFrame          :: forall a. FunctionName -> IO a -> IO a
  , profExecFeatures :: [GenericExecutionFeature sym]
  , writeProf        :: IO ()
  }

noProfiling :: ProfData sym
noProfiling = ProfData
  { inFrame           = \_ x -> x
  , profExecFeatures  = []
  , writeProf         = pure ()
  }

setupProfiling :: IsSymInterface sym => sym -> CruxOptions -> IO (ProfData sym)
setupProfiling sym cruxOpts =
  do tbl <- newProfilingTable

     when (profileSolver cruxOpts) $
       startRecordingSolverEvents sym tbl

     let profSource = case inputFiles cruxOpts of
                        [f] -> f
                        _ -> "multiple files"

         profOutFile = outDir cruxOpts </> "report_data.js"
         saveProf = writeProfileReport profOutFile "crux profile" profSource
         profOpts = ProfilingOptions
                      { periodicProfileInterval = profileOutputInterval cruxOpts
                      , periodicProfileAction = saveProf
                      }

     pfs <- execFeatureIf (profileCrucibleFunctions cruxOpts)
                          (profilingFeature tbl (Just profOpts))

     pure ProfData
       { inFrame = \str -> inProfilingFrame tbl str Nothing
       , profExecFeatures = pfs
       , writeProf = saveProf tbl
       }

execFeatureIf ::
  Bool ->
  IO (GenericExecutionFeature sym) ->
  IO [GenericExecutionFeature sym]
execFeatureIf b m = if b then (:[]) <$> m else pure []

execFeatureMaybe ::
  Maybe a ->
  (a -> IO (GenericExecutionFeature sym)) ->
  IO [GenericExecutionFeature sym]
execFeatureMaybe mb m =
  case mb of
    Nothing -> pure []
    Just a  -> (:[]) <$> m a


data ProgramCompleteness
 = ProgramComplete
 | ProgramIncomplete
 deriving (Eq,Ord,Show)

runSimulator ::
  Logs =>
  Language opts ->
  Options opts  ->
  IO (ProgramCompleteness, Seq.Seq (ProvedGoals (Either AssumptionReason SimError)))
runSimulator lang opts@(cruxOpts,_) =
  withIONonceGenerator $ \nonceGen ->
  withBackend cruxOpts nonceGen $ \sym ->

  do -- The simulator verbosity is one less than our verbosity.
     -- In this way, we can say things, without the simulator also
     -- being verbose
     symCfg sym verbosity $ toInteger $ if simVerbose cruxOpts > 1
                                          then simVerbose cruxOpts - 1
                                          else 0

     -- XXX: add an option for this
     symCfg sym solverInteractionFile "crux-solver.out"

     frm <- pushAssumptionFrame sym

     createDirectoryIfMissing True (outDir cruxOpts)

     compRef <- newIORef ProgramComplete

     -- Setup profiling
     let profiling = profileCrucibleFunctions cruxOpts || profileSolver cruxOpts
     profInfo <- if profiling then setupProfiling sym cruxOpts
                              else pure noProfiling

     -- Global timeout
     tfs <- execFeatureMaybe (globalTimeout cruxOpts) timeoutFeature

     -- Loop bound
     bfs <- execFeatureMaybe (loopBound cruxOpts) $ \i ->
             boundedExecFeature (\_ -> return (Just i)) True {- side cond: yes -}

     -- Recursion bound
     rfs <- execFeatureMaybe (recursionBound cruxOpts) $ \i ->
             boundedRecursionFeature (\_ -> return (Just i)) True {- side cond: yes -}

     -- Check path satisfiability
     psat_fs <- execFeatureIf (checkPathSat cruxOpts)
              $ pathSatisfiabilityFeature sym (considerSatisfiability sym)

     let execFeatures = tfs ++ profExecFeatures profInfo ++ bfs ++ rfs ++ psat_fs

     -- Ready to go!
     gls <- newIORef Seq.empty
     inFrame profInfo "<Crux>" $
       simulate lang execFeatures opts sym emptyModel $ \(Result res) ->
        do case res of
             TimeoutResult _ ->
               do sayWarn "Crux" "Simulation timed out! Program might not be fully verified!"
                  writeIORef compRef ProgramIncomplete
             _ -> return ()

           popUntilAssumptionFrame sym frm

           let ctx' = execResultContext res

           inFrame profInfo "<Prove Goals>" $
             do todo <- getProofObligations sym
                proved <- proveGoals cruxOpts ctx' todo
                mgt <- provedGoalsTree ctx' proved
                case mgt of
                  Nothing -> return ()
                  Just gt ->
                    modifyIORef gls (Seq.|> gt)

     when (simVerbose cruxOpts > 1) $
       say "Crux" "Simulation complete."

     when profiling $
       writeProf profInfo

     (,) <$> readIORef compRef <*> readIORef gls

computeExitCode :: ProgramCompleteness -> Seq.Seq (ProvedGoals a) -> ExitCode
computeExitCode cmpl = maximum . (base:) . fmap f . toList
 where
 base = case cmpl of
          ProgramComplete   -> ExitSuccess
          ProgramIncomplete -> ExitFailure 1
 f gl =
  let tot = countTotalGoals gl
      proved = countProvedGoals gl
  in if proved == tot then
       ExitSuccess
     else
       ExitFailure 1

reportStatus :: (?outputConfig::OutputConfig) => Seq.Seq (ProvedGoals a) -> IO ()
reportStatus gls =
  do let tot        = sum (fmap countTotalGoals gls)
         proved     = sum (fmap countProvedGoals gls)
         incomplete = sum (fmap countIncompleteGoals gls)
         disproved  = sum (fmap countDisprovedGoals gls) - incomplete
         unknown    = sum (fmap countUnknownGoals gls)
     say "Crux" "Goal status:"
     say "Crux" ("  Total: " ++ show tot)
     say "Crux" ("  Proved: " ++ show proved)
     say "Crux" ("  Disproved: " ++ show disproved)
     say "Crux" ("  Incomplete: " ++ show incomplete)
     say "Crux" ("  Unknown: " ++ show unknown)
     if | disproved > 0 ->
            sayFail "Crux" "Overall status: Invalid."
        | incomplete > 0 ->
            sayWarn "Crux" "Overall status: Unknown (incomplete)."
        | unknown > 0 -> sayWarn "Crux" "Overall status: Unknown."
        | proved == tot -> sayOK "Crux" "Overall status: Valid."
        | otherwise ->
            sayFail "Crux" "Internal error computing overall status."
