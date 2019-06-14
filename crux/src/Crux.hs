{-# Language RankNTypes, ImplicitParams, TypeApplications #-}
{-# Language OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module Crux
  ( main
  , mainWithOutputConfig
  , CruxOptions(..)
  , module Crux.Extension
  , module Crux.Config
  , module Crux.Log
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.List(intercalate)
import Control.Exception(catch, displayException)
import Control.Monad(when)
import System.Exit(exitSuccess)
import System.Directory(createDirectoryIfMissing)
import System.FilePath((</>))

import Data.Parameterized.Nonce(withIONonceGenerator, NonceGenerator)

import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.BoundedExec
import Lang.Crucible.Simulator.Profiling
import Lang.Crucible.Simulator.PathSatisfiability

import What4.Config (Opt, ConfigOption, setOpt, getOptionSetting, verbosity)
import What4.InterpretedFloatingPoint (IsInterpretedFloatExprBuilder)
import What4.Interface (IsExprBuilder, getConfiguration)
import What4.FunctionName (FunctionName)
import What4.Protocol.Online (OnlineSolver)
import What4.Solver.Z3 (z3Timeout)
import What4.Solver.Yices (yicesEnableMCSat)

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
main :: Language opts -> IO ()
main = mainWithOutputConfig defaultOutputConfig

-- | Throws 'ConfigError' (in addition to whatever the crucible and the
-- callbacks may throw)
mainWithOutputConfig :: OutputConfig -> Language opts -> IO ()
mainWithOutputConfig cfg lang =
  do opts  <- loadOptions lang
     opts1@(cruxOpts,_) <- initialize lang opts

     -- Run the simulator
     let fileText = intercalate ", " (map show (inputFiles cruxOpts))
     when (simVerbose cruxOpts > 1) $
       say "Crux" ("Checking " ++ fileText)
     res <- runSimulator lang opts1

     -- Generate report
     when (outDir cruxOpts /= "") $
        generateReport cruxOpts res

     -- Generate counter examples
     when (makeCexes cruxOpts) $
       mapM_ (makeCounterExamples lang opts) res
  `catch` \(e :: Cfg.ConfigError) -> sayFail "Crux" (displayException e)
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
          pure (crux { inputFiles = files ++ inputFiles crux }, os)

showHelp :: Logs => Text -> Config opts -> IO ()
showHelp nm cfg = outputLn (show (configDocs nm cfg))

showVersion :: Logs => Language opts -> IO ()
showVersion l = outputLn ("crux version: " ++ Crux.version ++ ", " ++
                          name l ++ " version: " ++ version l)


--------------------------------------------------------------------------------


-- Run a computation in the context of a given online solver. For the
-- moment, each solver is associated with a fixed floating-point
-- interpretation. Ultimately, this should be an option, too.
withBackend ::
  CruxOptions ->
  NonceGenerator IO scope ->
  (forall solver fs.
    ( OnlineSolver scope solver
    , IsInterpretedFloatExprBuilder (OnlineBackend scope solver fs)
    ) =>
    OnlineBackend scope solver fs -> IO a) -> IO a
withBackend cruxOpts nonceGen f =
  case solver cruxOpts of

    "cvc4" ->
      withCVC4OnlineBackend @(Flags FloatReal) nonceGen ProduceUnsatCores f

    "yices" ->
      withYicesOnlineBackend @(Flags FloatReal) nonceGen unsatCores $ \sym ->
        do symCfg sym yicesEnableMCSat (yicesMCSat cruxOpts)
           f sym

    "z3" ->
      withZ3OnlineBackend @(Flags FloatIEEE) nonceGen ProduceUnsatCores $ \sym->
        do symCfg sym z3Timeout (goalTimeout cruxOpts * 1000)
           f sym


    s -> fail $ "unknown solver: " ++ s

  where
  unsatCores | yicesMCSat cruxOpts = NoUnsatFeatures
             | otherwise           = ProduceUnsatCores


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




runSimulator ::
  Logs =>
  Language opts ->
  Options opts  ->
  IO (Maybe (ProvedGoals (Either AssumptionReason SimError)))
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

     -- Setup profiling
     let profiling = profileCrucibleFunctions cruxOpts || profileSolver cruxOpts
     profInfo <- if profiling then setupProfiling sym cruxOpts
                              else pure noProfiling

     -- Global timeout
     tfs <- execFeatureMaybe (globalTimeout cruxOpts) timeoutFeature

     -- Loop bound
     bfs <- execFeatureMaybe (loopBound cruxOpts) $ \i ->
             boundedExecFeature (\_ -> return (Just i)) True {- side cond: yes-}

     -- Check path satisfiability
     psat_fs <- execFeatureIf (checkPathSat cruxOpts)
              $ pathSatisfiabilityFeature sym (considerSatisfiability sym)

     let execFeatures = tfs ++ profExecFeatures profInfo ++ bfs ++ psat_fs

     -- Ready to go!
     gls <- inFrame profInfo "<Crux>" $
       do Result res <- simulate lang execFeatures opts sym emptyModel

          case res of
            TimeoutResult _ ->
              do outputLn
                   "Simulation timed out! Program might not be fully verified!"
            _ -> return ()

          popUntilAssumptionFrame sym frm

          let ctx' = execResultContext res

          inFrame profInfo "<Prove Goals>" $
            do todo <- getProofObligations sym
               proved <- proveGoals cruxOpts ctx' todo
               provedGoalsTree ctx' proved

     when (simVerbose cruxOpts > 1) $
      say "Crux" "Simulation complete."

     when profiling $
       writeProf profInfo

     pure gls


