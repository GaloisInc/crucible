{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# Language RankNTypes, ImplicitParams, TypeApplications, MultiWayIf #-}
{-# Language OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module Crux
  ( runSimulator
  , postprocessSimResult
  , loadOptions
  , mkOutputConfig
  , defaultOutputConfig
  , SimulatorCallbacks(..)
  , SimulatorHooks(..)
  , RunnableState(..)
  , pattern RunnableState
  , Explainer
  , CruxOptions(..)
  , SomeOnlineSolver(..)
  , Crux(..)
  , module Crux.Config
  , module Crux.Log
  ) where

import qualified Control.Applicative as Applicative
import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad ( unless, void, when )
import qualified Data.Aeson as JSON
import           Data.Foldable
import           Data.Functor.Contravariant ( (>$<) )
import           Data.Functor.Contravariant.Divisible ( divide )
import           Data.Generics.Product.Fields (field)
import           Data.IORef
import           Data.Maybe ( fromMaybe )
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Version (Version)
import           Data.Void (Void)
import qualified Lumberjack as LJ
import           Prettyprinter
import qualified System.Console.ANSI as AC
import           System.Console.Terminal.Size (Window(Window), size)
import           System.Directory (createDirectoryIfMissing)
import           System.Exit (exitSuccess, ExitCode(..), exitFailure, exitWith)
import           System.FilePath ((</>))
import           System.IO ( Handle, hPutStr, stdout, stderr )

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce (newIONonceGenerator, NonceGenerator)
import           Data.Parameterized.Some ( Some(..) )

import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.Online
import qualified Lang.Crucible.Backend.Simple as CBS
import           Lang.Crucible.CFG.Extension
import qualified Lang.Crucible.Debug as Debug
import           Lang.Crucible.Simulator
import           Lang.Crucible.Simulator.BoundedExec
import           Lang.Crucible.Simulator.BoundedRecursion
import           Lang.Crucible.Simulator.PathSatisfiability
import           Lang.Crucible.Simulator.PathSplitting
import           Lang.Crucible.Simulator.PositionTracking
import           Lang.Crucible.Simulator.Profiling
import qualified Lang.Crucible.Syntax.Concrete as Syn
import           Lang.Crucible.Types


import           What4.Config (setOpt, getOptionSetting, verbosity, extendConfig)
import qualified What4.Expr as WE
import           What4.FunctionName (FunctionName)
import           What4.Interface (IsExprBuilder, getConfiguration)
import           What4.Protocol.Online (OnlineSolver)
import qualified What4.Solver as WS
import           What4.Solver.Bitwuzla (bitwuzlaTimeout)
import           What4.Solver.CVC4 (cvc4Timeout)
import           What4.Solver.CVC5 (cvc5Timeout)
import           What4.Solver.Yices (yicesEnableMCSat, yicesGoalTimeout)
import           What4.Solver.Z3 (z3Timeout)

import           Crux.Config
import           Crux.Config.Common
import           Crux.Config.Doc
import qualified Crux.Config.Load as Cfg
import qualified Crux.Config.Solver as CCS
import           Crux.FormatOut ( sayWhatFailedGoals, sayWhatResultStatus )
import           Crux.Goal
import           Crux.Log -- for the export list
import           Crux.Log as Log
import           Crux.Report
import           Crux.Types

pattern RunnableState :: forall sym . () => forall ext personality . (IsSyntaxExtension ext) => ExecState personality sym ext (RegEntry sym UnitType) -> RunnableState sym
pattern RunnableState es = RunnableStateWithExtensions es []

-- | A crucible @ExecState@ that is ready to be passed into the simulator.
--   This will usually, but not necessarily, be an @InitialState@.
data RunnableState sym where
  RunnableStateWithExtensions :: (IsSyntaxExtension ext)
                              => ExecState personality sym ext (RegEntry sym UnitType)
                              -> [ExecutionFeature personality sym ext (RegEntry sym UnitType)]
                              -> RunnableState sym

-- | Individual crux tools will generally call the @runSimulator@ combinator to
--   handle the nitty-gritty of setting up and running the simulator. Tools
--   provide @SimulatorCallbacks@ to hook into the simulation process at three
--   points:
--
--   * Before simulation begins, to set up global variables, register override
--     functions, construct the initial program entry point, and generally do
--     any necessary language-specific setup (i.e., to produce a 'RunnableState')
--   * When simulation ends with an assertion failure ('Explainer')
--   * When simulation ends, regardless of the outcome, to interpret the results.
--
--   All of these callbacks have access to the symbolic backend.
newtype SimulatorCallbacks msgs r
  = SimulatorCallbacks
    { getSimulatorCallbacks ::
        forall sym bak t st fs.
          ( IsSymBackend sym bak
          , Logs msgs
          , sym ~ WE.ExprBuilder t st fs
          ) =>
          IO (SimulatorHooks sym bak t r)
    }


-- | A GADT to capture the online solver constraints when we need them
data SomeOnlineSolver sym bak where
  SomeOnlineSolver :: ( sym ~ WE.ExprBuilder scope st fs
                      , bak ~ OnlineBackend solver scope st fs
                      , IsSymBackend sym bak
                      , OnlineSolver solver
                      ) => bak -> SomeOnlineSolver sym bak

-- | See 'SimulatorCallbacks'
data SimulatorHooks sym bak t r =
  SimulatorHooks
    { setupHook   :: bak -> Maybe (SomeOnlineSolver sym bak) -> IO (RunnableState sym)
    , onErrorHook :: bak -> IO (Explainer sym t Void)
    , resultHook  :: bak -> CruxSimulationResult -> IO r
    }

-- | Given the result of a simulation and proof run, report the overall
--   status, generate user-consumable reports and compute the exit code.
postprocessSimResult ::
  Logs msgs =>
  Bool -> CruxOptions -> CruxSimulationResult -> IO ExitCode
postprocessSimResult showFailedGoals opts res =
  do -- print goals that failed and overall result
     logSimResult showFailedGoals res

     -- Generate report
     generateReport opts res

     return $! computeExitCode res


-- | Load crux generic and the provided options, and provide them to
--   the given continuation.
--
--   IMPORTANT:  This processes options like @help@ and @version@, which
--   just print something and exit, so this function may never call
--   its continuation.
loadOptions ::
  SupportsCruxLogMessage msgs =>
  (Maybe OutputOptions -> OutputConfig msgs) ->
  Text {- ^ Name -} ->
  Version ->
  Config opts ->
  (Logs msgs => (CruxOptions, opts) -> IO a) ->
  IO a
loadOptions mkOutCfg nm ver config cont =
  do let optSpec = cfgJoin cruxOptions config
     (copts, opts) <- Cfg.loadConfig nm optSpec
     case opts of
       Cfg.ShowHelp ->
          do let ?outputConfig = mkOutCfg (Just (defaultOutputOptions copts))
             showHelp nm optSpec
             exitSuccess
       Cfg.ShowVersion ->
          do let ?outputConfig = mkOutCfg (Just (defaultOutputOptions copts))
             showVersion nm ver
             exitSuccess
       Cfg.Options (cruxWithoutColorOptions, os) files ->
          do let crux = set (field @"outputOptions" . field @"colorOptions") copts cruxWithoutColorOptions
             let ?outputConfig = mkOutCfg (Just (outputOptions crux))
             crux' <- postprocessOptions crux { inputFiles = files ++ inputFiles crux }
             cont (crux', os)

 `Ex.catch` \(e :: Ex.SomeException) ->
   do let ?outputConfig = mkOutCfg Nothing
      case (Ex.fromException e :: Maybe ExitCode) of
        Just exitCode -> exitWith exitCode
        Nothing -> logException e >> exitFailure


showHelp ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  Text -> Config opts -> IO ()
showHelp nm cfg = do
  -- Ideally, this would be done in the log handler.  We will soon try to change
  -- the logging mechanism so thaat it prefers 'Doc' over 'Text' so that layout
  -- decisions can be delayed to the log handlers.
  outWidth <- maybe 80 (\(Window _ w) -> w) <$> size
  let opts = LayoutOptions $ AvailablePerLine outWidth 0.98
  sayCrux (Log.Help (LogDoc (layoutPretty opts (configDocs nm cfg))))


showVersion ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  Text -> Version -> IO ()
showVersion nm ver = sayCrux (Log.Version nm ver)


-- | Create an OutputConfig for Crux, based on an indication of whether colored
-- output should be used, the normal and error output handles, and the parsed
-- CruxOptions.
--
-- If no CruxOptions are available (i.e. Nothing, as used in the preliminary
-- portions of loadOptions), then a default output stance is applied; the
-- default stance is described along with the individual option below.
--
-- The following CruxOptions affect the generated OutputConfig:
--
--  * noColorsErr    (default stance: False when the error handle supports
--    colors, as reported by System.Console.ANSI.hSupportsANSIColor)
--  * noColorsOut    (default stance: False when the output handle supports
--    colors, as reported by System.Console.ANSI.hSupportsANSIColor)
--  * printFailures  (default stance: True)
--  * quietMode      (default stance: False)
--  * simVerbose     (default stance: False)
mkOutputConfig ::
  JSON.ToJSON msgs =>
  (Handle, Bool) -> (Handle, Bool) ->
  (msgs -> SayWhat) -> Maybe OutputOptions ->
  OutputConfig msgs
mkOutputConfig (outHandle, outWantsColor) (errHandle, errWantsColor) logMessageToSayWhat opts =
  let consensusBetween wants maybeRefuses = wants && not (fromMaybe False maybeRefuses)
      copts = colorOptions <$> opts
      outSpec = (outHandle, consensusBetween outWantsColor (Cfg.noColorsOut <$> copts))
      errSpec@(_, errShouldColor) = (errHandle, consensusBetween errWantsColor (Cfg.noColorsErr <$> copts))
      lgWhat = let la = LJ.LogAction $ logToStd outSpec errSpec
                   -- TODO simVerbose may not be the best setting to use here...
                   baseline = if maybe False ((> 1) . simVerbose) opts
                              then Noisily
                              else Simply
               in if beQuiet
                  then logfltr OK >$< la
                  else logfltr baseline >$< la
      beQuiet = maybe False quietMode opts
      logfltr allowed = \case
        SayNothing -> SayNothing
        w@(SayWhat lvl _ _) -> if lvl >= allowed then w else SayNothing
        SayMore m1 m2 -> case (logfltr allowed m1, logfltr allowed m2) of
          (SayNothing, SayNothing) -> SayNothing
          (SayNothing, m) -> m
          (m, SayNothing) -> m
          (m1', m2') -> SayMore m1' m2'

      printFails = maybe True printFailures opts
      printVars = maybe False printSymbolicVars opts
      lgGoal = sayWhatFailedGoals printFails printVars >$< lgWhat
      splitResults r@(CruxSimulationResult _cmpl gls) = (snd <$> gls, r)
  in OutputConfig
     { _outputHandle = outHandle
     , _quiet = beQuiet
     , _logMsg = logMessageToSayWhat >$< lgWhat
     , _logExc = let seeRed = AC.hSetSGR errHandle
                              [ AC.SetConsoleIntensity AC.BoldIntensity
                              , AC.SetColor AC.Foreground AC.Vivid AC.Red]
                     seeCalm = AC.hSetSGR errHandle [AC.Reset]
                     dispExc = hPutStr errHandle . Ex.displayException
                 in if errShouldColor
                    then LJ.LogAction $ \e -> Ex.bracket_ seeRed seeCalm $ dispExc e
                    else LJ.LogAction $ dispExc
     , _logSimResult = \showDetails ->
                         if showDetails
                         then divide splitResults
                              lgGoal
                              (sayWhatResultStatus >$< lgWhat)
                         else sayWhatResultStatus >$< lgWhat
     , _logGoal = Seq.singleton >$< lgGoal
     }

defaultOutputConfig ::
  JSON.ToJSON msgs =>
  (msgs -> SayWhat) -> IO (Maybe OutputOptions -> OutputConfig msgs)
defaultOutputConfig logMessagesToSayWhat = do
  outWantsColor <- AC.hSupportsANSIColor stdout
  errWantsColor <- AC.hSupportsANSIColor stderr
  return $ Crux.mkOutputConfig (stdout, outWantsColor) (stderr, errWantsColor) logMessagesToSayWhat


--------------------------------------------------------------------------------

-- | For a given configuration, compute the 'FloatModeRepr'
--
-- Note that this needs to be CPS-ed because of the type parameter to the float
-- mode.  Also note that we can't use this function in
-- 'withSelectedOnlineBackend', unfortunately, because that function requires a
-- 'IsInterpretedFloatExprBuilder' constraint that we don't seem to have a way
-- to capture in this CPS-ed style.
withFloatRepr ::
  CCS.HasDefaultFloatRepr solver =>
  st s ->
  CruxOptions ->
  [solver] ->
  (forall fm .
    IsInterpretedFloatExprBuilder (WE.ExprBuilder s st (WE.Flags fm)) =>
    WE.FloatModeRepr fm ->
    IO a) ->
  IO a
withFloatRepr st cruxOpts selectedSolvers k =
  case floatMode cruxOpts of
    "real" -> k WE.FloatRealRepr
    "ieee" -> k WE.FloatIEEERepr
    "uninterpreted" -> k WE.FloatUninterpretedRepr
    "default" -> case selectedSolvers of
                   [oneSolver] -> CCS.withDefaultFloatRepr st oneSolver k
                   _           -> k WE.FloatUninterpretedRepr
    fm -> fail ("Unknown floating point mode: " ++ fm ++ "; expected one of [real|ieee|uninterpreted|default]")

-- | Parse through the options structure to determine which online backend to
-- instantiate (including the chosen floating point mode).
--
-- The choice of solver is provided as a separate argument (the
-- 'CCS.SolverOnline').  This function dispatches primarily on floating point
-- mode.  An explicit floating point mode can be provided if it has to match
-- another solver that has already started.  This code is slightly complicated
-- and duplicated because it is very hard to quantify over 'FloatModeRepr's in
-- such a way that captures the necessary 'IsInterpretedFloatExprBuilder'
-- constraints.
withSelectedOnlineBackend :: forall msgs scope st a.
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions ->
  NonceGenerator IO scope ->
  CCS.SolverOnline ->
  Maybe String ->
  st scope ->
  -- The string is an optional explicitly-requested float mode that supersedes the choice in
  -- the configuration (probably due to using two different online connections)
  (forall solver fm .
    ( OnlineSolver solver
    , IsInterpretedFloatExprBuilder (WE.ExprBuilder scope st (WE.Flags fm))
    ) =>
    (OnlineBackend solver scope st (WE.Flags fm) -> IO a)) ->
    IO a
withSelectedOnlineBackend cruxOpts nonceGen selectedSolver maybeExplicitFloatMode initSt k =
  case fromMaybe (floatMode cruxOpts) maybeExplicitFloatMode of
    "real" -> withOnlineBackendFM WE.FloatRealRepr
    "ieee" -> withOnlineBackendFM WE.FloatIEEERepr
    "uninterpreted" -> withOnlineBackendFM WE.FloatUninterpretedRepr
    "default" ->
      case selectedSolver of
        CCS.Yices -> withOnlineBackendFM WE.FloatRealRepr
        CCS.CVC4 -> withOnlineBackendFM WE.FloatRealRepr
        CCS.CVC5 -> withOnlineBackendFM WE.FloatRealRepr
        CCS.STP -> withOnlineBackendFM WE.FloatRealRepr
        CCS.Z3 -> withOnlineBackendFM WE.FloatIEEERepr
        CCS.Bitwuzla -> withOnlineBackendFM WE.FloatIEEERepr
    fm -> fail ("Unknown floating point mode: " ++ fm ++ "; expected one of [real|ieee|uninterpreted|default]")

  where
    withOnlineBackendFM ::
      IsInterpretedFloatExprBuilder (WE.ExprBuilder scope st (WE.Flags fm)) =>
      WE.FloatModeRepr fm ->
      IO a
    withOnlineBackendFM fm =
      do sym <- WE.newExprBuilder fm initSt nonceGen
         withSelectedOnlineBackend' cruxOpts selectedSolver sym k

withSelectedOnlineBackend' ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  IsInterpretedFloatExprBuilder (WE.ExprBuilder scope st fs) =>

  CruxOptions ->
  CCS.SolverOnline ->
  WE.ExprBuilder scope st fs ->
  (forall solver.
    OnlineSolver solver =>
    (OnlineBackend solver scope st fs -> IO a)) ->
    IO a
withSelectedOnlineBackend' cruxOpts selectedSolver sym k =
  let unsatCoreFeat | unsatCores cruxOpts
                    , not (yicesMCSat cruxOpts) = ProduceUnsatCores
                    | otherwise                 = NoUnsatFeatures
      extraFeatures = onlineProblemFeatures cruxOpts

   in case selectedSolver of
     CCS.Yices -> withYicesOnlineBackend sym unsatCoreFeat extraFeatures $ \bak -> do
       symCfg sym yicesEnableMCSat (yicesMCSat cruxOpts)
       case goalTimeout cruxOpts of
         Just s -> symCfg sym yicesGoalTimeout (floor s)
         Nothing -> return ()
       k bak
     CCS.CVC4 -> withCVC4OnlineBackend sym unsatCoreFeat extraFeatures $ \bak -> do
       case goalTimeout cruxOpts of
         Just s -> symCfg sym cvc4Timeout (floor (s * 1000))
         Nothing -> return ()
       k bak
     CCS.CVC5 -> withCVC5OnlineBackend sym unsatCoreFeat extraFeatures $ \bak -> do
       case goalTimeout cruxOpts of
         Just s -> symCfg sym cvc5Timeout (floor (s * 1000))
         Nothing -> return ()
       k bak
     CCS.Z3 -> withZ3OnlineBackend sym unsatCoreFeat extraFeatures $ \bak -> do
       case goalTimeout cruxOpts of
         Just s -> symCfg sym z3Timeout (floor (s * 1000))
         Nothing -> return ()
       k bak
     CCS.Bitwuzla -> withBitwuzlaOnlineBackend sym unsatCoreFeat extraFeatures $ \bak -> do
       case goalTimeout cruxOpts of
         Just s -> symCfg sym bitwuzlaTimeout (floor (s * 1000))
         Nothing -> return ()
       k bak
     CCS.STP -> do
       -- We don't have a timeout option for STP
       case goalTimeout cruxOpts of
         Just _ -> sayCrux (Log.UnsupportedTimeoutFor "STP")
         Nothing -> return ()
       withSTPOnlineBackend sym k

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

         profFilt = EventFilter
                      { recordProfiling = profileCrucibleFunctions cruxOpts
                      , recordCoverage = branchCoverage cruxOpts
                      }

     pfs <- execFeatureIf (profileCrucibleFunctions cruxOpts || branchCoverage cruxOpts)
                          (profilingFeature tbl profFilt (Just profOpts))

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


-- | Common setup for all solver connections
setupSolver :: (IsExprBuilder sym, sym ~ WE.ExprBuilder t st fs) => CruxOptions -> Maybe FilePath -> sym -> IO ()
setupSolver cruxOpts mInteractionFile sym = do
  mapM_ (symCfg sym solverInteractionFile) (fmap T.pack mInteractionFile)

  -- Turn on hash-consing, if enabled
  when (hashConsing cruxOpts) (WE.startCaching sym)

  let outOpts = outputOptions cruxOpts
  -- The simulator verbosity is one less than our verbosity.
  -- In this way, we can say things, without the simulator also
  -- being verbose
  symCfg sym verbosity $ toInteger $ if simVerbose outOpts > 1
                                       then simVerbose outOpts - 1
                                       else 0

-- | Common code for initializing all of the requested execution features
--
-- This function is a bit funny because one feature, path satisfiability
-- checking, requires on online solver while the others do not.  In order to
-- maximally reuse code, we pass in the necessary online constraints as an extra
-- argument when we have them available (i.e., when we build an online solver)
-- and elide them otherwise.
setupExecutionFeatures :: IsSymBackend sym bak
                       => CruxOptions
                       -> bak
                       -> Maybe (SomeOnlineSolver sym bak)
                       -> IO
                       ([GenericExecutionFeature sym], ProfData sym)
setupExecutionFeatures cruxOpts bak maybeOnline = do
  let sym = backendGetSym bak
  -- Setup profiling
  let profiling = isProfiling cruxOpts
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
  psat_fs <- case maybeOnline of
    Just (SomeOnlineSolver _bak) ->
      do enableOpt <- getOptionSetting enableOnlineBackend (getConfiguration sym)
         _ <- setOpt enableOpt (checkPathSat cruxOpts)
         execFeatureIf (checkPathSat cruxOpts)
           $ pathSatisfiabilityFeature sym (considerSatisfiability bak)
    Nothing -> return []

  -- Position tracking
  trackfs <- positionTrackingFeature sym

  return (concat [tfs, profExecFeatures profInfo, bfs, rfs, psat_fs, [trackfs]], profInfo)

-- | Select the What4 solver adapter for the user's solver choice (used for
-- offline solvers)
withSolverAdapter :: CCS.SolverOffline -> (WS.SolverAdapter st -> a) -> a
withSolverAdapter solverOff k =
  case solverOff of
    CCS.Boolector -> k WS.boolectorAdapter
    CCS.DReal -> k WS.drealAdapter
    CCS.SolverOnline CCS.CVC4 -> k WS.cvc4Adapter
    CCS.SolverOnline CCS.CVC5 -> k WS.cvc5Adapter
    CCS.SolverOnline CCS.STP -> k WS.stpAdapter
    CCS.SolverOnline CCS.Yices -> k WS.yicesAdapter
    CCS.SolverOnline CCS.Z3 -> k WS.z3Adapter
    CCS.SolverOnline CCS.Bitwuzla -> k WS.bitwuzlaAdapter

withSolverAdapters :: [CCS.SolverOffline] -> ([WS.SolverAdapter st] -> a) -> a
withSolverAdapters solverOffs k =
  foldr go base solverOffs $ []
  where
    base adapters = k adapters
    go nextOff withAdapters adapters = withSolverAdapter nextOff (\adapter -> withAdapters (adapter:adapters))

-- | Parse through all of the user-provided options and start up the verification process
--
-- This figures out which solvers need to be run, and in which modes.  It takes
-- as arguments some of the results of common setup code.  It also tries to
-- minimize code duplication between the different verification paths (e.g.,
-- online vs offline solving).
runSimulator ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions ->
  SimulatorCallbacks msgs r ->
  IO r
runSimulator cruxOpts simCallback = do
  sayCrux (Log.Checking (inputFiles cruxOpts))
  createDirectoryIfMissing True (outDir cruxOpts)
  Some (nonceGen :: NonceGenerator IO s) <- newIONonceGenerator
  case CCS.parseSolverConfig cruxOpts of

    Right (CCS.SingleOnlineSolver onSolver) ->
      withSelectedOnlineBackend cruxOpts nonceGen onSolver Nothing WE.EmptyExprBuilderState $ \bak -> do
        let monline = Just (SomeOnlineSolver bak)
        setupSolver cruxOpts (pathSatSolverOutput cruxOpts) (backendGetSym bak)
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts bak monline
        doSimWithResults cruxOpts simCallback bak execFeatures profInfo monline (proveGoalsOnline bak)

    Right (CCS.OnlineSolverWithOfflineGoals onSolver offSolver) ->
      withSelectedOnlineBackend cruxOpts nonceGen onSolver Nothing WE.EmptyExprBuilderState $ \bak -> do
        let monline = Just (SomeOnlineSolver bak)
        setupSolver cruxOpts (pathSatSolverOutput cruxOpts) (backendGetSym bak)
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts bak monline
        withSolverAdapter offSolver $ \adapter -> do
          -- We have to add the configuration options from the solver adapter,
          -- since they weren't included in the symbolic backend configuration
          -- with the initial setup of the online solver (since it could have
          -- been a different solver)
          unless (CCS.sameSolver onSolver offSolver) $
            extendConfig (WS.solver_adapter_config_options adapter) (getConfiguration (backendGetSym bak))
          doSimWithResults cruxOpts simCallback bak execFeatures profInfo monline (proveGoalsOffline [adapter])

    Right (CCS.OnlyOfflineSolvers offSolvers) ->
      withFloatRepr (WE.EmptyExprBuilderState @s) cruxOpts offSolvers $ \floatRepr -> do
        withSolverAdapters offSolvers $ \adapters -> do
          sym <- WE.newExprBuilder floatRepr WE.EmptyExprBuilderState nonceGen
          bak <- CBS.newSimpleBackend sym
          setupSolver cruxOpts Nothing sym
          -- Since we have a bare SimpleBackend here, we have to initialize it
          -- with the options taken from the solver adapter (e.g., solver path)
          extendConfig (WS.solver_adapter_config_options =<< adapters) (getConfiguration sym)
          (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts bak Nothing
          doSimWithResults cruxOpts simCallback bak execFeatures profInfo Nothing (proveGoalsOffline adapters)

    Right (CCS.OnlineSolverWithSeparateOnlineGoals pathSolver goalSolver) ->
      -- This case is probably the most complicated because it needs two
      -- separate online solvers.  The two must agree on the floating point
      -- mode.
      withSelectedOnlineBackend cruxOpts nonceGen pathSolver Nothing WE.EmptyExprBuilderState $ \pathSatBak -> do
        let sym = backendGetSym pathSatBak
        setupSolver cruxOpts (pathSatSolverOutput cruxOpts) sym
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts pathSatBak (Just (SomeOnlineSolver pathSatBak))
        withSelectedOnlineBackend' cruxOpts goalSolver sym $ \goalBak -> do
          doSimWithResults cruxOpts simCallback pathSatBak execFeatures profInfo (Just (SomeOnlineSolver pathSatBak)) (proveGoalsOnline goalBak)

    Left rsns -> fail ("Invalid solver configuration:\n" ++ unlines rsns)


-- | Core invocation of the symbolic execution engine
--
-- This is separated out so that we don't have to duplicate the code sequence in
-- 'runSimulator'.  The strategy used to ultimately discharge proof obligations
-- is a parameter to allow this code to use either an online or offline solver
-- connection.
--
-- The main work in this function is setting up appropriate solver frames and
-- traversing the goals tree, as well as handling some reporting.
doSimWithResults ::
  forall sym bak r t st fs msgs.
  sym ~ WE.ExprBuilder t st fs =>
  IsSymBackend sym bak =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions ->
  SimulatorCallbacks msgs r ->
  bak ->
  [GenericExecutionFeature sym] ->
  ProfData sym ->
  Maybe (SomeOnlineSolver sym bak) ->
  ProverCallback sym
    {- ^ The function to use to prove goals; this is intended to be
         one of 'proveGoalsOffline' or 'proveGoalsOnline' -} ->
  IO r
doSimWithResults cruxOpts simCallback bak execFeatures profInfo monline goalProver = do
  compRef <- newIORef ProgramComplete
  glsRef <- newIORef Seq.empty

  frm <- pushAssumptionFrame bak

  SimulatorHooks setup onError interpretResult <-
    getSimulatorCallbacks simCallback
  inFrame profInfo "<Crux>" $ do
    -- perform tool-specific setup
    RunnableStateWithExtensions initSt exts <- setup bak monline
    explainFailure <- onError bak

    -- This can't be initialized with the rest of the execution features,
    -- because it is not a 'GenericExecutionFeature'.
    --
    -- Ideally, we would use language-extension-specific command extensions
    -- (e.g., LLVM commands for Crux-LLVM) and parser hooks, but that would
    -- require some refactoring to pass those in...
    let debugging = debug cruxOpts
    debugger <-
      if debugging
      then do
        let ?parserHooks = Syn.ParserHooks Applicative.empty Applicative.empty
        let cExts = Debug.voidExts
        inps <- Debug.defaultDebuggerInputs cExts
        dbg <-
          Debug.debugger
            cExts
            Debug.voidImpl
            (Debug.IntrinsicPrinters MapF.empty)
            inps
            Debug.defaultDebuggerOutputs
            UnitRepr
        pure [dbg]
      else pure []

    -- execute the simulator
    case pathStrategy cruxOpts of
      AlwaysMergePaths ->
        do res <- executeCrucible (map genericToExecutionFeature execFeatures ++ exts ++ debugger) initSt
           void $ resultCont compRef glsRef frm explainFailure (Result res)
      SplitAndExploreDepthFirst ->
        do (i,ws) <- executeCrucibleDFSPaths
                         (map genericToExecutionFeature execFeatures ++ exts ++ debugger)
                         initSt
                         (resultCont compRef glsRef frm explainFailure . Result)
           sayCrux (Log.TotalPathsExplored i)
           unless (null ws) $
             sayCrux (Log.PathsUnexplored (Seq.length ws))

  sayCrux Log.SimulationComplete
  when (isProfiling cruxOpts) $ writeProf profInfo
  result <- CruxSimulationResult <$> readIORef compRef <*> readIORef glsRef
  interpretResult bak result

 where
 failfast = proofGoalsFailFast cruxOpts

 resultCont ::
      IORef ProgramCompleteness
   -> IORef (Seq.Seq (ProcessedGoals, ProvedGoals))
   -> FrameIdentifier
   -> (Maybe (WE.GroundEvalFn t) -> LabeledPred (WE.Expr t BaseBoolType) SimError -> IO (Doc Void))
   -> Result personality (WE.ExprBuilder t st fs)
   -> IO Bool
 resultCont compRef glsRef frm explainFailure (Result res) =
   do timedOut <-
        case res of
          TimeoutResult {} ->
            do sayCrux Log.SimulationTimedOut
               writeIORef compRef ProgramIncomplete
               return True
          _ -> return False
      popUntilAssumptionFrame bak frm
      let ctx = execResultContext res
      inFrame profInfo "<Prove Goals>" $ do
        todo <- getProofObligations bak
        sayCrux $ Log.ProofObligations (LogProofObligation <$> maybe [] goalsToList todo)
        when (isJust todo) $ sayCrux Log.AttemptingProvingVCs
        (nms, proved) <- goalProver cruxOpts ctx explainFailure todo
        mgt <- provedGoalsTree (backendGetSym bak) proved
        case mgt of
          Nothing -> return (not timedOut)
          Just gt ->
            do modifyIORef glsRef (Seq.|> (nms,gt))
               return (not (timedOut || (failfast && disprovedGoals nms > 0)))

isProfiling :: CruxOptions -> Bool
isProfiling cruxOpts =
  profileCrucibleFunctions cruxOpts || profileSolver cruxOpts || branchCoverage cruxOpts

computeExitCode :: CruxSimulationResult -> ExitCode
computeExitCode (CruxSimulationResult cmpl gls) = maximum . (base:) . fmap f . toList $ gls
 where
 base = case cmpl of
          ProgramComplete   -> ExitSuccess
          ProgramIncomplete -> ExitFailure 1
 f (nms,_gl) =
  let tot = totalProcessedGoals nms
      proved = provedGoals nms
  in if proved == tot then
       ExitSuccess
     else
       ExitFailure 1
