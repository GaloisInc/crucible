{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# Language RankNTypes, ImplicitParams, TypeApplications, MultiWayIf #-}
{-# Language OverloadedStrings, FlexibleContexts, ScopedTypeVariables #-}
module Crux
  ( runSimulator
  , postprocessSimResult
  , loadOptions
  , withOutputConfig
  , SimulatorCallback(..)
  , RunnableState(..)
  , pattern RunnableState
  , CruxOptions(..)
  , SomeOnlineSolver(..)
  , module Crux.Config
  , module Crux.Log
  ) where

import qualified Control.Exception as Ex
import Control.Lens
import Control.Monad ( unless, void )
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Foldable
import Data.IORef
import Data.List ( intercalate )
import Data.Maybe ( fromMaybe )
import Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Control.Monad(when)
import System.Exit(exitSuccess, ExitCode(..), exitFailure)
import System.Directory(createDirectoryIfMissing)
import System.FilePath((</>))

import Data.Parameterized.Classes
import Data.Parameterized.Nonce(newIONonceGenerator, NonceGenerator)
import Data.Parameterized.Some ( Some(..) )

import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import qualified Lang.Crucible.Backend.Simple as CBS
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.BoundedExec
import Lang.Crucible.Simulator.BoundedRecursion
import Lang.Crucible.Simulator.Profiling
import Lang.Crucible.Simulator.PathSatisfiability
import Lang.Crucible.Simulator.PathSplitting
import Lang.Crucible.Types


import What4.Config (Opt, ConfigOption, setOpt, getOptionSetting, verbosity, extendConfig)
import What4.InterpretedFloatingPoint (IsInterpretedFloatExprBuilder)
import What4.Interface (IsExprBuilder, getConfiguration)
import qualified What4.Expr.Builder as WEB
import What4.FunctionName (FunctionName)
import What4.Protocol.Online (OnlineSolver)
import qualified What4.Solver as WS
import What4.Solver.CVC4 (cvc4Timeout)
import What4.Solver.Z3 (z3Timeout)
import What4.Solver.Yices (yicesEnableMCSat, yicesGoalTimeout)

import Crux.Log
import Crux.Types
import Crux.Config
import Crux.Goal
import Crux.Report
import qualified Crux.Config.Load as Cfg
import qualified Crux.Config.Solver as CCS
import Crux.Config.Common
import Crux.Config.Doc
import qualified Crux.Version as Crux

pattern RunnableState :: forall sym . () => forall ext . (IsSyntaxExtension ext) => ExecState (Model sym) sym ext (RegEntry sym UnitType) -> RunnableState sym
pattern RunnableState es = RunnableStateWithExtensions es []

-- | A crucible @ExecState@ that is ready to be passed into the simulator.
--   This will usually, but not necessarily, be an @InitialState@.
data RunnableState sym where
  RunnableStateWithExtensions :: (IsSyntaxExtension ext)
                              => ExecState (Model sym) sym ext (RegEntry sym UnitType)
                              -> [ExecutionFeature (Model sym) sym ext (RegEntry sym UnitType)]
                              -> RunnableState sym

-- | Individual crux tools will generally call the @runSimulator@ combinator
--   to handle the nitty-gritty of setting up and running the simulator.
--   During that process, crux needs to know how to setup the initial state
--   for the simulator.  To do that, crux tools will provide a @SimulatorCallback@,
--   which is provided a symbolic interface object and is responsible for setting up
--   global variables, registering override functions, constructing the initial
--   program entry point, and generally doing any necessary language-specific setup.
newtype SimulatorCallback
  = SimulatorCallback
    { initSimulatorState ::
        forall s st fs . (IsSymInterface (WEB.ExprBuilder s st fs), Logs) =>
          WEB.ExprBuilder s st fs -> Maybe (SomeOnlineSolver (WEB.ExprBuilder s st fs)) -> IO (RunnableState (WEB.ExprBuilder s st fs))
    }

-- | Given the reuslt of a simulation and proof run, report the overall
--   status, generate user-consumable reports and compute the exit code.
postprocessSimResult :: Logs => CruxOptions -> CruxSimulationResult -> IO ExitCode
postprocessSimResult opts res =
  do -- print the overall result
     reportStatus res

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
  OutputConfig ->
  Text {- ^ Name -} ->
  Text {- ^ Version -}->
  Config opts ->
  (Logs => (CruxOptions, opts) -> IO a) ->
  IO a
loadOptions outCfg nm ver config cont =
  do let optSpec = cfgJoin cruxOptions config
     opts <- Cfg.loadConfig nm optSpec
     case opts of
       Cfg.ShowHelp ->
          do let ?outputConfig = outCfg
             showHelp nm optSpec
             exitSuccess
       Cfg.ShowVersion ->
          do let ?outputConfig = outCfg
             showVersion nm ver
             exitSuccess
       Cfg.Options (crux, os) files ->
          do let ?outputConfig = outCfg & quiet %~ (|| quietMode crux)
             crux' <- postprocessOptions crux { inputFiles = files ++ inputFiles crux }
             cont (crux', os)

 `Ex.catch` \(e :: Ex.SomeException) ->
   do let ?outputConfig = outCfg
      sayFail "Crux" (Ex.displayException e)
      exitFailure

showHelp :: Logs => Text -> Config opts -> IO ()
showHelp nm cfg = outputLn (show (configDocs nm cfg))

showVersion :: Logs => Text -> Text -> IO ()
showVersion nm ver =
  outputLn $ "crux version: " <> Crux.version <> ", " <> Text.unpack nm <> " version: " <> Text.unpack ver


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
  proxy s ->
  CruxOptions ->
  solver ->
  (forall fm .
    IsInterpretedFloatExprBuilder (WEB.ExprBuilder s CBS.SimpleBackendState (Flags fm)) =>
    FloatModeRepr fm ->
    IO a) ->
  IO a
withFloatRepr proxy cruxOpts selectedSolver k =
  case floatMode cruxOpts of
    "real" -> k FloatRealRepr
    "ieee" -> k FloatIEEERepr
    "uninterpreted" -> k FloatUninterpretedRepr
    "default" -> CCS.withDefaultFloatRepr proxy selectedSolver k
    fm -> fail ("Unknown floating point mode: " ++ fm ++ "; expected one of [real|ieee|uninterpreted|default]")

floatReprString :: FloatModeRepr fm -> String
floatReprString floatRepr =
  case floatRepr of
    FloatRealRepr -> "real"
    FloatIEEERepr -> "ieee"
    FloatUninterpretedRepr -> "uninterpreted"

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
withSelectedOnlineBackend ::
  Logs =>
  CruxOptions ->
  NonceGenerator IO scope ->
  CCS.SolverOnline ->
  Maybe String ->
  -- The string is an optional explicitly-requested float mode that supersedes the choice in
  -- the configuration (probably due to using two different online connections)
  (forall solver fm .
    ( OnlineSolver scope solver
    , IsInterpretedFloatExprBuilder (OnlineBackend scope solver (Flags fm))
    ) =>
    FloatModeRepr fm -> OnlineBackend scope solver (Flags fm) -> IO a) -> IO a
withSelectedOnlineBackend cruxOpts nonceGen selectedSolver maybeExplicitFloatMode k =
  case fromMaybe (floatMode cruxOpts) maybeExplicitFloatMode of
    "real" -> withOnlineBackendFM FloatRealRepr
    "ieee" -> withOnlineBackendFM FloatIEEERepr
    "uninterpreted" -> withOnlineBackendFM FloatUninterpretedRepr
    "default" ->
      case selectedSolver of
        CCS.Yices -> withOnlineBackendFM FloatRealRepr
        CCS.CVC4 -> withOnlineBackendFM FloatRealRepr
        CCS.STP -> withOnlineBackendFM FloatRealRepr
        CCS.Z3 -> withOnlineBackendFM FloatIEEERepr
    fm -> fail ("Unknown floating point mode: " ++ fm ++ "; expected one of [real|ieee|uninterpreted|default]")
  where
    unsatCores | yicesMCSat cruxOpts = NoUnsatFeatures
               | otherwise           = ProduceUnsatCores

    withOnlineBackendFM floatRepr =
      case selectedSolver of
        CCS.Yices -> withYicesOnlineBackend floatRepr nonceGen unsatCores $ \sym -> do
          symCfg sym yicesEnableMCSat (yicesMCSat cruxOpts)
          case goalTimeout cruxOpts of
            Just s -> symCfg sym yicesGoalTimeout (floor s)
            Nothing -> return ()
          k floatRepr sym
        CCS.CVC4 -> withCVC4OnlineBackend floatRepr nonceGen ProduceUnsatCores $ \sym -> do
          case goalTimeout cruxOpts of
            Just s -> symCfg sym cvc4Timeout (floor (s * 1000))
            Nothing -> return ()
          k floatRepr sym
        CCS.Z3 -> withZ3OnlineBackend floatRepr nonceGen ProduceUnsatCores $ \sym -> do
          case goalTimeout cruxOpts of
            Just s -> symCfg sym z3Timeout (floor (s * 1000))
            Nothing -> return ()
          k floatRepr sym
        CCS.STP -> do
          -- We don't have a timeout option for STP
          case goalTimeout cruxOpts of
            Just _ -> sayWarn "Crux" "Goal timeout requested but not supported by STP"
            Nothing -> return ()
          withSTPOnlineBackend floatRepr nonceGen (k floatRepr)

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


-- | Common setup for all solver connections
setupSolver :: (IsExprBuilder sym, sym ~ WEB.ExprBuilder t st fs) => CruxOptions -> Maybe FilePath -> sym -> IO ()
setupSolver cruxOpts mInteractionFile sym = do
  mapM_ (symCfg sym solverInteractionFile) (fmap T.pack mInteractionFile)

  -- Turn on hash-consing, if enabled
  when (hashConsing cruxOpts) (WEB.startCaching sym)

  -- The simulator verbosity is one less than our verbosity.
  -- In this way, we can say things, without the simulator also
  -- being verbose
  symCfg sym verbosity $ toInteger $ if simVerbose cruxOpts > 1
                                       then simVerbose cruxOpts - 1
                                       else 0

-- | A GADT to capture the online solver constraints when we need them
data SomeOnlineSolver sym where
  SomeOnlineSolver :: (sym ~ OnlineBackend scope solver fs
                      , OnlineSolver scope solver
                      ) => SomeOnlineSolver sym

-- | Common code for initializing all of the requested execution features
--
-- This function is a bit funny because one feature, path satisfiability
-- checking, requires on online solver while the others do not.  In order to
-- maximally reuse code, we pass in the necessary online constraints as an extra
-- argument when we have them available (i.e., when we build an online solver)
-- and elide them otherwise.
setupExecutionFeatures :: (IsSymInterface sym)
                       => CruxOptions
                       -> sym
                       -> Maybe (SomeOnlineSolver sym)
                       -> IO
                       ([GenericExecutionFeature sym], ProfData sym)
setupExecutionFeatures cruxOpts sym maybeOnline = do
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
    Just SomeOnlineSolver -> execFeatureIf (checkPathSat cruxOpts)
           $ pathSatisfiabilityFeature sym (considerSatisfiability sym)
    Nothing -> return []

  return (concat [tfs, profExecFeatures profInfo, bfs, rfs, psat_fs], profInfo)

-- | Select the What4 solver adapter for the user's solver choice (used for
-- offline solvers)
withSolverAdapter :: CCS.SolverOffline -> (WS.SolverAdapter st -> a) -> a
withSolverAdapter solverOff k =
  case solverOff of
    CCS.Boolector -> k WS.boolectorAdapter
    CCS.DReal -> k WS.drealAdapter
    CCS.SolverOnline CCS.CVC4 -> k WS.cvc4Adapter
    CCS.SolverOnline CCS.STP -> k WS.stpAdapter
    CCS.SolverOnline CCS.Yices -> k WS.yicesAdapter
    CCS.SolverOnline CCS.Z3 -> k WS.z3Adapter

withOutputConfig ::
  OutputConfig ->
  CruxOptions ->
  (Logs => a) ->
  a
withOutputConfig outCfg opts k = k
 where ?outputConfig = outCfg & quiet %~ (|| (quietMode opts))

-- | Parse through all of the user-provided options and start up the verification process
--
-- This figures out which solvers need to be run, and in which modes.  It takes
-- as arguments some of the results of common setup code.  It also tries to
-- minimize code duplication between the different verification paths (e.g.,
-- online vs offline solving).
runSimulator ::
  Logs =>
  CruxOptions ->
  SimulatorCallback ->
  IO CruxSimulationResult
runSimulator cruxOpts simCallback = do
  when (simVerbose cruxOpts > 1) $
    do let fileText = intercalate ", " (map show (inputFiles cruxOpts))
       say "Crux" ("Checking " ++ fileText)
  createDirectoryIfMissing True (outDir cruxOpts)
  compRef <- newIORef ProgramComplete
  glsRef <- newIORef Seq.empty
  Some (nonceGen :: NonceGenerator IO s) <- newIONonceGenerator
  case CCS.parseSolverConfig cruxOpts of
    Right (CCS.SingleOnlineSolver onSolver) ->
      withSelectedOnlineBackend cruxOpts nonceGen onSolver Nothing $ \_ sym -> do
        let monline = Just SomeOnlineSolver
        setupSolver cruxOpts (onlineSolverOutput cruxOpts) sym
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts sym monline
        doSimWithResults cruxOpts simCallback compRef glsRef sym execFeatures profInfo monline (proveGoalsOnline sym)
    Right (CCS.OnlineSolverWithOfflineGoals onSolver offSolver) ->
      withSelectedOnlineBackend cruxOpts nonceGen onSolver Nothing $ \_ sym -> do
        let monline = Just SomeOnlineSolver
        setupSolver cruxOpts (pathSatSolverOutput cruxOpts) sym
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts sym monline
        withSolverAdapter offSolver $ \adapter -> do
          -- We have to add the configuration options from the solver adapter,
          -- since they weren't included in the symbolic backend configuration
          -- with the initial setup of the online solver (since it could have
          -- been a different solver)
          unless (CCS.sameSolver onSolver offSolver) $ do
            -- In this case we don't add the extra configuration options because
            -- the online solver setup already added them.  What4 raises an
            -- error if the same option is added more than once.
            extendConfig (WS.solver_adapter_config_options adapter) (getConfiguration sym)
          doSimWithResults cruxOpts simCallback compRef glsRef sym execFeatures profInfo monline (proveGoalsOffline adapter)
    Right (CCS.OnlyOfflineSolver offSolver) -> do
      withFloatRepr (Proxy @s) cruxOpts offSolver $ \floatRepr -> do
        withSolverAdapter offSolver $ \adapter -> do
          sym <- CBS.newSimpleBackend floatRepr nonceGen
          setupSolver cruxOpts Nothing sym
          -- Since we have a bare SimpleBackend here, we have to initialize it
          -- with the options taken from the solver adapter (e.g., solver path)
          extendConfig (WS.solver_adapter_config_options adapter) (getConfiguration sym)
          (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts sym Nothing
          doSimWithResults cruxOpts simCallback compRef glsRef sym execFeatures profInfo Nothing (proveGoalsOffline adapter)
    Right (CCS.OnlineSolverWithSeparateOnlineGoals pathSolver goalSolver) -> do
      -- This case is probably the most complicated because it needs two
      -- separate online solvers.  The two must agree on the floating point
      -- mode.
      withSelectedOnlineBackend cruxOpts nonceGen pathSolver Nothing $ \floatRepr1 pathSatSym -> do
        setupSolver cruxOpts (pathSatSolverOutput cruxOpts) pathSatSym
        (execFeatures, profInfo) <- setupExecutionFeatures cruxOpts pathSatSym (Just SomeOnlineSolver)
        withSelectedOnlineBackend cruxOpts nonceGen goalSolver (Just (floatReprString floatRepr1)) $ \floatRepr2 goalSym -> do
          setupSolver cruxOpts (onlineSolverOutput cruxOpts) goalSym
          -- NOTE: We pass in an explicit requested float mode in our second
          -- online solver connection instantiation to ensure that both solvers
          -- use the same float mode, so no mismatch here should be possible.
          case testEquality floatRepr1 floatRepr2 of
            Just Refl ->
              doSimWithResults cruxOpts simCallback compRef glsRef pathSatSym execFeatures profInfo (Just SomeOnlineSolver) (proveGoalsOnline goalSym)
            Nothing -> fail "Impossible: the argument interpretation produced two different float modes"

    Left rsns -> fail ("Invalid solver configuration:\n" ++ unlines rsns)


type ProverCallback sym =
  forall ext .
    CruxOptions ->
    SimCtxt sym ext ->
    Maybe (Goals (LPred sym AssumptionReason) (LPred sym SimError)) ->
    IO (Maybe (Goals (LPred sym AssumptionReason) (LPred sym SimError, ProofResult (Either (LPred sym AssumptionReason) (LPred sym SimError)))))

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
  (Logs, IsSymInterface sym, sym ~ WEB.ExprBuilder s st fs) =>
  CruxOptions ->
  SimulatorCallback ->
  IORef ProgramCompleteness ->
  IORef (Seq.Seq (ProvedGoals (Either AssumptionReason SimError))) ->
  sym ->
  [GenericExecutionFeature sym] ->
  ProfData sym ->
  Maybe (SomeOnlineSolver sym) ->
  ProverCallback sym
    {- ^ The function to use to prove goals; this is intended to be
         one of 'proveGoalsOffline' or 'proveGoalsOnline' -} ->
  IO CruxSimulationResult
doSimWithResults cruxOpts simCallback compRef glsRef sym execFeatures profInfo monline goalProver = do

  frm <- pushAssumptionFrame sym
  inFrame profInfo "<Crux>" $ do
    -- perform tool-specific setup

    RunnableStateWithExtensions initSt exts <- initSimulatorState simCallback sym monline
    -- execute the simulator
    case pathStrategy cruxOpts of
      AlwaysMergePaths ->
        do res <- executeCrucible (map genericToExecutionFeature execFeatures ++ exts) initSt
           void $ resultCont frm (Result res)
      SplitAndExploreDepthFirst ->
        do (i,ws) <- executeCrucibleDFSPaths (map genericToExecutionFeature execFeatures ++ exts) initSt (resultCont frm . Result)
           say "Crux" ("Total paths explored: " ++ show i)
           unless (null ws) $
             sayWarn "Crux"
               (unwords [show (Seq.length ws), "paths remaining not explored: program might not be fully verified"])

  when (simVerbose cruxOpts > 1) $ do
    say "Crux" "Simulation complete."
  when (isProfiling cruxOpts) $ writeProf profInfo
  CruxSimulationResult <$> readIORef compRef <*> readIORef glsRef

 where
 failfast = proofGoalsFailFast cruxOpts

 resultCont frm (Result res) =
   do timedOut <-
        case res of
          TimeoutResult {} ->
            do sayWarn "Crux" "Simulation timed out! Program might not be fully verified!"
               writeIORef compRef ProgramIncomplete
               return True
          _ -> return False
      popUntilAssumptionFrame sym frm
      let ctx = execResultContext res
      inFrame profInfo "<Prove Goals>" $ do
        todo <- getProofObligations sym
        when (isJust todo) $
          say "Crux" "Attempting to prove verification conditions."
        proved <- goalProver cruxOpts ctx todo
        mgt <- provedGoalsTree ctx proved
        case mgt of
          Nothing -> return (not timedOut)
          Just gt ->
            do modifyIORef glsRef (Seq.|> gt)
               return (not (timedOut || (failfast && countDisprovedGoals gt > 0)))

isProfiling :: CruxOptions -> Bool
isProfiling cruxOpts = profileCrucibleFunctions cruxOpts || profileSolver cruxOpts

computeExitCode :: CruxSimulationResult -> ExitCode
computeExitCode (CruxSimulationResult cmpl gls) = maximum . (base:) . fmap f . toList $ gls
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

reportStatus ::
  Logs =>
  CruxSimulationResult ->
  IO ()
reportStatus (CruxSimulationResult cmpl gls) =
  do let tot        = sum (fmap countTotalGoals gls)
         proved     = sum (fmap countProvedGoals gls)
         incomplete = sum (fmap countIncompleteGoals gls)
         disproved  = sum (fmap countDisprovedGoals gls)
         unknown    = sum (fmap countUnknownGoals gls) - incomplete
     if tot == 0 then
       do say "Crux" "All goals discharged through internal simplification."
     else
       do say "Crux" "Goal status:"
          say "Crux" ("  Total: " ++ show tot)
          say "Crux" ("  Proved: " ++ show proved)
          say "Crux" ("  Disproved: " ++ show disproved)
          say "Crux" ("  Incomplete: " ++ show incomplete)
          say "Crux" ("  Unknown: " ++ show unknown)
     if | disproved > 0 ->
            sayFail "Crux" "Overall status: Invalid."
        | incomplete > 0 || cmpl == ProgramIncomplete ->
            sayWarn "Crux" "Overall status: Unknown (incomplete)."
        | unknown > 0 -> sayWarn "Crux" "Overall status: Unknown."
        | proved == tot -> sayOK "Crux" "Overall status: Valid."
        | otherwise ->
            sayFail "Crux" "Internal error computing overall status."
