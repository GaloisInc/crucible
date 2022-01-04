{- |
Module           : Cruces.ExploreCrux
Description      : Wrappers for driving Crucibles with Crux
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Cruces.ExploreCrux where

import           Control.Monad.IO.Class
import           Control.Monad (when)
import           Control.Lens
import           Data.Generics.Product.Fields (field, setField)
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map
import           System.IO (Handle)

import           What4.Interface
import           What4.Config

import           Data.Parameterized.Pair(Pair)
import qualified Data.Parameterized.Context as Ctx
import           Lang.Crucible.FunctionHandle (HandleAllocator)
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.Simulator
import           Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import           Lang.Crucible.Backend

import qualified Crux
import qualified Crux.Types

import           Crucibles.SchedulingAlgorithm hiding (_exec, exec)
import           Crucibles.Execution
import           Crucibles.ExploreTypes
import           Crucibles.Primitives
import           Crucibles.Explore
import           Crucibles.Scheduler
import           Crucibles.Common

import           Crux.Goal (proveGoalsOnline)
import           Crux.Types (totalProcessedGoals, provedGoals)

-- | Callback for crucible-syntax exploration
exploreCallback :: forall alg.
  (?bound::Int, SchedulingAlgorithm alg) =>
  Crux.Logs Crux.CruxLogMessage =>
  Crux.CruxOptions ->
  HandleAllocator ->
  Handle ->
  (forall s bak.
   (IsSymInterface s, IsBoolSolver s bak) =>
   bak ->
        IO ( FnVal s Ctx.EmptyCtx C.UnitType
           , ExplorePrimitives (ThreadExec alg s () C.UnitType) s ()
           , [Pair C.TypeRepr C.GlobalVar]
           , FunctionBindings (ThreadExec alg s () C.UnitType) s ())
           ) ->
  Crux.SimulatorCallbacks Crux.CruxLogMessage Crux.Types.CruxSimulationResult
exploreCallback cruxOpts ha outh mkSym =
  Crux.withCruxLogMessage $
  Crux.SimulatorCallbacks $
    return $
      Crux.SimulatorHooks
        { Crux.setupHook =
            \bak symOnline ->
              do (mainHdl, prims, globs, fns) <- mkSym bak
                 let simCtx = initSimContext bak emptyIntrinsicTypes ha outh fns emptyExtensionImpl emptyExploration

                     st0  = InitialState simCtx emptyGlobals defaultAbortHandler C.UnitRepr $
                                runOverrideSim
                                  C.UnitRepr
                                  (exploreOvr
                                     bak
                                     symOnline
                                     cruxOpts
                                     (regValue <$> callFnVal mainHdl emptyRegMap))

                     feats = [scheduleFeature prims globs]

                 return $ Crux.RunnableStateWithExtensions st0 feats
        , Crux.onErrorHook = \_bak -> return (\_ _ -> return mempty)
        , Crux.resultHook = \_bak result -> return result
        }


-- | Empty exploration state
emptyExploration :: SchedulingAlgorithm alg => Exploration alg ext C.UnitType sym
emptyExploration = Exploration { _exec      = initialExecutions
                               , _scheduler = s0
                               , _schedAlg  = initialAlgState
                               , _num       = 0
                               , _gVars     = mempty
                               }
  where
    s0 = Scheduler { _threads      = V.fromList [EmptyThread]
                   , _retRepr      = C.UnitRepr
                   , mainCont      = return ()
                   , _activeThread = 0
                   , _numSwitches  = 0
                   }

-- | Wrap an override to produce a NEW override that will explore the executions of a concurrent program.
-- Must also use the 'scheduleFeature' 'ExecutionFeature'
exploreOvr :: forall sym bak ext alg ret rtp msgs.
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  (?bound::Int, IsSymInterface sym, IsBoolSolver sym bak, IsSyntaxExtension ext, SchedulingAlgorithm alg, RegValue sym ret ~ ()) =>
  bak -> 
  Maybe (Crux.SomeOnlineSolver sym bak) ->
  Crux.CruxOptions ->
  (forall rtp'. OverrideSim (Exploration alg ext ret sym) sym ext rtp' Ctx.EmptyCtx ret (RegValue sym ret)) ->
  OverrideSim (Exploration alg ext ret sym) sym ext rtp Ctx.EmptyCtx ret (RegValue sym ret)
exploreOvr bak symOnline cruxOpts mainAct =
  do assmSt  <- liftIO $ saveAssumptionState bak
     verbOpt <- liftIO $ getOptionSetting verbosity $ getConfiguration sym
     verb    <- fromInteger <$> (liftIO $ getOpt verbOpt)
     loop verb assmSt

  where
    sym = backendGetSym bak

    loop ::
      Int ->
      AssumptionState sym ->
      forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    loop verb assmSt =
      do reset verb assmSt
         exploreAPath
         retH verb assmSt

    checkGoals :: forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret Bool
    checkGoals =
      Crux.withCruxLogMessage $
      case symOnline of
      Just (Crux.SomeOnlineSolver _) ->
        do ctx <- use stateContext
           todo <- liftIO $ getProofObligations bak
           let cruxOpts' = over (field @"outputOptions") (setField @"quietMode" True . setField @"simVerbose" 0) cruxOpts
           mkOutCfg <- liftIO $ Crux.defaultOutputConfig Crux.cruxLogMessageToSayWhat
           let ?outputConfig = mkOutCfg (Just (Crux.outputOptions cruxOpts'))
           (processed, _) <- liftIO $ proveGoalsOnline bak cruxOpts' ctx (\_ _ -> return mempty) todo
           let provedAll = totalProcessedGoals processed == provedGoals processed
           when provedAll $ liftIO $ clearProofObligations bak
           return provedAll
      Nothing -> return True

    retH :: Int -> AssumptionState sym -> forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    retH verb assmSt =
     do stateExpl.num %= (+1)
        exc          <- use stateExec
        stateExplAlg %= processExecution exc
        alg          <- use stateExplAlg

        when (verb > 2) $
           do liftIO $ putStrLn " == Begin Exploration =="
              liftIO $ putStrLn $ ppExecutions exc alg
              liftIO $ putStrLn " == End Exploration   ==\n"

        let amDone = fullyExplored (exc { _currentEventID = 0 }) alg
        provedAllGoals <- checkGoals

        if amDone || not provedAllGoals then
          return ()
        else
          loop verb assmSt

    exploreAPath :: forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    exploreAPath = mainAct

    reset ::  Int -> AssumptionState sym -> forall r. OverrideSim (Exploration alg ext ret sym) sym ext r Ctx.EmptyCtx ret (RegValue sym ret)
    reset verb assmSt =
      do stateExec.currentEventID .= 0
         -- Reset scheduler state
         stateExpl.scheduler.activeThread .= 0
         stateExpl.scheduler.threads      .= V.fromList [EmptyThread]
         stateExpl.scheduler %= \s -> s { mainCont = retH verb assmSt }
         stateExpl.scheduler.numSwitches  .= 0
         -- Per-run exploration bookkeeping
         runUpdateSchedAlg prepareNewExecution
         stateExec.birthdays              .= Map.fromList [(ThreadID 0, 0)]
