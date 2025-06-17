{-|
Module : Lang.Crucible.Syntax.Overrides

A collection of overrides that are useful in testing and debugging Crucible.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Syntax.Overrides
  ( setupOverrides
  ) where

import qualified Control.Lens as Lens
import Control.Lens hiding ((:>), Empty)
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class
import qualified Control.Monad.State.Strict as State
import System.IO

import Data.Parameterized.Context hiding (view)

import What4.Expr.Builder
import What4.ProgramLoc
import What4.Solver (LogData(..), defaultLogData)
import What4.Solver.Z3 (z3Adapter)

import Lang.Crucible.Backend
import qualified Lang.Crucible.Backend.Prove as CB
import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Utils.Seconds as Sec
import qualified Lang.Crucible.Utils.Timeout as CTO
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP


setupOverrides ::
  (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
  sym -> HandleAllocator -> IO [(FnBinding p sym ext, Position)]
setupOverrides _ ha =
  do f1 <- FnBinding <$> mkHandle ha "proveObligations"
                     <*> pure (UseOverride (mkOverride "proveObligations" proveObligations))
     f2 <- FnBinding <$> mkHandle ha "crucible-print-assumption-state"
                     <*> pure (UseOverride (mkOverride "crucible-print-assumption-state" printAssumptionState))
     return [(f1, InternalPos), (f2, InternalPos)]


proveObligations :: (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
  OverrideSim p sym ext r EmptyCtx UnitType (RegValue sym UnitType)
proveObligations =
  ovrWithBackend $ \bak ->
  do let sym = backendGetSym bak
     h <- printHandle <$> getContext
     liftIO $ do
       hPutStrLn h "Attempting to prove all outstanding obligations!\n"

       let logData = defaultLogData { logCallbackVerbose = \_ -> hPutStrLn h
                                    , logReason = "assertion proof" }
       let timeout = CTO.Timeout (Sec.secondsFromInt 5)
       let prover = CB.offlineProver timeout sym logData z3Adapter
       let strat = CB.ProofStrategy prover CB.keepGoing
       let ppResult o =
             \case
               CB.Proved {}  -> unlines ["Proof Succeeded!", show $ ppSimError (proofGoal o ^. labeledPredMsg)]
               CB.Disproved {} -> unlines ["Proof failed!", show $ ppSimError (proofGoal o ^. labeledPredMsg)]
               CB.Unknown {} -> unlines ["Proof inconclusive!", show $ ppSimError (proofGoal o ^. labeledPredMsg)]
       let printer = CB.ProofConsumer $ \o r -> hPutStrLn h (ppResult o r)
       runExceptT (CB.proveCurrentObligations bak strat printer) >>=
         \case
           Left CTO.TimedOut -> hPutStrLn h "Proof timed out!"
           Right () -> pure ()

       clearProofObligations bak

printAssumptionState ::
  IsSymInterface sym =>
  OverrideSim p sym ext r EmptyCtx UnitType (RegValue sym UnitType)
printAssumptionState = do
  ctx <- State.gets (Lens.view stateContext)
  let hdl = printHandle ctx
  CS.ovrWithBackend $ \bak -> liftIO $ do
    let render =  PP.renderIO hdl . PP.layoutSmart PP.defaultLayoutOptions
    render =<< debugPrintBackendState bak
