{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Overrides
  ( setupOverrides
  ) where

import qualified Control.Lens as Lens
import Control.Lens hiding ((:>), Empty)
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class
import qualified Control.Monad.State.Strict as State
import System.IO

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import Data.Parameterized.Context hiding (view)
import qualified Data.Parameterized.Map as MapF

import qualified What4.Concretize as WC
import What4.Expr.Builder
import What4.Interface
import What4.ProgramLoc
import qualified What4.Protocol.Online as WPO
import What4.Solver (LogData(..), defaultLogData)
import What4.Solver.Z3 (z3Adapter)

import Lang.Crucible.Backend
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Backend.Prove as CB
import qualified Lang.Crucible.Concretize as Conc
import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Utils.Seconds as Sec
import qualified Lang.Crucible.Utils.Timeout as CTO


-- | Set up all test overrides
setupOverrides ::
  ( IsSymBackend sym bak
  , sym ~ ExprBuilder scope st fs
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  HandleAllocator ->
  IO [(FnBinding p sym ext, Position)]
setupOverrides bak ha =
  do let sym = backendGetSym bak
     f1 <- FnBinding <$> mkHandle ha "symbolicBranchTest"
                     <*> pure (UseOverride (mkOverride "symbolicBranchTest" symbolicBranchTest))
     f2 <- FnBinding <$> mkHandle ha "symbolicBranchesTest"
                     <*> pure (UseOverride (mkOverride "symbolicBranchesTest" symbolicBranchesTest))
     f3 <- FnBinding <$> mkHandle ha "nondetBranchesTest"
                     <*> pure (UseOverride (mkOverride "nondetBranchesTest" (nondetBranchesTest (Just sym))))
     f4 <- FnBinding <$> mkHandle ha "concBool"
                     <*> pure (UseOverride (mkOverride "concBool" (concBool bak)))
     f5 <- FnBinding <$> mkHandle ha "proveObligations"
                     <*> pure (UseOverride (mkOverride "proveObligations" (proveObligations (Just sym))))
     f6 <- FnBinding <$> mkHandle ha "crucible-print-assumption-state"
                     <*> pure (UseOverride (mkOverride "crucible-print-assumption-state" (printAssumptionState (Just sym))))
     return [(f1, InternalPos),(f2,InternalPos),(f3,InternalPos),(f4,InternalPos),(f5,InternalPos),(f6,InternalPos)]


-- Test the @symbolicBranch@ override operation.
symbolicBranchTest :: IsSymInterface sym =>
  OverrideSim p sym ext r
    (EmptyCtx ::> BoolType ::> IntegerType ::> IntegerType) IntegerType (RegValue sym IntegerType)
symbolicBranchTest =
  do args <- getOverrideArgs
     let p = reg @0 args
     z <- symbolicBranch p args thn (Just (OtherPos "then branch")) args els (Just (OtherPos "else branch"))
     return z

 where
 thn = reg @1 <$> getOverrideArgs
 els = reg @2 <$> getOverrideArgs

-- Test concretization of `Bool`
concBool :: IsSymInterface sym =>
  ( IsSymBackend sym bak
  , sym ~ ExprBuilder scope st fs
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  OverrideSim p sym ext r
    (EmptyCtx ::> BoolType) BoolType (RegValue sym BoolType)
concBool bak = do
  let sym = backendGetSym bak
  args <- getOverrideArgs
  mb <- liftIO (Conc.concRegValue bak MapF.empty BoolRepr (reg @0 args))
  case mb of
    Left WC.SolverUnknown -> fail "Solver returned UNKNOWN"
    Left WC.UnsatInitialAssumptions -> fail "Unsat assumptions"
    Right b -> pure (if b then truePred sym else falsePred sym)

-- Test the @symbolicBranches@ override operation.
symbolicBranchesTest :: IsSymInterface sym =>
  OverrideSim p sym ext r
    (EmptyCtx ::> IntegerType ::> IntegerType) IntegerType (RegValue sym IntegerType)
symbolicBranchesTest =
  do sym <- getSymInterface
     x <- reg @0 <$> getOverrideArgs
     x2 <- liftIO $ intAdd sym x x
     p1 <- liftIO $ intEq sym x =<< intLit sym 1
     p2 <- liftIO $ intEq sym x =<< intLit sym 2
     p3 <- liftIO $ intEq sym x =<< intLit sym 3
     z <- symbolicBranches (RegMap (Empty :> RegEntry IntegerRepr x2))
            [ (p1, b1, Just (OtherPos "first branch"))
            , (p2, b2, Just (OtherPos "second branch"))
            , (p3, b3 sym, Just (OtherPos "third branch"))
            , (truePred sym, b4, Just (OtherPos "default branch"))
            ]
     return z

  where
  b1 =
     do y <- reg @1 <$> getOverrideArgs
        return y

  b2 =
     do x2 <- reg @2 <$> getOverrideArgs
        overrideReturn x2

  b3 sym =
     do y <- reg @1 <$> getOverrideArgs
        x2 <- reg @2 <$> getOverrideArgs
        liftIO $ intAdd sym y x2

  b4 = overrideError (GenericSimError "fall-through branch")


-- Test the @nondetBranches@ override operation.
--
-- If the first argument is zero, returns the second argument. If it is one,
-- returns the third argument. If it could be either, returns both (i.e.,
-- nondeterministic choice). If it couldn't be either, errors out.
nondetBranchesTest :: IsSymInterface sym =>
  proxy sym ->
  OverrideSim p sym ext r
    (EmptyCtx ::> IntegerType ::> IntegerType ::> IntegerType) IntegerType (RegValue sym IntegerType)
nondetBranchesTest _proxy =
  do sym <- getSymInterface
     args <- getOverrideArgs
     cond <- reg @0 <$> getOverrideArgs
     p1 <- liftIO $ intEq sym cond =<< intLit sym 0
     p2 <- liftIO $ intEq sym cond =<< intLit sym 1
     fallbackPred <- liftIO $ notPred sym =<< orPred sym p1 p2
     let fallback = overrideError (GenericSimError "fall-through branch")
     nondetBranches args
       [ (p1, reg @1 <$> getOverrideArgs, Just (OtherPos "first branch"))
       , (p2, reg @2 <$> getOverrideArgs, Just (OtherPos "second branch"))
       , (fallbackPred, fallback, Just (OtherPos "default branch"))
       ]

-- | Prove all outstanding proof obligations
proveObligations :: (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
  proxy sym ->
  OverrideSim p sym ext r EmptyCtx UnitType (RegValue sym UnitType)
proveObligations _proxy =
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

-- | Print the current assumption state
printAssumptionState ::
  IsSymInterface sym =>
  proxy sym ->
  OverrideSim p sym ext r EmptyCtx UnitType (RegValue sym UnitType)
printAssumptionState _proxy = do
  ctx <- State.gets (Lens.view stateContext)
  let hdl = printHandle ctx
  CS.ovrWithBackend $ \bak -> liftIO $ do
    let render =  PP.renderIO hdl . PP.layoutSmart PP.defaultLayoutOptions
    let sym = CB.backendGetSym bak
    state <- getBackendState bak
    render (ppAssumptionState (Just sym) state)
