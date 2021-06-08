{-
Module       : UCCrux.LLVM.Run.Loop
Description  : Run the simulator in a loop, creating a 'BugfindingResult'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Run.Loop
  ( bugfindingLoop,
    loopOnFunction,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.))
import           Control.Monad (foldM)
import           Data.Function ((&))
import qualified Data.Text as Text
import           Panic (Panic)

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (MemOptions, withPtrWidth)
import Lang.Crucible.LLVM.Extension( LLVM )
import Lang.Crucible.LLVM.Translation (llvmPtrWidth, transContext)

-- crux
import Crux.Config.Common
import Crux.Log as Crux

 -- local
import Crux.LLVM.Config (throwCError, CError(MissingFun), memOpts)
import Crux.LLVM.Overrides

import           UCCrux.LLVM.Classify.Types (partitionExplanations)
import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Constraints (ppConstraints, emptyConstraints, addConstraint, ppExpansionError)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentFullTypes, makeFunctionContext, functionName, ppFunctionContextError)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation, CFGWithTypes(..), findFun)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, catchUnimplemented)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.FullType (MapToCrucibleType)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import qualified UCCrux.LLVM.Run.Simulate as Sim
{- ORMOLU_ENABLE -}

-- | Run the simulator in a loop, creating a 'BugfindingResult'
bugfindingLoop ::
  ArchOk arch =>
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  MemOptions ->
  Crucible.HandleAllocator ->
  IO (BugfindingResult m arch argTypes)
bugfindingLoop appCtx modCtx funCtx cfg cruxOpts memOptions halloc =
  do
    let runSim preconds =
          Sim.runSimulator appCtx modCtx funCtx halloc preconds cfg cruxOpts memOptions

    -- Loop, learning preconditions and reporting errors
    let loop truePositives constraints precondTags unsoundness =
          do
            -- TODO(lb) We basically ignore symbolic assertion failures. Maybe
            -- configurably don't?
            simResult <- runSim constraints
            let (newTruePositives, newConstraints, newUncertain, newResourceExhausted) =
                  partitionExplanations (Sim.explanations simResult)
            let (newPrecondTags, newConstraints') = unzip newConstraints
            let allConstraints =
                  foldM
                    (addConstraint modCtx (funCtx ^. argumentFullTypes))
                    constraints
                    (concat newConstraints')
                    & \case
                      Left err ->
                        panic
                          "bugfindingLoop"
                          ["Error adding constraints", Text.unpack (ppExpansionError err)]
                      Right allCs -> allCs

            let allTruePositives = truePositives <> newTruePositives
            let allPrecondTags = newPrecondTags <> precondTags
            let allUnsoundness = unsoundness <> Sim.unsoundness simResult
            let result =
                  BugfindingResult
                    newUncertain
                    allPrecondTags
                    ( Result.makeFunctionSummary
                        allConstraints
                        -- This only needs to look at the latest run because we
                        -- don't continue if there was any uncertainty
                        newUncertain
                        allTruePositives
                        -- This only needs to look at the latest run because we
                        -- don't continue if the bounds were hit
                        ( if null newResourceExhausted
                            then Result.DidntHitBounds
                            else Result.DidHitBounds
                        )
                        allUnsoundness
                    )
            case (null newConstraints, newTruePositives, not (null newUncertain), not (null newResourceExhausted)) of
              (True, [], False, _) -> pure result
              (noNewConstraints, _, isUncertain, isExhausted) ->
                do
                  if noNewConstraints || isUncertain || isExhausted
                    then pure result -- We can't really go on
                    else do
                      (appCtx ^. log) Hi "New preconditions:"
                      (appCtx ^. log) Hi $ Text.pack (show (ppConstraints allConstraints))
                      loop allTruePositives allConstraints allPrecondTags allUnsoundness

    let emptyConstraints' =
          emptyConstraints (funCtx ^. argumentFullTypes)
    loop [] emptyConstraints' [] mempty

loopOnFunction ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  UCCruxLLVMOptions ->
  String ->
  IO (Either (Panic Unimplemented) Result.SomeBugfindingResult)
loopOnFunction appCtx modCtx halloc cruxOpts ucOpts fn =
  catchUnimplemented $
    llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( do
                CFGWithTypes cfg argFTys _retTy _varArgs <-
                  case findFun modCtx fn of
                    Nothing -> throwCError (MissingFun fn)
                    Just cfg -> pure cfg
                case makeFunctionContext modCtx (Text.pack fn) argFTys (Crucible.cfgArgTypes cfg) of
                  Left err -> panic "loopOnFunction" [Text.unpack (ppFunctionContextError err)]
                  Right funCtx ->
                    do
                      (appCtx ^. log) Hi $ "Checking function " <> (funCtx ^. functionName)
                      SomeBugfindingResult
                        <$> bugfindingLoop
                          appCtx
                          modCtx
                          funCtx
                          cfg
                          cruxOpts
                          (memOpts (Config.ucLLVMOptions ucOpts))
                          halloc
            )
      )
