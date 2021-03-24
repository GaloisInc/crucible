{-
Module       : UCCrux.LLVM.Run.Loop
Description  : Run the simulator in a loop, creating a 'BugfindingResult'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE ImplicitParams #-}
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
import           Control.Monad.IO.Class (liftIO)
import           Data.Function ((&))
import qualified Data.Map.Strict as Map
import           Data.String (fromString)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl))
import           Panic (Panic)

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (MemOptions, withPtrWidth)
import Lang.Crucible.LLVM.Extension( LLVM )
import Lang.Crucible.LLVM.Translation (llvmPtrWidth, transContext, ModuleCFGMap, cfgMap)

-- crux
import Crux.Config.Common
import Crux.Log (Logs, OutputConfig(..))

 -- local
import Crux.LLVM.Config (throwCError, CError(MissingFun), memOpts)
import Crux.LLVM.Overrides

import           UCCrux.LLVM.Classify.Types (partitionExplanations)
import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Constraints (ppConstraints, emptyConstraints, addConstraint, ppExpansionError)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, SomeFunctionContext(..), argumentFullTypes, makeFunctionContext, functionName, ppFunctionContextError, moduleTypes)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation)
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
  ( ?outputConfig :: OutputConfig,
    ArchOk arch
  ) =>
  AppContext ->
  ModuleContext arch ->
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
                    (addConstraint (funCtx ^. argumentFullTypes) (funCtx ^. moduleTypes))
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

    loop [] (emptyConstraints (funCtx ^. argumentFullTypes)) [] mempty

findFun ::
  Logs =>
  String ->
  ModuleCFGMap ->
  IO (Crucible.AnyCFG LLVM)
findFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, anyCfg) -> pure anyCfg
    Nothing -> throwCError (MissingFun nm)

loopOnFunction ::
  (?outputConfig :: OutputConfig) =>
  AppContext ->
  ModuleContext arch ->
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
                Crucible.AnyCFG cfg <- liftIO $ findFun fn (cfgMap (modCtx ^. moduleTranslation))
                case makeFunctionContext modCtx (Text.pack fn) (Crucible.cfgArgTypes cfg) of
                  Left err -> panic "loopOnFunction" [Text.unpack (ppFunctionContextError err)]
                  Right (SomeFunctionContext funCtx Refl) ->
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
