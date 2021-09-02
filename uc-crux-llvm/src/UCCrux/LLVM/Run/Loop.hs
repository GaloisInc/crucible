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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Run.Loop
  ( bugfindingLoop,
    loopOnFunction,
    loopOnFunctions,
    zipResults,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.))
import           Control.Monad (foldM)
import           Control.Exception (throw)
import           Data.Foldable (toList)
import           Data.Function ((&))
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Traversable (for)
import           Panic (Panic)

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (withPtrWidth)
import Lang.Crucible.LLVM.Extension( LLVM )
import Lang.Crucible.LLVM.Translation (llvmPtrWidth, transContext)

-- crux
import Crux.Config.Common
import Crux.Log as Crux

 -- local
import Crux.LLVM.Config (LLVMOptions, throwCError, CError(MissingFun))
import Crux.LLVM.Overrides

import           UCCrux.LLVM.Classify.Types (Located(locatedValue), Explanation, partitionExplanations)
import           UCCrux.LLVM.Constraints (Constraints, NewConstraint, ppConstraints, emptyConstraints, addConstraint, ppExpansionError)
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameToString)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentFullTypes, makeFunctionContext, functionName, ppFunctionContextError)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation, CFGWithTypes(..), findFun, llvmModule, declTypes)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, catchUnimplemented)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.FullType (MapToCrucibleType)
import           UCCrux.LLVM.FullType.Translation (DeclSymbol, getDeclSymbol, makeDeclSymbol)
import           UCCrux.LLVM.Run.EntryPoints (EntryPoints, getEntryPoints, makeEntryPoints)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import qualified UCCrux.LLVM.Run.Simulate as Sim
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness)
{- ORMOLU_ENABLE -}

-- | Run the simulator in a loop, creating a 'BugfindingResult'
--
-- Also returns the individual 'UCCruxSimulationResult' results in the order in
-- which they were encountered.
bugfindingLoop ::
  forall m msgs arch argTypes blocks ret.
  ArchOk arch =>
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  Crucible.HandleAllocator ->
  IO (BugfindingResult m arch argTypes, Seq (Sim.UCCruxSimulationResult m arch argTypes))
bugfindingLoop appCtx modCtx funCtx cfg cruxOpts llvmOpts halloc =
  do
    let runSim preconds =
          Sim.runSimulator appCtx modCtx funCtx halloc preconds cfg cruxOpts llvmOpts

    -- Loop, learning preconditions and reporting errors
    let loop constraints results unsoundness =
          do
            -- TODO(lb) We basically ignore symbolic assertion failures. Maybe
            -- configurably don't?
            simResult <- runSim constraints
            let newExpls = Sim.explanations simResult
            let (_, newConstraints, _, _) =
                  partitionExplanations locatedValue newExpls
            let (_, newConstraints') = unzip (map locatedValue newConstraints)
            let allConstraints = addConstraints constraints (concat newConstraints')
            let allUnsoundness = unsoundness <> Sim.unsoundness simResult
            let allResults = results Seq.|> simResult
            if shouldStop newExpls
              then
                pure
                  ( makeResult
                      allConstraints
                      (concatMap Sim.explanations (toList allResults))
                      allUnsoundness,
                    allResults
                  )
              else do
                (appCtx ^. log) Hi "New preconditions:"
                (appCtx ^. log) Hi $ Text.pack (show (ppConstraints allConstraints))
                loop allConstraints allResults allUnsoundness

    loop (emptyConstraints (funCtx ^. argumentFullTypes)) Seq.empty mempty
  where
    addConstraints ::
      Constraints m argTypes ->
      [NewConstraint m argTypes] ->
      Constraints m argTypes
    addConstraints constraints newConstraints =
      foldM
        (addConstraint modCtx (funCtx ^. argumentFullTypes))
        constraints
        newConstraints
        & \case
          Left err ->
            panic
              "bugfindingLoop"
              ["Error adding constraints", Text.unpack (ppExpansionError err)]
          Right allCs -> allCs

    -- Given these results from simulation, should we continue looping?
    shouldStop ::
      [Located (Explanation m arch argTypes)] ->
      Bool
    shouldStop expls =
      let (truePositives, constraints, uncertain, resourceExhausted) =
            partitionExplanations locatedValue expls
       in case ( null constraints,
                 truePositives,
                 not (null uncertain),
                 not (null resourceExhausted)
               ) of
            (True, [], False, _) ->
              -- No new constraints were learned, nor were any bugs found, nor
              -- was there any uncertain results. The code is conditionally
              -- safe, we can stop here.
              True
            (noNewConstraints, _, isUncertain, isExhausted) ->
              -- We can't proceed if (1) new input constraints weren't learned,
              -- (2) uncertainty was encountered, or (3) resource bounds were
              -- exhausted.
              noNewConstraints || isUncertain || isExhausted

    makeResult ::
      Constraints m argTypes ->
      [Located (Explanation m arch argTypes)] ->
      Unsoundness ->
      BugfindingResult m arch argTypes
    makeResult constraints expls unsoundness =
      let (truePositives, newConstraints, uncertain, resourceExhausted) =
            partitionExplanations locatedValue (toList expls)
          (precondTags, _) = unzip (map locatedValue newConstraints)
       in BugfindingResult
            uncertain
            precondTags
            ( Result.makeFunctionSummary
                constraints
                uncertain
                truePositives
                ( if null resourceExhausted
                    then Result.DidntHitBounds
                    else Result.DidHitBounds
                )
                unsoundness
            )

loopOnFunction ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  DeclSymbol m ->
  IO (Either (Panic Unimplemented) Result.SomeBugfindingResult)
loopOnFunction appCtx modCtx halloc cruxOpts llOpts fn =
  catchUnimplemented $
    llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( do
                CFGWithTypes cfg argFTys _retTy _varArgs <-
                  pure (findFun modCtx fn)
                case makeFunctionContext modCtx fn argFTys (Crucible.cfgArgTypes cfg) of
                  Left err -> panic "loopOnFunction" [Text.unpack (ppFunctionContextError err)]
                  Right funCtx ->
                    do
                      (appCtx ^. log) Hi $ "Checking function " <> (funCtx ^. functionName)
                      uncurry SomeBugfindingResult
                        <$> bugfindingLoop
                          appCtx
                          modCtx
                          funCtx
                          cfg
                          cruxOpts
                          llOpts
                          halloc
            )
      )

-- | Postcondition: The keys of the returned map are exactly the input function
-- names.
loopOnFunctions ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  EntryPoints m ->
  IO (Map.Map String SomeBugfindingResult)
loopOnFunctions appCtx modCtx halloc cruxOpts llOpts entries =
  Map.fromList
    <$> llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( for (getEntryPoints entries) $
                \entry ->
                  let L.Symbol name = getDeclSymbol entry
                  in (name,) . either throw id
                       <$> loopOnFunction appCtx modCtx halloc cruxOpts llOpts entry
            )
      )

-- | Given two modules, run the bugfinding loop on the specified functions
-- (which need to be present in both modules), or if @--explore@ was set, run the
-- loop on all functions present in both modules.
zipResults ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m1 arch1 ->
  ModuleContext m2 arch2 ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Entry points. If empty, check functions that are in both modules.
  [FunctionName] ->
  IO (Map.Map String (SomeBugfindingResult, SomeBugfindingResult))
zipResults appCtx modCtx1 modCtx2 halloc cruxOpts llOpts entries =
  do
    let getFuncs modc =
          Set.fromList
            ( map
                ((\(L.Symbol f) -> f) . L.defName)
                (L.modDefines (modc ^. llvmModule))
            )
    let intersect =
          Set.toList
            (Set.intersection
              (getFuncs modCtx1)
              (getFuncs modCtx2))
    let makeEntries :: ModuleContext m arch -> IO (EntryPoints m)
        makeEntries modCtx =
          makeEntryPoints <$>
            mapM
              (\nm ->
                 case makeDeclSymbol (L.Symbol nm) (modCtx ^. declTypes) of
                   Nothing -> throwCError (MissingFun nm)
                   Just d -> pure d)
              (if null entries
               then intersect
               else map functionNameToString entries)
    entries1 <- makeEntries modCtx1
    entries2 <- makeEntries modCtx2
    results1 <- loopOnFunctions appCtx modCtx1 halloc cruxOpts llOpts entries1
    results2 <- loopOnFunctions appCtx modCtx2 halloc cruxOpts llOpts entries2
    pure $
      -- Note: It's a postcondition of loopOnFunctions that these two maps
      -- have the same keys.
      Map.merge
        Map.dropMissing
        Map.dropMissing
        (Map.zipWithMatched (const (,)))
        results1
        results2
