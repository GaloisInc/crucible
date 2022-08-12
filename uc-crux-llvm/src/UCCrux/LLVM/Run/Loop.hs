{-# LANGUAGE ImplicitParams #-}
{-
Module       : UCCrux.LLVM.Run.Loop
Description  : Run the simulator in a loop, creating a 'BugfindingResult'
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

TODO: Rename this module (and the functions in it) to something more useful,
like \"Infer\".
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Run.Loop
  ( bugfindingLoopWithCallbacks,
    bugfindingLoop,
    loopOnFunction,
    loopOnFunctions,
    zipResults,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), to)
import           Control.Monad (foldM)
import           Control.Exception (throw)
import           Data.Foldable (toList)
import           Data.Function ((&))
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import qualified Data.Map.Merge.Strict as Map
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Traversable (for)
import           Panic (Panic)

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (withPtrWidth)
import Lang.Crucible.LLVM.Extension( LLVM )
import Lang.Crucible.LLVM.Translation (llvmPtrWidth, transContext, llvmTypeCtx)

-- crux
import           Crux.Config.Common (CruxOptions)
import           Crux.Log as Crux

-- crux-llvm
import           Crux.LLVM.Config (LLVMOptions, throwCError, CError(MissingFun))
import qualified Crux.LLVM.Config as CruxLLVM
import           Crux.LLVM.Overrides

 -- local
import           UCCrux.LLVM.Classify.Types (Located(locatedValue), Explanation, partitionExplanations)
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameToString, functionNameFromString)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentFullTypes, makeFunctionContext, functionName)
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation, CFGWithTypes(..), findFun, llvmModule, defnTypes)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, catchUnimplemented)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.FullType (MapToCrucibleType)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr(FuncSigRepr))
import           UCCrux.LLVM.Module (DefnSymbol, FuncSymbol(..), defnSymbolToString, makeDefnSymbol, getModule)
import           UCCrux.LLVM.Overrides.Spec (createSpecOverride)
import           UCCrux.LLVM.Precondition (Preconds, NewConstraint, ppPreconds, emptyPreconds, addPrecond, ppExpansionError)
import           UCCrux.LLVM.Run.EntryPoints (EntryPoints, getEntryPoints, makeEntryPoints)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import qualified UCCrux.LLVM.Run.Simulate as Sim
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness)
import           UCCrux.LLVM.Specs.Type (SomeSpecs(SomeSpecs))
{- ORMOLU_ENABLE -}

-- | Run the simulator in a loop, creating a 'BugfindingResult'
--
-- Also returns the individual 'UCCruxSimulationResult' results in the order in
-- which they were encountered, along with any data returned by the result
-- hook.
bugfindingLoopWithCallbacks ::
  forall r m msgs arch argTypes blocks ret.
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
  -- | Customizations to the symbolic execution process. See 'SimulatorHooks'.
  Sim.SimulatorCallbacks m arch argTypes (Sim.UCCruxSimulationResult m arch argTypes, r) ->
  IO (BugfindingResult m arch argTypes, Seq (Sim.UCCruxSimulationResult m arch argTypes, r))
bugfindingLoopWithCallbacks appCtx modCtx funCtx cfg cruxOpts llvmOpts halloc callbacks =
  do
    let runSim preconds =
          Sim.runSimulatorWithCallbacks appCtx modCtx funCtx halloc preconds cfg cruxOpts llvmOpts callbacks

    -- Loop, learning preconditions and reporting errors
    let loop constraints results unsoundness =
          do
            -- TODO(lb) We basically ignore symbolic assertion failures. Maybe
            -- configurably don't?
            (simResult, r) <- runSim constraints
            let newExpls = Sim.explanations simResult
            let (_, newPreconds, _, _) =
                  partitionExplanations locatedValue newExpls
            let (_, newPreconds') = unzip (map locatedValue newPreconds)
            let allPreconds = addPreconds constraints (concat newPreconds')
            let allUnsoundness = unsoundness <> Sim.unsoundness simResult
            let allResults = results Seq.|> (simResult, r)
            if shouldStop newExpls
              then
                pure
                  ( makeResult
                      allPreconds
                      (concatMap (Sim.explanations . fst) (toList allResults))
                      allUnsoundness,
                    allResults
                  )
              else do
                (appCtx ^. log) Hi "New preconditions:"
                (appCtx ^. log) Hi $ Text.pack (show (ppPreconds allPreconds))
                loop allPreconds allResults allUnsoundness

    loop (emptyPreconds (funCtx ^. argumentFullTypes)) Seq.empty mempty
  where
    addPreconds ::
      Preconds m argTypes ->
      [NewConstraint m argTypes] ->
      Preconds m argTypes
    addPreconds constraints newPreconds =
      foldM
        (addPrecond modCtx (funCtx ^. argumentFullTypes))
        constraints
        newPreconds
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
            (noNewPreconds, _, isUncertain, isExhausted) ->
              -- We can't proceed if (1) new input constraints weren't learned,
              -- (2) uncertainty was encountered, or (3) resource bounds were
              -- exhausted.
              noNewPreconds || isUncertain || isExhausted

    makeResult ::
      Preconds m argTypes ->
      [Located (Explanation m arch argTypes)] ->
      Unsoundness ->
      BugfindingResult m arch argTypes
    makeResult constraints expls unsoundness =
      let (truePositives, newPreconds, uncertain, resourceExhausted) =
            partitionExplanations locatedValue (toList expls)
          (precondTags, _) = unzip (map locatedValue newPreconds)
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

-- | Run the simulator in a loop, creating a 'BugfindingResult'
--
-- Also returns the individual 'UCCruxSimulationResult' results in the order in
-- which they were encountered.
bugfindingLoop ::
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
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  IO (BugfindingResult m arch argTypes, Seq (Sim.UCCruxSimulationResult m arch argTypes))
bugfindingLoop appCtx modCtx funCtx cfg cruxOpts llvmOpts halloc specs =
  post <$>
    bugfindingLoopWithCallbacks appCtx modCtx funCtx cfg cruxOpts llvmOpts halloc callbacks
  where
    swap (cruxResult, ucCruxResult) = (ucCruxResult, cruxResult)
    post (result, results) = (result, fmap fst results)

    -- Callbacks that register overrides for all the provided function specs.
    callbacks =
      Sim.addOverrides
        (map (uncurry mkSpecOverride) (Map.toList specs))
        (fmap swap Sim.defaultCallbacks)

    mkSpecOverride funcSymb specs_ =
      Sim.CreateOverrideFn $ \bak tracker ->
        do SomeSpecs fsRep@FuncSigRepr{} specs' <- return specs_
           let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
           let ?memOpts = CruxLLVM.memOpts llvmOpts
           return (createSpecOverride modCtx bak tracker funcSymb fsRep specs')

loopOnFunction ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  -- | Entry point for symbolic execution
  DefnSymbol m ->
  IO (Either (Panic Unimplemented) (SomeBugfindingResult m arch))
loopOnFunction appCtx modCtx halloc cruxOpts llOpts specs fn =
  catchUnimplemented $
    llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( do
                CFGWithTypes cfg argFTys _retTy _varArgs <-
                  findFun modCtx (FuncDefnSymbol fn)
                let funCtx =
                      makeFunctionContext modCtx fn argFTys (Crucible.cfgArgTypes cfg)
                (appCtx ^. log) Hi $ "Checking function " <> (funCtx ^. functionName)
                uncurry (SomeBugfindingResult argFTys)
                  <$> bugfindingLoop
                    appCtx
                    modCtx
                    funCtx
                    cfg
                    cruxOpts
                    llOpts
                    halloc
                    specs
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
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  EntryPoints m ->
  IO (Map (DefnSymbol m) (SomeBugfindingResult m arch))
loopOnFunctions appCtx modCtx halloc cruxOpts llOpts specs entries =
  Map.fromList
    <$> llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( for (getEntryPoints entries) $
                \entry ->
                  (entry,) . either throw id
                    <$> loopOnFunction appCtx modCtx halloc cruxOpts llOpts specs entry
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
  IO (Map.Map FunctionName (SomeBugfindingResult m1 arch1, SomeBugfindingResult m2 arch2))
zipResults appCtx modCtx1 modCtx2 halloc cruxOpts llOpts entries =
  do
    let getFuncs modc =
          Set.fromList
            ( map
                ((\(L.Symbol f) -> f) . L.defName)
                (L.modDefines (modc ^. llvmModule . to getModule))
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
                 case makeDefnSymbol (L.Symbol nm) (modCtx ^. defnTypes) of
                   Nothing -> throwCError (MissingFun nm)
                   Just d -> pure d)
              (if null entries
               then intersect
               else map functionNameToString entries)
    entries1 <- makeEntries modCtx1
    entries2 <- makeEntries modCtx2
    results1 <- loopOnFunctions appCtx modCtx1 halloc cruxOpts llOpts Map.empty entries1
    results2 <- loopOnFunctions appCtx modCtx2 halloc cruxOpts llOpts Map.empty entries2
    let mkFunName = functionNameFromString . defnSymbolToString
    pure $
      -- Note: It's a postcondition of loopOnFunctions that these two maps
      -- have the same keys.
      Map.merge
        Map.dropMissing
        Map.dropMissing
        (Map.zipWithMatched (const (,)))
        (Map.mapKeys mkFunName results1)
        (Map.mapKeys mkFunName results2)
