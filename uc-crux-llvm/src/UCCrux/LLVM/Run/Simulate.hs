{-
Module       : UCCrux.LLVM.Run.Simulate
Description  : Run the simulator once.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Run.Simulate
  ( UCCruxSimulationResult (..),
    CreateOverrideFn(..),
    createUnsoundOverrides,
    runSimulator,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), view, to)
import           Control.Monad (void, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (for_)
import qualified Data.IORef as IORef
import           Data.IORef (IORef)
import           Data.List (isInfixOf)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Traversable (for)
import           Data.Void (Void)

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Context (Assignment)
import           Data.Parameterized.Some (Some)

import qualified What4.Expr.Builder as What4
import qualified What4.Interface as What4
import qualified What4.ProgramLoc as What4

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Backend as Crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM (llvmGlobalsToCtx)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Intrinsics as LLVMIntrinsics
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, LLVMAnnMap, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.Translation (transContext, llvmMemVar, llvmTypeCtx)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Lang.Crucible.LLVM.MemModel.Partial (BoolAnn(BoolAnn))
import           Lang.Crucible.LLVM.Extension (LLVM)

-- crux
import qualified Crux
import qualified Crux.Types as Crux

import           Crux.Config.Common (CruxOptions)
import           Crux.Log (outputHandle)

 -- crux-llvm
import           Crux.LLVM.Config (LLVMOptions(..))
import           Crux.LLVM.Overrides (ArchOk)
import           Crux.LLVM.Simulate (setupSimCtxt, registerFunctions)

 -- local
import           UCCrux.LLVM.Classify (classifyAssertion, classifyBadBehavior)
import           UCCrux.LLVM.Classify.Types (Located(Located), Explanation(..), Uncertainty(..))
import           UCCrux.LLVM.Constraints (Constraints, returnConstraints, relationalConstraints)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, functionName)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTranslation)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Module (getModule)
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName, unsoundSkipOverrides)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, getPolymorphicLLVMOverride, getForAllSymArch)
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName, unsoundOverrides)
import           UCCrux.LLVM.FullType.Type (FullType, MapToCrucibleType)
import           UCCrux.LLVM.PP (ppRegMap)
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness(Unsoundness))
import           UCCrux.LLVM.Setup (setupExecution, SetupResult(SetupResult), SymValue)
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Setup.Monad (TypedSelector)
import           UCCrux.LLVM.Shape (Shape)
{- ORMOLU_ENABLE -}

newtype CreateOverrideFn arch =
  CreateOverrideFn
    { runCreateOverrideFn ::
        forall sym.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        sym ->
        IO (PolymorphicLLVMOverride (Crux.Crux sym) sym arch)
    }

registerOverrides ::
  (?intrinsicsOpts :: LLVMIntrinsics.IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  ArchOk arch =>
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  AppContext ->
  ModuleContext m arch ->
  [PolymorphicLLVMOverride p sym arch] ->
  Crucible.OverrideSim p sym LLVM rtp l a ()
registerOverrides appCtx modCtx overrides =
  do for_ overrides $
       \override ->
         liftIO $
           (appCtx ^. log) Hi $
             Text.unwords
               [ "Registering override for",
                 describeOverride (getPolymorphicLLVMOverride override)
               ]

     LLVMIntrinsics.register_llvm_overrides
       (modCtx ^. llvmModule . to getModule)
       []
       (map getPolymorphicLLVMOverride overrides)
       (modCtx ^. moduleTranslation . transContext)
  where
    describeOverride :: LLVMIntrinsics.OverrideTemplate p sym arch rtp l a -> Text
    describeOverride override =
      case LLVMIntrinsics.overrideTemplateMatcher override of
        LLVMIntrinsics.ExactMatch nm -> Text.pack nm
        LLVMIntrinsics.PrefixMatch nm ->
          "functions with prefix " <> Text.pack nm
        LLVMIntrinsics.SubstringsMatch nms ->
          "functions with names containing " <> Text.pack (show nms)

simulateLLVM ::
  forall m arch argTypes blocks ret msgs.
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  IORef [Located (Explanation m arch argTypes)] ->
  IORef (Set SkipOverrideName) ->
  [CreateOverrideFn arch] ->
  Constraints m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  LLVMOptions ->
  Crux.SimulatorCallbacks msgs Crux.CruxSimulationResult
simulateLLVM appCtx modCtx funCtx halloc explRef skipOverrideRef overrideFns constraints cfg llvmOpts =
  Crux.SimulatorCallbacks $
    do -- References written to during setup
       memRef <- IORef.newIORef Nothing
       argRef <- IORef.newIORef Nothing
       argAnnRef <- IORef.newIORef Nothing
       argShapeRef <- IORef.newIORef Nothing
       -- References written to during simulation
       bbMapRef <- IORef.newIORef (Map.empty :: LLVMAnnMap sym)
       skipReturnValueAnns <- IORef.newIORef Map.empty
       return $
         Crux.SimulatorHooks
           { Crux.setupHook =
             \sym _symOnline ->
               setupHook sym memRef argRef argAnnRef argShapeRef bbMapRef skipReturnValueAnns
           , Crux.onErrorHook =
             \sym -> return (onErrorHook sym memRef argRef argAnnRef argShapeRef bbMapRef skipReturnValueAnns)
           , Crux.resultHook = \_sym result -> return result
           }
  where
    setupHook ::
      Crux.Logs msgs =>
      IsSymInterface sym =>
      sym ->
      IORef (Maybe (MemImpl sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (LLVMAnnMap sym) ->
      IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
      IO (Crux.RunnableState sym)
    setupHook sym memRef argRef argAnnRef argShapeRef bbMapRef skipReturnValueAnnotations =
      do
        let trans = modCtx ^. moduleTranslation
        let llvmCtxt = trans ^. transContext
        let memOptions = memOpts llvmOpts
        let ?lc = llvmCtxt ^. llvmTypeCtx
        let ?recordLLVMAnnotation = \an bb -> IORef.modifyIORef bbMapRef (Map.insert an bb)
        let ?intrinsicsOpts = intrinsicsOpts llvmOpts
        let ?memOpts = memOptions
        let simctx =
              (setupSimCtxt halloc sym memOptions (llvmMemVar llvmCtxt))
                { Crucible.printHandle = view outputHandle ?outputConfig
                }

        unless (null (constraints ^. relationalConstraints)) $
          panic "simulateLLVM" ["Unimplemented: relational constraints"]

        setupResult <-
          liftIO $ setupExecution appCtx modCtx funCtx sym constraints
        (mem, argAnnotations, assumptions, argShapes, args) <-
          case setupResult of
            (SetupResult mem anns assumptions, (argShapes, args)) ->
              pure (mem, anns, assumptions, argShapes, args)

        -- Save initial state so that it can be used during classification
        IORef.writeIORef memRef (Just mem)
        IORef.writeIORef argRef (Just args)
        IORef.writeIORef argAnnRef (Just argAnnotations)
        IORef.writeIORef argShapeRef (Just argShapes)

        -- Assume all predicates necessary to satisfy the deduced preconditions
        assume (funCtx ^. functionName) sym assumptions

        let globSt = llvmGlobalsToCtx llvmCtxt mem
        let initSt =
              Crucible.InitialState simctx globSt Crucible.defaultAbortHandler CrucibleTypes.UnitRepr $
                Crucible.runOverrideSim CrucibleTypes.UnitRepr $
                  do
                    -- TODO(lb): This could be more lazy: We could install only
                    -- those functions that are used by the program. It's an open
                    -- question whether this would be faster: it would mean more
                    -- superfluous errors when the program inevitably calls
                    -- functions that haven't yet been installed, but would mean
                    -- faster startup time generally, especially for large
                    -- programs where the vast majority of functions wouldn't be
                    -- called from any particular function. Needs some
                    -- benchmarking.
                    registerFunctions llvmOpts (modCtx ^. llvmModule . to getModule) trans Nothing
                    overrides <- liftIO $ for overrideFns (($ sym) . runCreateOverrideFn)
                    sOverrides <-
                      unsoundSkipOverrides
                        modCtx
                        sym
                        trans
                        skipOverrideRef
                        skipReturnValueAnnotations
                        (constraints ^. returnConstraints)
                        (L.modDeclares (modCtx ^. llvmModule . to getModule))
                    registerOverrides appCtx modCtx (overrides ++ sOverrides)

                    liftIO $ (appCtx ^. log) Hi $ "Running " <> funCtx ^. functionName <> " on arguments..."
                    printed <- ppRegMap modCtx funCtx sym mem args
                    mapM_ (liftIO . (appCtx ^. log) Hi . Text.pack . show) printed
                    void $ Crucible.callCFG cfg args

        return (Crux.RunnableState initSt)

    -- | Classify errors and write back the results to an IORef so they can be
    -- read in the outer loop
    onErrorHook ::
      IsSymInterface sym =>
      (sym ~ What4.ExprBuilder t st fs) =>
      sym ->
      IORef (Maybe (MemImpl sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (LLVMAnnMap sym) ->
      IORef (Map.Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
      Crux.Explainer sym t Void
    onErrorHook sym memRef argRef argAnnRef argShapeRef bbMapRef skipReturnValueAnnotations _groundEvalFn gl =
      do
        let rd = panic "onErrorHook" []
        -- Read info from initial state
        mem <- fromMaybe rd <$> IORef.readIORef memRef
        args <- fromMaybe rd <$> IORef.readIORef argRef
        argAnnotations <- fromMaybe rd <$> IORef.readIORef argAnnRef
        argShapes <- fromMaybe rd <$> IORef.readIORef argShapeRef
        -- Read info from execution
        bb <- IORef.readIORef bbMapRef
        let loc = gl ^. Crucible.labeledPredMsg . to Crucible.simErrorLoc
        case flip Map.lookup bb . BoolAnn
          =<< What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
          Nothing ->
            case What4.getAnnotation sym (gl ^. Crucible.labeledPred) of
              Just _ ->
                panic "simulateLLVM" ["Unexplained error: no error for annotation."]
              Nothing ->
                IORef.modifyIORef explRef . (:) $
                  case gl ^. Crucible.labeledPredMsg . to Crucible.simErrorReason of
                    Crucible.ResourceExhausted msg ->
                      Located loc (ExExhaustedBounds msg)
                    Crucible.AssertFailureSimError msg _ ->
                      if "Call to assert" `isInfixOf` msg -- HACK
                        then
                          classifyAssertion
                            sym
                            (gl ^. Crucible.labeledPred)
                            loc
                        else
                          Located
                            loc
                            (ExUncertain (UMissingAnnotation (gl ^. Crucible.labeledPredMsg)))
                    _ ->
                      Located
                        loc
                        (ExUncertain (UMissingAnnotation (gl ^. Crucible.labeledPredMsg)))
          Just badBehavior ->
            do
              -- Helpful for debugging:
              -- putStrLn "~~~~~~~~~~~"
              -- putStrLn (show (LLVMErrors.ppBB badBehavior))

              liftIO $ (appCtx ^. log) Hi ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior)))
              skipped <- IORef.readIORef skipOverrideRef
              retAnns <- IORef.readIORef skipReturnValueAnnotations
              classifyBadBehavior
                appCtx
                modCtx
                funCtx
                sym
                mem
                skipped
                (gl ^. Crucible.labeledPredMsg)
                args
                (Map.union argAnnotations retAnns)
                argShapes
                badBehavior
                >>= IORef.modifyIORef explRef . (:)
        return mempty

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.6
-- compatibility.
data UCCruxSimulationResult m arch (argTypes :: Ctx (FullType m)) = UCCruxSimulationResult
  { unsoundness :: Unsoundness,
    explanations :: [Located (Explanation m arch argTypes)]
  }

createUnsoundOverrides ::
  (?lc :: TypeContext) =>
  ArchOk arch =>
  proxy arch ->
  IO (IORef (Set UnsoundOverrideName), [CreateOverrideFn arch])
createUnsoundOverrides proxy =
  do unsoundOverrideRef <- IORef.newIORef Set.empty
     return
       ( unsoundOverrideRef
       , map (\ov ->
                CreateOverrideFn
                  (\_sym -> pure (getForAllSymArch ov proxy)))
             (unsoundOverrides unsoundOverrideRef)
       )

runSimulator ::
  ( Crux.Logs msgs,
    Crux.SupportsCruxLogMessage msgs,
    ArchOk arch
  ) =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  [CreateOverrideFn arch] ->
  Constraints m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  IO (UCCruxSimulationResult m arch argTypes)
runSimulator appCtx modCtx funCtx halloc overrideFns preconditions cfg cruxOpts llvmOpts =
  do
    explRef <- IORef.newIORef []
    skipOverrideRef <- IORef.newIORef Set.empty
    let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
    (unsoundOverrideRef, mkUnsoundOverrides) <-
      createUnsoundOverrides modCtx
    cruxResult <-
      Crux.runSimulator
        cruxOpts
        ( simulateLLVM
            appCtx
            modCtx
            funCtx
            halloc
            explRef
            skipOverrideRef
            (mkUnsoundOverrides ++ overrideFns)
            preconditions
            cfg
            llvmOpts
        )
    unsoundness' <-
      Unsoundness
        <$> IORef.readIORef unsoundOverrideRef
          <*> IORef.readIORef skipOverrideRef
    UCCruxSimulationResult unsoundness'
      <$> case cruxResult of
        Crux.CruxSimulationResult Crux.ProgramIncomplete _ ->
          pure
            [ Located
                What4.initializationLoc
                (ExUncertain (UTimeout (funCtx ^. functionName)))
            ]
        _ -> IORef.readIORef explRef
