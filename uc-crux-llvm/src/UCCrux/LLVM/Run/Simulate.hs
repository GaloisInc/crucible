{-
Module       : UCCrux.LLVM.Run.Simulate
Description  : Run the simulator once.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Run.Simulate
  ( UCCruxSimulationResult (..),
    CreateOverrideFn(..),
    SymCreateOverrideFn(..),
    symCreateOverrideFn,
    SimulatorHooks(..),
    SimulatorCallbacks(..),
    defaultCallbacks,
    addOverrides,
    createUnsoundOverrides,
    runSimulatorWithCallbacks,
    runSimulator,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), view, to)
import           Control.Monad (void, unless)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (for_, toList)
import qualified Data.IORef as IORef
import           Data.IORef (IORef)
import           Data.List (isInfixOf)
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Sequence (Seq)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Traversable (for)
import           Data.Void (Void)

import           GHC.Exts (proxy#)

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
import           Lang.Crucible.LLVM (llvmGlobalsToCtx, registerModuleFn)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Intrinsics as LLVMIntrinsics
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, LLVMAnnMap, MemImpl, MemOptions)
import           Lang.Crucible.LLVM.Translation (transContext, llvmMemVar, llvmTypeCtx, cfgMap, allModuleDeclares)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Lang.Crucible.LLVM.MemModel.Partial (BoolAnn(BoolAnn))
import           Lang.Crucible.LLVM.Extension (LLVM)

-- crux
import qualified Crux
import           Crux.Config.Common (CruxOptions)
import           Crux.Log (outputHandle)
import qualified Crux.Report as Crux (provedGoalTraces)
import qualified Crux.Types as Crux

 -- crux-llvm
import           Crux.LLVM.Config (LLVMOptions(..))
import           Crux.LLVM.Overrides (ArchOk, cruxLLVMOverrides)
import           Crux.LLVM.Simulate (setupSimCtxt)

 -- local
import           UCCrux.LLVM.Classify (classifyAssertion, classifyBadBehavior)
import           UCCrux.LLVM.Classify.Types (Located(Located), Explanation(..), Uncertainty(..), ppProgramLoc)
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
        IO (PolymorphicLLVMOverride arch (Crux.Crux sym) sym)
    }

-- | Used in 'SimulatorHooks' to register caller-specified overrides.
newtype SymCreateOverrideFn sym arch =
  SymCreateOverrideFn
    { runSymCreateOverrideFn ::
        sym -> IO (PolymorphicLLVMOverride arch (Crux.Crux sym) sym)
    }

symCreateOverrideFn ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  CreateOverrideFn arch ->
  SymCreateOverrideFn sym arch
symCreateOverrideFn = SymCreateOverrideFn . runCreateOverrideFn

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.6
-- compatibility.
data UCCruxSimulationResult m arch (argTypes :: Ctx (FullType m)) = UCCruxSimulationResult
  { unsoundness :: Unsoundness,
    explanations :: [Located (Explanation m arch argTypes)]
  }

-- | Based on 'Crux.SimulatorHooks'
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.6
-- compatibility.
data SimulatorHooks sym m arch (argTypes :: Ctx (FullType m)) r =
  SimulatorHooks
    { createOverrideHooks :: [SymCreateOverrideFn sym arch]
    , resultHook ::
        sym ->
        -- | Pre-simulation memory
        MemImpl sym ->
        -- | Arguments passed to the entry point
        Assignment (Shape m (SymValue sym arch)) argTypes ->
        Crux.CruxSimulationResult ->
        UCCruxSimulationResult m arch argTypes ->
        IO r
    }
  deriving Functor

-- | Based on 'Crux.SimulatorCallbacks'
newtype SimulatorCallbacks m arch (argTypes :: Ctx (FullType m)) r =
  SimulatorCallbacks
    { getSimulatorCallbacks ::
        forall sym t st fs.
          IsSymInterface sym =>
          (sym ~ What4.ExprBuilder t st fs) =>
          HasLLVMAnn sym =>
          IO (SimulatorHooks sym m arch argTypes r)
    }
  deriving Functor

defaultCallbacks ::
  SimulatorCallbacks m arch argTypes ( Crux.CruxSimulationResult
                                     , UCCruxSimulationResult m arch argTypes
                                     )
defaultCallbacks =
  SimulatorCallbacks $
   return $
     SimulatorHooks
       { createOverrideHooks = []
       , resultHook =
           \_sym _mem _args cruxResult ucCruxResult ->
             return (cruxResult, ucCruxResult)
       }

addOverrides ::
  [CreateOverrideFn arch] ->
  SimulatorCallbacks m arch argTypes r ->
  SimulatorCallbacks m arch argTypes r
addOverrides newOverrides cbs =
  SimulatorCallbacks $
    do SimulatorHooks oldOverrides resHook <- getSimulatorCallbacks cbs
       return $
         SimulatorHooks
           { createOverrideHooks =
               oldOverrides ++ map symCreateOverrideFn newOverrides
           , resultHook = resHook
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

registerOverrides ::
  (?intrinsicsOpts :: LLVMIntrinsics.IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  ArchOk arch =>
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  AppContext ->
  ModuleContext m arch ->
  -- | One word description of what kind of override this is
  Text ->
  [LLVMIntrinsics.OverrideTemplate (personality sym) sym arch rtp l a] ->
  Crucible.OverrideSim (personality sym) sym LLVM rtp l a ()
registerOverrides appCtx modCtx kind overrides =
  do for_ overrides $
       \override ->
         liftIO $
           (appCtx ^. log) Hi $
             Text.unwords
               ["Registering", kind, "override for", describeOverride override]

     LLVMIntrinsics.register_llvm_overrides_
       (modCtx ^. moduleTranslation . transContext)
       overrides
       (allModuleDeclares (modCtx ^. llvmModule . to getModule))
  where
    describeOverride :: LLVMIntrinsics.OverrideTemplate p sym arch rtp l a -> Text
    describeOverride override =
      case LLVMIntrinsics.overrideTemplateMatcher override of
        LLVMIntrinsics.ExactMatch nm -> Text.pack nm
        LLVMIntrinsics.PrefixMatch nm ->
          "functions with prefix " <> Text.pack nm
        LLVMIntrinsics.SubstringsMatch nms ->
          "functions with names containing " <> Text.pack (show nms)

registerDefinedFns ::
  (?intrinsicsOpts :: LLVMIntrinsics.IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  ArchOk arch =>
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.OverrideSim (personality sym) sym LLVM rtp l a ()
registerDefinedFns appCtx modCtx =
  do let trans = modCtx ^. moduleTranslation
     let llvmCtxt = trans ^. transContext
     for_ (Map.toList (cfgMap trans)) $
       \(L.Symbol symb, cfg) ->
         do liftIO $
              (appCtx ^. log) Hi $
                Text.unwords ["Registering definition of", Text.pack symb]
            registerModuleFn llvmCtxt cfg

mkCallbacks ::
  forall r m arch argTypes blocks ret msgs.
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  SimulatorCallbacks m arch argTypes r ->
  Constraints m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  LLVMOptions ->
  Crux.SimulatorCallbacks msgs r
mkCallbacks appCtx modCtx funCtx halloc callbacks constraints cfg llvmOpts =
  Crux.SimulatorCallbacks $
    do -- References written to during setup
       memRef <- IORef.newIORef Nothing
       argRef <- IORef.newIORef Nothing
       argAnnRef <- IORef.newIORef Nothing
       argShapeRef <- IORef.newIORef Nothing

       -- References written to during simulation
       bbMapRef <- IORef.newIORef (Map.empty :: LLVMAnnMap sym)
       explRef <- IORef.newIORef []
       skipReturnValueAnns <- IORef.newIORef Map.empty
       skipOverrideRef <- IORef.newIORef Set.empty
       let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
       (unsoundOverrideRef, uOverrides) <-
         createUnsoundOverrides modCtx

       -- Hooks
       let ?recordLLVMAnnotation =
             \an bb -> IORef.modifyIORef bbMapRef (Map.insert an bb)
       SimulatorHooks overrides resHook <-
         getSimulatorCallbacks callbacks

       return $
         Crux.SimulatorHooks
           { Crux.setupHook =
             \sym _symOnline ->
               setupHook sym uOverrides overrides skipOverrideRef memRef argRef argAnnRef argShapeRef skipReturnValueAnns
           , Crux.onErrorHook =
             \sym ->
               return (onErrorHook sym skipOverrideRef memRef argRef argAnnRef argShapeRef bbMapRef explRef skipReturnValueAnns)
           , Crux.resultHook =
             \sym result ->
               mkResultHook sym skipOverrideRef unsoundOverrideRef explRef memRef argShapeRef result resHook
           }
  where
    setupHook ::
      Crux.Logs msgs =>
      IsSymInterface sym =>
      HasLLVMAnn sym =>
      sym ->
      -- | Unsound overrides
      [CreateOverrideFn arch] ->
      -- | Overrides that were passed in as arguments
      [SymCreateOverrideFn sym arch] ->
      IORef (Set SkipOverrideName) ->
      IORef (Maybe (MemImpl sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
      IO (Crux.RunnableState sym)
    setupHook sym uOverrideFns overrideFns skipOverrideRef memRef argRef argAnnRef argShapeRef skipReturnValueAnnotations =
      do
        let trans = modCtx ^. moduleTranslation
        let llvmCtxt = trans ^. transContext
        let memOptions = memOpts llvmOpts
        let ?lc = llvmCtxt ^. llvmTypeCtx
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
                    --
                    -- Register all the functions that are defined in the
                    -- module. This happens first so that later overrides can
                    -- replace definitions if needed.
                    registerDefinedFns appCtx modCtx

                    -- Register default LLVM overrides
                    --
                    -- Stuff like LLVM intrinsics, `free`, `malloc`
                    let llMod = modCtx ^. llvmModule . to getModule
                    LLVMIntrinsics.register_llvm_overrides llMod [] [] llvmCtxt

                    -- These are aligned for easy reading in the logs
                    let sCruxLLVM = "crux-llvm"
                    let sUnsound  = "unsound  "
                    let sArg      = "arg      "
                    let sSkip     = "skip     "

                    -- Crux-LLVM overrides, i.e., crucible_*
                    registerOverrides appCtx modCtx sCruxLLVM (cruxLLVMOverrides proxy#)

                    overrides <- liftIO $ for overrideFns (($ sym) . runSymCreateOverrideFn)
                    let overrides' = map getPolymorphicLLVMOverride overrides
                    registerOverrides appCtx modCtx sArg overrides'

                    -- Register unsound overrides, e.g., `getenv`
                    uOverrides <-
                      liftIO $ traverse (($ sym) . runCreateOverrideFn) uOverrideFns
                    let uOverrides' = map getPolymorphicLLVMOverride uOverrides
                    registerOverrides appCtx modCtx sUnsound uOverrides'

                    -- NB: This should be run after all other overrides have
                    -- been registered, since it creates and registers an
                    -- override to skip each function that is
                    -- declared-but-not-defined and doesn't yet have an override
                    -- registered.
                    sOverrides <-
                      unsoundSkipOverrides
                        modCtx
                        sym
                        trans
                        skipOverrideRef
                        skipReturnValueAnnotations
                        (constraints ^. returnConstraints)
                        (L.modDeclares (modCtx ^. llvmModule . to getModule))
                    let sOverrides' = map getPolymorphicLLVMOverride sOverrides
                    registerOverrides appCtx modCtx sSkip sOverrides'

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
      IORef (Set SkipOverrideName) ->
      IORef (Maybe (MemImpl sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)))) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (LLVMAnnMap sym) ->
      IORef [Located (Explanation m arch argTypes)] ->
      IORef (Map.Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes))) ->
      Crux.Explainer sym t Void
    onErrorHook sym skipOverrideRef memRef argRef argAnnRef argShapeRef bbMapRef explRef skipReturnValueAnnotations _groundEvalFn gl =
      do
        let rd = panic "onErrorHook" ["IORef not written during simulation"]
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

    mkResultHook ::
      IsSymInterface sym =>
      (sym ~ What4.ExprBuilder t st fs) =>
      sym ->
      IORef (Set SkipOverrideName) ->
      IORef (Set UnsoundOverrideName) ->
      IORef [Located (Explanation m arch argTypes)] ->
      IORef (Maybe (MemImpl sym)) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      Crux.CruxSimulationResult ->
      (sym ->
        MemImpl sym ->
        Assignment (Shape m (SymValue sym arch)) argTypes ->
        Crux.CruxSimulationResult ->
        UCCruxSimulationResult m arch argTypes ->
        IO r) ->
      IO r
    mkResultHook sym skipOverrideRef unsoundOverrideRef explRef memRef argShapeRef cruxResult resHook =
      do for_ (traces cruxResult) $
           \trace ->
             do liftIO $ (appCtx ^. log) Hi "Trace:"
                for_ trace $
                  \loc ->
                    unless (What4.InternalPos == What4.plSourceLoc loc) $
                      liftIO $ (appCtx ^. log) Hi ("  " <> ppProgramLoc loc)

         unsoundness' <-
           Unsoundness
             <$> IORef.readIORef unsoundOverrideRef
               <*> IORef.readIORef skipOverrideRef
         ucCruxResult <-
           UCCruxSimulationResult unsoundness'
             <$> case cruxResult of
               Crux.CruxSimulationResult Crux.ProgramIncomplete _ ->
                 pure
                   [ Located
                       What4.initializationLoc
                       (ExUncertain (UTimeout (funCtx ^. functionName)))
                   ]
               _ -> IORef.readIORef explRef
         let rd = panic "mkResultHook" ["IORef not written during simulation"]
         mem <- fromMaybe rd <$> IORef.readIORef memRef
         argShapes <- fromMaybe rd <$> IORef.readIORef argShapeRef
         resHook sym mem argShapes cruxResult ucCruxResult

    traces :: Crux.CruxSimulationResult -> Set (Seq What4.ProgramLoc)
    traces =
      Set.fromList .
        toList .
        mconcat .
        toList .
        fmap (Crux.provedGoalTraces . snd) .
        Crux.cruxSimResultGoals



runSimulatorWithCallbacks ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  Constraints m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  SimulatorCallbacks m arch argTypes r ->
  IO r
runSimulatorWithCallbacks appCtx modCtx funCtx halloc preconditions cfg cruxOpts llvmOpts callbacks =
  Crux.runSimulator
    cruxOpts
    ( mkCallbacks
        appCtx
        modCtx
        funCtx
        halloc
        callbacks
        preconditions
        cfg
        llvmOpts
    )

runSimulator ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
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
runSimulator appCtx modCtx funCtx halloc overrides preconditions cfg cruxOpts llvmOpts =
  runSimulatorWithCallbacks
    appCtx
    modCtx
    funCtx
    halloc
    preconditions
    cfg
    cruxOpts
    llvmOpts
    (SimulatorCallbacks $
      return $
        SimulatorHooks
          { createOverrideHooks = map symCreateOverrideFn overrides
          , resultHook =
              \_sym _mem _args _cruxResult ucCruxResult -> return ucCruxResult
          })
