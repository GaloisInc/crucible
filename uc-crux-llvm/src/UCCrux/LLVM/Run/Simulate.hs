{-# LANGUAGE TupleSections #-}
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
import           Control.Monad (void, unless, when)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (for_, toList)
import qualified Data.IORef as IORef
import           Data.IORef (IORef)
import           Data.List (isInfixOf)
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Sequence (Seq)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as Text
import           Data.Text (Text)
import           Data.Traversable (for)
import           Data.Void (Void)

import           GHC.Exts (proxy#)

import           Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Context (Assignment)

import qualified What4.Expr.Builder as What4
import qualified What4.Interface as What4
import qualified What4.ProgramLoc as What4

-- crucible
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Backend as Crucible
import           Lang.Crucible.Backend (IsSymInterface, IsSymBackend, backendGetSym)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes

-- crucible-llvm
import           Lang.Crucible.LLVM (llvmGlobalsToCtx, registerLazyModuleFn)
import qualified Lang.Crucible.LLVM.Errors as LLVMErrors
import qualified Lang.Crucible.LLVM.Intrinsics as LLVMIntrinsics
import           Lang.Crucible.LLVM.MemModel.CallStack (ppCallStack)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn, LLVMAnnMap, MemOptions)
import           Lang.Crucible.LLVM.Translation (transContext, llvmMemVar, llvmTypeCtx, allModuleDeclares, modTransDefs)
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
import           UCCrux.LLVM.Classify.Types (Located(Located), Explanation(..), Uncertainty(..))
import           UCCrux.LLVM.Context.App (AppContext, log, soundness)
import           UCCrux.LLVM.Context.Function (FunctionContext, functionName)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTranslation)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.ExprTracker (ExprTracker)
import qualified UCCrux.LLVM.ExprTracker as ET
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Module (FuncSymbol, getModule)
import           UCCrux.LLVM.Newtypes.PreSimulationMem (PreSimulationMem, makePreSimulationMem)
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName, unsoundSkipOverrides)
import           UCCrux.LLVM.Overrides.Spec (SpecUse, createSpecOverride)
import           UCCrux.LLVM.Overrides.Polymorphic (PolymorphicLLVMOverride, getPolymorphicLLVMOverride, getForAllSymArch)
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName, unsoundOverrides)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr(..))
import           UCCrux.LLVM.FullType.Type (FullType, MapToCrucibleType)
import           UCCrux.LLVM.PP (ppRegMap, ppProgramLoc)
import           UCCrux.LLVM.Precondition (Preconds, postconds, relationalPreconds)
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness(Unsoundness))
import           UCCrux.LLVM.Setup (setupExecution, SetupResult(SetupResult), SymValue)
import           UCCrux.LLVM.Setup.Assume (assume)
import           UCCrux.LLVM.Shape (Shape)
import           UCCrux.LLVM.Soundness (Soundness)
import qualified UCCrux.LLVM.Soundness as Sound
import           UCCrux.LLVM.Specs.Type (SomeSpecs)
import qualified UCCrux.LLVM.Specs.Type as Spec
{- ORMOLU_ENABLE -}

newtype CreateOverrideFn m arch =
  CreateOverrideFn
    { runCreateOverrideFn ::
        forall sym bak args.
        IsSymBackend sym bak =>
        HasLLVMAnn sym =>
        bak ->
        -- Origins of created values
        IORef (ExprTracker m sym args) ->
        IO (PolymorphicLLVMOverride arch (Crux.Crux sym) sym)
    }

-- | Used in 'SimulatorHooks' to register caller-specified overrides.
newtype SymCreateOverrideFn m sym bak arch =
  SymCreateOverrideFn
    { runSymCreateOverrideFn ::
        forall args.
        bak ->
        -- Origins of created values
        IORef (ExprTracker m sym args) ->
        IO (PolymorphicLLVMOverride arch (Crux.Crux sym) sym)
    }

symCreateOverrideFn ::
  IsSymBackend sym bak =>
  HasLLVMAnn sym =>
  CreateOverrideFn m arch ->
  SymCreateOverrideFn m sym bak arch
symCreateOverrideFn ov = SymCreateOverrideFn $ runCreateOverrideFn ov

data UCCruxSimulationResult m arch argTypes = UCCruxSimulationResult
  { unsoundness :: Unsoundness,
    explanations :: [Located (Explanation m arch argTypes)]
  }

-- | Like 'Crux.SimulatorHooks', these hooks provide the ability to customize
-- the symbolic execution process. In particular, they allow for registering
-- additional overrides via 'createOverrideHooks', and post-processing the
-- results of symbolic execution with access to the symbolic backend via
-- 'resultHook'.
data SimulatorHooks sym bak m arch argTypes r =
  SimulatorHooks
    { createOverrideHooks :: [SymCreateOverrideFn m sym bak arch]
    -- | The 'PreSimulationMem sym' parameter is the Pre-simulation memory.
    -- The 'Assignment' specifies the Arguments passed to the entry point.
    , resultHook ::
        bak ->
        PreSimulationMem sym ->
        Assignment (Shape m (SymValue sym arch)) argTypes ->
        Crux.CruxSimulationResult ->
        UCCruxSimulationResult m arch argTypes ->
        IO r
    }
  deriving Functor

-- | Callbacks that customize the symbolic execution process.
--
-- Compare to 'Crux.SimulatorCallbacks'.
newtype SimulatorCallbacks m arch (argTypes :: Ctx (FullType m)) r =
  SimulatorCallbacks
    { getSimulatorCallbacks ::
        forall sym bak t st fs.
          IsSymBackend sym bak =>
          (sym ~ What4.ExprBuilder t st fs) =>
          HasLLVMAnn sym =>
          IO (SimulatorHooks sym bak m arch argTypes r)
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
  [CreateOverrideFn m arch] ->
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

-- | Create overrides from specifications.
createSpecOverrides ::
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  ArchOk arch =>
  ModuleContext m arch ->
  Soundness ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  IO (IORef (Set SpecUse), [CreateOverrideFn m arch])
createSpecOverrides modCtx sound specs =
  do specsUsedRef <- IORef.newIORef Set.empty
     return
       ( specsUsedRef
       , map
           (uncurry (mkSpecOverride specsUsedRef))
           (filterSpecsBySoundness (Map.toList specs))
       )
  where

    filterNonEmpty f = NE.nonEmpty . filter f . toList

    filterSpecs ::
      (Spec.Spec n fs -> Bool) ->
      Spec.Specs n fs ->
      Maybe (Spec.Specs n fs)
    filterSpecs f = fmap Spec.Specs . filterNonEmpty f . Spec.getSpecs

    filterSomeSpecs ::
      (forall n fs. Spec.Spec n fs -> Bool) ->
      Spec.SomeSpecs m ->
      Maybe (Spec.SomeSpecs m)
    filterSomeSpecs f (Spec.SomeSpecs fs ss) =
      case filterSpecs f ss of
        Nothing -> Nothing
        Just specs' -> Just (Spec.SomeSpecs fs specs')

    specSoundEnough :: forall n fs. Spec.Spec n fs -> Bool
    specSoundEnough spec =
      Spec.specPreSound spec `Sound.atLeastAsSound` sound &&
        Spec.specPostSound spec `Sound.atLeastAsSound` sound

    filterSpecsBySoundness specsList =
      mapMaybe (\(x, ss) -> (x,) <$> filterSomeSpecs specSoundEnough ss) specsList

    mkSpecOverride specsUsedRef funcSymb specs_ =
      CreateOverrideFn $ \bak tracker ->
        do Spec.SomeSpecs fsRep@FuncSigRepr{} specs' <- return specs_
           return (createSpecOverride modCtx bak specsUsedRef tracker funcSymb fsRep specs')

-- | Create intentionally unsound overrides for library functions.
--
-- If the soundness criterion is anything other than 'Sound.Imprecise', return
-- an empty list of overrides.
createUnsoundOverrides ::
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  ArchOk arch =>
  proxy arch ->
  Soundness ->
  IO (IORef (Set UnsoundOverrideName), [CreateOverrideFn m arch])
createUnsoundOverrides proxy sound =
  do unsoundOverrideRef <- IORef.newIORef Set.empty
     return
       ( unsoundOverrideRef
       , if sound /= Sound.Indefinite
         then []
         else map mkOverride (unsoundOverrides unsoundOverrideRef)
       )
  where mkOverride ov =
          CreateOverrideFn (\_sym _tracker -> pure (getForAllSymArch ov proxy))

registerOverrides ::
  (?intrinsicsOpts :: LLVMIntrinsics.IntrinsicsOptions) =>
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
  ArchOk arch =>
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  AppContext ->
  ModuleContext m arch ->
  Crucible.OverrideSim (personality sym) sym LLVM rtp l a ()
registerDefinedFns appCtx modCtx =
  do let trans = modCtx ^. moduleTranslation
     for_ (trans ^. modTransDefs) $
       \(decl, _) ->
         do let s@(L.Symbol symb) = L.decName decl
            liftIO $
              (appCtx ^. log) Hi $
                Text.unwords ["Registering definition of", Text.pack symb]
            -- TODO? handle these warnings?
            let handleTranslationWarning _warn = return ()
            registerLazyModuleFn handleTranslationWarning trans s

mkCallbacks ::
  forall r m arch argTypes blocks ret msgs.
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  SimulatorCallbacks m arch argTypes r ->
  Preconds m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  LLVMOptions ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  Crux.SimulatorCallbacks msgs r
mkCallbacks appCtx modCtx funCtx halloc callbacks constraints cfg llvmOpts specs =
  Crux.SimulatorCallbacks $
    do -- References written to during setup
       memRef <- IORef.newIORef Nothing
       argRef <- IORef.newIORef Nothing
       argAnnRef <- IORef.newIORef Nothing
       argShapeRef <- IORef.newIORef Nothing

       -- References written to during simulation
       bbMapRef <- IORef.newIORef (Map.empty :: LLVMAnnMap sym)
       explRef <- IORef.newIORef []
       skipReturnValueAnns <- IORef.newIORef ET.empty
       skipOverrideRef <- IORef.newIORef Set.empty
       let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
           ?memOpts = memOpts llvmOpts
       (specsUsedRef, specOverrides) <-
         createSpecOverrides modCtx (soundness appCtx) specs
       (unsoundOverrideRef, uOverrides) <-
         createUnsoundOverrides modCtx (soundness appCtx)
       let ovs = uOverrides ++ specOverrides

       -- Hooks
       let ?recordLLVMAnnotation =
             \callStack an bb ->
               IORef.modifyIORef bbMapRef (Map.insert an (callStack, bb))
       SimulatorHooks overrides resHook <-
         getSimulatorCallbacks callbacks

       return $
         Crux.SimulatorHooks
           { Crux.setupHook =
             \bak _symOnline ->
               setupHook bak ovs overrides skipOverrideRef memRef argRef argAnnRef argShapeRef skipReturnValueAnns
           , Crux.onErrorHook =
             \bak ->
               return (onErrorHook bak skipOverrideRef memRef argRef argAnnRef argShapeRef bbMapRef explRef skipReturnValueAnns)
           , Crux.resultHook =
             \bak result ->
               mkResultHook bak skipOverrideRef specsUsedRef unsoundOverrideRef explRef memRef argShapeRef result resHook
           }
  where
    setupHook ::
      Crux.Logs msgs =>
      IsSymBackend sym bak =>
      HasLLVMAnn sym =>
      bak ->
      -- | Unsound and spec overrides
      [CreateOverrideFn m arch] ->
      -- | Overrides that were passed in as arguments
      [SymCreateOverrideFn m sym bak arch] ->
      IORef (Set SkipOverrideName) ->
      IORef (Maybe (PreSimulationMem sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (ExprTracker m sym argTypes)) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (ExprTracker m sym argTypes) ->
      IO (Crux.RunnableState sym)
    setupHook bak uOverrideFns overrideFns skipOverrideRef memRef argRef argAnnRef argShapeRef skipReturnValueAnnotations =
      do
        let trans = modCtx ^. moduleTranslation
        let llvmCtxt = trans ^. transContext
        let memOptions = memOpts llvmOpts
        let ?lc = llvmCtxt ^. llvmTypeCtx
        let ?intrinsicsOpts = intrinsicsOpts llvmOpts
        let ?memOpts = memOptions
        let simctx =
              (setupSimCtxt halloc bak memOptions (llvmMemVar llvmCtxt))
                { Crucible.printHandle = view outputHandle ?outputConfig
                }

        unless (null (constraints ^. relationalPreconds)) $
          panic "simulateLLVM" ["Unimplemented: relational constraints"]

        setupResult <-
          liftIO $ setupExecution appCtx modCtx funCtx bak constraints
        (mem, argAnnotations, assumptions, argShapes, args) <-
          case setupResult of
            (SetupResult mem anns assumptions, (argShapes, args)) ->
              pure (mem, anns, assumptions, argShapes, args)

        -- Save initial state so that it can be used during classification
        IORef.writeIORef memRef (Just (makePreSimulationMem mem))
        IORef.writeIORef argRef (Just args)
        IORef.writeIORef argAnnRef (Just argAnnotations)
        IORef.writeIORef argShapeRef (Just argShapes)

        -- Assume all predicates necessary to satisfy the deduced preconditions
        assume (funCtx ^. functionName) bak assumptions

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

                    let apOv f = runSymCreateOverrideFn f bak skipReturnValueAnnotations
                    overrides <- liftIO $ for overrideFns apOv
                    let overrides' = map (\ov -> getPolymorphicLLVMOverride ov) overrides
                    registerOverrides appCtx modCtx sArg overrides'

                    -- Register unsound overrides, e.g., `getenv`
                    uOverrides <-
                      liftIO $ traverse (\ov -> runCreateOverrideFn ov bak skipReturnValueAnnotations) uOverrideFns
                    let uOverrides' = map (\ov -> getPolymorphicLLVMOverride ov) uOverrides
                    registerOverrides appCtx modCtx sUnsound uOverrides'

                    -- NB: This should be run after all other overrides have
                    -- been registered, since it creates and registers an
                    -- override to skip each function that is
                    -- declared-but-not-defined and doesn't yet have an override
                    -- registered.
                    when (soundness appCtx == Sound.Indefinite) $
                      do sOverrides <-
                           unsoundSkipOverrides
                             modCtx
                             bak
                             trans
                             skipOverrideRef
                             skipReturnValueAnnotations
                             (constraints ^. postconds)
                             (L.modDeclares (modCtx ^. llvmModule . to getModule))
                         let sOverrides' =
                               map
                                 (\ov -> getPolymorphicLLVMOverride ov)
                                 sOverrides
                         registerOverrides appCtx modCtx sSkip sOverrides'

                    liftIO $ (appCtx ^. log) Hi $ "Running " <> funCtx ^. functionName <> " on arguments..."
                    printed <- ppRegMap modCtx funCtx (backendGetSym bak) mem args
                    mapM_ (liftIO . (appCtx ^. log) Hi . Text.pack . show) printed
                    void $ Crucible.callCFG cfg args

        return (Crux.RunnableState initSt)

    -- | Classify errors and write back the results to an IORef so they can be
    -- read in the outer loop
    onErrorHook ::
      IsSymBackend sym bak =>
      (sym ~ What4.ExprBuilder t st fs) =>
      bak ->
      IORef (Set SkipOverrideName) ->
      IORef (Maybe (PreSimulationMem sym)) ->
      IORef (Maybe (Crucible.RegMap sym (MapToCrucibleType arch argTypes))) ->
      IORef (Maybe (ExprTracker m sym argTypes)) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      IORef (LLVMAnnMap sym) ->
      IORef [Located (Explanation m arch argTypes)] ->
      IORef (ExprTracker m sym argTypes) ->
      Crux.Explainer sym t Void
    onErrorHook bak skipOverrideRef memRef argRef argAnnRef argShapeRef bbMapRef explRef skipReturnValueAnnotations _groundEvalFn gl =
      do
        let sym = backendGetSym bak
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
          Just (callStack, badBehavior) ->
            do
              -- Helpful for debugging:
              -- putStrLn "~~~~~~~~~~~"
              -- putStrLn (show (LLVMErrors.ppBB badBehavior))

              liftIO $ (appCtx ^. log) Hi ("Explaining error: " <> Text.pack (show (LLVMErrors.explainBB badBehavior)))
              let render =  PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions

              liftIO $ (appCtx ^. log) Hi "Error call stack:"
              liftIO $ (appCtx ^. log) Hi (render (ppCallStack callStack))
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
                (ET.union argAnnotations retAnns)
                argShapes
                badBehavior
                callStack
                >>= IORef.modifyIORef explRef . (:)
        return mempty

    mkResultHook ::
      IsSymBackend sym bak =>
      (sym ~ What4.ExprBuilder t st fs) =>
      bak ->
      IORef (Set SkipOverrideName) ->
      IORef (Set SpecUse) ->
      IORef (Set UnsoundOverrideName) ->
      IORef [Located (Explanation m arch argTypes)] ->
      IORef (Maybe (PreSimulationMem sym)) ->
      IORef (Maybe (Assignment (Shape m (SymValue sym arch)) argTypes)) ->
      Crux.CruxSimulationResult ->
      (bak ->
        PreSimulationMem sym ->
        Assignment (Shape m (SymValue sym arch)) argTypes ->
        Crux.CruxSimulationResult ->
        UCCruxSimulationResult m arch argTypes ->
        IO r) ->
      IO r
    mkResultHook bak skipOverrideRef specsUsedRef unsoundOverrideRef explRef memRef argShapeRef cruxResult resHook =
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
             <*> IORef.readIORef specsUsedRef
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
         resHook bak mem argShapes cruxResult ucCruxResult

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
  Preconds m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  SimulatorCallbacks m arch argTypes r ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  IO r
runSimulatorWithCallbacks appCtx modCtx funCtx halloc preconditions cfg cruxOpts llvmOpts callbacks specs =
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
        specs
    )

runSimulator ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  Crucible.HandleAllocator ->
  [CreateOverrideFn m arch] ->
  Preconds m argTypes ->
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  CruxOptions ->
  LLVMOptions ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  IO (UCCruxSimulationResult m arch argTypes)
runSimulator appCtx modCtx funCtx halloc overrides preconditions cfg cruxOpts llvmOpts specs =
  runSimulatorWithCallbacks
    appCtx
    modCtx
    funCtx
    halloc
    preconditions
    cfg
    cruxOpts
    llvmOpts
    callbacks
    specs
  where
    callbacks =
      SimulatorCallbacks $
        return $
          SimulatorHooks
            { createOverrideHooks = map symCreateOverrideFn overrides
            , resultHook =
                \_bak _mem _args _cruxResult ucCruxResult -> return ucCruxResult
            }
