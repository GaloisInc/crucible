{-
Module           : UCCrux.LLVM.Run.Check
Description      : Check inferred function contracts. See 'inferThenCheck'.
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Run.Check
  ( CheckResult,
    getCheckResult,
    SomeCheckResult(..),
    SomeCheckedCalls,
    getSomeCheckedCalls,
    checkInferredContracts,
    checkInferredContractsFromEntryPoints,
    inferThenCheck,
    ppSomeCheckResult,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), to)
import           Data.Foldable (toList)
import qualified Data.IORef as IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (catMaybes)
import qualified Data.Text as Text
import           Data.Traversable (for)
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import qualified Prettyprinter as PP

import           Data.Parameterized.Context (Assignment, Ctx)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (IxedF'(ixF'))
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Interface as What4

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import           Lang.Crucible.FunctionHandle (HandleAllocator)

-- crucible-llvm
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import           Lang.Crucible.LLVM.Extension (LLVM)

-- crux
import           Crux.Config.Common (CruxOptions)
import qualified Crux.Log as Crux
import qualified Crux.Types as Crux

-- crux-llvm
import           Crux.LLVM.Config (LLVMOptions)
import qualified Crux.LLVM.Config as CruxLLVM
import           Crux.LLVM.Overrides (ArchOk)

-- local
import           UCCrux.LLVM.Constraints (Constraints, emptyConstraints, ppConstraint, ppShapeConstraint)
import           UCCrux.LLVM.Cursor (ppSelector)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), findFun)
import           UCCrux.LLVM.Context.Function (FunctionContext, makeFunctionContext, ppFunctionContextError, argumentFullTypes)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType (FullType, FullTypeRepr, MapToCrucibleType)
import qualified UCCrux.LLVM.FullType.CrucibleType as FT
import           UCCrux.LLVM.Module (DefnSymbol, FuncSymbol(FuncDefnSymbol), defnSymbolToString)
import           UCCrux.LLVM.Newtypes.PreSimulationMem (PreSimulationMem, getPreSimulationMem)
import qualified UCCrux.LLVM.Overrides.Check as Check
import qualified UCCrux.LLVM.Overrides.Stack as Stack
import           UCCrux.LLVM.PP (ppRegMap)
import           UCCrux.LLVM.Run.EntryPoints (EntryPoints, getEntryPoints)
import qualified UCCrux.LLVM.Run.Simulate as Sim
import qualified UCCrux.LLVM.Run.Loop as Loop
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Setup (SymValue)
import           UCCrux.LLVM.Shape (Shape)
{- ORMOLU_ENABLE -}

-- | The result of encountering a check override some number of times during
-- forward symbolic execution. The arguments to the callback are (1) the name of
-- the function that was overridden (i.e., had its preconditions checked), (2) a
-- 'FunctionContext' describing, among other things, the types of the arguments
-- to the function, and (3) the individual results of calling the override some
-- number of times (see 'Check.CheckedCall' for details).
newtype SomeCheckedCalls m sym arch =
  SomeCheckedCalls
    { getSomeCheckedCalls ::
        forall r.
        (forall argTypes.
         DefnSymbol m ->
         FunctionContext m arch argTypes ->
         [Check.CheckedCall m sym arch argTypes] ->
         IO r) ->
        IO r
    }

-- | The result of checking inferred contracts
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
newtype CheckResult m arch (argTypes :: Ctx (FullType m)) =
  CheckResult
    { getCheckResult ::
        forall r.
        (forall sym.
         IsSymInterface sym =>
         sym ->
         -- | Pre-simulation memory
         PreSimulationMem sym ->
         -- | Arguments passed to the entry point
         Assignment (Shape m (SymValue sym arch)) argTypes ->
         Crux.CruxSimulationResult ->
         Sim.UCCruxSimulationResult m arch argTypes ->
         [SomeCheckedCalls m sym arch] ->
         r) ->
        r
    }

data SomeCheckResult m arch =
  forall argTypes.
  SomeCheckResult
    { checkResultFunContext :: FunctionContext m arch argTypes,
      checkResult :: CheckResult m arch argTypes
    }

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data TypedConstraints m (argTypes :: Ctx (FullType m))
  = TypedConstraints
      { _tcConstraints :: Constraints m argTypes
      , _tcTypes :: Assignment (FullTypeRepr m) argTypes
      }

checkInferredContracts ::
  forall m arch argTypes blocks ret msgs.
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  FunctionContext m arch argTypes ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  Constraints m argTypes ->
  -- | Entry point
  Crucible.CFG LLVM blocks (MapToCrucibleType arch argTypes) ret ->
  -- | Inferred function contracts
  Map (DefnSymbol m) (Some (TypedConstraints m)) ->
  IO (CheckResult m arch argTypes)
checkInferredContracts appCtx modCtx funCtx halloc cruxOpts llOpts constraints cfg contracts =
   Sim.runSimulatorWithCallbacks
     appCtx
     modCtx
     funCtx
     halloc
     constraints
     cfg
     cruxOpts
     llOpts
     (Sim.SimulatorCallbacks $
       do ovs <- overrides
          return $
            Sim.SimulatorHooks
              { Sim.createOverrideHooks = map fst ovs
              , Sim.resultHook =
                \sym mem args cruxResult ucResult ->
                  return $
                    CheckResult $
                      \k -> k sym mem args cruxResult ucResult (map snd ovs)
              })
  where
    -- Create one override for each function with preconditions we want to
    -- check, as well as a way to get the results ('SomeCheckedCalls').
    overrides ::
      IsSymInterface sym =>
      HasLLVMAnn sym =>
      IO [ ( Sim.SymCreateOverrideFn sym arch
           , SomeCheckedCalls m sym arch
           )
         ]
    overrides =
      for
        (Map.toList contracts)
        (\(func, Some (TypedConstraints tcs types)) ->
           do CFGWithTypes ovCfg argFTys _retTy _varArgs <-
                pure (findFun modCtx (FuncDefnSymbol func))
              let argCTys = Crucible.cfgArgTypes ovCfg
              ovFunCtx <-
                case makeFunctionContext modCtx func argFTys argCTys of
                  Left err ->
                    panic
                      "checkInferredContracts"
                      [ "Function: " ++ defnSymbolToString func
                      , Text.unpack (ppFunctionContextError err)
                      ]
                  Right funCtx' -> return funCtx'
              let ?memOpts = CruxLLVM.memOpts llOpts
              case testEquality argFTys types of
                Nothing ->
                  panic
                    "checkInferredContracts"
                    [ "Function: " ++ defnSymbolToString func
                    , "CFG/constraint type mismatch!"
                    ]
                Just Refl ->
                  do ref <- IORef.newIORef []
                     return
                       ( Sim.SymCreateOverrideFn $
                           \_sym ->
                             return $
                               Check.createCheckOverride
                                 appCtx
                                 modCtx
                                 ref
                                 types
                                 tcs
                                 ovCfg
                                 (FuncDefnSymbol func)
                       , SomeCheckedCalls
                           (\f -> f func ovFunCtx =<< IORef.readIORef ref)
                       )
        )

-- | Postcondition: The keys of the returned 'Map' are exactly the
-- 'EntryPoints'.
checkInferredContractsFromEntryPoints ::
  forall m arch msgs.
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Where to begin symbolic execution
  EntryPoints m ->
  -- | Inferred function contracts
  Map (DefnSymbol m) (Some (TypedConstraints m)) ->
  IO (Map (DefnSymbol m) (SomeCheckResult m arch))
checkInferredContractsFromEntryPoints appCtx modCtx halloc cruxOpts llOpts entries contracts =
  fmap Map.fromList $
    for (getEntryPoints entries) $
      \entry ->
        do CFGWithTypes cfg argFTys _retTy _varArgs <-
             pure (findFun modCtx (FuncDefnSymbol entry))

           funCtx <-
             case makeFunctionContext modCtx entry argFTys (Crucible.cfgArgTypes cfg) of
               Left err ->
                 panic
                   "checkInferredContracts"
                   [Text.unpack (ppFunctionContextError err)]
               Right funCtxF -> return funCtxF
           result <-
            checkInferredContracts
              appCtx
              modCtx
              funCtx
              halloc
              cruxOpts
              llOpts
              (emptyConstraints argFTys)
              cfg
              contracts
           return (entry, SomeCheckResult funCtx result)

-- | Infer preconditions for a group of functions, then for the ones that are
-- safe-with-preconditions (and also didn't hit iteration limits), check their
-- inferred preconditions by seeing if they hold during symbolic execution from
-- some (other) group of functions.
--
-- Postcondition:
-- * The keys of the first map are the 'EntryPoints' given for inference
-- * The keys of the second map are the 'EntryPoints' given for checking
inferThenCheck ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  ArchOk arch =>
  AppContext ->
  ModuleContext m arch ->
  HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Functions to infer contracts for
  EntryPoints m ->
  -- | Entry points for checking inferred contracts
  EntryPoints m ->
  IO ( Map (DefnSymbol m) (SomeBugfindingResult m arch)
     , Map (DefnSymbol m) (SomeCheckResult m arch)
     )
inferThenCheck appCtx modCtx halloc cruxOpts llOpts toInfer entries =
  do inferResult <-
       Loop.loopOnFunctions appCtx modCtx halloc cruxOpts llOpts toInfer
     chkResult <-
       checkInferredContractsFromEntryPoints appCtx modCtx halloc cruxOpts llOpts entries $
         Map.mapMaybe getConstraints inferResult
     return (inferResult, chkResult)
  where
    getConstraints ::
      forall m' arch'.
      Result.SomeBugfindingResult m' arch' ->
      Maybe (Some (TypedConstraints m'))
    getConstraints (Result.SomeBugfindingResult types result _) =
      case Result.summary result of
        Result.AlwaysSafe {} -> Nothing
        Result.FoundBugs {} -> Nothing
        Result.SafeUpToBounds {} -> Nothing
        Result.Unclear {} -> Nothing
        Result.SafeWithPreconditions Result.DidHitBounds _ _ -> Nothing
        Result.SafeWithPreconditions Result.DidntHitBounds _unsound cs ->
          Just (Some (TypedConstraints cs types))

ppSomeCheckResult ::
  forall m arch ann.
  ArchOk arch =>
  AppContext ->
  -- | Entry point
  DefnSymbol m ->
  SomeCheckResult m arch ->
  IO (PP.Doc ann)
ppSomeCheckResult _appCtx entry proxy@(SomeCheckResult _ftReprs (CheckResult k)) =
  k $
    \sym mem _args _cruxResult _ucCruxResult checkOvResults ->
      -- TODO: Print args with ppRegMap
      PP.vsep .
        ([ "When executing from " <> PP.pretty (defnSymbolToString entry) <> ",",
          "encountered these calls to functions which had inferred contracts:"
         ] ++) .
        catMaybes <$>
          mapM (ppOne sym mem) checkOvResults
  where
    bullets = map ("-" PP.<+>)

    ppOne ::
      forall sym.
      IsSymInterface sym =>
      sym ->
      PreSimulationMem sym ->
      SomeCheckedCalls m sym arch ->
      IO (Maybe (PP.Doc ann))
    ppOne sym mem (SomeCheckedCalls k') =
      k' $
        \_checkedFuncName funCtx checkedCalls ->
          case checkedCalls of
            [] -> return Nothing
            _ ->
              do prettyCalls <- mapM (ppCheckedCall funCtx sym mem) checkedCalls
                 -- The callstack includes the function name (checkedFuncName),
                 -- so we don't add it here.
                 return (Just (PP.vsep prettyCalls))

    ppCheckedCall ::
      forall sym argTypes.
      IsSymInterface sym =>
      FunctionContext m arch argTypes ->
      sym ->
      PreSimulationMem sym ->
      Check.CheckedCall m sym arch argTypes ->
      IO (PP.Doc ann)
    ppCheckedCall funCtx sym mem call =
      do let argFTys = funCtx ^. argumentFullTypes
         let args =
               FT.generate
                 proxy
                 (Ctx.size argFTys)
                 (\i i' Refl ->
                    Crucible.RegEntry
                      (argFTys ^. ixF' i . to (FT.toCrucibleType proxy))
                      (Check.checkedCallArgs call ^. ixF' i' . to Crucible.unRV))
         prettyArgs <- ppRegMap proxy funCtx sym (getPreSimulationMem mem) (Crucible.RegMap args)
         prettyChecked <-
           mapM (ppCheckedConstraint sym) (Check.checkedCallConstraints call)
         return $
            PP.vsep
              ([ -- This starts with "When calling <func>"
                 Stack.ppStack (Check.checkedCallContext call),
                 "With arguments:",
                 PP.vsep (bullets prettyArgs),
                 "Checked constraints:"
               ] ++ toList prettyChecked)

    ppCheckedConstraint ::
      forall sym argTypes.
      IsSymInterface sym =>
      sym ->
      Check.SomeCheckedConstraint m sym argTypes ->
      IO (PP.Doc ann)
    ppCheckedConstraint _sym (Check.SomeCheckedConstraint constraint) =
      do return $
           PP.vsep
             [ "Constraint:" PP.<+>
                 case Check.checkedConstraint constraint of
                   Left c -> ppShapeConstraint c
                   Right c -> ppConstraint c,
               "Applied at:" PP.<+>
                 ppSelector (Check.checkedSelector constraint),
               "Result:" PP.<+>
                 case What4.asConstantPred (Check.checkedPred constraint) of
                   Just True -> "concretely true"
                   Just False -> "concretely false"
                   -- TODO: Figure out how to invoke the solver here
                   _ -> "<symbolic/unknown>"

             ]
