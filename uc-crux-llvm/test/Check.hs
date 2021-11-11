{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures -fno-warn-incomplete-uni-patterns #-}

module Check (checkOverrideTests) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Data.Foldable (toList)
import qualified Data.IORef as IORef
import           Data.Maybe (fromMaybe)
import qualified Data.Text as Text

import qualified Lang.Crucible.CFG.Core as Crucible

import qualified Crux.LLVM.Config as CruxLLVM

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import qualified What4.Interface as What4

import           UCCrux.LLVM.Constraints (emptyConstraints)
import           UCCrux.LLVM.Context.Function (makeFunctionContext, ppFunctionContextError)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), defnTypes, findFun, withModulePtrWidth)
import           UCCrux.LLVM.Module (FuncSymbol(FuncDefnSymbol), DefnSymbol, defnSymbolToString)
import           UCCrux.LLVM.Newtypes.FunctionName (functionNameFromString)
import qualified UCCrux.LLVM.Overrides.Check as Check
import           UCCrux.LLVM.Run.Check (SomeCheckResult(SomeCheckResult), inferThenCheck, getCheckResult, getSomeCheckedCalls)
import qualified UCCrux.LLVM.Run.EntryPoints as EntryPoints
import           UCCrux.LLVM.Run.Loop (bugfindingLoop)
import qualified UCCrux.LLVM.Run.Simulate as Sim

-- Tests
import qualified Utils
import qualified Data.Map.Strict as Map
{- ORMOLU_ENABLE -}

getEntryPoint :: ModuleContext m arch -> String -> IO (DefnSymbol m)
getEntryPoint modCtx funcName =
  do entries <-
       EntryPoints.makeEntryPointsOrThrow
         (modCtx ^. defnTypes)
         [functionNameFromString funcName]
     case EntryPoints.getEntryPoints entries of
       [entry] -> return entry
       _ -> error "Wrong number of entry points"

checkOverrideTests :: TT.TestTree
checkOverrideTests =
  TT.testGroup
    "check overrides"
    [ TH.testCase
        "disjunctive generalization"
        (Utils.withOptions
          Nothing
          "check_disjunctive_generalization.c"
          (\appCtx (modCtx :: ModuleContext m arch) halloc cruxOpts llOpts ->
             do [f] <-
                  EntryPoints.getEntryPoints <$>
                    EntryPoints.makeEntryPointsOrThrow
                      (modCtx ^. defnTypes)
                      [functionNameFromString "f"]
                [g] <-
                  EntryPoints.getEntryPoints <$>
                    EntryPoints.makeEntryPointsOrThrow
                      (modCtx ^. defnTypes)
                      [functionNameFromString "g"]

                -- Without something explicit here to fix a type, GHC will get
                -- mad about leaking existentials (of which there are many - the
                -- pointer width, the CFG argument types...)
                () <-
                  withModulePtrWidth
                    modCtx
                    ( do
                        CFGWithTypes fcgf fArgFTys _retTy _varArgs <-
                          pure (findFun modCtx (FuncDefnSymbol f))

                        funCtxF <-
                          case makeFunctionContext modCtx f fArgFTys (Crucible.cfgArgTypes fcgf) of
                            Left err ->
                              error (Text.unpack (ppFunctionContextError err))
                            Right funCtxF -> return funCtxF

                        -- Run main loop on f, to deduce the precondition
                        -- that y should be nonnull
                        (result, _) <-
                          bugfindingLoop
                            appCtx
                            modCtx
                            funCtxF
                            fcgf
                            cruxOpts
                            llOpts
                            halloc

                        -- Construct override that checks that y is nonnull

                        let ?memOpts = CruxLLVM.memOpts llOpts
                        let
                          -- This type signature is necessary for some
                          -- reason...
                          msg = "Test failure: 'f' should have been safe with preconditions"
                          callbacks :: Sim.SimulatorCallbacks m _ _ _
                          callbacks =
                            Sim.SimulatorCallbacks $
                              do ref <- IORef.newIORef []
                                 return $
                                   Sim.SimulatorHooks
                                     { Sim.createOverrideHooks =
                                         [ Sim.SymCreateOverrideFn $
                                             \_sym ->
                                               return $
                                                 fromMaybe (error msg) $
                                                   Check.checkOverrideFromResult
                                                     appCtx
                                                     modCtx
                                                     ref
                                                     fArgFTys
                                                     fcgf
                                                     (FuncDefnSymbol f)
                                                     result
                                         ]
                                     , Sim.resultHook =
                                       \_sym _mem _args _cruxResult _ucCruxResult ->
                                         -- TODO: Confirm that the values
                                         -- indicate a precondition violation
                                         do calls <- IORef.readIORef ref
                                            TH.assertEqual
                                              "The override for 'f' was exec'd"
                                              1
                                              (length calls)
                                            return ()
                                     }

                        -- Simulate g, but with override that checks the
                        -- inferred preconditions of f
                        --
                        -- Additional checks happen in the result hook,
                        -- see 'callbacks'.
                        CFGWithTypes gcfg gArgFTys _retTy _varArgs <-
                          pure (findFun modCtx (FuncDefnSymbol g))

                        funCtxG <-
                          case makeFunctionContext modCtx g gArgFTys (Crucible.cfgArgTypes gcfg) of
                            Left err ->
                              error (Text.unpack (ppFunctionContextError err))
                            Right funCtxG -> return funCtxG

                        () <-
                          Sim.runSimulatorWithCallbacks
                            appCtx
                            modCtx
                            funCtxG
                            halloc
                            (emptyConstraints gArgFTys)
                            gcfg
                            cruxOpts
                            llOpts
                            callbacks

                        return ()
                    )
                return ()
          )
        )

    , TH.testCase "two callsites" $
        Utils.withOptions Nothing "check_two_callsites.c" $
          \appCtx (modCtx :: ModuleContext m arch) halloc cruxOpts llOpts ->
            do f <- getEntryPoint modCtx "f"
               g <- getEntryPoint modCtx "g"
               h <- getEntryPoint modCtx "h"
               () <-
                 withModulePtrWidth modCtx $
                   do (_inferResult, checkResult) <-
                        inferThenCheck
                          appCtx
                          modCtx
                          halloc
                          cruxOpts
                          llOpts
                          (EntryPoints.makeEntryPoints [f])
                          (EntryPoints.makeEntryPoints [g, h])
                      let getResult fun =
                            return $
                              fromMaybe
                                (error ("No result for " ++ defnSymbolToString fun))
                                (Map.lookup fun checkResult)
                      SomeCheckResult _ gResult <- getResult g
                      SomeCheckResult _ hResult <- getResult h
                      () <-
                        getCheckResult gResult $
                          \_sym _mem _args _cruxResult _ucCruxResult checkedCalls ->
                            case checkedCalls of
                              [fCalls] ->
                                getSomeCheckedCalls fCalls $
                                  \defnSym _funCtx [fCall] ->
                                    do TH.assertEqual
                                         "f was called from g"
                                         (defnSymbolToString f)
                                         (defnSymbolToString defnSym)
                                       [Check.SomeCheckedConstraint c] <-
                                         return (toList (Check.checkedCallConstraints fCall))
                                       TH.assertEqual
                                         "constraint passed"
                                         (Just True)
                                         (What4.asConstantPred
                                           (Check.checkedPred c))
                              _ -> error "Wrong number of calls"
                      () <-
                        getCheckResult hResult $
                          \_sym _mem _args _cruxResult _ucCruxResult checkedCalls ->
                            case checkedCalls of
                              [fCalls] ->
                                getSomeCheckedCalls fCalls $
                                  \defnSym _funCtx [fCall] ->
                                    do TH.assertEqual
                                         "f was called from h"
                                         (defnSymbolToString f)
                                         (defnSymbolToString defnSym)
                                       [Check.SomeCheckedConstraint c] <-
                                         return (toList (Check.checkedCallConstraints fCall))
                                       TH.assertEqual
                                         "constraint failed"
                                         (Just False)
                                         (What4.asConstantPred
                                           (Check.checkedPred c))

                              _ -> error "Wrong number of checked calls"
                      return ()
               return ()

    ]
