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

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Check (checkOverrideTests) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import qualified Data.Text as Text

import qualified Lang.Crucible.CFG.Core as Crucible

import qualified Crux.LLVM.Config as CruxLLVM

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           UCCrux.LLVM.Constraints (emptyConstraints)
import           UCCrux.LLVM.Context.Function (makeFunctionContext, ppFunctionContextError)
import           UCCrux.LLVM.Context.Module (ModuleContext, CFGWithTypes(..), defnTypes, findFun, withModulePtrWidth)
import           UCCrux.LLVM.Module (FuncSymbol(FuncDefnSymbol))
import           UCCrux.LLVM.Newtypes.FunctionName (functionNameFromString)
import qualified UCCrux.LLVM.Overrides.Check as Check
import qualified UCCrux.LLVM.Run.EntryPoints as EntryPoints
import           UCCrux.LLVM.Run.Loop (bugfindingLoop)
import qualified UCCrux.LLVM.Run.Simulate as Sim

-- Tests
import qualified Utils
{- ORMOLU_ENABLE -}

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
                              do ref <- IORef.newIORef Map.empty
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
                                         do mp <- IORef.readIORef ref
                                            TH.assertEqual
                                              "The override for 'f' was exec'd"
                                              (Set.singleton
                                               (Check.CheckOverrideName "f"))
                                              (Map.keysSet mp)
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

    ]
