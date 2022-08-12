{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures -fno-warn-incomplete-uni-patterns #-}

module Postcond (postcondTests) where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Data.Functor.Compose (Compose(Compose))
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import           Data.Type.Equality ((:~:)(Refl))

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import           Text.LLVM.AST as L

import           Data.Parameterized.NatRepr (knownNat)

import           Lang.Crucible.LLVM.Translation (transContext, llvmTypeCtx)

import qualified Crux.LLVM.Config as CruxLLVM

import           UCCrux.LLVM.Constraints (ConstrainedShape(..))
import           UCCrux.LLVM.Context.Module (moduleTranslation, declTypes)
import qualified UCCrux.LLVM.Cursor as Cursor
import qualified UCCrux.LLVM.ExprTracker as ET
import           UCCrux.LLVM.FullType.CrucibleType (makeSameCrucibleType)
import qualified UCCrux.LLVM.FullType.Type as FT
import           UCCrux.LLVM.Module (FuncSymbol(FuncDeclSymbol), makeDeclSymbol)
import qualified UCCrux.LLVM.Run.Simulate as Sim
import qualified UCCrux.LLVM.Overrides.Skip as Skip
import qualified UCCrux.LLVM.Postcondition.Type as Post
import qualified UCCrux.LLVM.Shape as Shape

-- Tests
import qualified Utils
{- ORMOLU_ENABLE -}

postcondTests :: TT.TestTree
postcondTests =
  TT.testGroup
    "postconditions"
    [ TH.testCase
        "clobbers_arg.c"
        ( Utils.simulateFunc
            "clobbers_arg.c"
            "calls_clobbers_arg"
            ( \_appCtx modCtx _halloc _cruxOpts llOpts _funCtx ->
                do let Just callee =
                         makeDeclSymbol
                           (L.Symbol "clobbers_arg")
                           (modCtx ^. declTypes)
                   let ?memOpts = CruxLLVM.memOpts llOpts
                   let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
                   let
                     i32p = FT.FTPtrRepr (FT.toPartType (FT.FTIntRepr (knownNat @32)))
                     shape = ConstrainedShape (Shape.ShapeInt (Compose []))
                     argVal :: Post.ClobberValue m ('FT.FTPtr ('FT.FTInt 32))
                     argVal = Post.ClobberValue (Cursor.Here i32p) shape i32p (makeSameCrucibleType (\_arch -> Refl))
                     arg = Post.SomeClobberArg (Post.DoClobberArg argVal)
                     specs = Post.UPostcond (IntMap.singleton 0 arg) Map.empty Nothing

                   return $
                     Sim.SimulatorCallbacks $
                       do nameRef <- IORef.newIORef Set.empty
                          annRef <- IORef.newIORef ET.empty
                          return $
                            Sim.SimulatorHooks
                              { Sim.createOverrideHooks =
                                  [ Sim.SymCreateOverrideFn $
                                      \bak _tracker ->
                                        return $
                                          Skip.createSkipOverride
                                            modCtx
                                            bak
                                            nameRef
                                            annRef
                                            specs
                                            (FuncDeclSymbol callee)
                                  ]
                              , Sim.resultHook =
                                \_bak _mem _args _cruxResult ucCruxResult ->
                                  do calls <- IORef.readIORef nameRef
                                     TH.assertEqual
                                       "The override for 'clobbers_arg' was exec'd"
                                       1
                                       (length calls)
                                     TH.assertBool
                                       "No read of uninitialized memory"
                                       (null (Sim.explanations ucCruxResult))
                                     return ()
                              }

            )
        )
    , TH.testCase
        "clobbers_arg_void_ptr.c"
        ( Utils.simulateFunc
            "clobbers_arg_void_ptr.c"
            "calls_clobbers_arg_void_ptr"
            ( \_appCtx modCtx _halloc _cruxOpts llOpts _funCtx ->
                do let Just callee =
                         makeDeclSymbol
                           (L.Symbol "clobbers_arg_void_ptr")
                           (modCtx ^. declTypes)
                   let ?memOpts = CruxLLVM.memOpts llOpts
                   let ?lc = modCtx ^. moduleTranslation . transContext . llvmTypeCtx
                   let
                     i32 = FT.FTIntRepr (knownNat @32)
                     i32p = FT.FTPtrRepr (FT.toPartType i32)
                     shape = ConstrainedShape (Shape.ShapeInt (Compose []))
                     argVal :: Post.ClobberValue m ('FT.FTPtr ('FT.FTInt 32))
                     argVal = Post.ClobberValue (Cursor.Here i32p) shape i32p (makeSameCrucibleType (\_arch -> Refl))
                     arg = Post.SomeClobberArg (Post.DoClobberArg argVal)
                     specs = Post.UPostcond (IntMap.singleton 0 arg) Map.empty Nothing

                   return $
                     Sim.SimulatorCallbacks $
                       do nameRef <- IORef.newIORef Set.empty
                          annRef <- IORef.newIORef ET.empty
                          return $
                            Sim.SimulatorHooks
                              { Sim.createOverrideHooks =
                                  [ Sim.SymCreateOverrideFn $
                                      \sym _tracker ->
                                        return $
                                          Skip.createSkipOverride
                                            modCtx
                                            sym
                                            nameRef
                                            annRef
                                            specs
                                            (FuncDeclSymbol callee)
                                  ]
                              , Sim.resultHook =
                                \_sym _mem _args _cruxResult ucCruxResult ->
                                  do calls <- IORef.readIORef nameRef
                                     TH.assertEqual
                                       "The override for 'clobbers_arg' was exec'd"
                                       1
                                       (length calls)
                                     TH.assertBool
                                       "No read of uninitialized memory"
                                       (null (Sim.explanations ucCruxResult))
                                     return ()
                              }
            )
        )
    ]
