{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language PatternSynonyms #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}
{-# Language TypeApplications #-}
{-# Language PartialTypeSignatures #-}

module Mir.Overrides (bindFn) where

import Control.Monad.IO.Class

import Data.Map (Map, fromList)
import qualified Data.Map as Map

import Data.Parameterized.Context (pattern Empty, pattern (:>))

import Data.Text (Text)
import qualified Data.Text as Text

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend (IsBoolSolver, assert)
import Lang.Crucible.CFG.Core (CFG, cfgArgTypes, cfgHandle, cfgReturnType, lastReg)
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.SimError

import Lang.Crucible.Types

import What4.FunctionName (FunctionName, functionNameFromText)
import What4.Interface

import Mir.Intrinsics (MIR)


data SomeOverride p sym where
  SomeOverride :: CtxRepr args -> TypeRepr ret -> Override p sym MIR args ret -> SomeOverride p sym


bindFn ::
  forall args ret blocks p sym rtp a r .
  (IsSymExprBuilder sym, IsExprBuilder sym, IsBoolSolver sym) =>
  Text -> CFG MIR blocks args ret ->
  OverrideSim p sym MIR rtp a r ()
bindFn fn cfg =
  getSymInterface >>= \s ->
  case Map.lookup fn (overrides s) of
    Nothing ->
      bindFnHandle (cfgHandle cfg) $ UseCFG cfg (postdomInfo cfg)
    Just (($ functionNameFromText fn) -> o) ->
      case o of
        SomeOverride argTys retTy f ->
          case (,) <$> testEquality (cfgReturnType cfg) retTy <*> testEquality (cfgArgTypes cfg) argTys of
            Nothing -> error $ "Mismatching override type for " ++ Text.unpack fn ++
                               ".\n\tExpected (" ++ show (cfgArgTypes cfg) ++ ") → " ++ show (cfgReturnType cfg) ++
                               "\n\tbut got (" ++ show argTys ++ ") → (" ++ show retTy ++ ")."
            Just (Refl, Refl) ->
              bindFnHandle (cfgHandle cfg) $ UseOverride f

  where
    override ::
      forall args ret .
      Text -> CtxRepr args -> TypeRepr ret ->
      (forall rtp . OverrideSim p sym MIR rtp args ret (RegValue sym ret)) ->
      (Text, FunctionName -> SomeOverride p sym)
    override n args ret act = (n, \funName -> SomeOverride args ret (mkOverride' funName ret act))

    overrides :: sym -> Map Text (FunctionName -> SomeOverride p sym)
    overrides s = fromList [ override "::one[0]" Empty (BVRepr (knownNat @ 8)) $
                             do liftIO (putStrLn "Hello, I'm an override")
                                v <- liftIO $ bvLit (s :: sym) knownNat 1
                                return v
                           , override "::crucible_i8[0]" (Empty :> StringRepr) (BVRepr (knownNat @ 8)) $
                             do RegMap (Empty :> str) <- getOverrideArgs
                                name <-
                                  case userSymbol "x" of -- TODO get user-provided name
                                    Left err -> fail (show err)
                                    Right a -> return a
                                v <- liftIO (freshConstant s name (BaseBVRepr (knownNat @ 8)))
                                -- TODO crucible-c has references to stateContext.cruciblePersonality with a variable added - do we need this?
                                return v
                           , override "::crucible_assert[0]" (Empty :> BoolRepr) (StructRepr Empty) $
                             do RegMap (Empty :> c) <- getOverrideArgs
                                s <- getSymInterface
                                liftIO $ assert s (regValue c) (AssertFailureSimError "MIR assertion failed")
                                return knownRepr
                           ]
