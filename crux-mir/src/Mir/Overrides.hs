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
import Lang.Crucible.Backend (AssumptionReason(..), IsBoolSolver, LabeledPred(..), addAssumption, assert)
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

    u8repr :: TypeRepr (BaseToType (BaseBVType 8))
    u8repr = knownRepr

    u32repr :: TypeRepr (BaseToType (BaseBVType 32))
    u32repr = knownRepr


    overrides :: sym -> Map Text (FunctionName -> SomeOverride p sym)
    overrides s = fromList [ override "::one[0]" Empty (BVRepr (knownNat @ 8)) $
                             do liftIO (putStrLn "Hello, I'm an override")
                                v <- liftIO $ bvLit (s :: sym) knownNat 1
                                return v
                           , override "::crucible_i8[0]" (Empty :> StringRepr) u8repr $
                             do RegMap (Empty :> str) <- getOverrideArgs
                                x <- maybe (fail "not a constant string") pure (asString (regValue str))
                                name <-
                                  case userSymbol (Text.unpack x) of
                                    Left err -> fail (show err)
                                    Right a -> return a
                                v <- liftIO (freshConstant s name (BaseBVRepr (knownNat @ 8)))
                                -- TODO crucible-c has references to stateContext.cruciblePersonality with a variable added
                                -- This is to know which variables to ask for when getting a model out of the solver
                                return v
                           , let argTys = (Empty :> BoolRepr :> StringRepr :> StringRepr :> u32repr :> u32repr)
                             in override "::crucible_assert_impl[0]" argTys (StructRepr Empty) $
                                do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                                   s <- getSymInterface
                                   src <- maybe (fail "not a constant src string")
                                            (pure . Text.unpack)
                                            (asString (regValue srcArg))
                                   file <- maybe (fail "not a constant filename string") pure (asString (regValue fileArg))
                                   line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                                   col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                                   let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                                   let reason = AssertFailureSimError ("MIR assertion at " <> locStr <> ":\n\t" <> src)
                                   liftIO $ assert s (regValue c) reason
                                   return knownRepr
                           , let argTys = (Empty :> BoolRepr :> StringRepr :> StringRepr :> u32repr :> u32repr)
                             in override "::crucible_assume_impl[0]" argTys (StructRepr Empty) $
                                do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                                   s <- getSymInterface
                                   loc <- liftIO $ getCurrentProgramLoc s
                                   src <- maybe (fail "not a constant src string")
                                            (pure . Text.unpack)
                                            (asString (regValue srcArg))
                                   file <- maybe (fail "not a constant filename string") pure (asString (regValue fileArg))
                                   line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                                   col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                                   let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                                   let reason = AssumptionReason loc $ "Assumption \n\t" <> src <> "\nfrom " <> locStr
                                   liftIO $ addAssumption s (LabeledPred (regValue c) reason)
                                   return knownRepr
                           ]
