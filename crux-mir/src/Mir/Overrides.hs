{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language KindSignatures #-}
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
import Data.Parameterized.NatRepr

import Data.Semigroup

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

    symb_bv :: forall n . (1 <= n) => Text -> NatRepr n -> (Text, FunctionName -> SomeOverride p sym)
    symb_bv name n =
      override name (Empty :> StringRepr) (BVRepr n) $
      do RegMap (Empty :> str) <- getOverrideArgs
         x <- maybe (fail "not a constant string") pure (asString (regValue str))
         let y = filter ((/=) '\"') (Text.unpack x)
         nname <-
           case userSymbol y of
             Left err -> fail (show err ++ " " ++ y)
             Right a -> return a
         s <- getSymInterface
         v <- liftIO (freshConstant s nname (BaseBVRepr n))
         -- TODO crucible-c has references to stateContext.cruciblePersonality with a variable added
         -- This is to know which variables to ask for when getting a model out of the solver
         return v

    overrides :: sym -> Map Text (FunctionName -> SomeOverride p sym)
    overrides s =
      fromList [ override "::one[0]" Empty (BVRepr (knownNat @ 8)) $
                 do liftIO (putStrLn "Hello, I'm an override")
                    v <- liftIO $ bvLit (s :: sym) knownNat 1
                    return v
               , symb_bv "::crucible_i8[0]"  (knownNat @ 8)
               , symb_bv "::crucible_i16[0]" (knownNat @ 16)
               , symb_bv "::crucible_i32[0]" (knownNat @ 32)
               , symb_bv "::crucible_i64[0]" (knownNat @ 64)
               , symb_bv "::crucible_u8[0]"  (knownNat @ 8)
               , symb_bv "::crucible_u16[0]" (knownNat @ 16)
               , symb_bv "::crucible_u32[0]" (knownNat @ 32)
               , symb_bv "::crucible_u64[0]" (knownNat @ 64)
               , let argTys = (Empty :> BoolRepr :> StringRepr :> StringRepr :> u32repr :> u32repr)
                 in override "::crucible_assert_impl[0]" argTys UnitRepr $
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
                       return ()
               , let argTys = (Empty :> BoolRepr :> StringRepr :> StringRepr :> u32repr :> u32repr)
                 in override "::crucible_assume_impl[0]" argTys UnitRepr $
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
                       return ()
               ]
