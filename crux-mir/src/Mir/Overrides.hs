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
{-# Language FlexibleContexts #-}

module Mir.Overrides (bindFn) where

import Control.Lens ((%=))
import Control.Monad.IO.Class

import qualified Data.ByteString as BS
import qualified Data.Char as Char
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Vector(Vector)
import qualified Data.Vector as V
import Data.Word

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import Data.Parameterized.NatRepr

import Data.Semigroup

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text

import System.IO (hPutStrLn)

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend
    ( AssumptionReason(..), IsBoolSolver, LabeledPred(..), addAssumption, assert
    , addFailedAssertion )
import Lang.Crucible.CFG.Core (CFG, cfgArgTypes, cfgHandle, cfgReturnType, lastReg)
import Lang.Crucible.Simulator (SimErrorReason(..))
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.SimError

import Lang.Crucible.Types

import What4.FunctionName (FunctionName, functionNameFromText)
import What4.Interface

import Crux.Model (addVar)
import Crux.Types (Model)

import Mir.Intrinsics
import Mir.DefId

import Debug.Trace

getString :: forall sym. (IsSymExprBuilder sym) => sym -> RegValue sym (MirImmSlice (BVType 8)) -> Maybe Text
getString _ (Empty :> RV mirVec :> RV startExpr :> RV lenExpr)
  | MirVector_Vector vec <- mirVec = do
    start <- asUnsignedBV startExpr
    len <- asUnsignedBV lenExpr
    let slice = V.slice (fromInteger start) (fromInteger len) vec

    let f :: RegValue sym (BVType 8) -> Maybe Word8
        f rv = case asUnsignedBV rv of
                      Just i  -> Just (fromInteger i)
                      Nothing -> Nothing
    bs <- BS.pack <$> mapM f (V.toList slice)
    return $ Text.decodeUtf8 bs
  | otherwise = Nothing

data SomeOverride p sym where
  SomeOverride :: CtxRepr args -> TypeRepr ret -> Override p sym MIR args ret -> SomeOverride p sym

makeSymbolicVar ::
    (IsSymExprBuilder sym) =>
    RegEntry sym (MirImmSlice (BVType 8)) ->
    BaseTypeRepr btp ->
    OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym (BaseToType btp))
makeSymbolicVar nameReg btpr = do
    sym <- getSymInterface
    name <- case getString sym (regValue nameReg) of
        Just x -> return $ Text.unpack x
        Nothing -> fail "symbolic variable name must be a concrete string"
    nameSymbol <- case userSymbol name of
        Left err -> fail $ "invalid symbolic variable name " ++ show name ++ ": " ++ show err
        Right x -> return x
    v <- liftIO $ freshConstant sym nameSymbol btpr
    loc <- liftIO $ getCurrentProgramLoc sym
    stateContext.cruciblePersonality %= addVar loc name btpr v
    return v

array_symbolic ::
  forall sym rtp btp .
  (IsSymExprBuilder sym, IsExprBuilder sym, IsBoolSolver sym) =>
  BaseTypeRepr btp ->
  OverrideSim (Model sym) sym MIR rtp
    (EmptyCtx ::> MirImmSlice (BVType 8)) (UsizeArrayType btp)
    (RegValue sym (UsizeArrayType btp))
array_symbolic btpr = do
    RegMap (Empty :> nameReg) <- getOverrideArgs
    makeSymbolicVar nameReg $ BaseArrayRepr (Empty :> BaseUsizeRepr) btpr

bindFn ::
  forall args ret blocks sym rtp a r .
  (IsSymExprBuilder sym, IsExprBuilder sym, IsBoolSolver sym) =>
  Text -> CFG MIR blocks args ret ->
  OverrideSim (Model sym) sym MIR rtp a r ()
bindFn name cfg
  | (normDefId "crucible::array::symbolic" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MirImmSliceRepr (BVRepr w) <- cfgArgTypes cfg
  , UsizeArrayRepr btpr <- cfgReturnType cfg
  , Just Refl <- testEquality w (knownNat @8)
  = bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "array::symbolic" (UsizeArrayRepr btpr) (array_symbolic btpr)
bindFn fn cfg =
  getSymInterface >>= \s ->
  case Map.lookup fn (overrides s) of
    Nothing ->
      bindFnHandle (cfgHandle cfg) $ UseCFG cfg (postdomInfo cfg)
    Just (($ functionNameFromText fn) -> SomeOverride argTys retTy f) ->
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
      (forall rtp . OverrideSim (Model sym) sym MIR rtp args ret (RegValue sym ret)) ->
      (Text, FunctionName -> SomeOverride (Model sym) sym)
    override n args ret act =
        -- Round-trip through `DefId` to normalize the path.  In particular,
        -- this adds the current `defaultDisambiguator` and any missing `[0]`s.
        ( normDefId n
        , \funName -> SomeOverride args ret (mkOverride' funName ret act)
        )

    u8repr :: TypeRepr (BaseToType (BaseBVType 8))
    u8repr = knownRepr

    u32repr :: TypeRepr (BaseToType (BaseBVType 32))
    u32repr = knownRepr

    strrepr :: TypeRepr (MirImmSlice (BVType 8))
    strrepr = knownRepr

    symb_bv :: forall n . (1 <= n) => Text -> NatRepr n -> (Text, FunctionName -> SomeOverride (Model sym) sym)
    symb_bv name n =
      override name (Empty :> strrepr) (BVRepr n) $
      do RegMap (Empty :> str) <- getOverrideArgs
         makeSymbolicVar str $ BaseBVRepr n

    overrides :: sym -> Map Text (FunctionName -> SomeOverride (Model sym) sym)
    overrides s =
      fromList [ override "crucible::one" Empty (BVRepr (knownNat @ 8)) $
                 do h <- printHandle <$> getContext
                    liftIO (hPutStrLn h "Hello, I'm an override")
                    v <- liftIO $ bvLit (s :: sym) knownNat 1
                    return v
               , symb_bv "crucible::symbolic::symbolic_u8"  (knownNat @ 8)
               , symb_bv "crucible::symbolic::symbolic_u16" (knownNat @ 16)
               , symb_bv "crucible::symbolic::symbolic_u32" (knownNat @ 32)
               , symb_bv "crucible::symbolic::symbolic_u64" (knownNat @ 64)
               , symb_bv "crucible::symbolic::symbolic_u128" (knownNat @ 128)
               , symb_bv "int512::symbolic" (knownNat @ 512)
               , symb_bv "crucible::bitvector::make_symbolic_128" (knownNat @ 128)
               , symb_bv "crucible::bitvector::make_symbolic_256" (knownNat @ 256)
               , symb_bv "crucible::bitvector::make_symbolic_512" (knownNat @ 512)
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override "crucible::crucible_assert_impl" argTys UnitRepr $
                    do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                       s <- getSymInterface
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                (getString s (regValue srcArg))
                       file <- maybe (fail "not a constant filename string") pure (getString s (regValue fileArg))
                       line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                       col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = AssertFailureSimError ("MIR assertion at " <> locStr <> ":\n\t" <> src) ""
                       liftIO $ assert s (regValue c) reason
                       return ()
               , let argTys = (Empty :> BoolRepr :> strrepr :> strrepr :> u32repr :> u32repr)
                 in override "crucible::crucible_assume_impl" argTys UnitRepr $
                    do RegMap (Empty :> c :> srcArg :> fileArg :> lineArg :> colArg) <- getOverrideArgs
                       s <- getSymInterface
                       loc <- liftIO $ getCurrentProgramLoc s
                       src <- maybe (fail "not a constant src string")
                                (pure . Text.unpack)
                                (getString s (regValue srcArg))
                       file <- maybe (fail "not a constant filename string") pure (getString s (regValue fileArg))
                       line <- maybe (fail "not a constant line number") pure (asUnsignedBV (regValue lineArg))
                       col <- maybe (fail "not a constant column number") pure (asUnsignedBV (regValue colArg))
                       let locStr = Text.unpack file <> ":" <> show line <> ":" <> show col
                       let reason = AssumptionReason loc $ "Assumption \n\t" <> src <> "\nfrom " <> locStr
                       liftIO $ addAssumption s (LabeledPred (regValue c) reason)
                       return ()
               ]
