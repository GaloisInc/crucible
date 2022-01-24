{-|
Module      : Lang.Crucible.Go.Overrides
Description : Symbolic override functions for Go.
Maintainer  : abagnall@galois.com
Stability   : experimental

This file contains overrides for generating fresh symbolic variables
as well as assuming and asserting boolean predicates.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Overrides where

import           Control.Monad.State

import           Data.Maybe (fromJust)
import           Data.Text (Text, pack, unpack)

import           GHC.TypeNats as TypeNats

import           System.IO

import           Data.Parameterized.Context as Ctx

import           What4.FunctionName (FunctionName, functionNameFromText)
import qualified What4.Interface as W4
import           What4.ProgramLoc as W4

import           Lang.Crucible.Backend
import qualified Lang.Crucible.Simulator as C
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           Lang.Crucible.Go.Types

import qualified Crux.Types   as Crux

data SomeOverride p sym ext where
  SomeOverride :: Text -- ^ package name
               -> CtxRepr args
               -> TypeRepr ret
               -> Override p sym ext args ret
               -> SomeOverride p sym ext

nameOfOverride :: Override p sym ext args ret -> Text
nameOfOverride (Override { overrideName = nm }) =
  pack $ show nm

mkSomeOverride :: Text -> Text -> CtxRepr args -> TypeRepr ret ->
                  (forall r. C.OverrideSim p sym ext r args ret
                    (RegValue sym ret)) ->
                  SomeOverride p sym ext
mkSomeOverride pkg nm argsRepr retRepr overrideSim =
  SomeOverride pkg argsRepr retRepr $
  Override { overrideName = functionNameFromText nm
           , overrideHandler = C.runOverrideSim retRepr overrideSim }

mkFresh :: IsSymInterface sym
        => String
        -> BaseTypeRepr ty
        -> Crux.OverM p sym ext (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- C.getSymInterface
     liftIO $ W4.freshConstant sym (W4.safeSymbol nm) ty

fresh_int :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> Crux.OverM p sym ext (RegValue sym (BVType w))
fresh_int w = mkFresh "X" $ BaseBVRepr w

fresh_int' :: (IsSymInterface sym, KnownNat w, 1 <= w)
           => Crux.OverM p sym ext (RegValue sym (BVType w))
fresh_int' = fresh_int knownNat

fresh_float :: IsSymInterface sym
            => FloatPrecisionRepr fp
            -> Crux.OverM p sym ext
            (RegValue sym (BaseToType (BaseFloatType fp)))
fresh_float fp = mkFresh "X" $ BaseFloatRepr fp

-- TODO: float, float32, float64

fresh_string :: IsSymInterface sym
             => StringInfoRepr si
             -> Crux.OverM p sym ext
             (RegValue sym (BaseToType (BaseStringType si)))
fresh_string si = mkFresh "X" $ BaseStringRepr si

do_assume :: IsSymInterface sym
          => C.OverrideSim p sym ext gret
          (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          (StructType EmptyCtx) (RegValue sym (StructType EmptyCtx))
do_assume = C.ovrWithBackend $ \bak -> do
  let sym = backendGetSym bak
  RegMap (Empty :> mgs :> file :> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addAssumption bak (GenericAssumption loc "assume" (regValue b))
  return Ctx.empty

do_assert :: IsSymInterface sym
          => C.OverrideSim p sym ext gret
          (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          (StructType EmptyCtx) (RegValue sym (StructType EmptyCtx))
do_assert = C.ovrWithBackend $ \bak -> do
  let sym = backendGetSym bak
  RegMap (Empty :> mgs :> file :> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addDurableAssertion bak (LabeledPred (regValue b)
                                    (C.SimError loc $ C.AssertFailureSimError
                                     "assertion_failure" ""))
  return Ctx.empty

go_overrides :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> [SomeOverride (p sym) sym ext]
go_overrides w =
  [ mkSomeOverride "crucible" "FreshInt" Ctx.empty (BVRepr w) (fresh_int w)
  , mkSomeOverride "crucible" "FreshInt8" Ctx.empty
    (BVRepr (knownNat :: NatRepr 8)) fresh_int'
  , mkSomeOverride "crucible" "FreshInt16" Ctx.empty
    (BVRepr (knownNat :: NatRepr 16)) fresh_int'
  , mkSomeOverride "crucible" "FreshInt32" Ctx.empty
    (BVRepr (knownNat :: NatRepr 32)) fresh_int'
  , mkSomeOverride "crucible" "FreshInt64" Ctx.empty
    (BVRepr (knownNat :: NatRepr 64)) fresh_int'
  , mkSomeOverride "crucible" "FreshUint" Ctx.empty (BVRepr w) (fresh_int w)
  , mkSomeOverride "crucible" "FreshUint8" Ctx.empty
    (BVRepr (knownNat :: NatRepr 8)) fresh_int'
  , mkSomeOverride "crucible" "FreshUint16" Ctx.empty
    (BVRepr (knownNat :: NatRepr 16)) fresh_int'
  , mkSomeOverride "crucible" "FreshUint32" Ctx.empty
    (BVRepr (knownNat :: NatRepr 32)) fresh_int'
  , mkSomeOverride "crucible" "FreshUint64" Ctx.empty
    (BVRepr (knownNat :: NatRepr 64)) fresh_int'
  , mkSomeOverride "crucible" "FreshString" Ctx.empty
    (StringRepr UnicodeRepr) $ fresh_string UnicodeRepr
  , mkSomeOverride "crucible" "Assume"
    (Ctx.Empty :> StringRepr UnicodeRepr :> StringRepr UnicodeRepr :> BoolRepr)
    (StructRepr Ctx.empty) do_assume
  , mkSomeOverride "crucible" "Assert"
    (Ctx.Empty :> StringRepr UnicodeRepr :> StringRepr UnicodeRepr :> BoolRepr)
    (StructRepr Ctx.empty) do_assert ]

lookupOverride :: Text
               -> FunctionName
               -> [SomeOverride p sym ext]
               -> Maybe (SomeOverride p sym ext)
lookupOverride _pkgName _fName [] = Nothing
lookupOverride pkgName fName
  (o@(SomeOverride pkg _argsRepr _retRepr override) : overrides) =
  if pkgName == pkg && fName == overrideName override then
    Just o
  else
    lookupOverride pkgName fName overrides

lookupOverride' :: Maybe (Text, FunctionName)
                -> [SomeOverride p sym ext]
                -> Maybe (SomeOverride p sym ext)
lookupOverride' nm overrides =
  -- TODO: use a map instead
  nm >>= flip (uncurry lookupOverride) overrides
