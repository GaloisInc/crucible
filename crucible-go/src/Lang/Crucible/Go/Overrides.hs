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

import qualified Crux.Overrides as Crux
import qualified Crux.Types   as Crux

data SomeOverride p sym ext where
  SomeOverride :: Text -- ^ package name
               -> FunctionName
               -> C.TypedOverride p sym ext args ret
               -> SomeOverride p sym ext

nameOfOverride :: Override p sym ext args ret -> Text
nameOfOverride (Override { overrideName = nm }) =
  pack $ show nm

mkSomeOverride :: Text -> Text -> CtxRepr args -> TypeRepr ret ->
                  (forall r args' ret'.
                    Assignment (C.RegValue' sym) args ->
                    C.OverrideSim p sym ext r args' ret'
                    (RegValue sym ret)) ->
                  SomeOverride p sym ext
mkSomeOverride pkg nm argsRepr retRepr overrideSim =
  SomeOverride pkg (functionNameFromText nm) $
  C.TypedOverride
  { C.typedOverrideHandler = overrideSim
  , C.typedOverrideArgs = argsRepr
  , C.typedOverrideRet = retRepr
  }

fresh_int :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> Crux.OverM p sym ext (RegValue sym (BVType w))
fresh_int w = Crux.mkFresh "X" $ BaseBVRepr w

fresh_int' :: (IsSymInterface sym, KnownNat w, 1 <= w)
           => Crux.OverM p sym ext (RegValue sym (BVType w))
fresh_int' = fresh_int knownNat

fresh_float :: IsSymInterface sym
            => FloatPrecisionRepr fp
            -> Crux.OverM p sym ext
            (RegValue sym (BaseToType (BaseFloatType fp)))
fresh_float fp = Crux.mkFresh "X" $ BaseFloatRepr fp

-- TODO: float, float32, float64

fresh_string :: IsSymInterface sym
             => StringInfoRepr si
             -> Crux.OverM p sym ext
             (RegValue sym (BaseToType (BaseStringType si)))
fresh_string si = Crux.mkFresh "X" $ BaseStringRepr si

do_assume :: IsSymInterface sym
          => Assignment (C.RegValue' sym) (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          -> C.OverrideSim p sym ext gret args ret (RegValue sym (StructType EmptyCtx))
do_assume args = C.ovrWithBackend $ \bak -> do
  let sym = backendGetSym bak
  (Empty :> _mgs :> _file :> C.RV b) <- pure args
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addAssumption bak (GenericAssumption loc "assume" b)
  return Ctx.empty

do_assert :: IsSymInterface sym
          => Assignment (C.RegValue' sym) (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          -> C.OverrideSim p sym ext gret args ret (RegValue sym (StructType EmptyCtx))
do_assert args = C.ovrWithBackend $ \bak -> do
  let sym = backendGetSym bak
  (Empty :> _mgs :> _file :> C.RV b) <- pure args
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addDurableAssertion bak (LabeledPred b
                                    (C.SimError loc $ C.AssertFailureSimError
                                     "assertion_failure" ""))
  return Ctx.empty

go_overrides :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> [SomeOverride (p sym) sym ext]
go_overrides w =
  [ mkSomeOverride "crucible" "FreshInt" Ctx.empty (BVRepr w) (\_args -> fresh_int w)
  , mkSomeOverride "crucible" "FreshInt8" Ctx.empty
    (BVRepr (knownNat :: NatRepr 8)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshInt16" Ctx.empty
    (BVRepr (knownNat :: NatRepr 16)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshInt32" Ctx.empty
    (BVRepr (knownNat :: NatRepr 32)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshInt64" Ctx.empty
    (BVRepr (knownNat :: NatRepr 64)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshUint" Ctx.empty (BVRepr w) (\_args -> fresh_int w)
  , mkSomeOverride "crucible" "FreshUint8" Ctx.empty
    (BVRepr (knownNat :: NatRepr 8)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshUint16" Ctx.empty
    (BVRepr (knownNat :: NatRepr 16)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshUint32" Ctx.empty
    (BVRepr (knownNat :: NatRepr 32)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshUint64" Ctx.empty
    (BVRepr (knownNat :: NatRepr 64)) (\_args -> fresh_int')
  , mkSomeOverride "crucible" "FreshString" Ctx.empty
    (StringRepr UnicodeRepr) $ (\_args -> fresh_string UnicodeRepr)
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
  (o@(SomeOverride pkg ovrName typedOvr) : overrides) =
  if pkgName == pkg && fName == ovrName then
    Just o
  else
    lookupOverride pkgName fName overrides

lookupOverride' :: Maybe (Text, FunctionName)
                -> [SomeOverride p sym ext]
                -> Maybe (SomeOverride p sym ext)
lookupOverride' nm overrides =
  -- TODO: use a map instead
  nm >>= flip (uncurry lookupOverride) overrides
