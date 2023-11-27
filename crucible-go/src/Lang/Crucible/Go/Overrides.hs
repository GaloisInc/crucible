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
{-# LANGUAGE TypeApplications #-}
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
             -> C.TypedOverride (p sym) sym ext Ctx.EmptyCtx (BVType w)
fresh_int w = Crux.baseFreshOverride' (W4.safeSymbol "X") (BaseBVRepr w)

fresh_int' :: (KnownNat w, 1 <= w, IsSymInterface sym)
           => C.TypedOverride (p sym) sym ext Ctx.EmptyCtx (BVType w)
fresh_int' = fresh_int knownNat

fresh_float :: IsSymInterface sym
            => FloatPrecisionRepr fp
            -> Crux.OverM p sym ext
            (RegValue sym (BaseToType (BaseFloatType fp)))
fresh_float fp = Crux.mkFresh (W4.safeSymbol "X") $ BaseFloatRepr fp

-- TODO: float, float32, float64

fresh_string :: IsSymInterface sym
             => StringInfoRepr si
             -> Crux.OverM p sym ext
             (RegValue sym (BaseToType (BaseStringType si)))
fresh_string si = Crux.mkFresh (W4.safeSymbol "X") $ BaseStringRepr si

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
  Crux.doCrucibleAssert "assertion_failure" b (plSourceLoc loc)
  return Ctx.empty

go_overrides :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> [SomeOverride (p sym) sym ext]
go_overrides w =
  [ SomeOverride "crucible" "FreshInt" (fresh_int w)
  , SomeOverride "crucible" "FreshInt8" (fresh_int' @8)
  , SomeOverride "crucible" "FreshInt16" (fresh_int' @16) 
  , SomeOverride "crucible" "FreshInt32" (fresh_int' @32)
  , SomeOverride "crucible" "FreshInt64" (fresh_int' @64)
  , SomeOverride "crucible" "FreshUint" (fresh_int w)
  , SomeOverride "crucible" "FreshUint8" (fresh_int' @8)
  , SomeOverride "crucible" "FreshUint16" (fresh_int' @16)
  , SomeOverride "crucible" "FreshUint32" (fresh_int' @32)
  , SomeOverride "crucible" "FreshUint64" (fresh_int' @64)
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
