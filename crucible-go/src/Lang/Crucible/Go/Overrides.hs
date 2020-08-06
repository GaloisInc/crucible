{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Overrides where

import           Control.Monad.State

import           Data.Text (Text, pack, unpack)

import           Debug.Trace (trace)

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
                  (forall r. C.OverrideSim p sym ext r args ret (RegValue sym ret)) ->
                  SomeOverride p sym ext
mkSomeOverride pkg nm argsRepr retRepr overrideSim =
  SomeOverride pkg argsRepr retRepr $
  Override { overrideName = functionNameFromText nm
           , overrideHandler = C.runOverrideSim retRepr overrideSim }

mkFresh :: IsSymInterface sym
        => String
        -> BaseTypeRepr ty
        -> Crux.OverM sym ext (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- C.getSymInterface
     name <- case W4.userSymbol nm of
               Left err -> fail (show err)
               Right a  -> return a
     liftIO $ W4.freshConstant sym name ty

fresh_int :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> Crux.OverM sym ext (RegValue sym (BVType w))
fresh_int w = mkFresh "X" (BaseBVRepr w)

do_assume :: IsSymInterface sym
          => C.OverrideSim p sym ext gret
          (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          (StructType EmptyCtx) (RegValue sym (StructType EmptyCtx))
do_assume = do
  sym <- C.getSymInterface
  RegMap (Empty :> mgs :> file :> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addAssumption sym (LabeledPred (regValue b) (AssumptionReason loc "assume"))
  return Ctx.empty

do_assert :: IsSymInterface sym
          => C.OverrideSim p sym ext gret
          (EmptyCtx ::> StringType Unicode ::> StringType Unicode ::> BoolType)
          (StructType EmptyCtx) (RegValue sym (StructType EmptyCtx))
do_assert = do
  sym <- C.getSymInterface
  RegMap (Empty :> mgs :> file :> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addDurableAssertion sym (LabeledPred (regValue b)
                                    (C.SimError loc $ C.AssertFailureSimError
                                     "assertion_failure" ""))
  return Ctx.empty

go_overrides :: (IsSymInterface sym, 1 <= w)
             => NatRepr w
             -> [(SomeOverride (Crux.Model sym) sym ext)]
go_overrides w =
  [ mkSomeOverride "crucible" "FreshInt" Ctx.empty (BVRepr w) (fresh_int w)
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
  nm >>= flip (uncurry lookupOverride) overrides
