{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Crux.Overrides
  ( mkFresh
  , mkFreshFloat
  , baseFreshOverride
  , baseFreshOverride'
  ) where

import qualified Data.Parameterized.Context as Ctx

import What4.BaseTypes (BaseTypeRepr)
import qualified What4.Interface as W4
import qualified What4.InterpretedFloatingPoint as W4

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Simulator.RegValue as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Simulator.OverrideSim as C

import Crux.Types (OverM)
import Control.Monad.IO.Class (liftIO)

-- | Create a fresh constant ('W4.freshConstant') with the given base type
mkFresh ::
  C.IsSymInterface sym =>
  W4.SolverSymbol ->
  BaseTypeRepr ty ->
  OverM personality sym ext (C.RegValue sym (C.BaseToType ty))
mkFresh name ty =
  C.ovrWithBackend $ \bak ->
    do let sym = C.backendGetSym bak
       elt <- liftIO (W4.freshConstant sym name ty)
       loc <- liftIO $ W4.getCurrentProgramLoc sym
       let ev = C.CreateVariableEvent loc (show name) ty elt
       liftIO $ C.addAssumptions bak (C.singleEvent ev)
       return elt

-- | Create a fresh float constant ('W4.freshFloatConstant')
mkFreshFloat ::
  C.IsSymInterface sym =>
  W4.SolverSymbol ->
  C.FloatInfoRepr fi ->
  OverM personality sym ext (C.RegValue sym (C.FloatType fi))
mkFreshFloat name fi =
  C.ovrWithBackend $ \bak ->
    do let sym = C.backendGetSym bak
       elt <- liftIO $ W4.freshFloatConstant sym name fi
       loc <- liftIO $ W4.getCurrentProgramLoc sym
       let ev = C.CreateVariableEvent loc (show name) (W4.iFloatBaseTypeRepr sym fi) elt
       liftIO $ C.addAssumptions bak (C.singleEvent ev)
       return elt

-- | Build an override that takes a string and returns a fresh constant with
-- that string as its name.
baseFreshOverride :: 
  C.IsSymInterface sym =>
  W4.BaseTypeRepr bty ->
  -- | The language's string type (e.g., @LLVMPointerType@ for LLVM)
  C.TypeRepr stringTy ->
  -- | Get the variable name as a concrete string from the override arguments
  (C.RegValue' sym stringTy -> OverM p sym ext W4.SolverSymbol) ->
  C.TypedOverride p sym ext (C.EmptyCtx C.::> stringTy) (C.BaseToType bty)
baseFreshOverride bty sty getStr =
  C.TypedOverride
  { C.typedOverrideHandler = \(Ctx.Empty Ctx.:> strVal) -> do
      str <- getStr strVal
      mkFresh str bty
  , C.typedOverrideArgs = Ctx.Empty Ctx.:> sty
  , C.typedOverrideRet = C.baseToType bty
  }

-- | Build an override that takes no arguments and returns a fresh
-- constant that uses the given name. Generally, frontends should prefer
-- 'baseFreshOverride', to allow users to specify variable names.
baseFreshOverride' :: 
  C.IsSymInterface sym =>
  -- | Variable name
  W4.SolverSymbol ->
  W4.BaseTypeRepr bty ->
  C.TypedOverride (p sym) sym ext C.EmptyCtx (C.BaseToType bty)
baseFreshOverride' nm bty =
  C.TypedOverride
  { C.typedOverrideHandler = \Ctx.Empty -> mkFresh nm bty
  , C.typedOverrideArgs = Ctx.Empty
  , C.typedOverrideRet = C.baseToType bty
  }
