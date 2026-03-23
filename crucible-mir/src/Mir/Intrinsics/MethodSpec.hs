{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- See: https://ghc.haskell.org/trac/ghc/ticket/11581
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- TODO(#1786): refine exports, if necessary
module Mir.Intrinsics.MethodSpec
  ( MethodSpecImpl (..),
    MethodSpec (..),
    MethodSpecSymbol,
    MethodSpecType,
    pattern MethodSpecRepr,
    MethodSpecFam,
    MethodSpecBuilderImpl (..),
    MethodSpecBuilder(..),
    MethodSpecBuilderSymbol,
    MethodSpecBuilderType,
    pattern MethodSpecBuilderRepr,
    MethodSpecBuilderFam,
  )
where

import GHC.TypeLits (ErrorMessage (ShowType, Text, (:<>:)), TypeError)

import Data.Kind (Type)
import Data.Parameterized.Context (Ctx, EmptyCtx, pattern Empty)
import Data.Parameterized.SymbolRepr (knownSymbol)
import Data.Type.Equality (testEquality, pattern Refl)
import Data.Word (Word64)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.Simulator.Intrinsics
  ( IntrinsicClass (Intrinsic, muxIntrinsic),
    typeError,
  )
import Lang.Crucible.Simulator.OverrideSim (OverrideSim)
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Types (CrucibleType, IntrinsicType, TypeRepr (..))

import Mir.Intrinsics.Reference (MirReferenceMux)
import Mir.Intrinsics.Slice (MirSlice)
import Mir.Intrinsics.Syntax (MIR)

--------------------------------------------------------------------------------
-- ** MethodSpec and MethodSpecBuilder
--
-- We define the intrinsics here so they can be used in `TransTy.tyToRepr`, and
-- also define their interfaces (as typeclasses), but we don't provide any
-- concrete implementations in `crux-mir`.  Instead, implementations of these
-- types are in `saw-script/crux-mir-comp`, since they depend on some SAW
-- components, such as `saw-script`'s `MethodSpec`.

class MethodSpecImpl sym ms where
    -- | Pretty-print the MethodSpec, returning the result as a Rust string
    -- (`&str`).
    msPrettyPrint ::
        forall p rtp args ret.
        ms ->
        OverrideSim (p sym) sym MIR rtp args ret (RegValue sym MirSlice)

    -- | Enable the MethodSpec for use as an override for the remainder of the
    -- current test.
    msEnable ::
        forall p rtp args ret.
        ms ->
        OverrideSim (p sym) sym MIR rtp args ret ()

data MethodSpec sym = forall ms. MethodSpecImpl sym ms => MethodSpec {
    msData :: ms,
    msNonce :: Word64
}

type MethodSpecSymbol = "MethodSpec"
type MethodSpecType = IntrinsicType MethodSpecSymbol EmptyCtx

pattern MethodSpecRepr :: () => tp' ~ MethodSpecType => TypeRepr tp'
pattern MethodSpecRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MethodSpecSymbol) -> Just Refl) Empty
 where MethodSpecRepr = IntrinsicRepr (knownSymbol @MethodSpecSymbol) Empty

type family MethodSpecFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MethodSpecFam sym EmptyCtx = MethodSpec sym
  MethodSpecFam sym ctx = TypeError
    ('Text "MethodSpecType expects no arguments, but was given" :<>: 'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MethodSpecSymbol where
  type Intrinsic sym MethodSpecSymbol ctx = MethodSpecFam sym ctx

  muxIntrinsic _sym _iTypes _nm Empty _p ms1 ms2
    | msNonce ms1 == msNonce ms2 = return ms1
    | otherwise = fail "can't mux MethodSpecs"
  muxIntrinsic _sym _tys nm ctx _ _ _ = typeError nm ctx


class MethodSpecBuilderImpl sym msb where
    msbAddArg :: forall p rtp args ret tp.
        TypeRepr tp -> MirReferenceMux sym -> msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbSetReturn :: forall p rtp args ret tp.
        TypeRepr tp -> MirReferenceMux sym -> msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbGatherAssumes :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbGatherAsserts :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret msb
    msbFinish :: forall p rtp args ret.
        msb ->
        OverrideSim (p sym) sym MIR rtp args ret (MethodSpec sym)

data MethodSpecBuilder sym = forall msb. MethodSpecBuilderImpl sym msb => MethodSpecBuilder msb

type MethodSpecBuilderSymbol = "MethodSpecBuilder"
type MethodSpecBuilderType = IntrinsicType MethodSpecBuilderSymbol EmptyCtx

pattern MethodSpecBuilderRepr :: () => tp' ~ MethodSpecBuilderType => TypeRepr tp'
pattern MethodSpecBuilderRepr <-
     IntrinsicRepr (testEquality (knownSymbol @MethodSpecBuilderSymbol) -> Just Refl) Empty
 where MethodSpecBuilderRepr = IntrinsicRepr (knownSymbol @MethodSpecBuilderSymbol) Empty

type family MethodSpecBuilderFam (sym :: Type) (ctx :: Ctx CrucibleType) :: Type where
  MethodSpecBuilderFam sym EmptyCtx = MethodSpecBuilder sym
  MethodSpecBuilderFam sym ctx = TypeError
    ('Text "MethodSpecBuilderType expects no arguments, but was given" :<>: 'ShowType ctx)
instance IsSymInterface sym => IntrinsicClass sym MethodSpecBuilderSymbol where
  type Intrinsic sym MethodSpecBuilderSymbol ctx = MethodSpecBuilderFam sym ctx

  muxIntrinsic _sym _iTypes _nm Empty _ _ _ =
    fail "can't mux MethodSpecBuilders"
  muxIntrinsic _sym _tys nm ctx _ _ _ = typeError nm ctx
