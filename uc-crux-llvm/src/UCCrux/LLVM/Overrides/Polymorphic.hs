{-
Module       : UCCrux.LLVM.Overrides.Polymorphic
Description  : A 'PolymorphicLLVMOverride' is one that's maximally polymorphic
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Overrides.Polymorphic
  ( PolymorphicLLVMOverride,
    makePolymorphicLLVMOverride,
    getPolymorphicLLVMOverride,
    ForAllSym,
    makeForAllSym,
    getForAllSym,
    withForAllSym,
    ForAllSymArch,
    makeForAllSymArch,
    getForAllSymArch,
    withForAllSymArch
  )
where

{- ORMOLU_DISABLE -}
import           Lang.Crucible.Backend (IsSymInterface)

import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)

import           Crux.LLVM.Overrides (ArchOk)
{- ORMOLU_ENABLE -}

-- | An LLVM override that can be registered in a Crucible override of any type.
newtype PolymorphicLLVMOverride arch p sym =
  PolymorphicLLVMOverride
    { getPolymorphicLLVMOverride ::
        forall rtp l a.
        OverrideTemplate p sym arch rtp l a
    }

makePolymorphicLLVMOverride ::
  (forall rtp l a. OverrideTemplate p sym arch rtp l a) ->
  PolymorphicLLVMOverride arch p sym
makePolymorphicLLVMOverride = PolymorphicLLVMOverride

newtype ForAllSym f =
  ForAllSym
    { getForAllSym ::
        forall p sym.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f p sym
    }

makeForAllSym ::
  (forall p sym.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   f p sym) ->
  ForAllSym f
makeForAllSym = ForAllSym

withForAllSym ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ForAllSym f ->
  (f p sym -> r) ->
  r
withForAllSym (ForAllSym f) g = g f

newtype ForAllSymArch f =
  ForAllSymArch
    { getForAllSymArch ::
        forall proxy p sym arch.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        ArchOk arch =>
        proxy arch ->
        f arch p sym
    }

makeForAllSymArch ::
  (forall proxy p sym arch.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   ArchOk arch =>
   proxy arch ->
   f arch p sym) ->
  ForAllSymArch f
makeForAllSymArch = ForAllSymArch

withForAllSymArch ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  ForAllSymArch f ->
  proxy arch ->
  (f arch p sym -> r) ->
  r
withForAllSymArch (ForAllSymArch f) proxy g = g (f proxy)
