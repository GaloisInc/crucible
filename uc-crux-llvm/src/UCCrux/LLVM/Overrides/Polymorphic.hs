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
newtype PolymorphicLLVMOverride p sym arch =
  PolymorphicLLVMOverride
    { getPolymorphicLLVMOverride ::
        forall rtp l a.
        OverrideTemplate p sym arch rtp l a
    }

makePolymorphicLLVMOverride ::
  (forall rtp l a. OverrideTemplate p sym arch rtp l a) ->
  PolymorphicLLVMOverride p sym arch
makePolymorphicLLVMOverride = PolymorphicLLVMOverride

newtype ForAllSymArch f =
  ForAllSymArch
    { getForAllSymArch ::
        forall proxy p sym arch.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        ArchOk arch =>
        proxy arch ->
        f p sym arch
    }

makeForAllSymArch ::
  (forall proxy p sym arch.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   ArchOk arch =>
   proxy arch ->
   f p sym arch) ->
  ForAllSymArch f
makeForAllSymArch = ForAllSymArch

withForAllSymArch ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  ForAllSymArch f ->
  proxy arch ->
  (f p sym arch -> r) ->
  r
withForAllSymArch (ForAllSymArch f) proxy g = g (f proxy)
