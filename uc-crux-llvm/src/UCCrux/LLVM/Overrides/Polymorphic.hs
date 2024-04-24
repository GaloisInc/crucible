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
  ( ForAllSym,
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

import           Lang.Crucible.LLVM (LLVM)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)

import           Crux.LLVM.Overrides (ArchOk)
{- ORMOLU_ENABLE -}

newtype ForAllSym f =
  ForAllSym
    { getForAllSym ::
        forall p sym.
        IsSymInterface sym =>
        HasLLVMAnn sym =>
        f p sym LLVM
    }

makeForAllSym ::
  (forall p sym.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   f p sym LLVM) ->
  ForAllSym f
makeForAllSym = ForAllSym

withForAllSym ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ForAllSym f ->
  (f p sym LLVM -> r) ->
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
        f p sym LLVM arch
    }

makeForAllSymArch ::
  (forall proxy p sym arch.
   IsSymInterface sym =>
   HasLLVMAnn sym =>
   ArchOk arch =>
   proxy arch ->
   f p sym LLVM arch) ->
  ForAllSymArch f
makeForAllSymArch = ForAllSymArch

withForAllSymArch ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  ForAllSymArch f ->
  proxy arch ->
  (f p sym LLVM arch -> r) ->
  r
withForAllSymArch (ForAllSymArch f) proxy g = g (f proxy)
