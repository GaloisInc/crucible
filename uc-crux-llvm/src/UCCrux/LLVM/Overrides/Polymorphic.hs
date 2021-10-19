{-
Module       : UCCrux.LLVM.Overrides.Polymorphic
Description  : A 'PolymorphicLLVMOverride' is one that's maximally polymorphic
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.Overrides.Polymorphic
  ( PolymorphicLLVMOverride,
    makePolymorphicLLVMOverride,
    getPolymorphicLLVMOverride
  )
where

{- ORMOLU_DISABLE -}
import           Lang.Crucible.LLVM.Intrinsics (OverrideTemplate)
{- ORMOLU_ENABLE -}

-- | An override that is compatible with any suitable symbolic backend.
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
