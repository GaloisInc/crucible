-- |
-- Module           : Lang.Crucible.LLVM.Arch
-- Description      : Representations of LLVM architectures
-- Copyright        : (c) Galois, Inc 2015-2018
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.Extension.Arch
  ( type LLVMArch
  , type X86
  , ArchWidth
  , ArchRepr(..)
  ) where

import           Data.Parameterized (NatRepr)
import           Data.Parameterized.Classes (OrdF(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Type.Equality (TestEquality(..))
import           GHC.TypeLits (Nat)

import           Lang.Crucible.LLVM.Extension.PtrSize

-- | Data kind for representing LLVM architectures.
type LLVMArch = PtrSize
{-# DEPRECATED LLVMArch "Use Lang.Crucible.LLVM.Extension.PtrSize" #-}

-- | LLVM Architecture tag for X86 variants
--
--   @X86 :: Nat -> LLVMArch@
type X86 = 'PtrSize
{-# DEPRECATED X86 "Use Lang.Crucible.LLVM.Extension.PtrSize" #-}

-- | Type family defining the native machine word size
--   for a given architecture.
type family ArchWidth (arch :: LLVMArch) :: Nat where
  ArchWidth ptrsz = PtrSizeBits ptrsz
{-# DEPRECATED ArchWidth "Use Lang.Crucible.LLVM.Extension.PtrSize" #-}

-- | Runtime representation of architectures.
data ArchRepr (arch :: LLVMArch) where
  X86Repr :: NatRepr w -> ArchRepr (X86 w)
{-# DEPRECATED ArchRepr "Use Lang.Crucible.LLVM.Extension.PtrSize" #-}
{-# DEPRECATED X86Repr "Use Lang.Crucible.LLVM.Extension.PtrSize" #-}

$(return [])

instance TestEquality ArchRepr where
  testEquality =
    $(U.structuralTypeEquality [t|ArchRepr|]
        [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
        ])

instance OrdF ArchRepr where
  compareF =
    $(U.structuralTypeOrd [t|ArchRepr|]
        [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
        ])
