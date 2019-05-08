-- |
-- Module           : Lang.Crucible.LLVM.Arch
-- Description      : Representations of LLVM architectures
-- Copyright        : (c) Galois, Inc 2015-2018
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Extension.Arch
  ( type LLVMArch
  , type X86
  , ArchWidth
  , ArchRepr(..)
  ) where

import           GHC.Generics (Generic)
import           Data.Parameterized (NatRepr)
import           Data.Parameterized.Classes (OrdF(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Type.Equality (TestEquality(..))
import           Data.Typeable (Typeable)
import           GHC.TypeLits (Nat)

-- | Data kind for representing LLVM architectures.
--   Currently only X86 variants are supported.
data LLVMArch = X86 Nat
  deriving (Generic, Typeable)

-- | LLVM Architecture tag for X86 variants
--
--   @X86 :: Nat -> LLVMArch@
type X86 = 'X86

-- | Type family defining the native machine word size
--   for a given architecture.
type family ArchWidth (arch :: LLVMArch) :: Nat where
  ArchWidth (X86 wptr) = wptr

-- | Runtime representation of architectures.
data ArchRepr (arch :: LLVMArch) where
  X86Repr :: NatRepr w -> ArchRepr (X86 w)

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
