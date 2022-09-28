-- |
-- Module           : Lang.Crucible.LLVM.PtrSize
-- Description      : Type-level representation of LLVM pointer width
-- Copyright        : (c) Galois, Inc 2022
-- License          : BSD3
-- Maintainer       : langston@galois.com
-- Stability        : provisional
--
-- The Crucible type of LLVM pointers
-- ('Lang.Crucible.LLVM.MemModel.Pointer.LLVMPointerType') explicitly represents
-- the size of pointers at the type level, which can help prevent ill-typed
-- expressions from being formed. This module provides a data kind ('PtrSize')
-- and corresponding singleton ('PtrSizeRepr') for representing the size of
-- pointers in a given LLVM module (which can be derived from the module's
-- target triple and/or data layout).
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Extension.PtrSize
  ( type PtrSize(PtrSize)
  , PtrSizeRepr(..)
  , PtrSizeBits
  ) where

import           Data.Kind (Type)

import           Data.Parameterized (NatRepr)
import           Data.Parameterized.Classes (OrdF(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Type.Equality (TestEquality(..))
import           GHC.TypeLits (Nat)

-- | Data kind for representing pointer width. Size is measured in number of
-- bits.
--
-- TODO(lb): Stop exporting the constructor when Arch.hs is removed.
data PtrSize = PtrSize Nat

-- | Get the width of pointers, measured in number of bits.
type PtrSizeBits :: PtrSize -> Nat
type family PtrSizeBits ptrsz where
  PtrSizeBits ('PtrSize wptr) = wptr

-- | Runtime representation of pointer width.
type PtrSizeRepr :: PtrSize -> Type
data PtrSizeRepr ptrsz where
  PtrSizeRepr :: NatRepr wptr -> PtrSizeRepr ('PtrSize wptr)

$(return [])

instance TestEquality PtrSizeRepr where
  testEquality =
    $(U.structuralTypeEquality [t|PtrSizeRepr|]
        [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
        ])

instance OrdF PtrSizeRepr where
  compareF =
    $(U.structuralTypeOrd [t|PtrSizeRepr|]
        [ (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
        ])
