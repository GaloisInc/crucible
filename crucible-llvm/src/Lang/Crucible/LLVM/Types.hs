{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Types
-- Description      : Crucible type definitions related to LLVM
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Types
  ( Mem
  , memRepr
  , LLVMPointerType
  , LLVMPtr
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , pattern SizeT
  , withPtrWidth
  , HasPtrWidth
  , pattern PtrWidth
  , GlobalSymbol(..)
  , globalSymbolName
  ) where

import           GHC.TypeLits
import           Data.Typeable

import           Data.Parameterized.Context
import           Data.Parameterized.NatRepr

import qualified Text.LLVM.AST as L

import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Types

newtype GlobalSymbol = GlobalSymbol L.Symbol
  deriving (Typeable, Eq, Ord, Show)

globalSymbolName :: GlobalSymbol -> String
globalSymbolName (GlobalSymbol (L.Symbol nm)) = nm

-- | The 'CrucibleType' of an LLVM memory. @'RegValue' sym 'Mem'@ is
-- implemented as @'MemImpl' sym@.
type Mem = IntrinsicType "LLVM_memory" EmptyCtx

memRepr :: TypeRepr Mem
memRepr = knownRepr

-- | This constraint captures the idea that there is a distinguished
--   pointer width in scope which is appropriate according to the C
--   notion of pointer, and object size. In particular, it must be at
--   least 16-bits wide (as required for the @size_t@ type).
type HasPtrWidth w = (1 <= w, 16 <= w, ?ptrWidth :: NatRepr w)

pattern PtrWidth :: HasPtrWidth w => w ~ w' => NatRepr w'
pattern PtrWidth <- (testEquality ?ptrWidth -> Just Refl)
  where PtrWidth = ?ptrWidth

withPtrWidth :: forall w a. (16 <= w) => NatRepr w -> (HasPtrWidth w => a) -> a
withPtrWidth w a =
  case leqTrans (LeqProof :: LeqProof 1 16) (LeqProof :: LeqProof 16 w) of
    LeqProof -> let ?ptrWidth = w in a

-- | Crucible type of pointers/bitvector values of width @w@.
type LLVMPointerType w = RecursiveType "LLVM_pointer" (EmptyCtx ::> BVType w)

-- | Symbolic LLVM pointer or bitvector values of width @w@.
type LLVMPtr sym w = RegValue sym (LLVMPointerType w)

-- | Type family defining how @LLVMPointerType@ unfolds.
type family LLVMPointerImpl ctx where
  LLVMPointerImpl (EmptyCtx ::> BVType w) = StructType (EmptyCtx ::> NatType ::> BVType w)
  LLVMPointerImpl ctx = TypeError ('Text "LLVM_pointer expects a single argument of BVType, but was given" ':<>:
                                   'ShowType ctx)

instance IsRecursiveType "LLVM_pointer" where
  type UnrollType "LLVM_pointer" ctx = LLVMPointerImpl ctx
  unrollType _nm (Empty :> (BVRepr w)) = StructRepr (Empty :> NatRepr :> BVRepr w)
  unrollType nm ctx = typeError nm ctx


-- | This pattern synonym makes it easy to build and destruct runtime
--   representatives of @'LLVMPointerType' w@.
pattern LLVMPointerRepr :: () => (1 <= w, ty ~ LLVMPointerType w) => NatRepr w -> TypeRepr ty
pattern LLVMPointerRepr w <- RecursiveRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
                                           (Empty :> BVRepr w)
  where
    LLVMPointerRepr w = RecursiveRepr knownSymbol (Empty :> BVRepr w)

-- | This pattern creates/matches against the TypeRepr for LLVM pointer values
--   that are of the distinguished pointer width.
pattern PtrRepr :: HasPtrWidth wptr => (ty ~ LLVMPointerType wptr) => TypeRepr ty
pattern PtrRepr = LLVMPointerRepr PtrWidth

-- | This pattern creates/matches against the TypeRepr for raw bitvector values
--   that are of the distinguished pointer width.
pattern SizeT :: HasPtrWidth wptr => (ty ~ BVType wptr) => TypeRepr ty
pattern SizeT = BVRepr PtrWidth
