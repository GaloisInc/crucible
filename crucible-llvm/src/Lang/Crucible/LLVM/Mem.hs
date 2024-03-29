-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Mem
-- Description      : TODO
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : langston@galois.com
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Mem
  ( PosNat(..)
  , SomePointerRepr(..)
  , Mem(..)
  , IsPtrRepr(IsPtrRepr)
  , isPtrRepr
  , isPtrRepr'
  , pattern IsPointerRepr
  , pattern PointerRepr
  , pattern KnownPointerRepr
  , pattern PtrRepr
  ) where

import Data.Kind (Type)
import GHC.TypeLits (KnownNat, Nat, type (<=))

import Data.Parameterized.NatRepr (NatRepr, knownNat)

import Lang.Crucible.Types (BVType, CrucibleType, IntrinsicType, TypeRepr(..))

import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.Types as T
import Data.Type.Equality ((:~:) (Refl), testEquality)
import Data.Parameterized.Context (EmptyCtx)
import Data.Parameterized (KnownRepr(knownRepr))

type PosNat :: Nat -> Type
data PosNat w = 1 <= w => PosNat (NatRepr w)

_withPosNat :: PosNat w -> (1 <= w => NatRepr w -> k) -> k
_withPosNat (PosNat w) k = k w

type SomePointerRepr :: CrucibleType -> CrucibleType -> Type
data SomePointerRepr mem tp
  = forall w. (1 <= w, tp ~ PointerType mem w) => SomePointerRepr (NatRepr w)

class Mem (mem :: CrucibleType) where
  type MemData (mem :: CrucibleType) sym = (r :: Type) | r -> mem
  type PointerType (mem :: CrucibleType) (w :: Nat) = (r :: CrucibleType) | r -> mem w

  memRepr :: TypeRepr mem

  ptrRepr :: 1 <= w => NatRepr w -> TypeRepr (PointerType mem w)
  testPtrRepr :: TypeRepr tp -> Maybe (SomePointerRepr mem tp)
  ptrEqAxiom :: (PointerType mem w0 ~ PointerType mem w) => w0 :~: w
  -- | Intended for use in 'PointerRepr'
  ptrReprWidth :: TypeRepr (PointerType mem w) -> PosNat w

type IsPtrRepr :: CrucibleType -> CrucibleType -> Nat -> Type
data IsPtrRepr mem tp w
  = (1 <= w, tp ~ PointerType mem w) => IsPtrRepr

isPtrRepr ::
  forall w tp mem.
  Mem mem =>
  NatRepr w ->
  TypeRepr tp ->
  Maybe (IsPtrRepr mem tp w)
isPtrRepr w r =
  case testPtrRepr @mem r of
    Just (SomePointerRepr (testEquality w -> Just Refl)) ->
      Just IsPtrRepr
    _ -> Nothing

isPtrRepr' ::
  forall mem tp wptr.
  T.HasPtrWidth wptr =>
  Mem mem =>
  TypeRepr tp ->
  Maybe (IsPtrRepr mem tp wptr)
isPtrRepr' = isPtrRepr ?ptrWidth

-- pattern PointerRepr' :: forall mem tp. Mem mem => forall w. (1 <= w, tp ~ PointerType mem w) => NatRepr w -> Proxy mem -> TypeRepr tp
-- pattern PointerRepr' w <- (testPtrRepr @mem -> Just (SomePointerRepr w))
--   where PointerRepr' w = ptrRepr w

pattern IsPointerRepr :: forall mem tp. Mem mem => SomePointerRepr mem tp -> TypeRepr tp
pattern IsPointerRepr t <- (testPtrRepr @mem -> Just t)

-- pattern SomePointer :: Mem mem => TypeRepr tp -> SomePointerRepr mem tp
-- pattern SomePointer r <- SomePointerRepr (ptrRepr -> PosNat r)

pattern PointerRepr :: Mem mem => (1 <= w) => NatRepr w -> TypeRepr (PointerType mem w)
pattern PointerRepr w <- (ptrReprWidth -> PosNat w)
  where PointerRepr w = ptrRepr w

pattern KnownPointerRepr :: forall w mem. (KnownNat w, Mem mem) => (1 <= w) => TypeRepr (PointerType mem w)
pattern KnownPointerRepr <- (ptrReprWidth -> PosNat _)
  where KnownPointerRepr = ptrRepr (knownNat @w)

pattern PtrRepr :: forall mem wptr. (T.HasPtrWidth wptr, Mem mem) => TypeRepr (PointerType mem wptr)
pattern PtrRepr = PointerRepr T.PtrWidth

-------------------------------------------

type Fresh = IntrinsicType "fresh_llvm_memory" EmptyCtx

instance Mem Fresh where
  type MemData Fresh sym = ()
  type PointerType Fresh w = BVType w

  memRepr = knownRepr
  {-# INLINE memRepr #-}

  ptrRepr = BVRepr

  testPtrRepr =
    \case
      BVRepr w -> Just (SomePointerRepr w)
      _ -> Nothing

  ptrEqAxiom = Refl
  {-# INLINE ptrEqAxiom #-}

  ptrReprWidth (BVRepr w) = PosNat w

-------------------------------------------

instance Mem T.Mem where
  type MemData T.Mem sym = G.Mem sym
  type PointerType T.Mem w = T.LLVMPointerType w

  memRepr = T.memRepr
  {-# INLINE memRepr #-}

  ptrRepr w = T.LLVMPointerRepr w

  testPtrRepr =
    \case
      T.LLVMPointerRepr w -> Just (SomePointerRepr w)
      _ -> Nothing

  ptrEqAxiom = Refl
  {-# INLINE ptrEqAxiom #-}

  ptrReprWidth = 
    \case
      T.LLVMPointerRepr w -> PosNat w
      _ -> error "Bad LLVM pointer repr"
