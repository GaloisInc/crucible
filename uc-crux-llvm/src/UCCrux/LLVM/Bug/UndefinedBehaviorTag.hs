{-
Module           : UCCrux.LLVM.Bug.UndefinedBehaviorTag
Description      : Representation of undefined behavior
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module UCCrux.LLVM.Bug.UndefinedBehaviorTag
  ( UndefinedBehaviorTag,
    getUndefinedBehaviorTag,
    makeUndefinedBehaviorTag,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Type.Equality (testEquality)

import           Lang.Crucible.Simulator.RegValue (RegValue'(unRV))
import           Lang.Crucible.Types (BVType, TypeRepr, baseToType)

import           Data.Parameterized.Classes (compareF)
import           Data.Parameterized.ClassesC (testEqualityC, compareC)

import           What4.Interface (IsExpr, SymExpr, exprType)

import           Lang.Crucible.LLVM.Errors.Poison (Poison(..))
import           Lang.Crucible.LLVM.Errors.UndefinedBehavior (UndefinedBehavior(..))
import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPointerType, llvmPointerType)
{- ORMOLU_ENABLE -}

-- | A simplification of 'UndefinedBehavior' that keeps less information around.
-- Used for deduplicating reports about possible bugs/errors in programs and
-- explaining the provenance of inferred function preconditions.
newtype UndefinedBehaviorTag =
  UndefinedBehaviorTag { getUndefinedBehaviorTag :: UndefinedBehavior TypeRepr }

makeUndefinedBehaviorTag ::
  IsExpr (SymExpr sym) =>
  UndefinedBehavior (RegValue' sym) ->
  UndefinedBehaviorTag
makeUndefinedBehaviorTag =
  UndefinedBehaviorTag .
    \case
      FreeBadOffset ptr ->
        FreeBadOffset (pointer ptr)
      FreeUnallocated ptr ->
        FreeUnallocated (pointer ptr)
      DoubleFree ptr ->
        DoubleFree (pointer ptr)
      MemsetInvalidRegion ptr val len ->
        MemsetInvalidRegion (pointer ptr) (bv val) (bv len)
      ReadBadAlignment ptr a ->
        ReadBadAlignment (pointer ptr) a
      WriteBadAlignment ptr a ->
        WriteBadAlignment (pointer ptr) a
      PtrAddOffsetOutOfBounds ptr off ->
        PtrAddOffsetOutOfBounds (pointer ptr) (bv off)
      CompareInvalidPointer op p1 p2 ->
        CompareInvalidPointer op (pointer p1) (pointer p2)
      CompareDifferentAllocs p1 p2 ->
        CompareDifferentAllocs (pointer p1) (pointer p2)
      PtrSubDifferentAllocs p1 p2 ->
        PtrSubDifferentAllocs (pointer p1) (pointer p2)
      PointerFloatCast ptr tp ->
        PointerFloatCast (pointer ptr) tp
      PointerIntCast ptr tp ->
        PointerIntCast (pointer ptr) tp
      PointerUnsupportedOp ptr msg ->
        PointerUnsupportedOp (pointer ptr) msg
      ComparePointerToBV ptr val ->
        ComparePointerToBV (pointer ptr) (bv val)
      UDivByZero v1 v2 ->
        UDivByZero (bv v1) (bv v2)
      SDivByZero v1 v2 ->
        SDivByZero (bv v1) (bv v2)
      URemByZero v1 v2 ->
        URemByZero (bv v1) (bv v2)
      SRemByZero v1 v2 ->
        SRemByZero (bv v1) (bv v2)
      SDivOverflow v1 v2 ->
        SDivOverflow (bv v1) (bv v2)
      SRemOverflow v1 v2 ->
        SRemOverflow (bv v1) (bv v2)
      AbsIntMin v ->
        AbsIntMin (bv v)
      PoisonValueCreated p ->
        PoisonValueCreated (poison p)
  where
    pointer ::
      IsExpr (SymExpr sym) =>
      RegValue' sym (LLVMPointerType w) ->
      TypeRepr (LLVMPointerType w)
    pointer = llvmPointerType . unRV

    bv ::
      IsExpr (SymExpr sym) =>
      RegValue' sym (BVType w) ->
      TypeRepr (BVType w)
    bv = baseToType . exprType . unRV

    poison ::
      IsExpr (SymExpr sym) =>
      Poison (RegValue' sym) ->
      Poison TypeRepr
    poison =
      \case
        AddNoUnsignedWrap v1 v2 ->
          AddNoUnsignedWrap (bv v1) (bv v2)
        AddNoSignedWrap v1 v2 ->
          AddNoSignedWrap (bv v1) (bv v2)
        SubNoUnsignedWrap v1 v2 ->
          SubNoUnsignedWrap (bv v1) (bv v2)
        SubNoSignedWrap v1 v2 ->
          SubNoSignedWrap (bv v1) (bv v2)
        MulNoUnsignedWrap v1 v2 ->
          MulNoUnsignedWrap(bv v1) (bv v2)
        MulNoSignedWrap v1 v2 ->
          MulNoSignedWrap (bv v1) (bv v2)
        UDivExact v1 v2 ->
          UDivExact (bv v1) (bv v2)
        SDivExact v1 v2 ->
          SDivExact (bv v1) (bv v2)
        ShlOp2Big v1 v2 ->
          ShlOp2Big (bv v1) (bv v2)
        ShlNoUnsignedWrap v1 v2 ->
          ShlNoUnsignedWrap (bv v1) (bv v2)
        ShlNoSignedWrap v1 v2 ->
          ShlNoSignedWrap (bv v1) (bv v2)
        LshrExact v1 v2 ->
          LshrExact (bv v1) (bv v2)
        LshrOp2Big v1 v2 ->
          LshrOp2Big (bv v1) (bv v2)
        AshrExact v1 v2 ->
          AshrExact (bv v1) (bv v2)
        AshrOp2Big v1 v2 ->
          AshrOp2Big (bv v1) (bv v2)
        ExtractElementIndex v ->
          ExtractElementIndex (bv v)
        InsertElementIndex v ->
          InsertElementIndex (bv v)
        GEPOutOfBounds p v ->
          GEPOutOfBounds (pointer p) (bv v)
        LLVMAbsIntMin v ->
          LLVMAbsIntMin (bv v)

-- | This instance is a coarsening of that for 'UndefinedBehavior'. In
-- particular, there may be instances of 'UndefinedBehavior' that do not compare
-- equal, but their projections under 'makeUndefinedBehaviorTag' do compare
-- equal.
instance Eq UndefinedBehaviorTag where
  UndefinedBehaviorTag t1 == UndefinedBehaviorTag t2 =
    testEqualityC testEquality t1 t2

-- | See comment on 'Eq'.
--
-- Under the hood, this uses 'unsafeCoerce'.
instance Ord UndefinedBehaviorTag where
  compare (UndefinedBehaviorTag t1) (UndefinedBehaviorTag t2) =
    compareC compareF t1 t2
