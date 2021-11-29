{-
Module           : UCCrux.LLVM.Bug.UndefinedBehaviorTag
Description      : Representation of undefined behavior
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Bug.UndefinedBehaviorTag
  ( UndefinedBehaviorTag,
    getUndefinedBehaviorTag,
    makeUndefinedBehaviorTag,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Functor.Const (Const(Const))

import           Data.Parameterized.TraversableF (fmapF)

import           Lang.Crucible.LLVM.Errors.UndefinedBehavior (UndefinedBehavior)
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
{- ORMOLU_ENABLE -}

-- | A simplification of 'UndefinedBehavior' that keeps less information around.
-- Used for deduplicating reports about possible bugs/errors in programs and
-- explaining the provenance of inferred function preconditions.
newtype UndefinedBehaviorTag =
  UndefinedBehaviorTag { getUndefinedBehaviorTag :: UndefinedBehavior (Const ()) }

makeUndefinedBehaviorTag :: UndefinedBehavior e -> UndefinedBehaviorTag
makeUndefinedBehaviorTag = UndefinedBehaviorTag . fmapF (const (Const ()))

-- | This instance is a coarsening of that for 'UndefinedBehavior'. In
-- particular, there may be instances of 'UndefinedBehavior' that do not compare
-- equal, but their projections under 'makeUndefinedBehaviorTag' do compare
-- equal.
--
-- The less coarse this becomes, the more effortful it gets to write, but also
-- the better it will be for deduplicating possible bugs/errors.
instance Eq UndefinedBehaviorTag where
  UndefinedBehaviorTag t1 == UndefinedBehaviorTag t2 =
    -- All of these cases are explicit about arguments in case e.g. some integer
    -- gets added as a field of one of these constructors, which would then
    -- optionally be considered as part of the Eq instance.
    case (t1, t2) of
      (UB.FreeBadOffset (Const ()), UB.FreeBadOffset (Const ())) -> True
      (UB.FreeUnallocated (Const ()), UB.FreeUnallocated (Const ())) -> True
      (UB.DoubleFree (Const ()), UB.DoubleFree (Const ())) -> True
      (UB.MemsetInvalidRegion (Const ()) (Const ()) (Const ()), UB.MemsetInvalidRegion (Const ()) (Const ()) (Const ())) -> True
      (UB.ReadBadAlignment (Const ()) align1, UB.ReadBadAlignment (Const ()) align2) -> align1 == align2
      (UB.WriteBadAlignment (Const ()) align1, UB.WriteBadAlignment (Const ()) align2) -> align1 == align2
      (UB.PtrAddOffsetOutOfBounds (Const ()) (Const ()), UB.PtrAddOffsetOutOfBounds (Const ()) (Const ())) -> True
      (UB.CompareInvalidPointer op1 (Const ()) (Const ()), UB.CompareInvalidPointer op2 (Const ()) (Const ())) -> op1 == op2
      (UB.CompareDifferentAllocs (Const ()) (Const ()), UB.CompareDifferentAllocs (Const ()) (Const ())) -> True
      (UB.PtrSubDifferentAllocs (Const ()) (Const ()), UB.PtrSubDifferentAllocs (Const ()) (Const ())) -> True
      (UB.PointerIntCast (Const ()) sty1, UB.PointerIntCast (Const ()) sty2) -> sty1 == sty2
      (UB.PointerUnsupportedOp (Const ()) str1, UB.PointerUnsupportedOp (Const ()) str2) -> str1 == str2
      (UB.PointerFloatCast (Const ()) sty1, UB.PointerFloatCast (Const ()) sty2) -> sty1 == sty2
      (UB.ComparePointerToBV (Const ()) (Const ()), UB.ComparePointerToBV (Const ()) (Const ())) -> True
      (UB.UDivByZero (Const ()) (Const ()), UB.UDivByZero (Const ()) (Const ())) -> True
      (UB.SDivByZero (Const ()) (Const ()), UB.SDivByZero (Const ()) (Const ())) -> True
      (UB.URemByZero (Const ()) (Const ()), UB.URemByZero (Const ()) (Const ())) -> True
      (UB.SRemByZero (Const ()) (Const ()), UB.SRemByZero (Const ()) (Const ())) -> True
      (UB.SDivOverflow (Const ()) (Const ()), UB.SDivOverflow (Const ()) (Const ())) -> True
      (UB.SRemOverflow (Const ()) (Const ()), UB.SRemOverflow (Const ()) (Const ())) -> True
      (UB.AbsIntMin (Const ()), UB.AbsIntMin (Const ())) -> True
      -- NB: We ignore what kind of poison it was.
      (UB.PoisonValueCreated _p1, UB.PoisonValueCreated _p2) -> True
      _ -> False

-- | See comment on 'Eq' instance.
instance Ord UndefinedBehaviorTag where
  -- # This instance was generated with this Python script (with a few post-hoc
  -- # manual fixes).
  --
  -- args = dict()
  -- args["UB.AbsIntMin"] = 1
  -- args["UB.CompareDifferentAllocs"] = 2
  -- args["UB.CompareInvalidPointer"] = "op (Const ()) (Const ())"
  -- args["UB.ComparePointerToBV"] = 2
  -- args["UB.DoubleFree"] = 1
  -- args["UB.FreeBadOffset"] = 1
  -- args["UB.FreeUnallocated"] = 1
  -- args["UB.MemsetInvalidRegion"] = 3
  -- args["UB.PointerFloatCast"] = "(Const ()) sty"
  -- args["UB.PointerIntCast"] = "(Const ()) sty"
  -- args["UB.PointerUnsupportedOp"] = "(Const ()) str"
  -- args["UB.PoisonValueCreated"] = "p"
  -- args["UB.PtrAddOffsetOutOfBounds"] = 2
  -- args["UB.PtrSubDifferentAllocs"] = 2
  -- args["UB.ReadBadAlignment"] = "(Const ()) align"
  -- args["UB.SDivByZero"] = 2
  -- args["UB.SDivOverflow"] = 2
  -- args["UB.SRemByZero"] = 2
  -- args["UB.SRemOverflow"] = 2
  -- args["UB.UDivByZero"] = 2
  -- args["UB.URemByZero"] = 2
  -- args["UB.WriteBadAlignment"] = "(Const ()) align"
  --
  -- ORD = [
  --     "UB.FreeBadOffset",
  --     "UB.FreeUnallocated",
  --     "UB.DoubleFree",
  --     "UB.MemsetInvalidRegion",
  --     "UB.ReadBadAlignment",
  --     "UB.WriteBadAlignment",
  --     "UB.PtrAddOffsetOutOfBounds",
  --     "UB.CompareInvalidPointer",
  --     "UB.CompareDifferentAllocs",
  --     "UB.PtrSubDifferentAllocs",
  --     "UB.PointerIntCast",
  --     "UB.PointerUnsupportedOp",
  --     "UB.PointerFloatCast",
  --     "UB.ComparePointerToBV",
  --     "UB.UDivByZero",
  --     "UB.SDivByZero",
  --     "UB.URemByZero",
  --     "UB.SRemByZero",
  --     "UB.SDivOverflow",
  --     "UB.SRemOverflow",
  --     "UB.AbsIntMin",
  --     "UB.PoisonValueCreated",
  -- ]
  --
  -- SPC = "      "
  --
  -- for (idx, constr) in enumerate(ORD):
  --     # reflexivity
  --     if type(args[constr]) == int:
  --         ars = ' '.join(['(Const ())' for _ in range(args[constr])])
  --         print(SPC + f"({constr} {ars}, {constr} {ars}) -> EQ")
  --     else:
  --         print(SPC + f"({constr} {args[constr]}1, {constr} {args[constr]}2) -> compare {args[constr]}1 {args[constr]}2")

  --     for other in ORD[idx + 1:]:
  --         print(SPC + f"({constr} {{}}, {other} {{}}) -> LT")
  --     for other in ORD[:idx]:
  --         print(SPC + f"({constr} {{}}, {other} {{}}) -> GT")

  compare (UndefinedBehaviorTag t1) (UndefinedBehaviorTag t2) =
    case (t1, t2) of
      (UB.FreeBadOffset (Const ()), UB.FreeBadOffset (Const ())) -> EQ
      (UB.FreeBadOffset {}, UB.FreeUnallocated {}) -> LT
      (UB.FreeBadOffset {}, UB.DoubleFree {}) -> LT
      (UB.FreeBadOffset {}, UB.MemsetInvalidRegion {}) -> LT
      (UB.FreeBadOffset {}, UB.ReadBadAlignment {}) -> LT
      (UB.FreeBadOffset {}, UB.WriteBadAlignment {}) -> LT
      (UB.FreeBadOffset {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.FreeBadOffset {}, UB.CompareInvalidPointer {}) -> LT
      (UB.FreeBadOffset {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.FreeBadOffset {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.FreeBadOffset {}, UB.PointerIntCast {}) -> LT
      (UB.FreeBadOffset {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.FreeBadOffset {}, UB.PointerFloatCast {}) -> LT
      (UB.FreeBadOffset {}, UB.ComparePointerToBV {}) -> LT
      (UB.FreeBadOffset {}, UB.UDivByZero {}) -> LT
      (UB.FreeBadOffset {}, UB.SDivByZero {}) -> LT
      (UB.FreeBadOffset {}, UB.URemByZero {}) -> LT
      (UB.FreeBadOffset {}, UB.SRemByZero {}) -> LT
      (UB.FreeBadOffset {}, UB.SDivOverflow {}) -> LT
      (UB.FreeBadOffset {}, UB.SRemOverflow {}) -> LT
      (UB.FreeBadOffset {}, UB.AbsIntMin {}) -> LT
      (UB.FreeBadOffset {}, UB.PoisonValueCreated {}) -> LT
      (UB.FreeUnallocated (Const ()), UB.FreeUnallocated (Const ())) -> EQ
      (UB.FreeUnallocated {}, UB.DoubleFree {}) -> LT
      (UB.FreeUnallocated {}, UB.MemsetInvalidRegion {}) -> LT
      (UB.FreeUnallocated {}, UB.ReadBadAlignment {}) -> LT
      (UB.FreeUnallocated {}, UB.WriteBadAlignment {}) -> LT
      (UB.FreeUnallocated {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.FreeUnallocated {}, UB.CompareInvalidPointer {}) -> LT
      (UB.FreeUnallocated {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.FreeUnallocated {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.FreeUnallocated {}, UB.PointerIntCast {}) -> LT
      (UB.FreeUnallocated {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.FreeUnallocated {}, UB.PointerFloatCast {}) -> LT
      (UB.FreeUnallocated {}, UB.ComparePointerToBV {}) -> LT
      (UB.FreeUnallocated {}, UB.UDivByZero {}) -> LT
      (UB.FreeUnallocated {}, UB.SDivByZero {}) -> LT
      (UB.FreeUnallocated {}, UB.URemByZero {}) -> LT
      (UB.FreeUnallocated {}, UB.SRemByZero {}) -> LT
      (UB.FreeUnallocated {}, UB.SDivOverflow {}) -> LT
      (UB.FreeUnallocated {}, UB.SRemOverflow {}) -> LT
      (UB.FreeUnallocated {}, UB.AbsIntMin {}) -> LT
      (UB.FreeUnallocated {}, UB.PoisonValueCreated {}) -> LT
      (UB.FreeUnallocated {}, UB.FreeBadOffset {}) -> GT
      (UB.DoubleFree (Const ()), UB.DoubleFree (Const ())) -> EQ
      (UB.DoubleFree {}, UB.MemsetInvalidRegion {}) -> LT
      (UB.DoubleFree {}, UB.ReadBadAlignment {}) -> LT
      (UB.DoubleFree {}, UB.WriteBadAlignment {}) -> LT
      (UB.DoubleFree {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.DoubleFree {}, UB.CompareInvalidPointer {}) -> LT
      (UB.DoubleFree {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.DoubleFree {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.DoubleFree {}, UB.PointerIntCast {}) -> LT
      (UB.DoubleFree {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.DoubleFree {}, UB.PointerFloatCast {}) -> LT
      (UB.DoubleFree {}, UB.ComparePointerToBV {}) -> LT
      (UB.DoubleFree {}, UB.UDivByZero {}) -> LT
      (UB.DoubleFree {}, UB.SDivByZero {}) -> LT
      (UB.DoubleFree {}, UB.URemByZero {}) -> LT
      (UB.DoubleFree {}, UB.SRemByZero {}) -> LT
      (UB.DoubleFree {}, UB.SDivOverflow {}) -> LT
      (UB.DoubleFree {}, UB.SRemOverflow {}) -> LT
      (UB.DoubleFree {}, UB.AbsIntMin {}) -> LT
      (UB.DoubleFree {}, UB.PoisonValueCreated {}) -> LT
      (UB.DoubleFree {}, UB.FreeBadOffset {}) -> GT
      (UB.DoubleFree {}, UB.FreeUnallocated {}) -> GT
      (UB.MemsetInvalidRegion (Const ()) (Const ()) (Const ()), UB.MemsetInvalidRegion (Const ()) (Const ()) (Const ())) -> EQ
      (UB.MemsetInvalidRegion {}, UB.ReadBadAlignment {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.WriteBadAlignment {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.CompareInvalidPointer {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PointerIntCast {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PointerFloatCast {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.ComparePointerToBV {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.UDivByZero {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.SDivByZero {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.URemByZero {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.SRemByZero {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.SDivOverflow {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.SRemOverflow {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.AbsIntMin {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.PoisonValueCreated {}) -> LT
      (UB.MemsetInvalidRegion {}, UB.FreeBadOffset {}) -> GT
      (UB.MemsetInvalidRegion {}, UB.FreeUnallocated {}) -> GT
      (UB.MemsetInvalidRegion {}, UB.DoubleFree {}) -> GT
      (UB.ReadBadAlignment (Const ()) align1, UB.ReadBadAlignment (Const ()) align2) -> compare align1 align2
      (UB.ReadBadAlignment {}, UB.WriteBadAlignment {}) -> LT
      (UB.ReadBadAlignment {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.ReadBadAlignment {}, UB.CompareInvalidPointer {}) -> LT
      (UB.ReadBadAlignment {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.ReadBadAlignment {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.ReadBadAlignment {}, UB.PointerIntCast {}) -> LT
      (UB.ReadBadAlignment {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.ReadBadAlignment {}, UB.PointerFloatCast {}) -> LT
      (UB.ReadBadAlignment {}, UB.ComparePointerToBV {}) -> LT
      (UB.ReadBadAlignment {}, UB.UDivByZero {}) -> LT
      (UB.ReadBadAlignment {}, UB.SDivByZero {}) -> LT
      (UB.ReadBadAlignment {}, UB.URemByZero {}) -> LT
      (UB.ReadBadAlignment {}, UB.SRemByZero {}) -> LT
      (UB.ReadBadAlignment {}, UB.SDivOverflow {}) -> LT
      (UB.ReadBadAlignment {}, UB.SRemOverflow {}) -> LT
      (UB.ReadBadAlignment {}, UB.AbsIntMin {}) -> LT
      (UB.ReadBadAlignment {}, UB.PoisonValueCreated {}) -> LT
      (UB.ReadBadAlignment {}, UB.FreeBadOffset {}) -> GT
      (UB.ReadBadAlignment {}, UB.FreeUnallocated {}) -> GT
      (UB.ReadBadAlignment {}, UB.DoubleFree {}) -> GT
      (UB.ReadBadAlignment {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.WriteBadAlignment (Const ()) align1, UB.WriteBadAlignment (Const ()) align2) -> compare align1 align2
      (UB.WriteBadAlignment {}, UB.PtrAddOffsetOutOfBounds {}) -> LT
      (UB.WriteBadAlignment {}, UB.CompareInvalidPointer {}) -> LT
      (UB.WriteBadAlignment {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.WriteBadAlignment {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.WriteBadAlignment {}, UB.PointerIntCast {}) -> LT
      (UB.WriteBadAlignment {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.WriteBadAlignment {}, UB.PointerFloatCast {}) -> LT
      (UB.WriteBadAlignment {}, UB.ComparePointerToBV {}) -> LT
      (UB.WriteBadAlignment {}, UB.UDivByZero {}) -> LT
      (UB.WriteBadAlignment {}, UB.SDivByZero {}) -> LT
      (UB.WriteBadAlignment {}, UB.URemByZero {}) -> LT
      (UB.WriteBadAlignment {}, UB.SRemByZero {}) -> LT
      (UB.WriteBadAlignment {}, UB.SDivOverflow {}) -> LT
      (UB.WriteBadAlignment {}, UB.SRemOverflow {}) -> LT
      (UB.WriteBadAlignment {}, UB.AbsIntMin {}) -> LT
      (UB.WriteBadAlignment {}, UB.PoisonValueCreated {}) -> LT
      (UB.WriteBadAlignment {}, UB.FreeBadOffset {}) -> GT
      (UB.WriteBadAlignment {}, UB.FreeUnallocated {}) -> GT
      (UB.WriteBadAlignment {}, UB.DoubleFree {}) -> GT
      (UB.WriteBadAlignment {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.WriteBadAlignment {}, UB.ReadBadAlignment {}) -> GT
      (UB.PtrAddOffsetOutOfBounds (Const ()) (Const ()), UB.PtrAddOffsetOutOfBounds (Const ()) (Const ())) -> EQ
      (UB.PtrAddOffsetOutOfBounds {}, UB.CompareInvalidPointer {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.PointerIntCast {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.PointerFloatCast {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.ComparePointerToBV {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.UDivByZero {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.SDivByZero {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.URemByZero {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.SRemByZero {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.SDivOverflow {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.SRemOverflow {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.AbsIntMin {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.PoisonValueCreated {}) -> LT
      (UB.PtrAddOffsetOutOfBounds {}, UB.FreeBadOffset {}) -> GT
      (UB.PtrAddOffsetOutOfBounds {}, UB.FreeUnallocated {}) -> GT
      (UB.PtrAddOffsetOutOfBounds {}, UB.DoubleFree {}) -> GT
      (UB.PtrAddOffsetOutOfBounds {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PtrAddOffsetOutOfBounds {}, UB.ReadBadAlignment {}) -> GT
      (UB.PtrAddOffsetOutOfBounds {}, UB.WriteBadAlignment {}) -> GT
      (UB.CompareInvalidPointer op1 (Const ()) (Const ()), UB.CompareInvalidPointer op2 (Const ()) (Const ())) -> compare op1 op2
      (UB.CompareInvalidPointer {}, UB.CompareDifferentAllocs {}) -> LT
      (UB.CompareInvalidPointer {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.CompareInvalidPointer {}, UB.PointerIntCast {}) -> LT
      (UB.CompareInvalidPointer {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.CompareInvalidPointer {}, UB.PointerFloatCast {}) -> LT
      (UB.CompareInvalidPointer {}, UB.ComparePointerToBV {}) -> LT
      (UB.CompareInvalidPointer {}, UB.UDivByZero {}) -> LT
      (UB.CompareInvalidPointer {}, UB.SDivByZero {}) -> LT
      (UB.CompareInvalidPointer {}, UB.URemByZero {}) -> LT
      (UB.CompareInvalidPointer {}, UB.SRemByZero {}) -> LT
      (UB.CompareInvalidPointer {}, UB.SDivOverflow {}) -> LT
      (UB.CompareInvalidPointer {}, UB.SRemOverflow {}) -> LT
      (UB.CompareInvalidPointer {}, UB.AbsIntMin {}) -> LT
      (UB.CompareInvalidPointer {}, UB.PoisonValueCreated {}) -> LT
      (UB.CompareInvalidPointer {}, UB.FreeBadOffset {}) -> GT
      (UB.CompareInvalidPointer {}, UB.FreeUnallocated {}) -> GT
      (UB.CompareInvalidPointer {}, UB.DoubleFree {}) -> GT
      (UB.CompareInvalidPointer {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.CompareInvalidPointer {}, UB.ReadBadAlignment {}) -> GT
      (UB.CompareInvalidPointer {}, UB.WriteBadAlignment {}) -> GT
      (UB.CompareInvalidPointer {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.CompareDifferentAllocs (Const ()) (Const ()), UB.CompareDifferentAllocs (Const ()) (Const ())) -> EQ
      (UB.CompareDifferentAllocs {}, UB.PtrSubDifferentAllocs {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.PointerIntCast {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.PointerFloatCast {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.ComparePointerToBV {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.UDivByZero {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.SDivByZero {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.URemByZero {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.SRemByZero {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.SDivOverflow {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.SRemOverflow {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.AbsIntMin {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.PoisonValueCreated {}) -> LT
      (UB.CompareDifferentAllocs {}, UB.FreeBadOffset {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.FreeUnallocated {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.DoubleFree {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.ReadBadAlignment {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.WriteBadAlignment {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.CompareDifferentAllocs {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PtrSubDifferentAllocs (Const ()) (Const ()), UB.PtrSubDifferentAllocs (Const ()) (Const ())) -> EQ
      (UB.PtrSubDifferentAllocs {}, UB.PointerIntCast {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.PointerFloatCast {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.ComparePointerToBV {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.UDivByZero {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.SDivByZero {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.URemByZero {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.SRemByZero {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.SDivOverflow {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.SRemOverflow {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.AbsIntMin {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.PoisonValueCreated {}) -> LT
      (UB.PtrSubDifferentAllocs {}, UB.FreeBadOffset {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.FreeUnallocated {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.DoubleFree {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.ReadBadAlignment {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.WriteBadAlignment {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PtrSubDifferentAllocs {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.PointerIntCast (Const ()) sty1, UB.PointerIntCast (Const ()) sty2) -> compare sty1 sty2
      (UB.PointerIntCast {}, UB.PointerUnsupportedOp {}) -> LT
      (UB.PointerIntCast {}, UB.PointerFloatCast {}) -> LT
      (UB.PointerIntCast {}, UB.ComparePointerToBV {}) -> LT
      (UB.PointerIntCast {}, UB.UDivByZero {}) -> LT
      (UB.PointerIntCast {}, UB.SDivByZero {}) -> LT
      (UB.PointerIntCast {}, UB.URemByZero {}) -> LT
      (UB.PointerIntCast {}, UB.SRemByZero {}) -> LT
      (UB.PointerIntCast {}, UB.SDivOverflow {}) -> LT
      (UB.PointerIntCast {}, UB.SRemOverflow {}) -> LT
      (UB.PointerIntCast {}, UB.AbsIntMin {}) -> LT
      (UB.PointerIntCast {}, UB.PoisonValueCreated {}) -> LT
      (UB.PointerIntCast {}, UB.FreeBadOffset {}) -> GT
      (UB.PointerIntCast {}, UB.FreeUnallocated {}) -> GT
      (UB.PointerIntCast {}, UB.DoubleFree {}) -> GT
      (UB.PointerIntCast {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PointerIntCast {}, UB.ReadBadAlignment {}) -> GT
      (UB.PointerIntCast {}, UB.WriteBadAlignment {}) -> GT
      (UB.PointerIntCast {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.PointerIntCast {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PointerIntCast {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.PointerIntCast {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.PointerUnsupportedOp (Const ()) str1, UB.PointerUnsupportedOp (Const ()) str2) -> compare str1 str2
      (UB.PointerUnsupportedOp {}, UB.PointerFloatCast {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.ComparePointerToBV {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.UDivByZero {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.SDivByZero {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.URemByZero {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.SRemByZero {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.SDivOverflow {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.SRemOverflow {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.AbsIntMin {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.PoisonValueCreated {}) -> LT
      (UB.PointerUnsupportedOp {}, UB.FreeBadOffset {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.FreeUnallocated {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.DoubleFree {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.ReadBadAlignment {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.WriteBadAlignment {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.PointerUnsupportedOp {}, UB.PointerIntCast {}) -> GT
      (UB.PointerFloatCast (Const ()) sty1, UB.PointerFloatCast (Const ()) sty2) -> compare sty1 sty2
      (UB.PointerFloatCast {}, UB.ComparePointerToBV {}) -> LT
      (UB.PointerFloatCast {}, UB.UDivByZero {}) -> LT
      (UB.PointerFloatCast {}, UB.SDivByZero {}) -> LT
      (UB.PointerFloatCast {}, UB.URemByZero {}) -> LT
      (UB.PointerFloatCast {}, UB.SRemByZero {}) -> LT
      (UB.PointerFloatCast {}, UB.SDivOverflow {}) -> LT
      (UB.PointerFloatCast {}, UB.SRemOverflow {}) -> LT
      (UB.PointerFloatCast {}, UB.AbsIntMin {}) -> LT
      (UB.PointerFloatCast {}, UB.PoisonValueCreated {}) -> LT
      (UB.PointerFloatCast {}, UB.FreeBadOffset {}) -> GT
      (UB.PointerFloatCast {}, UB.FreeUnallocated {}) -> GT
      (UB.PointerFloatCast {}, UB.DoubleFree {}) -> GT
      (UB.PointerFloatCast {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PointerFloatCast {}, UB.ReadBadAlignment {}) -> GT
      (UB.PointerFloatCast {}, UB.WriteBadAlignment {}) -> GT
      (UB.PointerFloatCast {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.PointerFloatCast {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PointerFloatCast {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.PointerFloatCast {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.PointerFloatCast {}, UB.PointerIntCast {}) -> GT
      (UB.PointerFloatCast {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.ComparePointerToBV (Const ()) (Const ()), UB.ComparePointerToBV (Const ()) (Const ())) -> EQ
      (UB.ComparePointerToBV {}, UB.UDivByZero {}) -> LT
      (UB.ComparePointerToBV {}, UB.SDivByZero {}) -> LT
      (UB.ComparePointerToBV {}, UB.URemByZero {}) -> LT
      (UB.ComparePointerToBV {}, UB.SRemByZero {}) -> LT
      (UB.ComparePointerToBV {}, UB.SDivOverflow {}) -> LT
      (UB.ComparePointerToBV {}, UB.SRemOverflow {}) -> LT
      (UB.ComparePointerToBV {}, UB.AbsIntMin {}) -> LT
      (UB.ComparePointerToBV {}, UB.PoisonValueCreated {}) -> LT
      (UB.ComparePointerToBV {}, UB.FreeBadOffset {}) -> GT
      (UB.ComparePointerToBV {}, UB.FreeUnallocated {}) -> GT
      (UB.ComparePointerToBV {}, UB.DoubleFree {}) -> GT
      (UB.ComparePointerToBV {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.ComparePointerToBV {}, UB.ReadBadAlignment {}) -> GT
      (UB.ComparePointerToBV {}, UB.WriteBadAlignment {}) -> GT
      (UB.ComparePointerToBV {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.ComparePointerToBV {}, UB.CompareInvalidPointer {}) -> GT
      (UB.ComparePointerToBV {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.ComparePointerToBV {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.ComparePointerToBV {}, UB.PointerIntCast {}) -> GT
      (UB.ComparePointerToBV {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.ComparePointerToBV {}, UB.PointerFloatCast {}) -> GT
      (UB.UDivByZero (Const ()) (Const ()), UB.UDivByZero (Const ()) (Const ())) -> EQ
      (UB.UDivByZero {}, UB.SDivByZero {}) -> LT
      (UB.UDivByZero {}, UB.URemByZero {}) -> LT
      (UB.UDivByZero {}, UB.SRemByZero {}) -> LT
      (UB.UDivByZero {}, UB.SDivOverflow {}) -> LT
      (UB.UDivByZero {}, UB.SRemOverflow {}) -> LT
      (UB.UDivByZero {}, UB.AbsIntMin {}) -> LT
      (UB.UDivByZero {}, UB.PoisonValueCreated {}) -> LT
      (UB.UDivByZero {}, UB.FreeBadOffset {}) -> GT
      (UB.UDivByZero {}, UB.FreeUnallocated {}) -> GT
      (UB.UDivByZero {}, UB.DoubleFree {}) -> GT
      (UB.UDivByZero {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.UDivByZero {}, UB.ReadBadAlignment {}) -> GT
      (UB.UDivByZero {}, UB.WriteBadAlignment {}) -> GT
      (UB.UDivByZero {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.UDivByZero {}, UB.CompareInvalidPointer {}) -> GT
      (UB.UDivByZero {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.UDivByZero {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.UDivByZero {}, UB.PointerIntCast {}) -> GT
      (UB.UDivByZero {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.UDivByZero {}, UB.PointerFloatCast {}) -> GT
      (UB.UDivByZero {}, UB.ComparePointerToBV {}) -> GT
      (UB.SDivByZero (Const ()) (Const ()), UB.SDivByZero (Const ()) (Const ())) -> EQ
      (UB.SDivByZero {}, UB.URemByZero {}) -> LT
      (UB.SDivByZero {}, UB.SRemByZero {}) -> LT
      (UB.SDivByZero {}, UB.SDivOverflow {}) -> LT
      (UB.SDivByZero {}, UB.SRemOverflow {}) -> LT
      (UB.SDivByZero {}, UB.AbsIntMin {}) -> LT
      (UB.SDivByZero {}, UB.PoisonValueCreated {}) -> LT
      (UB.SDivByZero {}, UB.FreeBadOffset {}) -> GT
      (UB.SDivByZero {}, UB.FreeUnallocated {}) -> GT
      (UB.SDivByZero {}, UB.DoubleFree {}) -> GT
      (UB.SDivByZero {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.SDivByZero {}, UB.ReadBadAlignment {}) -> GT
      (UB.SDivByZero {}, UB.WriteBadAlignment {}) -> GT
      (UB.SDivByZero {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.SDivByZero {}, UB.CompareInvalidPointer {}) -> GT
      (UB.SDivByZero {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.SDivByZero {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.SDivByZero {}, UB.PointerIntCast {}) -> GT
      (UB.SDivByZero {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.SDivByZero {}, UB.PointerFloatCast {}) -> GT
      (UB.SDivByZero {}, UB.ComparePointerToBV {}) -> GT
      (UB.SDivByZero {}, UB.UDivByZero {}) -> GT
      (UB.URemByZero (Const ()) (Const ()), UB.URemByZero (Const ()) (Const ())) -> EQ
      (UB.URemByZero {}, UB.SRemByZero {}) -> LT
      (UB.URemByZero {}, UB.SDivOverflow {}) -> LT
      (UB.URemByZero {}, UB.SRemOverflow {}) -> LT
      (UB.URemByZero {}, UB.AbsIntMin {}) -> LT
      (UB.URemByZero {}, UB.PoisonValueCreated {}) -> LT
      (UB.URemByZero {}, UB.FreeBadOffset {}) -> GT
      (UB.URemByZero {}, UB.FreeUnallocated {}) -> GT
      (UB.URemByZero {}, UB.DoubleFree {}) -> GT
      (UB.URemByZero {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.URemByZero {}, UB.ReadBadAlignment {}) -> GT
      (UB.URemByZero {}, UB.WriteBadAlignment {}) -> GT
      (UB.URemByZero {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.URemByZero {}, UB.CompareInvalidPointer {}) -> GT
      (UB.URemByZero {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.URemByZero {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.URemByZero {}, UB.PointerIntCast {}) -> GT
      (UB.URemByZero {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.URemByZero {}, UB.PointerFloatCast {}) -> GT
      (UB.URemByZero {}, UB.ComparePointerToBV {}) -> GT
      (UB.URemByZero {}, UB.UDivByZero {}) -> GT
      (UB.URemByZero {}, UB.SDivByZero {}) -> GT
      (UB.SRemByZero (Const ()) (Const ()), UB.SRemByZero (Const ()) (Const ())) -> EQ
      (UB.SRemByZero {}, UB.SDivOverflow {}) -> LT
      (UB.SRemByZero {}, UB.SRemOverflow {}) -> LT
      (UB.SRemByZero {}, UB.AbsIntMin {}) -> LT
      (UB.SRemByZero {}, UB.PoisonValueCreated {}) -> LT
      (UB.SRemByZero {}, UB.FreeBadOffset {}) -> GT
      (UB.SRemByZero {}, UB.FreeUnallocated {}) -> GT
      (UB.SRemByZero {}, UB.DoubleFree {}) -> GT
      (UB.SRemByZero {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.SRemByZero {}, UB.ReadBadAlignment {}) -> GT
      (UB.SRemByZero {}, UB.WriteBadAlignment {}) -> GT
      (UB.SRemByZero {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.SRemByZero {}, UB.CompareInvalidPointer {}) -> GT
      (UB.SRemByZero {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.SRemByZero {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.SRemByZero {}, UB.PointerIntCast {}) -> GT
      (UB.SRemByZero {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.SRemByZero {}, UB.PointerFloatCast {}) -> GT
      (UB.SRemByZero {}, UB.ComparePointerToBV {}) -> GT
      (UB.SRemByZero {}, UB.UDivByZero {}) -> GT
      (UB.SRemByZero {}, UB.SDivByZero {}) -> GT
      (UB.SRemByZero {}, UB.URemByZero {}) -> GT
      (UB.SDivOverflow (Const ()) (Const ()), UB.SDivOverflow (Const ()) (Const ())) -> EQ
      (UB.SDivOverflow {}, UB.SRemOverflow {}) -> LT
      (UB.SDivOverflow {}, UB.AbsIntMin {}) -> LT
      (UB.SDivOverflow {}, UB.PoisonValueCreated {}) -> LT
      (UB.SDivOverflow {}, UB.FreeBadOffset {}) -> GT
      (UB.SDivOverflow {}, UB.FreeUnallocated {}) -> GT
      (UB.SDivOverflow {}, UB.DoubleFree {}) -> GT
      (UB.SDivOverflow {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.SDivOverflow {}, UB.ReadBadAlignment {}) -> GT
      (UB.SDivOverflow {}, UB.WriteBadAlignment {}) -> GT
      (UB.SDivOverflow {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.SDivOverflow {}, UB.CompareInvalidPointer {}) -> GT
      (UB.SDivOverflow {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.SDivOverflow {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.SDivOverflow {}, UB.PointerIntCast {}) -> GT
      (UB.SDivOverflow {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.SDivOverflow {}, UB.PointerFloatCast {}) -> GT
      (UB.SDivOverflow {}, UB.ComparePointerToBV {}) -> GT
      (UB.SDivOverflow {}, UB.UDivByZero {}) -> GT
      (UB.SDivOverflow {}, UB.SDivByZero {}) -> GT
      (UB.SDivOverflow {}, UB.URemByZero {}) -> GT
      (UB.SDivOverflow {}, UB.SRemByZero {}) -> GT
      (UB.SRemOverflow (Const ()) (Const ()), UB.SRemOverflow (Const ()) (Const ())) -> EQ
      (UB.SRemOverflow {}, UB.AbsIntMin {}) -> LT
      (UB.SRemOverflow {}, UB.PoisonValueCreated {}) -> LT
      (UB.SRemOverflow {}, UB.FreeBadOffset {}) -> GT
      (UB.SRemOverflow {}, UB.FreeUnallocated {}) -> GT
      (UB.SRemOverflow {}, UB.DoubleFree {}) -> GT
      (UB.SRemOverflow {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.SRemOverflow {}, UB.ReadBadAlignment {}) -> GT
      (UB.SRemOverflow {}, UB.WriteBadAlignment {}) -> GT
      (UB.SRemOverflow {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.SRemOverflow {}, UB.CompareInvalidPointer {}) -> GT
      (UB.SRemOverflow {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.SRemOverflow {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.SRemOverflow {}, UB.PointerIntCast {}) -> GT
      (UB.SRemOverflow {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.SRemOverflow {}, UB.PointerFloatCast {}) -> GT
      (UB.SRemOverflow {}, UB.ComparePointerToBV {}) -> GT
      (UB.SRemOverflow {}, UB.UDivByZero {}) -> GT
      (UB.SRemOverflow {}, UB.SDivByZero {}) -> GT
      (UB.SRemOverflow {}, UB.URemByZero {}) -> GT
      (UB.SRemOverflow {}, UB.SRemByZero {}) -> GT
      (UB.SRemOverflow {}, UB.SDivOverflow {}) -> GT
      (UB.AbsIntMin (Const ()), UB.AbsIntMin (Const ())) -> EQ
      (UB.AbsIntMin {}, UB.PoisonValueCreated {}) -> LT
      (UB.AbsIntMin {}, UB.FreeBadOffset {}) -> GT
      (UB.AbsIntMin {}, UB.FreeUnallocated {}) -> GT
      (UB.AbsIntMin {}, UB.DoubleFree {}) -> GT
      (UB.AbsIntMin {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.AbsIntMin {}, UB.ReadBadAlignment {}) -> GT
      (UB.AbsIntMin {}, UB.WriteBadAlignment {}) -> GT
      (UB.AbsIntMin {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.AbsIntMin {}, UB.CompareInvalidPointer {}) -> GT
      (UB.AbsIntMin {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.AbsIntMin {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.AbsIntMin {}, UB.PointerIntCast {}) -> GT
      (UB.AbsIntMin {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.AbsIntMin {}, UB.PointerFloatCast {}) -> GT
      (UB.AbsIntMin {}, UB.ComparePointerToBV {}) -> GT
      (UB.AbsIntMin {}, UB.UDivByZero {}) -> GT
      (UB.AbsIntMin {}, UB.SDivByZero {}) -> GT
      (UB.AbsIntMin {}, UB.URemByZero {}) -> GT
      (UB.AbsIntMin {}, UB.SRemByZero {}) -> GT
      (UB.AbsIntMin {}, UB.SDivOverflow {}) -> GT
      (UB.AbsIntMin {}, UB.SRemOverflow {}) -> GT
      (UB.PoisonValueCreated _p1, UB.PoisonValueCreated _p2) -> EQ
      (UB.PoisonValueCreated {}, UB.FreeBadOffset {}) -> GT
      (UB.PoisonValueCreated {}, UB.FreeUnallocated {}) -> GT
      (UB.PoisonValueCreated {}, UB.DoubleFree {}) -> GT
      (UB.PoisonValueCreated {}, UB.MemsetInvalidRegion {}) -> GT
      (UB.PoisonValueCreated {}, UB.ReadBadAlignment {}) -> GT
      (UB.PoisonValueCreated {}, UB.WriteBadAlignment {}) -> GT
      (UB.PoisonValueCreated {}, UB.PtrAddOffsetOutOfBounds {}) -> GT
      (UB.PoisonValueCreated {}, UB.CompareInvalidPointer {}) -> GT
      (UB.PoisonValueCreated {}, UB.CompareDifferentAllocs {}) -> GT
      (UB.PoisonValueCreated {}, UB.PtrSubDifferentAllocs {}) -> GT
      (UB.PoisonValueCreated {}, UB.PointerIntCast {}) -> GT
      (UB.PoisonValueCreated {}, UB.PointerUnsupportedOp {}) -> GT
      (UB.PoisonValueCreated {}, UB.PointerFloatCast {}) -> GT
      (UB.PoisonValueCreated {}, UB.ComparePointerToBV {}) -> GT
      (UB.PoisonValueCreated {}, UB.UDivByZero {}) -> GT
      (UB.PoisonValueCreated {}, UB.SDivByZero {}) -> GT
      (UB.PoisonValueCreated {}, UB.URemByZero {}) -> GT
      (UB.PoisonValueCreated {}, UB.SRemByZero {}) -> GT
      (UB.PoisonValueCreated {}, UB.SDivOverflow {}) -> GT
      (UB.PoisonValueCreated {}, UB.SRemOverflow {}) -> GT
      (UB.PoisonValueCreated {}, UB.AbsIntMin {}) -> GT
