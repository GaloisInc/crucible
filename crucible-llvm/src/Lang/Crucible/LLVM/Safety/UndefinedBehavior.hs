-- |
-- Module           : Lang.Crucible.LLVM.Safety.UndefinedBehavior
-- Description      : All about undefined behavior
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
-- This module is intended to be imported qualified.
--
-- This module serves as an ad-hoc reference for the sort of undefined behaviors
-- that the Crucible LLVM memory model is aware of. The information contained
-- here is used in
--  * providing helpful error messages
--  * configuring which safety checks to perform
--
-- Disabling checks for undefined behavior does not change the behavior of any
-- memory operations. If it is used to enable the simulation of undefined
-- behavior, the result is that any guarantees that Crucible provides about the
-- code essentially have an additional hypothesis: that the LLVM
-- compiler/hardware platform behave identically to Crucible's simulator when
-- encountering such behavior.
--------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.UndefinedBehavior
  (
  -- ** Undefined Behavior
    PtrComparisonOperator(..)
  , UndefinedBehavior(..)
  , cite
  , pp

  -- ** Config
  , Config
  , getConfig
  , strictConfig
  , laxConfig
  , defaultStrict
  ) where

import           Prelude hiding (unwords, unlines)

import           GHC.Generics (Generic)
import           Data.Data (Data)
import           Data.Functor.Contravariant (Predicate(..))
import           Data.Maybe (fromMaybe)
import           Data.Text (Text, unwords, unlines, pack)
import           Data.Typeable (Typeable)

import qualified What4.Interface as W4I

import           Lang.Crucible.LLVM.DataLayout (Alignment)
import           Lang.Crucible.LLVM.MemModel.Pointer (ppPtr)
import           Lang.Crucible.LLVM.MemModel.Type (StorageTypeF(..))
import           Lang.Crucible.LLVM.Types (LLVMPtr)
import           Lang.Crucible.LLVM.Safety.Standards

-- -----------------------------------------------------------------------
-- ** UndefinedBehavior

-- | The various comparison operators you can use on pointers
data PtrComparisonOperator =
    Eq
  | Leq
  deriving (Data, Eq, Generic, Enum, Ord, Read, Show)

ppPtrComparison :: PtrComparisonOperator -> Text
ppPtrComparison Eq  = "Equality comparison (==)"
ppPtrComparison Leq = "Ordering comparison (<=)"

-- | See 'cite' and 'explain'.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
data UndefinedBehavior sym where

  -------------------------------- Memory management

  FreeBadOffset :: LLVMPtr sym w
                -> UndefinedBehavior sym

  FreeUnallocated :: LLVMPtr sym w
                  -> UndefinedBehavior sym

  MemsetInvalidRegion :: LLVMPtr sym w   -- ^ Destination
                      -> W4I.SymBV sym 8 -- ^ Fill byte
                      -> W4I.SymBV sym v -- ^ Length
                      -> UndefinedBehavior sym

  -- | Is this actually undefined? I (Langston) can't find anything about it
  ReadBadAlignment :: LLVMPtr sym w   -- ^ Read from where?
                   -> Alignment       -- ^ What alignment?
                   -> UndefinedBehavior sym

  ReadUnallocated :: LLVMPtr sym w -- ^ Read from where?
                  -> UndefinedBehavior sym

  -------------------------------- Pointer arithmetic

  PtrAddOffsetOutOfBounds :: LLVMPtr sym w   -- ^ The pointer
                          -> W4I.SymBV sym w -- ^ Offset added
                          -> UndefinedBehavior sym

  CompareInvalidPointer :: PtrComparisonOperator -- ^ Kind of comparison
                        -> LLVMPtr sym w  -- ^ The invalid pointer
                        -> LLVMPtr sym w  -- ^ The pointer it was compared to
                        -> UndefinedBehavior sym

  -- | "In all other cases, the behavior is undefined"
  CompareDifferentAllocs :: LLVMPtr sym w
                         -> LLVMPtr sym w
                         -> UndefinedBehavior sym

  -- | "When two pointers are subtracted, both shall point to elements of the
  -- same array object"
  PtrSubDifferentAllocs :: LLVMPtr sym w
                        -> LLVMPtr sym w
                        -> UndefinedBehavior sym

  -- | "One of the following shall hold: [...] one operand is a pointer and the
  -- other is a null pointer constant."
  ComparePointerToBV :: LLVMPtr sym w -- ^ Pointer
                     -> LLVMPtr sym w -- ^ Bitvector
                     -> UndefinedBehavior sym

  PointerCast :: W4I.SymNat sym  -- ^ Pointer's allocation number
              -> W4I.SymBV sym w -- ^ Offset
              -> StorageTypeF () -- ^ Type being cast to
              -> UndefinedBehavior sym

  -------------------------------- LLVM: arithmetic

  UDivByZero   :: W4I.SymBV sym w -> UndefinedBehavior sym
  SDivByZero   :: W4I.SymBV sym w -> UndefinedBehavior sym
  URemByZero   :: W4I.SymBV sym w -> UndefinedBehavior sym
  SRemByZero   :: W4I.SymBV sym w -> UndefinedBehavior sym
  SDivOverflow :: W4I.SymBV sym w -> UndefinedBehavior sym
  SRemOverflow :: W4I.SymBV sym w -> UndefinedBehavior sym

  {-
  | MemcpyDisjoint
  | DoubleFree
  | DereferenceBadAlignment
  | ModifiedStringLiteral
  -}
  deriving (Typeable)

-- | Which document prohibits this behavior?
standard :: UndefinedBehavior sym -> Standard
standard =
  \case

    -------------------------------- Memory management

    FreeBadOffset _           -> CStd C99
    FreeUnallocated _         -> CStd C99
    MemsetInvalidRegion _ _ _ -> CXXStd CXX17
    ReadBadAlignment _ _      -> CStd C99
    ReadUnallocated _         -> CStd C99

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds _ _ -> CStd C99
    CompareInvalidPointer _ _ _ -> CStd C99
    CompareDifferentAllocs _ _  -> CStd C99
    PtrSubDifferentAllocs _ _   -> CStd C99
    ComparePointerToBV _ _      -> CStd C99
    PointerCast _ _ _           -> CStd C99

    -------------------------------- LLVM: arithmetic

    UDivByZero _   -> LLVMRef LLVM8
    SDivByZero _   -> LLVMRef LLVM8
    URemByZero _   -> LLVMRef LLVM8
    SRemByZero _   -> LLVMRef LLVM8
    SDivOverflow _ -> LLVMRef LLVM8
    SRemOverflow _ -> LLVMRef LLVM8

    {-
    MemcpyDisjoint          -> CStd C99
    DoubleFree              -> CStd C99
    DereferenceBadAlignment -> CStd C99
    ModifiedStringLiteral   -> CStd C99
    -}

-- | Which section(s) of the document prohibit this behavior?
cite :: UndefinedBehavior sym -> Text
cite =
  \case

    -------------------------------- Memory management

    FreeBadOffset _           -> "§7.22.3.3 The free function, ¶2"
    FreeUnallocated _         -> "§7.22.3.3 The free function, ¶2"
    MemsetInvalidRegion _ _ _ -> "https://en.cppreference.com/w/cpp/string/byte/memset"
    ReadBadAlignment _ _      -> "§6.2.8 Alignment of objects, ¶?"
    ReadUnallocated _         -> "§6.2.4 Storage durations of objects, ¶2"

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds _ _ -> "§6.5.6 Additive operators, ¶8"
    CompareInvalidPointer _ _ _ -> "§6.5.8 Relational operators, ¶5"
    CompareDifferentAllocs _ _  -> "§6.5.8 Relational operators, ¶5"
    PtrSubDifferentAllocs _ _   -> "§6.5.6 Additive operators, ¶9"
    ComparePointerToBV _ _      -> "§6.5.9 Equality operators, ¶2"
    PointerCast _ _ _           -> "TODO"

    -------------------------------- LLVM: arithmetic

    UDivByZero _   -> "‘udiv’ Instruction (Semantics)"
    SDivByZero _   -> "‘sdiv’ Instruction (Semantics)"
    URemByZero _   -> "‘urem’ Instruction (Semantics)"
    SRemByZero _   -> "‘srem’ Instruction (Semantics)"
    SDivOverflow _ -> "‘sdiv’ Instruction (Semantics)"
    SRemOverflow _ -> "‘srem’ Instruction (Semantics)"

    {-
    MemcpyDisjoint          -> "§7.24.2.1 The memcpy function"
    DoubleFree              -> "§7.22.3.3 The free function"
    DereferenceBadAlignment -> "§6.5.3.2 Address and indirection operators"
    ModifiedStringLiteral   -> "§J.2 Undefined behavior"
    -}


-- | What happened, and why is it a problem?
explain :: W4I.IsExpr (W4I.SymExpr sym) => UndefinedBehavior sym -> Text
explain =
  \case

    -------------------------------- Memory management

    FreeBadOffset ptr -> unlines $
      [ "`free` called on pointer that was not previously returned by `malloc`"
      , "`calloc`, or another memory management function (the pointer did not"
      , "point to the base of an allocation, its offset should be 0)."
      , "Pointer: " <++> ppPtr ptr
      ]
    FreeUnallocated ptr -> unlines $
      [ "`free` called on pointer that didn't point to a live region of the heap."
      , "Pointer: " <++> ppPtr ptr
      ]
    MemsetInvalidRegion destPtr fillByte len -> unlines $
      [ "Pointer passed to `memset` didn't point to a mutable allocation with"
      , "enough space."
      , "Destination pointer: " <++> ppPtr destPtr
      , "Fill byte: " <++> W4I.printSymExpr fillByte
      , "Length: " <++> W4I.printSymExpr len
      ]
    ReadBadAlignment ptr align -> unlines $
      [ "Read a value from a pointer with incorrect alignment"
      , "Alignment: " <++> pack (show align)
      , ppPtr1 ptr
      ]
    ReadUnallocated ptr -> unlines $
      [ "Read a value from a pointer into an unallocated region"
      , ppPtr1 ptr
      ]

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds ptr offset -> unlines $
      [ "Addition of an offset to a pointer resulted in a pointer to an"
      , "address outside of the allocation."
      , ppPtr1 ptr
      , ppOffset offset
      ]
    CompareInvalidPointer comparison invalid other -> unlines $
      [ "Comparison of a pointer which wasn't null or a pointer to a live heap"
      , "object."
      , "Comparison:                     " <> ppPtrComparison comparison
      , "Invalid pointer:                " <++> ppPtr invalid
      , "Other (possibly valid) pointer: " <++> ppPtr other
      ]
    CompareDifferentAllocs ptr1 ptr2 -> unlines $
      [ "Comparison of pointers from different allocations"
      , ppPtr2 ptr1 ptr2
      ]
    PtrSubDifferentAllocs ptr1 ptr2 -> unlines $
      [ "Subtraction of pointers from different allocations"
      , ppPtr2 ptr1 ptr2
      ]
    ComparePointerToBV ptr bv -> unlines $
      [ "Comparison of a pointer to a non zero (null) integer value"
      , ppPtr1 ptr
      , "Bitvector: " <++> ppPtr bv
      ]
    PointerCast allocNum offset castToType -> unlines $
      [ "Cast of a pointer to a non-integer type"
      , "Allocation number: " <++> W4I.printSymExpr allocNum
      , "Offset:            " <++> W4I.printSymExpr offset
      , "Cast to:           " <++> castToType
      ]

    -------------------------------- LLVM: arithmetic

    -- TODO: use the values
    UDivByZero _   -> "Unsigned division by zero"
    SDivByZero _   -> "Signed division by zero"
    URemByZero _   -> "Unsigned division by zero via remainder"
    SRemByZero _   -> "Signed division by zero via remainder"
    SDivOverflow _ -> "Overflow during signed division"
    SRemOverflow _ -> "Overflow during signed division (via signed remainder)"

    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}
  where ppPtrText :: forall sym w. W4I.IsExpr (W4I.SymExpr sym)
                  => LLVMPtr sym w -> Text
        ppPtrText = pack . show . ppPtr
        ppPtr1 = ("Pointer: " <>) . ppPtrText
        ppPtr2 ptr1 ptr2 = unlines [ "Pointer 1: " <>  ppPtrText ptr1
                                   , "Pointer 2: " <>  ppPtrText ptr2
                                   ]
        ppOffset = ("Offset: " <++>) . W4I.printSymExpr
        txt <++> doc = txt <> pack (show doc)

pp :: W4I.IsExpr (W4I.SymExpr sym) => UndefinedBehavior sym -> Text
pp ub = unlines $
  [ "Undefined behavior encountered: "
  , explain ub
  , unwords ["Reference: ", ppStd (standard ub), cite ub]
  ] ++ case stdURL (standard ub) of
         Just url -> ["Document URL: " <> url]
         Nothing  -> []

-- -----------------------------------------------------------------------
-- ** Config

-- | 'Config' has a monoid instance which takes the piecewise logical and of its
-- arguments
type Config sym = Predicate (UndefinedBehavior sym)

-- | Apply a 'Config' as a predicate
getConfig :: Config sym -> UndefinedBehavior sym -> Bool
getConfig = getPredicate
{-# INLINE getConfig #-}

-- | Disallow all undefined behavior.
strictConfig :: Config sym
strictConfig = Predicate $ const True
{-# INLINE strictConfig #-}

-- | Allow all undefined behavior.
laxConfig :: Config sym
laxConfig = Predicate $ const False
{-# INLINE laxConfig #-}

-- | For use in ViewPatterns.
defaultStrict :: Maybe (Config sym) -> Config sym
defaultStrict = fromMaybe strictConfig
