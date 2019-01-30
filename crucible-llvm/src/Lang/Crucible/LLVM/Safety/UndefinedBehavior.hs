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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.UndefinedBehavior
  (
  -- ** Undefined Behavior
    PtrComparisonOperator(..)
  , UndefinedBehavior(..)
  , cite
  , ppSym
  , ppExpr

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
import           Data.Kind (Type)
import           Data.Functor.Contravariant (Predicate(..))
import           Data.Maybe (fromMaybe)
import           Data.Text (Text, unwords, unlines, pack)
import           Data.Typeable (Typeable)

import qualified What4.Interface as W4I

import           Lang.Crucible.LLVM.DataLayout (Alignment)
import           Lang.Crucible.LLVM.MemModel.Pointer (ppPtr)
import           Lang.Crucible.LLVM.MemModel.Type (StorageTypeF(..))
import           Lang.Crucible.LLVM.Safety.Standards
import           Lang.Crucible.LLVM.Types (LLVMPtr)

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

-- | This type is parameterized on a higher-kinded term constructor so that it
-- can be instantiated for expressions at translation time (i.e. the 'Expr' in
-- 'LLVMGenerator'), or for expressions at runtime ('SymExpr').
--
-- See 'cite' and 'explain' for what each constructor means at the C/LLVM level.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
data UndefinedBehavior (e :: W4I.BaseType -> Type) where

  -------------------------------- Memory management

  FreeBadOffset :: LLVMPtr sym w
                -> UndefinedBehavior (W4I.SymExpr sym)

  FreeUnallocated :: LLVMPtr sym w
                  -> UndefinedBehavior (W4I.SymExpr sym)

  MemsetInvalidRegion :: LLVMPtr sym w   -- ^ Destination
                      -> W4I.SymBV sym 8 -- ^ Fill byte
                      -> W4I.SymBV sym v -- ^ Length
                      -> UndefinedBehavior (W4I.SymExpr sym)

  -- | Is this actually undefined? I (Langston) can't find anything about it
  ReadBadAlignment :: LLVMPtr sym w   -- ^ Read from where?
                   -> Alignment       -- ^ What alignment?
                   -> UndefinedBehavior (W4I.SymExpr sym)

  ReadUnallocated :: LLVMPtr sym w -- ^ Read from where?
                  -> UndefinedBehavior (W4I.SymExpr sym)

  -------------------------------- Pointer arithmetic

  PtrAddOffsetOutOfBounds :: LLVMPtr sym w   -- ^ The pointer
                          -> W4I.SymBV sym w -- ^ Offset added
                          -> UndefinedBehavior (W4I.SymExpr sym)

  CompareInvalidPointer :: PtrComparisonOperator -- ^ Kind of comparison
                        -> LLVMPtr sym w  -- ^ The invalid pointer
                        -> LLVMPtr sym w  -- ^ The pointer it was compared to
                        -> UndefinedBehavior (W4I.SymExpr sym)

  -- | "In all other cases, the behavior is undefined"
  -- TODO: 'PtrComparisonOperator' argument?
  CompareDifferentAllocs :: LLVMPtr sym w
                         -> LLVMPtr sym w
                         -> UndefinedBehavior (W4I.SymExpr sym)

  -- | "When two pointers are subtracted, both shall point to elements of the
  -- same array object"
  PtrSubDifferentAllocs :: LLVMPtr sym w
                        -> LLVMPtr sym w
                        -> UndefinedBehavior (W4I.SymExpr sym)

  PointerCast :: proxy sym        -- ^ (Eliminate ambiguous type error)
              -> W4I.SymNat sym   -- ^ Pointer's allocation number
              -> W4I.SymBV sym w
              -> StorageTypeF ()  -- ^ Type being cast to
              -> UndefinedBehavior (W4I.SymExpr sym)

  -- | "One of the following shall hold: [...] one operand is a pointer and the
  -- other is a null pointer constant."
  ComparePointerToBV :: e (W4I.BaseBVType w) -- ^ Pointer
                     -> e (W4I.BaseBVType w) -- ^ Bitvector
                     -> UndefinedBehavior e

  -------------------------------- LLVM: arithmetic

  -- | @SymBV@ or @Expr _ _ (BVType w)@
  UDivByZero   :: e (W4I.BaseBVType w) -> UndefinedBehavior e
  SDivByZero   :: e (W4I.BaseBVType w) -> UndefinedBehavior e
  URemByZero   :: e (W4I.BaseBVType w) -> UndefinedBehavior e
  SRemByZero   :: e (W4I.BaseBVType w) -> UndefinedBehavior e
  SDivOverflow :: e (W4I.BaseBVType w)
               -> e (W4I.BaseBVType w)
               -> UndefinedBehavior e
  SRemOverflow :: e (W4I.BaseBVType w)
               -> e (W4I.BaseBVType w)
               -> UndefinedBehavior e

  {-
  MemcpyDisjoint          :: UndefinedBehavior e
  DoubleFree              :: UndefinedBehavior e
  DereferenceBadAlignment :: UndefinedBehavior e
  ModifiedStringLiteral   :: UndefinedBehavior e
  -}
  deriving (Typeable)

-- | Which document prohibits this behavior?
standard :: UndefinedBehavior e -> Standard
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
    PointerCast _ _ _ _         -> CStd C99

    -------------------------------- LLVM: arithmetic

    UDivByZero _     -> LLVMRef LLVM8
    SDivByZero _     -> LLVMRef LLVM8
    URemByZero _     -> LLVMRef LLVM8
    SRemByZero _     -> LLVMRef LLVM8
    SDivOverflow _ _ -> LLVMRef LLVM8
    SRemOverflow _ _ -> LLVMRef LLVM8

    {-
    MemcpyDisjoint          -> CStd C99
    DoubleFree              -> CStd C99
    DereferenceBadAlignment -> CStd C99
    ModifiedStringLiteral   -> CStd C99
    -}

-- | Which section(s) of the document prohibit this behavior?
cite :: UndefinedBehavior e -> Text
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
    PointerCast _ _ _ _         -> "TODO"

    -------------------------------- LLVM: arithmetic

    UDivByZero _     -> "‘udiv’ Instruction (Semantics)"
    SDivByZero _     -> "‘sdiv’ Instruction (Semantics)"
    URemByZero _     -> "‘urem’ Instruction (Semantics)"
    SRemByZero _     -> "‘srem’ Instruction (Semantics)"
    SDivOverflow _ _ -> "‘sdiv’ Instruction (Semantics)"
    SRemOverflow _ _ -> "‘srem’ Instruction (Semantics)"

    {-
    MemcpyDisjoint          -> "§7.24.2.1 The memcpy function"
    DoubleFree              -> "§7.22.3.3 The free function"
    DereferenceBadAlignment -> "§6.5.3.2 Address and indirection operators"
    ModifiedStringLiteral   -> "§J.2 Undefined behavior"
    -}

-- | What happened, and why is it a problem?
--
-- This is a generic explanation that doesn't use the included data.
explain :: UndefinedBehavior e -> Text
explain =
  \case

    -------------------------------- Memory management

    FreeBadOffset _ -> unlines $
      [ "`free` called on pointer that was not previously returned by `malloc`"
      , "`calloc`, or another memory management function (the pointer did not"
      , "point to the base of an allocation, its offset should be 0)."
      ]
    FreeUnallocated _ -> 
      "`free` called on pointer that didn't point to a live region of the heap."
    MemsetInvalidRegion _ _ _ -> unlines $
      [ "Pointer passed to `memset` didn't point to a mutable allocation with"
      , "enough space."
      ]
    ReadBadAlignment _ _ -> 
      "Read a value from a pointer with incorrect alignment"
    ReadUnallocated _ -> 
      "Read a value from a pointer into an unallocated region"

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds _ _ -> unlines $
      [ "Addition of an offset to a pointer resulted in a pointer to an"
      , "address outside of the allocation."
      ]
    CompareInvalidPointer _ _ _ -> unlines $
      [ "Comparison of a pointer which wasn't null or a pointer to a live heap"
      , "object."
      ]
    CompareDifferentAllocs _ _ ->
      "Comparison of pointers from different allocations"
    PtrSubDifferentAllocs _ _ ->
      "Subtraction of pointers from different allocations"
    ComparePointerToBV _ _ ->
      "Comparison of a pointer to a non zero (null) integer value"
    PointerCast _ _ _ _ ->
      "Cast of a pointer to a non-integer type"

    -------------------------------- LLVM: arithmetic

    UDivByZero _     -> "Unsigned division by zero"
    SDivByZero _     -> "Signed division by zero"
    URemByZero _     -> "Unsigned division by zero via remainder"
    SRemByZero _     -> "Signed division by zero via remainder"
    SDivOverflow _ _ -> "Overflow during signed division"
    SRemOverflow _ _ -> "Overflow during signed division (via signed remainder)"

    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}

-- | Pretty-print the additional information held by the constructors
detailsExpr :: W4I.IsExpr e => UndefinedBehavior e -> [Text]
detailsExpr =
  \case
    UDivByZero v       -> [ "op1: " <++> W4I.printSymExpr v ]
    SDivByZero v       -> [ "op1: " <++> W4I.printSymExpr v ]
    URemByZero v       -> [ "op1: " <++> W4I.printSymExpr v ]
    SRemByZero v       -> [ "op1: " <++> W4I.printSymExpr v ]
    SDivOverflow v1 v2 -> [ "op1: " <++> W4I.printSymExpr v1
                          , "op2: " <++> W4I.printSymExpr v2
                          ]
    SRemOverflow v1 v2 -> [ "op1: " <++> W4I.printSymExpr v1
                          , "op2: " <++> W4I.printSymExpr v2
                          ]
    _                  -> []
  where txt <++> doc = txt <> pack (show doc)


-- | Pretty-print the additional information held by the constructors
-- (for symbolic expressions)
detailsSym :: W4I.IsExpr (W4I.SymExpr sym)
           => proxy sym
           -- ^ Not really used, prevents ambiguous types. Can use "Data.Proxy".
           -> UndefinedBehavior (W4I.SymExpr sym)
           -> [Text]
detailsSym proxySym =
  \case

    -------------------------------- Memory management

    FreeBadOffset ptr   -> [ "Pointer: " <++> ppPtr ptr ]
    FreeUnallocated ptr -> [ "Pointer: " <++> ppPtr ptr ]
    MemsetInvalidRegion destPtr fillByte len ->
      [ "Destination pointer: " <++> ppPtr destPtr
      , "Fill byte: " <++> W4I.printSymExpr fillByte
      , "Length: " <++> W4I.printSymExpr len
      ]
    ReadBadAlignment ptr align -> 
      [ "Alignment: " <++> pack (show align)
      , ppPtr1 ptr
      ]
    ReadUnallocated ptr -> [ ppPtr1 ptr ]

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds ptr offset ->
      [ ppPtr1 ptr
      , ppOffset proxySym offset
      ]
    CompareInvalidPointer comparison invalid other ->
      [ "Comparison:                     " <> ppPtrComparison comparison
      , "Invalid pointer:                " <++> ppPtr invalid
      , "Other (possibly valid) pointer: " <++> ppPtr other
      ]
    CompareDifferentAllocs ptr1 ptr2 -> [ ppPtr2 ptr1 ptr2 ]
    PtrSubDifferentAllocs ptr1 ptr2  -> [ ppPtr2 ptr1 ptr2 ]
    ComparePointerToBV ptr bv ->
      [ "Pointer:   " <++> W4I.printSymExpr ptr
      , "Bitvector: " <++> W4I.printSymExpr bv
      ]
    PointerCast _proxySym allocNum offset castToType ->
      [ "Allocation number: " <++> W4I.printSymExpr allocNum
      , "Offset:            " <++> W4I.printSymExpr offset
      , "Cast to:           " <++> castToType
      ]

    -------------------------------- LLVM: arithmetic

    -- The cases are manually listed to prevent unintentional fallthrough if a
    -- constructor is added.
    v@(UDivByZero _)     -> detailsExpr v
    v@(SDivByZero _)     -> detailsExpr v
    v@(URemByZero _)     -> detailsExpr v
    v@(SRemByZero _)     -> detailsExpr v
    v@(SDivOverflow _ _) -> detailsExpr v
    v@(SRemOverflow _ _) -> detailsExpr v

  where ppPtrText :: W4I.IsExpr (W4I.SymExpr sym) => LLVMPtr sym w -> Text
        ppPtrText = pack . show . ppPtr

        ppPtr1 :: W4I.IsExpr (W4I.SymExpr sym) => LLVMPtr sym w -> Text
        ppPtr1 = ("Pointer: " <>) . ppPtrText

        ppPtr2 ptr1 ptr2 = unlines [ "Pointer 1: " <>  ppPtrText ptr1
                                   , "Pointer 2: " <>  ppPtrText ptr2
                                   ]

        ppOffset :: W4I.IsExpr (W4I.SymExpr sym) => proxy sym -> W4I.SymBV sym w -> Text
        ppOffset _ = ("Offset: " <++>) . W4I.printSymExpr

        txt <++> doc = txt <> pack (show doc)

pp :: (UndefinedBehavior e -> [Text]) -- ^ Printer for constructor data
   -> UndefinedBehavior e
   -> Text
pp extra ub = unlines $
  "Undefined behavior encountered: "
  : explain ub
  : extra ub
  ++ unwords ["Reference: ", ppStd (standard ub), cite ub]
     : case stdURL (standard ub) of
         Just url -> ["Document URL: " <> url]
         Nothing  -> []

-- | Pretty-printer for symbolic backends
ppSym :: W4I.IsExpr (W4I.SymExpr sym)
      => proxy sym
      -- ^ Not really used, prevents ambiguous types. Can use "Data.Proxy".
      -> UndefinedBehavior (W4I.SymExpr sym)
      -> Text
ppSym proxySym = pp (detailsSym proxySym)

-- | General-purpose pretty-printer
ppExpr :: W4I.IsExpr e
       => UndefinedBehavior e
       -> Text
ppExpr = pp detailsExpr

-- -----------------------------------------------------------------------
-- ** Config

-- | 'Config' has a monoid instance which takes the piecewise logical and of its
-- arguments
type Config e = Predicate (UndefinedBehavior e)

-- | Apply a 'Config' as a predicate
getConfig :: Config e -> UndefinedBehavior e -> Bool
getConfig = getPredicate
{-# INLINE getConfig #-}

-- | Disallow all undefined behavior.
strictConfig :: Config e
strictConfig = Predicate $ const True
{-# INLINE strictConfig #-}

-- | Allow all undefined behavior.
laxConfig :: Config e
laxConfig = Predicate $ const False
{-# INLINE laxConfig #-}

-- | For use in ViewPatterns.
defaultStrict :: Maybe (Config e) -> Config e
defaultStrict = fromMaybe strictConfig
