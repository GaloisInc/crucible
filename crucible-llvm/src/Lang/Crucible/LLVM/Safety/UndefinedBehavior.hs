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
--
-- TODO: Distinguish between LLVM \"poison\" values and undefined values. The
-- latter follow control flow, wereas the former follow data flow. See the
-- module-level comment on the "Translation" module.
--------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.UndefinedBehavior
  ( Standard(..)
  , ppStd
  , stdURL

  -- ** Undefined Behavior
  , UndefinedBehavior(..)
  , cite
  , pp

  -- ** Config
  , Config
  , getConfig
  , strictConfig
  , laxConfig
  , defaultStrict
  , blacklist
  , whitelist
  ) where

import           Data.Maybe (fromMaybe)
import           Data.Functor.Contravariant (Predicate(..))

-- -----------------------------------------------------------------------
-- ** Standard

-- | The various standards that prohibit certain behaviors
data Standard =
    CStd    CStdVer    -- ^ The C language standard
  | CXXStd  CXXStdVer  -- ^ The C++ language standard
  | LLVMRef LLVMRefVer -- ^ The LLVM language reference
  deriving (Eq, Ord, Show)

-- | Versions of the C standard
data CStdVer =
    C99
  | C11
  | C18
  deriving (Eq, Enum, Ord, Show)

-- | Versions of the C++ standard
data CXXStdVer =
    CXX03
  | CXX11
  | CXX14
  | CXX17
  deriving (Eq, Enum, Ord, Show)

ppCXXStdVer :: CXXStdVer -> String
ppCXXStdVer CXX03 = "C++03"
ppCXXStdVer CXX11 = "C++11"
ppCXXStdVer CXX14 = "C++14"
ppCXXStdVer CXX17 = "C++17"

-- | Versions of the LLVM Language Reference
data LLVMRefVer =
    LLVM38
  | LLVM4
  | LLVM5
  | LLVM6
  | LLVM7
  | LLVM8
  deriving (Eq, Enum, Ord, Show)

ppLLVMRefVer :: LLVMRefVer -> String
ppLLVMRefVer LLVM38 = "3.8"
ppLLVMRefVer LLVM4  = "4"
ppLLVMRefVer LLVM5  = "5"
ppLLVMRefVer LLVM6  = "6"
ppLLVMRefVer LLVM7  = "7"
ppLLVMRefVer LLVM8  = "8"

stdURL :: Standard -> Maybe String
stdURL (CStd   C99)     = Just "http://www.iso-9899.info/n1570.html"
stdURL (CXXStd CXX17)   = Just "http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf"
stdURL (LLVMRef LLVM38) = Just "https://releases.llvm.org/3.8.0/docs/LangRef.html"
stdURL (LLVMRef LLVM4)  = Just "https://releases.llvm.org/4.0.1/docs/LangRef.html"
stdURL (LLVMRef LLVM5)  = Just "https://releases.llvm.org/5.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM6)  = Just "https://releases.llvm.org/6.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM7)  = Just "https://releases.llvm.org/7.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM8)  = Just "https://llvm.org/docs/LangRef.html"
stdURL _                = Nothing

ppStd :: Standard -> String
ppStd =
  \case
    CStd    ver -> "The C language standard, version " ++ show ver
    CXXStd  ver -> "The C++ language standard, version " ++ ppCXXStdVer ver
    LLVMRef ver -> "The LLVM language reference, version" ++ ppLLVMRefVer ver

-- -----------------------------------------------------------------------
-- ** UndefinedBehavior

-- | See 'cite' and 'explain'.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
--
-- TODO: Add the relevant information to these instructions
data UndefinedBehavior =

    -------------------------------- Memory management
    FreeInvalidPointer
  | MemsetInvalidRegion

    -------------------------------- Pointer arithmetic
  | PtrAddOffsetOutOfBounds
  | CompareInvalidPointer
  | CompareDifferentAllocs
    -- ^ "In all other cases, the behavior is undefined"
  | PtrSubDifferentAllocs
    -- ^ "When two pointers are subtracted, both shall point to elements of the
    -- same array object"
  | ComparePointerToBV
    -- ^ "One of the following shall hold: [...] one operand is a pointer and the
    -- other is a null pointer constant."

    -------------------------------- LLVM poison and undefined values
  | AddNoUnsignedWrap
  | AddNoSignedWrap
  | SubNoUnsignedWrap
  | SubNoSignedWrap
  | MulNoUnsignedWrap
  | MulNoSignedWrap
  | UDivByZero
  | SDivByZero
  | URemByZero
  | SRemByZero
  | UDivExact
  | SDivExact
  | SDivOverflow
  | SRemOverflow
  | ShlOp2Big
  | ShlNoUnsignedWrap
  | ShlNoSignedWrap
  | LshrExact
  | LshrOp2Big
  | AshrExact
  | AshrOp2Big
  | ExtractElementIndex
  | InsertElementIndex
  | GEPOutOfBounds

  {-
  | MemcpyDisjoint
  | DoubleFree
  | DereferenceBadAlignment
  | ModifiedStringLiteral
  -}
  deriving (Eq, Enum, Ord, Show)

-- | Which document prohibits this behavior?
standard :: UndefinedBehavior -> Standard
standard =
  \case
    -------------------------------- Memory management
    FreeInvalidPointer      -> CStd C99
    MemsetInvalidRegion     -> CXXStd CXX17

    -------------------------------- Pointer arithmetic
    PtrAddOffsetOutOfBounds -> CStd C99
    CompareInvalidPointer   -> CStd C99
    CompareDifferentAllocs  -> CStd C99
    PtrSubDifferentAllocs   -> CStd C99
    ComparePointerToBV      -> CStd C99

    -------------------------------- LLVM poison and undefined values
    AddNoUnsignedWrap       -> LLVMRef LLVM8
    AddNoSignedWrap         -> LLVMRef LLVM8
    SubNoUnsignedWrap       -> LLVMRef LLVM8
    SubNoSignedWrap         -> LLVMRef LLVM8
    MulNoUnsignedWrap       -> LLVMRef LLVM8
    MulNoSignedWrap         -> LLVMRef LLVM8
    UDivByZero              -> LLVMRef LLVM8
    SDivByZero              -> LLVMRef LLVM8
    URemByZero              -> LLVMRef LLVM8
    SRemByZero              -> LLVMRef LLVM8
    UDivExact               -> LLVMRef LLVM8
    SDivExact               -> LLVMRef LLVM8
    SDivOverflow            -> LLVMRef LLVM8
    SRemOverflow            -> LLVMRef LLVM8
    ShlOp2Big               -> LLVMRef LLVM8
    ShlNoUnsignedWrap       -> LLVMRef LLVM8
    ShlNoSignedWrap         -> LLVMRef LLVM8
    LshrExact               -> LLVMRef LLVM8
    LshrOp2Big              -> LLVMRef LLVM8
    AshrExact               -> LLVMRef LLVM8
    AshrOp2Big              -> LLVMRef LLVM8
    ExtractElementIndex     -> LLVMRef LLVM8
    InsertElementIndex      -> LLVMRef LLVM8
    GEPOutOfBounds          -> LLVMRef LLVM8
    {-
    MemcpyDisjoint          -> CStd C99
    DoubleFree              -> CStd C99
    DereferenceBadAlignment -> CStd C99
    ModifiedStringLiteral   -> CStd C99
    -}

-- | Which section(s) of the document prohibit this behavior?
cite :: UndefinedBehavior -> String
cite =
  \case
    -------------------------------- Memory management
    FreeInvalidPointer      -> "§7.22.3.3 The free function, ¶2"
    MemsetInvalidRegion     -> "https://en.cppreference.com/w/cpp/string/byte/memset"

    -------------------------------- Pointer arithmetic
    PtrAddOffsetOutOfBounds -> "§6.5.6 Additive operators, ¶8"
    CompareInvalidPointer   -> "§6.5.8 Relational operators, ¶5"
    CompareDifferentAllocs  -> "§6.5.8 Relational operators, ¶5"
    PtrSubDifferentAllocs   -> "§6.5.6 Additive operators, ¶9"
    ComparePointerToBV      -> "§6.5.9 Equality operators, ¶2"

    -------------------------------- LLVM poison and undefined values
    AddNoUnsignedWrap       -> "‘add’ Instruction (Semantics)"
    AddNoSignedWrap         -> "‘add’ Instruction (Semantics)"
    SubNoUnsignedWrap       -> "‘sub’ Instruction (Semantics)"
    SubNoSignedWrap         -> "‘sub’ Instruction (Semantics)"
    MulNoUnsignedWrap       -> "‘mul’ Instruction (Semantics)"
    MulNoSignedWrap         -> "‘mul’ Instruction (Semantics)"
    UDivByZero              -> "‘udiv’ Instruction (Semantics)"
    SDivByZero              -> "‘sdiv’ Instruction (Semantics)"
    URemByZero              -> "‘urem’ Instruction (Semantics)"
    SRemByZero              -> "‘srem’ Instruction (Semantics)"
    UDivExact               -> "‘udiv’ Instruction (Semantics)"
    SDivExact               -> "‘sdiv’ Instruction (Semantics)"
    SDivOverflow            -> "‘sdiv’ Instruction (Semantics)"
    SRemOverflow            -> "‘srem’ Instruction (Semantics)"
    ShlOp2Big               -> "‘shl’ Instruction (Semantics)"
    ShlNoUnsignedWrap       -> "‘shl’ Instruction (Semantics)"
    ShlNoSignedWrap         -> "‘shl’ Instruction (Semantics)"
    LshrExact               -> "‘lshr’ Instruction (Semantics)"
    LshrOp2Big              -> "‘lshr’ Instruction (Semantics)"
    AshrExact               -> "‘ashr’ Instruction (Semantics)"
    AshrOp2Big              -> "‘ashr’ Instruction (Semantics)"
    ExtractElementIndex     -> "‘extractelement’ Instruction (Semantics)"
    InsertElementIndex      -> "‘insertelement’ Instruction (Semantics)"
    GEPOutOfBounds          -> "‘getelementptr’ Instruction (Semantics)"
    {-
    MemcpyDisjoint          -> "§7.24.2.1 The memcpy function"
    DoubleFree              -> "§7.22.3.3 The free function"
    DereferenceBadAlignment -> "§6.5.3.2 Address and indirection operators"
    ModifiedStringLiteral   -> "§J.2 Undefined behavior"
    -}


-- | What happened, and why is it a problem?
explain :: UndefinedBehavior -> String
explain =
  \case
    -------------------------------- Memory management
    FreeInvalidPointer -> unwords $
      [ "`free` called on pointer that was not previously returned by `malloc`"
      , "`calloc`, or another memory management function"
      ]
    MemsetInvalidRegion -> unwords $
      [ "Pointer passed to `memset` didn't point to a mutable allocation with"
      , "enough space."
      ]

    -------------------------------- Pointer arithmetic
    PtrAddOffsetOutOfBounds -> unwords $
      [ "Addition of an offset to a pointer resulted in a pointer to an"
      , "address outside of the allocation."
      ]
    CompareInvalidPointer -> unwords $
      [ "Comparison of a pointer which wasn't null or a pointer to a live heap"
      , "object."
      ]
    CompareDifferentAllocs -> "Comparison of pointers from different allocations"
    PtrSubDifferentAllocs  -> "Subtraction of pointers from different allocations"
    ComparePointerToBV     ->
      "Comparison of a pointer to a non zero (null) integer value"

    -------------------------------- LLVM poison and undefined values
    AddNoUnsignedWrap ->
      "Unsigned addition caused wrapping even though the `nuw` flag was set"
    AddNoSignedWrap   ->
      "Signed addition caused wrapping even though the `nsw` flag was set"
    SubNoUnsignedWrap ->
      "Unsigned subtraction caused wrapping even though the `nuw` flag was set"
    SubNoSignedWrap   ->
      "Signed subtraction caused wrapping even though the `nsw` flag was set"
    MulNoUnsignedWrap ->
      "Unsigned multiplication caused wrapping even though the `nuw` flag was set"
    MulNoSignedWrap   ->
      "Signed multiplication caused wrapping even though the `nsw` flag was set"
    UDivByZero        -> "Unsigned division by zero"
    SDivByZero        -> "Signed division by zero"
    URemByZero        -> "Unsigned division by zero via remainder"
    SRemByZero        -> "Signed division by zero via remainder"
    SDivExact         ->
      "Inexact signed division even though the `exact` flag was set"
    UDivExact         ->
      "Inexact unsigned division even though the `exact` flag was set"
    SDivOverflow      -> "Overflow during signed division"
    SRemOverflow      -> "Overflow during signed division (via signed remainder)"
    ShlOp2Big         -> unwords $
      [ "The second operand of `shl` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ShlNoUnsignedWrap ->
      "Left shift shifted out non-zero bits even though the `nuw` flag was set"
    ShlNoSignedWrap   -> unwords $
      [ "Left shift shifted out some bits that disagreed with the sign bit"
      , "even though the `nsw` flag was set"
      ]
    LshrExact         -> unwords $
      [ "Inexact `lshr` (logical right shift) result even though the `exact`"
      , "flag was set"
      ]
    LshrOp2Big        -> unwords $
      [ "The second operand of `lshr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    AshrExact         -> unwords $
      [ "Inexact `ashr` (arithmetic right shift) result even though the `exact`"
      , "flag was set"
      ]
    AshrOp2Big        -> unwords $
      [ "The second operand of `ashr` was equal to or greater than the number of"
      , "bits in the first operand"
      ]
    ExtractElementIndex -> unwords $
      [ "Attempted to extract an element from a vector at an index that was"
      , "greater than the length of the vector"
      ]
    InsertElementIndex  -> unwords $
      [ "Attempted to insert an element into a vector at an index that was"
      , "greater than the length of the vector"
      ]
    -- The following explanation is a bit unsatisfactory, because it is specific
    -- to how we treat this instruction in Crucible.
    GEPOutOfBounds -> unwords $
      [ "Calling `getelementptr` resulted in an index that was out of bounds for"
      , "the given allocation (likely due to arithmetic overflow), but Crucible"
      , "currently treats all GEP instructions as if they had the `inbounds`"
      , "flag set."
      ]
    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}

pp :: UndefinedBehavior -> String
pp ub = unlines $
  [ "Undefined behavior encountered: "
  , explain ub
  , unwords ["Reference: ", ppStd (standard ub), cite ub]
  ] ++ case stdURL (standard ub) of
         Just url -> ["Document URL: " ++ url]
         Nothing  -> []

-- -----------------------------------------------------------------------
-- ** Config

-- | 'Config' has a monoid instance which takes the piecewise logical and of its
-- arguments
type Config = Predicate UndefinedBehavior

-- | Apply a 'Config' as a predicate
getConfig :: Config -> UndefinedBehavior -> Bool
getConfig = getPredicate
{-# INLINE getConfig #-}

-- | Disallow all undefined behavior.
strictConfig :: Config
strictConfig = Predicate $ const True
{-# INLINE strictConfig #-}

-- | Allow all undefined behavior.
laxConfig :: Config
laxConfig = Predicate $ const False
{-# INLINE laxConfig #-}

-- | For use in ViewPatterns.
defaultStrict :: Maybe Config -> Config
defaultStrict = fromMaybe strictConfig

-- | Disallow undefined behavior that appears in this list.
blacklist :: [UndefinedBehavior] -> Config
blacklist lst = Predicate (\x -> not (x `elem` lst))
{-# INLINE blacklist #-}

-- | Allow undefined behavior that appears in this list.
whitelist :: [UndefinedBehavior] -> Config
whitelist lst = Predicate (`elem` lst)
{-# INLINE whitelist #-}
