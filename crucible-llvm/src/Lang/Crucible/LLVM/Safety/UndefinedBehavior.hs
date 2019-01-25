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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.UndefinedBehavior
  (
  -- ** Undefined Behavior
    UndefinedBehavior(..)
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

import           Data.Functor.Contravariant (Predicate(..))
import           Data.Maybe (fromMaybe, maybeToList)
import           Data.Text (Text, unwords, unlines, pack)
import           Data.Typeable (Typeable)

import qualified What4.Interface as W4I

import           Lang.Crucible.LLVM.Safety.Standards
import           Lang.Crucible.LLVM.MemModel.Type (StorageTypeF(..))

-- -----------------------------------------------------------------------
-- ** UndefinedBehavior

-- | See 'cite' and 'explain'.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
--
-- TODO: Add the relevant information to these instructions
data UndefinedBehavior sym where
  -------------------------------- Memory management
  FreeInvalidPointer  :: W4I.SymNat sym         -- ^ Which allocation?
                      -> W4I.SymBV sym w        -- ^ What offset? (Should have been zero)
                      -> UndefinedBehavior sym
  MemsetInvalidRegion :: UndefinedBehavior sym

  -------------------------------- Pointer arithmetic
  PtrAddOffsetOutOfBounds :: UndefinedBehavior sym
  CompareInvalidPointer :: UndefinedBehavior sym
  CompareDifferentAllocs :: UndefinedBehavior sym
  -- ^ "In all other cases, the behavior is undefined"
  PtrSubDifferentAllocs :: UndefinedBehavior sym
  -- ^ "When two pointers are subtracted, both shall point to elements of the
  -- same array object"
  ComparePointerToBV :: UndefinedBehavior sym
  -- ^ "One of the following shall hold: [...] one operand is a pointer and the
  -- other is a null pointer constant."

  PointerCast :: W4I.SymNat sym  -- ^ Pointer's allocation number
              -> StorageTypeF () -- ^ Type being cast to
              -> UndefinedBehavior sym

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
    FreeInvalidPointer _ _  -> CStd C99
    MemsetInvalidRegion     -> CXXStd CXX17

    -------------------------------- Pointer arithmetic
    PtrAddOffsetOutOfBounds -> CStd C99
    CompareInvalidPointer   -> CStd C99
    CompareDifferentAllocs  -> CStd C99
    PtrSubDifferentAllocs   -> CStd C99
    ComparePointerToBV      -> CStd C99
    PointerCast _ _         -> CStd C99


    -------------------------------- LLVM poison and undefined values
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
    FreeInvalidPointer _ _  -> "§7.22.3.3 The free function, ¶2"
    MemsetInvalidRegion     -> "https://en.cppreference.com/w/cpp/string/byte/memset"

    -------------------------------- Pointer arithmetic
    PtrAddOffsetOutOfBounds -> "§6.5.6 Additive operators, ¶8"
    CompareInvalidPointer   -> "§6.5.8 Relational operators, ¶5"
    CompareDifferentAllocs  -> "§6.5.8 Relational operators, ¶5"
    PtrSubDifferentAllocs   -> "§6.5.6 Additive operators, ¶9"
    ComparePointerToBV      -> "§6.5.9 Equality operators, ¶2"
    PointerCast _ _         -> "TODO"
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
    FreeInvalidPointer _ _ -> unwords $
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
    PointerCast allocNum castToType -> unlines $
      [ "Cast of a pointer to a non-integer type"
      , "Cast to: " <> pack (show castToType)
      ] ++ maybeToList (fmap (\n -> "Allocation number: " <> pack (show n))
                             (W4I.asNat allocNum))
    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}

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
