-- |
-- Module           : Lang.Crucible.LLVM.MemModel.UndefinedBehavior
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
-- The following documents were used in the writing of this module:
--  * [C++17]: http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf
--  * [C99]: http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf
--    (text: http://www.iso-9899.info/n1570.html)
------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.MemModel.UndefinedBehavior
  ( UndefinedBehavior(..)
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

-- -----------------------------------------------------------------
-- ** UndefinedBehavior

-- | See 'cite' and 'explain'.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
data UndefinedBehavior =
    PtrAddOffsetOutOfBounds
  | FreeInvalidPointer
  | MemsetInvalidRegion
  | CompareInvalidPointer
  | CompareDifferentAllocs
    -- ^ "In all other cases, the behavior is undefined"
  | PtrSubDifferentAllocs
    -- ^ "When two pointers are subtracted, both shall point to elements of the
    -- same array object"
  {-
  | MemcpyDisjoint
  | DoubleFree
  | DereferenceBadAlignment
  | ModifiedStringLiteral
  -}
  deriving (Eq, Enum, Ord, Show)

-- | Which section(s) of the C or C++ specifications are relevant to this
-- behavior?
cite :: UndefinedBehavior -> String
cite =
  \case
    PtrAddOffsetOutOfBounds -> "C99: 6.5.6 Additive operators, ¶8"
    FreeInvalidPointer      -> "C99: 7.22.3.3 The free function, ¶2"
    MemsetInvalidRegion     -> "https://en.cppreference.com/w/cpp/string/byte/memset"
    CompareInvalidPointer   -> "C99: 6.5.8 Relational operators, ¶5"
    CompareDifferentAllocs  -> "C99: 6.5.8 Relational operators, ¶5"
    PtrSubDifferentAllocs   -> "C99: 6.5.6 Additive operators, ¶9"
    {-
    MemcpyDisjoint          -> "C99: 7.24.2.1 The memcpy function"
    DoubleFree              -> "C99: 7.22.3.3 The free function"
    DereferenceBadAlignment -> "C99: 6.5.3.2 Address and indirection operators"
    ModifiedStringLiteral   -> "C99: J.2 Undefined behavior"
    -}


explain :: UndefinedBehavior -> String
explain =
  \case
    PtrAddOffsetOutOfBounds -> unwords $
      [ "Addition of an offset to a pointer resulted in a pointer to an"
      , "address outside of the allocation."
      ]
    FreeInvalidPointer -> unwords $
      [ "`free` called on pointer that was not previously returned by `malloc`"
      , "`calloc`, or another memory management function"
      ]
    MemsetInvalidRegion -> unwords $
      [ "Pointer passed to `memset` didn't point to a mutable allocation with"
      , "enough space."
      ]
    CompareInvalidPointer -> unwords $
      [ "Comparison of a pointer which wasn't null or a pointer to a live heap"
      , "object."
      ]
    CompareDifferentAllocs -> "Comparison of pointers from different allocations"
    PtrSubDifferentAllocs -> "Subtraction of pointers from different allocations"
    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}

pp :: UndefinedBehavior -> String
pp ub = unlines [ "Undefined behavior: ", "Reference: " ++ cite ub, explain ub ]

-- -----------------------------------------------------------------
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
