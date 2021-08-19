------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Options
-- Description      : Definition of options that can be tweaked in the memory model
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module Lang.Crucible.LLVM.MemModel.Options
  ( MemOptions(..)
  , defaultMemOptions
  , laxPointerMemOptions
  ) where

-- | This datatype encodes a variety of tweakable settings supported
--   by the LLVM memory model.  They generally involve some weakening
--   of the strict rules of the language standard to allow common
--   idioms, at the cost that reasoning using the resulting memory model
--   is less generalizable (i.e., makes more assumptions about the
--   runtime behavior of the system).
data MemOptions
  = MemOptions
    { laxPointerOrdering :: !Bool
      -- ^ Should we allow ordering comparisons on pointers that are
      --   not from the same allocation unit?  This is not allowed
      --   by the C standard, but is nonetheless commonly done.

    , laxConstantEquality :: !Bool
      -- ^ Should we allow equality comparisons on pointers to constant
      --   data? Different symbols with the same data are allowed to
      --   be consolidated, so pointer apparently-distinct pointers
      --   will sometimes compare equal if the compiler decides to
      --   consolidate their storage.

    , laxLoadsAndStores :: !Bool
      -- ^ Should we relax some of Crucible's validity checks for memory loads
      --   and stores? If 'True', the following checks will be relaxed:
      --
      --   * If reading from previously unwritten memory, rather than throw a
      --     'NoSatisfyingWrite' error, the read will return an arbitrary,
      --     fixed value of the appropriate type.
      --
      --   * If reading from a region that isn't allocated or isn't large
      --     enough, Crucible will proceed rather than throw an
      --     'UnreadableRegion' error.
      --
      --   * Reading a value from a pointer with insufficent alignment is not
      --     treated as undefined behavior. That is, Crucible will not throw a
      --     'ReadBadAlignment' error.
      --
      --   * Adding an offset to a pointer that results in a pointer to an
      --     address outside of the allocation is not treated as undefined
      --     behavior. That is, Crucible will not throw a
      --     'PtrAddOffsetOutOfBounds' error.
      --
      --   This option is primarily useful for SV-COMP, which does not treat
      --   the scenarios listed above as fatal errors.
    }


-- | The default memory model options:
--
-- * Require strict adherence to the language standard regarding pointer
--   equality and ordering.
--
-- * Perform Crucible's default validity checks for memory loads and stores.
defaultMemOptions :: MemOptions
defaultMemOptions =
  MemOptions
  { laxPointerOrdering = False
  , laxConstantEquality = False
  , laxLoadsAndStores = False
  }


-- | Like 'defaultMemOptions', but allow pointer ordering comparisons
--   and equality comparisons of pointers to constant data.
laxPointerMemOptions :: MemOptions
laxPointerMemOptions =
  defaultMemOptions
  { laxPointerOrdering = True
  , laxConstantEquality = True
  }
