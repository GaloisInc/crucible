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
    }


-- | The default memory model options require strict adherence to
--   the language standard regarding pointer equality and ordering.
defaultMemOptions :: MemOptions
defaultMemOptions =
  MemOptions
  { laxPointerOrdering = False
  , laxConstantEquality = False
  }


-- | The lax pointer memory options allow pointer ordering comparisons
--   and equality comparisons of pointers to constant data.
laxPointerMemOptions :: MemOptions
laxPointerMemOptions =
  MemOptions
  { laxPointerOrdering = True
  , laxConstantEquality = True
  }
