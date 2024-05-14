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
  , IndeterminateLoadBehavior(..)
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
      --   * Reading from previously unwritten memory will succeed rather than
      --     throwing a 'NoSatisfyingWrite' error. The semantics of what it
      --     means to read from uninitialized memory is controlled separately
      --     by the 'indeterminateLoadBehavior' option.
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

    , indeterminateLoadBehavior :: IndeterminateLoadBehavior
      -- ^ If 'laxLoadsAndStores' is enabled, what should be the semantics of
      --   reading from uninitialized memory? See the Haddocks for
      --   'IndeterminateLoadBehavior' for an explanation of each possible
      --   semantics.
      --
      --   If 'laxLoadsAndStores' is disabled, this option has no effect.

    , noSatisfyingWriteFreshConstant :: !Bool
      -- ^ If 'True', for the 'NoSatisfyingWrite' annotation, make a fresh
      --   constant as a proof obligation, which ensures it always fails. But,
      --   because it's a variable, it won't be constant-folded away and it's
      --   relatively sure the annotation will survive. If 'False', annotate
      --   'false'.
    }


-- | What should be the semantics of reading from previously uninitialized
--   memory?
data IndeterminateLoadBehavior
  = StableSymbolic
    -- ^ After allocating memory (be it through @alloca@, @malloc@, @calloc@,
    --   or a similar function), initialize it with a fresh symbolic value of
    --   the corresponding type. As a result, reading from \"uninitialized\"
    --   memory will always succeed, as uninitialized memory will contain
    --   symbolic data if it has not yet been written to. This is \"stable\"
    --   in the sense that reading from the same section of uninitialized
    --   memory multiple times will always yield the same symbolic value.
    --
    --   This is primarily useful for SV-COMP, as these semantics closely align
    --   with SV-COMP's expectations.

  | UnstableSymbolic
    -- ^ Each read from a section of uninitialized memory will return a fresh
    --   symbolic value of the corresponding type. The operative word is
    --   \"fresh\", as each of these symbolic values will be considered
    --   distinct. That is, the symbolic values are \"unstable\". Contrast this
    --   with 'StableSymbolic', in which multiple reads from the same section
    --   of uninitialized memory will all yield the same symbolic value.
    --
    --   One consequence of the 'UnstableSymbolic' approach is that any
    --   pointer can be derefenced, even if it does not actually point to
    --   anything. Dereferencing such a pointer will simply yield a fresh
    --   symbolic value. On the other hand, dereferencing such a pointer
    --   continues to be a Crucible error in 'StableSymbolic'.
  deriving (Eq, Show)

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
    -- The choice of StableSymbolic here doesn't matter too much, since it
    -- won't have any effect when laxLoadsAndStores is disabled.
  , indeterminateLoadBehavior = StableSymbolic
  , noSatisfyingWriteFreshConstant = True
  }


-- | Like 'defaultMemOptions', but allow pointer ordering comparisons
--   and equality comparisons of pointers to constant data.
laxPointerMemOptions :: MemOptions
laxPointerMemOptions =
  defaultMemOptions
  { laxPointerOrdering = True
  , laxConstantEquality = True
  }
