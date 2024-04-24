-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Match
-- Description      : Matching overrides to function names
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module Lang.Crucible.LLVM.Intrinsics.Match
  ( TemplateMatcher(..)
  , matches
  , stripDarwinAliases
  ) where

import           Control.Applicative (asum)
import qualified Data.List as List
import qualified Data.List.Extra as List (stripInfix)
import           Data.Maybe (fromMaybe)

-- | This type controls whether an override is installed for a given name found in a module.
--  See 'Lang.Crucible.LLVM.Intrinsics.filterTemplates'.
data TemplateMatcher
  = ExactMatch String
  | PrefixMatch String
  | SubstringsMatch [String]
  | DarwinAliasMatch String
    -- ^ Match a name up to some number of Darwin aliases.
    -- See @Note [Darwin aliases]@.

-- | Check whether a 'TemplateMatcher' matches a given function name.
matches ::
  -- | Function name
  String ->
  TemplateMatcher ->
  Bool
matches nm (ExactMatch x)       = x == nm
matches nm (PrefixMatch pfx)    = pfx `List.isPrefixOf` nm
matches nm (DarwinAliasMatch x) = x == stripDarwinAliases nm
matches nm (SubstringsMatch as) = filterSubstrings as nm
  where
    filterSubstrings [] _ = True
    filterSubstrings (a:as) xs =
      case restAfterSubstring a xs of
        Nothing   -> False
        Just rest -> filterSubstrings as rest

    restAfterSubstring :: String -> String -> Maybe String
    restAfterSubstring sub xs = asum [ List.stripPrefix sub tl | tl <- List.tails xs ]


-- | Remove all prefixes and suffixes that might occur in a Darwin alias for
-- a function name. See @Note [Darwin aliases]@.
stripDarwinAliases :: String -> String
stripDarwinAliases str =
  -- Remove the \01_ prefix, if it exists...
  let strNoPrefix = fromMaybe str (List.stripPrefix "\01_" str) in
  -- ...and remove any suffixes as well. Because there can be multiple suffixes
  -- in an alias, we use `stripInfix` in case one of the prefixes does not
  -- appear at the very end of the name.
  foldr (\suf s ->
          case List.stripInfix suf s of
            Just (before, after) -> before ++ after
            Nothing              -> s)
        strNoPrefix
        suffixes
  where
    suffixes :: [String]
    suffixes = [ "$UNIX2003"
               , "$INODE64"
               , "$1050"
               , "$NOCANCEL"
               , "$DARWIN_EXTSN"
               ]

{-
Note [Darwin aliases]
~~~~~~~~~~~~~~~~~~~~~
Operating systems derived from Darwin, such as macOS, define several aliases
for common libc functions for versioning purposes. These aliases are defined
using __asm, so when Clang compiles these aliases, the name that appears in the
resulting bitcode will look slightly different from what appears in the source
C file. For example, compiling the write() function with Clang on macOS will
produce LLVM bitcode with the name \01_write(), where \01 represents a leading
ASCII character with code 0x01.

Aside from the \01_ prefix, there also a number of suffixes that can be used
in alias names (see `stripDarwinAliases` for the complete list). There are
enough possible combinations that it is not wise to try and write them all out
by hand. Instead, we take the approach that when using crucible-llvm on Darwin,
we treat any C function as possibly containing Darwin aliases. That is:

* In `basic_llvm_override`, we use a special DarwinAliasMatch template matcher
  on Darwin. When matching against possible overrides, DarwinAliasMatch
  indicates that function should be match the underlying name after removing
  any possible Darwin-related prefixes or suffixes (see the
  `stripDarwinAliases` function, which implements this).
* If a function name in a program matches an override name after stripping
  Darwin aliases, then we proceed to use the override, but with the override's
  name switched out for the name of the function from the program. This way,
  we write overrides for the "normalized" name (e.g., write) but have them work
  seamlessly for aliases names (e.g., \01_write) as well.

Currently, we only apply this special treatment in `basic_llvm_override`, as
we have only observed the aliases being used on libc functions. We may need to
apply this special case to other override functions (e.g.,
`register_cpp_override`) if that proves insufficient.
-}

