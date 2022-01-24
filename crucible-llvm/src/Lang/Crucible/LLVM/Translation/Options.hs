------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Options
-- Description      : Definition of options that can be tweaked during LLVM translation
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
module Lang.Crucible.LLVM.Translation.Options
  ( TranslationOptions(..)
  , defaultTranslationOptions
  , debugIntrinsicsTranslationOptions
  ) where

-- | This datatype encodes a variety of tweakable settings that apply during
--   LLVM translation.
data TranslationOptions
  = TranslationOptions
    { debugIntrinsics :: !Bool
      -- ^ Should we translate @llvm.dbg@ intrinsic statements? The upside to
      --   translating them is that they encode debugging information about a
      --   program that can be useful for external clients. The downside is
      --   that they can bloat the size of translated programs, despite being
      --   no-ops during simulation.
    , laxArith :: !Bool
      -- ^ Should we omit proof obligations related to arithmetic overflow
      --   and similar assertions?
    , optLoopMerge :: !Bool
      -- ^ Should we insert merge blocks in loops with early exits (i.e. breaks
      --   or returns)? This may improve simulation performance.
    }

-- | The default translation options:
--
-- * Do not translate @llvm.dbg@ intrinsic statements
--
-- * Do not produce proof obligations for arithmetic-related assertions.
--
-- * Do not insert merge blocks in loops with early exits.
defaultTranslationOptions :: TranslationOptions
defaultTranslationOptions =
  TranslationOptions
  { debugIntrinsics = False
  , laxArith = False
  , optLoopMerge = False
  }

-- | Like 'defaultTranslationOptions', but @llvm.dbg@ intrinsic statements are
-- translated.
debugIntrinsicsTranslationOptions :: TranslationOptions
debugIntrinsicsTranslationOptions =
  defaultTranslationOptions
  { debugIntrinsics = True
  }
