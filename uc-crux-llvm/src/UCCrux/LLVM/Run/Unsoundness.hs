{-
Module       : UCCrux.LLVM.Run.Unsoundness
Description  : Tracking sources of unsoundness; see doc/soundness.md.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

This module currently only tracks non-over-approximation, see issue #932.
-}

{-# LANGUAGE DeriveFunctor #-}

module UCCrux.LLVM.Run.Unsoundness
  ( Unsoundness (..),
    WithUnsoundness (..),
    ppUnsoundness,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName(getSkipOverrideName))
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName(getUnsoundOverrideName))
{- ORMOLU_ENABLE -}

-- | Track sources of unsoundness
data WithUnsoundness a = WithUnsoundness
  { unsoundness :: Unsoundness,
    possiblyUnsoundValue :: a
  }
  deriving (Eq, Functor, Ord, Show)

data Unsoundness = Unsoundness
  { unsoundOverridesUsed :: Set UnsoundOverrideName,
    unsoundSkipOverridesUsed :: Set SkipOverrideName
  }
  deriving (Eq, Ord, Show)

ppUnsoundness :: Unsoundness -> Doc Void
ppUnsoundness u =
  PP.nest 2 $
    PP.vcat $
      ( PP.pretty
          "The following unsound overrides (built-in functions) were used:" :
        bullets
          (map getUnsoundOverrideName (Set.toList (unsoundOverridesUsed u)))
      )
        ++ ( PP.pretty
               "Execution of the following functions was skipped:" :
             bullets
               (map getSkipOverrideName (Set.toList (unsoundSkipOverridesUsed u)))
           )
  where
    bullets = map ((PP.pretty "-" PP.<+>) . PP.pretty)

instance Semigroup Unsoundness where
  u1 <> u2 =
    Unsoundness
      { unsoundOverridesUsed =
          unsoundOverridesUsed u1 <> unsoundOverridesUsed u2,
        unsoundSkipOverridesUsed =
          unsoundSkipOverridesUsed u1 <> unsoundSkipOverridesUsed u2
      }

instance Monoid Unsoundness where
  mempty =
    Unsoundness
      { unsoundOverridesUsed = Set.empty,
        unsoundSkipOverridesUsed = Set.empty
      }
