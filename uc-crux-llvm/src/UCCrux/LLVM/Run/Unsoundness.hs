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
import           Data.Maybe (mapMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           UCCrux.LLVM.Newtypes.FunctionName (functionNameToString)
import           UCCrux.LLVM.Overrides.Skip (SkipOverrideName(getSkipOverrideName))
import           UCCrux.LLVM.Overrides.Spec (SpecUse)
import qualified UCCrux.LLVM.Overrides.Spec as OvSpec
import           UCCrux.LLVM.Overrides.Unsound (UnsoundOverrideName(getUnsoundOverrideName))
import           UCCrux.LLVM.Soundness (Soundness)
import qualified UCCrux.LLVM.Soundness as Sound
{- ORMOLU_ENABLE -}

-- | Track sources of unsoundness
data WithUnsoundness a = WithUnsoundness
  { unsoundness :: Unsoundness,
    possiblyUnsoundValue :: a
  }
  deriving (Eq, Functor, Ord, Show)

data Unsoundness = Unsoundness
  { unsoundOverridesUsed :: Set UnsoundOverrideName,
    unsoundSkipOverridesUsed :: Set SkipOverrideName,
    unsoundSpecsUsed :: Set SpecUse
  }
  deriving (Eq, Ord, Show)

ppUnsoundness ::
  -- | What kind of unsoundness do you care about? For instance, if this is
  -- 'Soundness.Overapprox', this function will print only things that are
  -- unsound for verification.
  Soundness ->
  Unsoundness ->
  Doc Void
ppUnsoundness s u =
  PP.nest 2 $
    PP.vcat $
      concat
        [ PP.pretty
            "The following unsound overrides (built-in functions) were used:" :
              bullets
                (map getUnsoundOverrideName (Set.toList (unsoundOverridesUsed u)))
        , PP.pretty
            "Execution of the following functions was skipped:" :
              bullets
                (map getSkipOverrideName (Set.toList (unsoundSkipOverridesUsed u)))
        , PP.pretty
            "The following unsound specifications were applied:" :
              bullets specs
        ]
  where
    bullets l =
      if null l
      then [PP.pretty "[None]"]
      else map ((PP.pretty "-" PP.<+>) . PP.pretty) l
    specs =
      mapMaybe
        (\(OvSpec.SpecUse nm s') ->
           if Sound.atLeastAsSound s' s
           then Nothing
           else Just (Text.pack (functionNameToString nm)
                        <> Text.pack ": "
                        <> Text.pack (Sound.soundnessToString s')))
        (Set.toList (unsoundSpecsUsed u))

instance Semigroup Unsoundness where
  u1 <> u2 =
    Unsoundness
      { unsoundOverridesUsed =
          unsoundOverridesUsed u1 <> unsoundOverridesUsed u2,
        unsoundSkipOverridesUsed =
          unsoundSkipOverridesUsed u1 <> unsoundSkipOverridesUsed u2,
        unsoundSpecsUsed = unsoundSpecsUsed u1 <> unsoundSpecsUsed u2
      }

instance Monoid Unsoundness where
  mempty =
    Unsoundness
      { unsoundOverridesUsed = Set.empty,
        unsoundSkipOverridesUsed = Set.empty,
        unsoundSpecsUsed = Set.empty
      }
