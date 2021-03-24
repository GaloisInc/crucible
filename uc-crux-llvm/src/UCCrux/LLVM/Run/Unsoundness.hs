{-
Module       : UCCrux.LLVM.Run.Unsoundness
Description  : Tracking sources of unsoundness
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
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

import           UCCrux.LLVM.Overrides (UnsoundOverrideName(getUnsoundOverrideName))
{- ORMOLU_ENABLE -}

-- | Track sources of unsoundness
data WithUnsoundness a = WithUnsoundness
  { unsoundness :: Unsoundness,
    possiblyUnsoundValue :: a
  }
  deriving (Eq, Functor, Ord, Show)

data Unsoundness = Unsoundness
  { unsoundOverridesUsed :: Set UnsoundOverrideName
  }
  deriving (Eq, Ord, Show)

ppUnsoundness :: Unsoundness -> Doc Void
ppUnsoundness u =
  PP.nest 2 $
    PP.vcat $
      PP.pretty
        "The following unsound overrides (built-in functions) were used:" :
      map
        ((PP.pretty "-" PP.<+>) . PP.pretty . getUnsoundOverrideName)
        (Set.toList (unsoundOverridesUsed u))

instance Semigroup Unsoundness where
  u1 <> u2 =
    Unsoundness
      { unsoundOverridesUsed =
          unsoundOverridesUsed u1 <> unsoundOverridesUsed u2
      }

instance Monoid Unsoundness where
  mempty =
    Unsoundness
      { unsoundOverridesUsed = Set.empty
      }
