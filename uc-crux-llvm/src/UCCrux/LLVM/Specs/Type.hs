{-
Module           : UCCrux.LLVM.Specs.Type
Description      : Collections of specifications for LLVM functions
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

* TODO(lb):
* User-provided
* Matching behavior
* Pre- and post-
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Specs.Type
  ( SpecPreconds(..),
    SpecSoundness(..),
    Spec(..),
    Specs(..),
    SomeSpecs(..),
    minimalSpec,
    minimalSpecs
  )
where

import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import           Data.Parameterized.Context (Ctx)
import qualified Data.Parameterized.Context as Ctx

import           UCCrux.LLVM.Constraints (ConstrainedShape)
import           UCCrux.LLVM.FullType.Type (FullType)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.Precondition (emptyArgPreconds)
import           UCCrux.LLVM.Postcondition.Type (Postcond)

-- TODO(lb): preconds on globals
data SpecPreconds m (args :: Ctx (FullType m))
  = SpecPreconds
      { specArgPreconds :: Ctx.Assignment (ConstrainedShape m) args }

data SpecSoundness
  = -- | For preconditions, means that the specified preconditions are more
    -- restrictive than the actual implementation. For postconditions, means
    -- that the specified postcondition encapsulates all possible effects of
    -- the implementation on the program state.
    Overapprox
    -- | For preconditions, means that the specified preconditions are less
    -- restrictive than the actual implementation. For postconditions, means
    -- that the specified postcondition encapsulates some definitely possible
    -- effects of the implementation on the program state.
  | Underapprox
  -- | Both over-approximate and under-approximate
  | Precise
  -- | Neither over-approximate nor under-approximate
  | Imprecise
  deriving (Bounded, Enum, Eq, Ord, Show)

-- TODO(lb): docs
data Spec m fs
  = forall va ret args. (fs ~ 'FS.FuncSig va ret args) =>
    Spec
      { specPre :: SpecPreconds m args
      , specPreSound :: SpecSoundness
      , specPost :: Maybe (Postcond m fs)
      , specPostSound :: SpecSoundness
      }

-- TODO(lb): docs
newtype Specs m fs
  = Specs { getSpecs :: NonEmpty (Spec m fs) }

-- | This is a bit inefficient, could avoid duplicating all the 'FuncSigRepr's
-- with one of the strategies outlined in
-- https://github.com/GaloisInc/crucible/issues/982.
data SomeSpecs m = forall fs. SomeSpecs (FS.FuncSigRepr m fs) (Specs m fs)

-- | The minimal spec - one with no preconditions which produces a fresh,
-- minimal, symbolic return value.
minimalSpec :: FS.FuncSigRepr m fs -> Spec m fs
minimalSpec (FS.FuncSigRepr _ args _) =
  Spec
    { specPre = SpecPreconds (emptyArgPreconds args)
    , specPreSound = Underapprox
    , specPost = Nothing
    , specPostSound = Imprecise
    }

-- | The minimal set of specs - just 'minimalSpec'.
minimalSpecs :: FS.FuncSigRepr m fs -> Specs m fs
minimalSpecs = Specs . NE.singleton . minimalSpec

-- TODO(lb): views
