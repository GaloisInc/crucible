{-
Module           : UCCrux.LLVM.Specs.Type
Description      : Collections of specifications for LLVM functions
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

The 'Specs' datatype represents a collection of specifications for a function.
The user can provide these specifications to the UC-Crux CLI using the
@--specs-path@ option, and they will be used to override the function's
behavior (see "UCCrux.LLVM.Overrides.Spec").

See also user-facing docs in @doc/specs.md@.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Specs.Type
  ( SpecPreconds(..),
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
import           UCCrux.LLVM.Soundness (Soundness)
import qualified UCCrux.LLVM.Soundness as Sound

-- | Preconditions required to hold for a 'Spec' to execute.
--
-- Currently only holds preconditions on arguments, but should be extended with
-- preconditions on globals at some point.
data SpecPreconds m (args :: Ctx (FullType m))
  = SpecPreconds
      { -- | Preconditions on arguments to the specified function
        specArgPreconds :: Ctx.Assignment (ConstrainedShape m) args
      }

-- | If the precondition ('specPre') holds, then the function will have the
-- effects on program state specified in the postcondition ('specPost') See
-- "UCCrux.LLVM.Specs.Apply" for how preconditions are checked against and
-- postconditions are applied to the state.
data Spec m fs
  = forall va ret args. (fs ~ 'FS.FuncSig va ret args) =>
    Spec
      { -- | See 'UCCrux.LLVM.Specs.Apply.matchPreconds' for details of the
        -- semantics.
        specPre :: SpecPreconds m args
      , specPreSound :: Soundness
      -- | A 'Nothing' causes a minimal, unconstrained, fresh, symbolic return
      -- value to be generated, see 'UCCrux.LLVM.Specs.Apply.applyPost' for
      -- details.
      , specPost :: Maybe (Postcond m fs)
      , specPostSound :: Soundness
      }

-- | A collection of specifications for a function.
--
-- The semantics are that the specs are tried in order. All specs with true
-- preconditions have their postcondition applied; they are used as branches in
-- 'Lang.Crucible.Simulator.OverrideSim.nondetBranches'.
--
-- TODO(lb): Configure whether matching is an error.
newtype Specs m fs
  = Specs { getSpecs :: NonEmpty (Spec m fs) }

-- | Package a spec together with a matching function signature.
--
-- To hold all of these in a map is bit inefficient, could avoid duplicating all
-- the 'FuncSigRepr's that appear in the @ModuleContext@ with one of the
-- strategies outlined in https://github.com/GaloisInc/crucible/issues/982.
data SomeSpecs m = forall fs. SomeSpecs (FS.FuncSigRepr m fs) (Specs m fs)

-- | The minimal spec - one with no preconditions which produces a fresh,
-- minimal, symbolic return value.
minimalSpec :: FS.FuncSigRepr m fs -> Spec m fs
minimalSpec (FS.FuncSigRepr _ args _) =
  Spec
    { specPre = SpecPreconds (emptyArgPreconds args)
    , specPreSound = Sound.Underapprox
    -- This causes the fresh, unconstrained, symbolic return value to be
    -- generated, see Spec.specPost
    , specPost = Nothing
    , specPostSound = Sound.Indefinite
    }

-- | The minimal set of specs - just a single 'minimalSpec'.
minimalSpecs :: FS.FuncSigRepr m fs -> Specs m fs
minimalSpecs = Specs . neSingleton . minimalSpec
  where
    -- | Added as NE.singleton in base-4.15/GHC 9.
    neSingleton x = x NE.:| []
