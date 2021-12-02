{-
Module           : UCCrux.LLVM.Bug.UndefinedBehaviorTag
Description      : Representation of undefined behavior
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

module UCCrux.LLVM.Bug.UndefinedBehaviorTag
  ( UndefinedBehaviorTag,
    getUndefinedBehaviorTag,
    makeUndefinedBehaviorTag,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Functor.Const (Const(Const))
import           Data.Type.Equality ((:~:)(Refl))
import           Unsafe.Coerce (unsafeCoerce)

import           Data.Parameterized.Classes (OrderingF(EQF))
import           Data.Parameterized.ClassesC (testEqualityC, compareC)
import           Data.Parameterized.TraversableF (fmapF)

import           Lang.Crucible.LLVM.Errors.UndefinedBehavior (UndefinedBehavior)
{- ORMOLU_ENABLE -}

-- | A simplification of 'UndefinedBehavior' that keeps less information around.
-- Used for deduplicating reports about possible bugs/errors in programs and
-- explaining the provenance of inferred function preconditions.
newtype UndefinedBehaviorTag =
  UndefinedBehaviorTag { getUndefinedBehaviorTag :: UndefinedBehavior (Const ()) }

makeUndefinedBehaviorTag :: UndefinedBehavior e -> UndefinedBehaviorTag
makeUndefinedBehaviorTag = UndefinedBehaviorTag . fmapF (const (Const ()))

-- | This instance is a coarsening of that for 'UndefinedBehavior'. In
-- particular, there may be instances of 'UndefinedBehavior' that do not compare
-- equal, but their projections under 'makeUndefinedBehaviorTag' do compare
-- equal.
--
-- Under the hood, this uses 'unsafeCoerce', but it should be OK because the
-- type information doesn't propagate anywhere.
instance Eq UndefinedBehaviorTag where
  UndefinedBehaviorTag t1 == UndefinedBehaviorTag t2 =
    testEqualityC (\(Const ()) (Const ()) -> unsafeCoerce (Just Refl)) t1 t2

-- | See comment on 'Eq'.
--
-- Under the hood, this uses 'unsafeCoerce'.
instance Ord UndefinedBehaviorTag where
  compare (UndefinedBehaviorTag t1) (UndefinedBehaviorTag t2) =
    compareC (\(Const ()) (Const ()) -> unsafeCoerce (Just EQF)) t1 t2
