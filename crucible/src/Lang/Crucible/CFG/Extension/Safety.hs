{-|
Module           : Lang.Crucible.CFG.Extension.Safety
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Explainable, composable side conditions raised by operations in syntax
extensions. These are used internally to syntax extensions.
-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Lang.Crucible.CFG.Extension.Safety
( SafetyAssertion
, EmptySafetyAssertion
, HasSafetyAssertions(..)
) where

import           Data.Kind
import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import           Text.PrettyPrint.ANSI.Leijen (Doc)
import           What4.Partial
import           What4.Interface

-- | This is the type of "safety assertions" that will be made about operations
-- of the syntax extension. For example, for the LLVM syntax extension, this type
-- contains constructors for instances of undefined behavior.
type family SafetyAssertion (ext :: Type) = sa | sa -> ext

-- | The empty safety assertion extension, which adds no new possible assertions.
data EmptySafetyAssertion :: Type
type instance SafetyAssertion () = EmptySafetyAssertion

-- | The two key operations on safety assertions are to collapse them into symbolic
-- predicates which can be added to the proof obligations, and to explain to the
-- user why the assertion was made.
--
-- For the sake of consistency, such explanations should contain the word \"should\",
-- e.g. \"the pointer should fall in a live allocation.\"
class HasSafetyAssertions (ext :: Type) where
  toPredicate :: IsExprBuilder sym
              => sym
              -> SafetyAssertion ext
              -> Pred sym

  -- | This is in this class because a given syntax extension might have a more
  -- efficient implementation, e.g. by realizing that one part of an And
  -- encompasses another. Same goes for 'explainTree'.
  treeToPredicate :: IsExprBuilder sym
                  => sym
                  -> AssertionTree (SafetyAssertion ext)
                  -> IO (Pred sym)
  treeToPredicate sym = collapseAT sym (toPredicate sym)

  explain     :: SafetyAssertion ext -> Doc
  explainTree :: AssertionTree (SafetyAssertion ext) -> Doc

  assertSafe :: (IsExprBuilder sym, IsBoolSolver sym)
             => sym
             -> SafetyAssertion ext
             -> IO ()
  assertSafe sym assertion =
    let predicate = toPredicate sym assertion
    -- TODO: Should SimErrorReason have another constructor for this?
    in assert sym predicate (AssertFailureSimError (show (explain assertion)))
