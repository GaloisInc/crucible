{-|
Module           : Lang.Crucible.CFG.Extension.Safety
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Explainable, composable side conditions raised by operations in syntax
extensions. These are used internally to syntax extensions.
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Lang.Crucible.CFG.Extension.Safety
( SafetyAssertion
, EmptySafetyAssertion
, HasSafetyAssertions(..)
) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Kind
import Lang.Crucible.Backend
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Text.PrettyPrint.ANSI.Leijen (Doc)
import What4.Interface
import What4.Partial

-- | This is the type of "safety assertions" that will be made about operations
-- of the syntax extension. For example, for the LLVM syntax extension, this type
-- contains constructors for instances of undefined behavior.
type family SafetyAssertion (ext :: Type) sym = sa | sa -> ext sym

-- | The empty safety assertion extension, which adds no new possible assertions.
data EmptySafetyAssertion sym :: Type
type instance SafetyAssertion () sym = EmptySafetyAssertion sym

-- | The two key operations on safety assertions are to collapse them into symbolic
-- predicates which can be added to the proof obligations, and to explain to the
-- user why the assertion was made.
--
-- For the sake of consistency, such explanations should contain the word \"should\",
-- e.g. \"the pointer should fall in a live allocation.\"
class HasSafetyAssertions (ext :: Type) sym where
  -- | TODO(langston): Default implementation in terms of 'treeToPredicate'
  toPredicate :: IsExprBuilder sym
              => sym
              -> SafetyAssertion ext sym
              -> Pred sym

  -- | This is in this class because a given syntax extension might have a more
  -- efficient implementation, e.g. by realizing that one part of an And
  -- encompasses another. Same goes for 'explainTree'.
  treeToPredicate :: (MonadIO io, IsExprBuilder sym)
                  => sym
                  -> AssertionTree (SafetyAssertion ext sym)
                  -> io (Pred sym)
  treeToPredicate sym = liftIO . collapseAT sym (toPredicate sym)

  explain     :: SafetyAssertion ext sym -> Doc
  explainTree :: AssertionTree (SafetyAssertion ext sym) -> Doc

  -- | TODO(langston): Default implementation in terms of 'assertTreeSafe'
  assertSafe :: (MonadIO io, IsExprBuilder sym, IsBoolSolver sym)
             => sym
             -> SafetyAssertion ext sym
             -> io ()
  assertSafe sym assertion =
    let predicate = toPredicate sym assertion
    -- TODO: Should SimErrorReason have another constructor for this?
    in liftIO $
      assert sym predicate (AssertFailureSimError (show (explain assertion)))

  assertTreeSafe :: (MonadIO io, IsExprBuilder sym, IsBoolSolver sym)
                 => sym
                 -> AssertionTree (SafetyAssertion ext sym)
                 -> io ()
  assertTreeSafe sym tree = do
    predicate <- treeToPredicate sym tree
    liftIO $
      assert sym predicate (AssertFailureSimError (show (explainTree tree)))

  -- TODO: a method that descends into an AssertionTree, asserting e.g. the
  -- conjuncts separately and reporting on their success or failure individually,
  -- within the context of a larger assertion i.e. "The following assertion
  -- failed: _. It was part of the larger assertion _."
