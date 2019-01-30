{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-|
Module           : Lang.Crucible.CFG.Extension.Safety
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Explainable, composable side conditions raised by operations in syntax
extensions. These are used internally to syntax extensions.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Lang.Crucible.CFG.Extension.Safety
( SafetyAssertion
, EmptySafetyAssertion
-- , HasSafetyAssertions(..)
) where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Kind (Type)
import Data.Parameterized.Classes (EqF(..), OrdF(..), HashableF(..), ShowF(..))
import Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import Lang.Crucible.Backend
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Types (CrucibleType, BaseToType, UnitType)
import Text.PrettyPrint.ANSI.Leijen (Doc)
import What4.Interface
import What4.Partial

-- | This is the type of \"safety assertions\" that will be made about operations
-- of the syntax extension. For example, for the LLVM syntax extension, this type
-- contains constructors for instances of undefined behavior.
--
-- The parameter @e@ is frequently @'SymExpr' sym@
type family SafetyAssertion (ext :: Type) :: (BaseType -> Type) -> Type

-- | The empty safety assertion extension, which adds no new possible assertions.
data EmptySafetyAssertion :: (BaseType -> Type) -> Type
type instance SafetyAssertion () = EmptySafetyAssertion

deriving instance Show (EmptySafetyAssertion ext)

instance EqF          EmptySafetyAssertion where eqF _             = \case
instance OrdF         EmptySafetyAssertion where compareF _        = \case
instance HashableF    EmptySafetyAssertion where hashWithSaltF _   = \case
instance ShowF        EmptySafetyAssertion where showsPrecF _ _    = \case
instance FunctorF     EmptySafetyAssertion where fmapF _           = \case
instance FoldableF    EmptySafetyAssertion where foldlF _ _        = \case
instance TraversableF EmptySafetyAssertion where traverseF _       = \case
instance TestEquality EmptySafetyAssertion where testEquality _    = \case

-- newtype CrucibleSymExpr sym baseTy =
--   CrucibleSymExpr { getExpr :: SymExpr sym baseTy }

-- | The two key operations on safety assertions are to collapse them into symbolic
-- predicates which can be added to the proof obligations, and to explain to the
-- user why the assertion was made.
--
-- For the sake of consistency, such explanations should contain the word \"should\",
-- e.g. \"the pointer should fall in a live allocation.\"

class HasSafetyAssertions (ext :: Type) where
  toPredicate :: IsSymInterface sym
              => proxy ext
              -> sym
              -> SafetyAssertion ext (SymExpr sym)
              -> Pred sym

  {-
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
                  -> AssertionTree (Pred sym) (SafetyAssertion ext sym)
                  -> io (Pred sym)
  treeToPredicate sym = liftIO . collapseAT sym (toPredicate sym) id

  explain     :: SafetyAssertion ext sym -> Doc
  explainTree :: AssertionTree (Pred sym) (SafetyAssertion ext sym) -> Doc

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
                 -> AssertionTree (Pred sym) (SafetyAssertion ext sym)
                 -> io ()
  assertTreeSafe sym tree = do
    predicate <- treeToPredicate sym tree
    liftIO $
      assert sym predicate (AssertFailureSimError (show (explainTree tree)))

  -- TODO: a method that descends into an AssertionTree, asserting e.g. the
  -- conjuncts separately and reporting on their success or failure individually,
  -- within the context of a larger assertion i.e. "The following assertion
  -- failed: _. It was part of the larger assertion _."
  -}
