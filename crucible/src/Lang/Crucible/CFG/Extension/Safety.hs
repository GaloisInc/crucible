{-|
Module           : Lang.Crucible.CFG.Extension.Safety
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Explainable, composable side conditions raised by operations in syntax
extensions. These are used internally to syntax extensions.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Lang.Crucible.CFG.Extension.Safety
( SafetyAssertion
, EmptySafetyAssertion
, HasSafetyAssertions(..)
, assertSafe
, traverseSafetyAssertion
) where

import           Prelude hiding (pred)

import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Foldable (toList)
import           Data.Functor.Compose (Compose(..))
import           Data.Kind (Type)
import           Data.Type.Equality (TestEquality(..))
import           Text.PrettyPrint.ANSI.Leijen (Doc)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes (EqF(..), OrdF(..), HashableF(..), ShowF(..))
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))

import           Lang.Crucible.Backend (assert, IsSymInterface)
import           Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import           Lang.Crucible.Types (CrucibleType, BaseToType)

import           What4.BaseTypes (BaseType)
import           What4.Interface (SymExpr, IsExpr, IsExprBuilder, Pred, printSymExpr)
import           What4.Partial (AssertionTree(..))
import qualified What4.Partial as W4P

-- -----------------------------------------------------------------------
-- ** Safety assertions

-- | This is the type of \"safety assertions\" that will be made about operations
-- of the syntax extension. For example, for the LLVM syntax extension, this type
-- contains constructors for instances of undefined behavior.
--
-- The parameter after @ext@ is frequently @'SymExpr' sym@
type family SafetyAssertion (ext :: Type) :: (BaseType -> Type) -> Type

-- | The two key operations on safety assertions are to collapse them into symbolic
-- predicates which can be added to the proof obligations, and to explain to the
-- user why the assertion was made.
--
-- For the sake of consistency, such explanations should contain the word \"should\",
-- e.g. \"the pointer should fall in a live allocation.\"
class HasSafetyAssertions (ext :: Type) where
  toPredicate :: (IsExprBuilder sym, IsSymInterface sym)
              => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> sym
              -> SafetyAssertion ext (SymExpr sym)
              -> Pred sym

  -- | This is in this class because a given syntax extension might have a more
  -- efficient implementation, e.g. by realizing that one part of an 'And'
  -- encompasses another. Same goes for 'explainTree'.
  treeToPredicate :: (MonadIO io, IsExprBuilder sym, IsSymInterface sym)
                  => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
                  -> sym
                  -> AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))
                  -> io (Pred sym)
  treeToPredicate proxyExt sym =
    liftIO . W4P.collapseAT sym (toPredicate proxyExt sym) id

  -- | Explain an assertion, including any relevant data.
  explain     :: (IsExprBuilder sym, IsExpr (SymExpr sym))
              => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> SafetyAssertion ext (SymExpr sym)
              -> Doc

  explainTree :: (IsExprBuilder sym, IsExpr (SymExpr sym))
              => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))
              -> Doc
  explainTree proxyExt proxySym =
    W4P.cataAT
      (explain proxyExt proxySym)
      (\factors ->
         "All of "
         <$$> indent 2 (vcat (toList factors)))
      (\summands ->
         "Any of "
         <$$> indent 2 (vcat (toList summands)))
      (\cond doc1 doc2 ->
         "If " <+> printSymExpr cond <$$>
          vcat [ "then " <$$> indent 2 doc1
               , "else " <$$> indent 2 doc2
               ])

-- | Take a partial value and assert its safety
assertSafe :: ( MonadIO io
              , IsSymInterface sym
              , HasSafetyAssertions ext
              )
           => proxy ext
           -> sym
           -> W4P.PartExpr (AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))) a
           -> io (Maybe a)
assertSafe _proxyExt _sym W4P.Unassigned = pure Nothing
assertSafe proxyExt sym (W4P.PE tree a) = do
  pred <- treeToPredicate proxyExt sym tree
  -- TODO: Should SimErrorReason have another constructor for this?
  liftIO $ assert sym pred $ AssertFailureSimError $
    show $ explainTree proxyExt (Just sym) tree
  pure (Just a)

-- TODO: a method that descends into an AssertionTree, asserting e.g. the
-- conjuncts separately and reporting on their success or failure individually,
-- within the context of a larger assertion i.e. "The following assertion
-- failed: _. It was part of the larger assertion _."

-- -----------------------------------------------------------------------
-- ** Utilities

-- | Change the underlying type family of kind @CrucibleType -> Type@
--
-- This is used e.g. to trnasform the translation-time
-- @'SafetyAssertion' ext (Compose (Expr ext s) 'BaseToType')@
-- into the run-time
-- @'SafetyAssertion' ext ('SymExpr' sym)@
traverseSafetyAssertion :: forall ext f g proxy m.
     (TraversableF (SafetyAssertion ext), Applicative m)
  => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
  -> (forall (u :: CrucibleType). f u -> m (g u))
  -> SafetyAssertion ext (Compose f BaseToType)
  -> m (SafetyAssertion ext (Compose g BaseToType))
traverseSafetyAssertion _proxy =
  let
    mkF :: forall  (f :: k -> *) (g :: k -> *) (h :: j -> k) m. Functor m
        => (forall (u :: k). f u -> m (g u))
        -> (forall (u :: j). Compose f h u -> m (Compose g h u))
    mkF f (Compose v) = Compose <$> (f v)
    t :: forall s (f :: k -> *) (g :: k -> *) (h :: l -> k) m.
          ( TraversableF s
          , Applicative m
          )
      => (forall (u :: k). f u -> m (g u))
      -> s (Compose f h)
      -> m (s (Compose g h))
    t f v = traverseF (mkF f) v
  in -- Instantiate @s@ as @SafetyAssertion ext@ and @h@ as @BaseToType@
     -- TODO: are the above at all generally useful? an instance of anything?
     t

-- -----------------------------------------------------------------------
-- ** The empty safety assertion

-- | The empty safety assertion extension, which adds no new possible assertions.
data EmptySafetyAssertion :: (BaseType -> Type) -> Type
type instance SafetyAssertion () = EmptySafetyAssertion

deriving instance Show (EmptySafetyAssertion ext)

instance EqF          EmptySafetyAssertion where eqF _           = \case
instance OrdF         EmptySafetyAssertion where compareF _      = \case
instance HashableF    EmptySafetyAssertion where hashWithSaltF _ = \case
instance ShowF        EmptySafetyAssertion where showsPrecF _    = \case
instance FunctorF     EmptySafetyAssertion where fmapF _         = \case
instance FoldableF    EmptySafetyAssertion where foldMapF _      = \case
instance TraversableF EmptySafetyAssertion where traverseF _     = \case
instance TestEquality EmptySafetyAssertion where testEquality _  = \case

instance HasSafetyAssertions () where
  explain _ _     = \case
  toPredicate _ _ = \case
