{-|
Module           : Lang.Crucible.CFG.Extension.Safety
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Explainable, composable side conditions raised by operations in syntax
extensions.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.CFG.Extension.Safety
( AssertionClassifier
, AssertionClassifierTree
, PartialExpr(..)
, classifier
, value
, HasStructuredAssertions(..)
, NoAssertionClassifier
) where

import Prelude hiding (pred)

import GHC.Generics (Generic)
import Control.Applicative ((<*))
import Control.Lens ((^.))
import Control.Lens (Simple(..), Lens, lens)
import Control.Lens.Iso (Iso, iso)
import Control.Monad (guard, join)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Data (Data)
import Data.Bifunctor (bimap)
import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq2(liftEq2), Ord2(liftCompare2))
import Data.Kind (Type)
import Data.Maybe (isJust)
import Data.Type.Equality (TestEquality(..))
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import Text.PrettyPrint.ANSI.Leijen (Doc)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import Unsafe.Coerce (unsafeCoerce)

import Data.Parameterized.Classes (EqF(..), OrdF(..), HashableF(..), ShowF(..))
import Data.Parameterized.Classes (OrderingF(..), toOrdering)
import Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import Lang.Crucible.Backend (assert, IsSymInterface)
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Simulator.RegValue (RegValue, RegValue'(..))
import Lang.Crucible.Types

import What4.Interface (SymExpr, IsExpr, IsExprBuilder, Pred, printSymExpr)
import What4.Partial

-- -----------------------------------------------------------------------
-- ** Safety assertions

-- | This is the type of \"safety assertions\" that will be made about operations
-- of the syntax extension. For example, for the LLVM syntax extension, this type
-- contains constructors for instances of undefined behavior.
--
-- The parameter after @ext@ is usually @'RegValue' sym@ or @'Expr' ext@
type family AssertionClassifier (ext :: Type) :: (CrucibleType -> Type) -> Type

type AssertionClassifierTree ext e =
  AssertionTree (e BoolType) (AssertionClassifier ext e)

-- |
--
-- Should only contain 'Nothing' if the assertion is constantly-false.
--
-- This is subtly but significantly different from What4's 'PartExpr':
-- @PartExpr pred val ≅ Maybe (pred, val)@ but
-- @PartialExpr ext e bt@ is more like @(pred, Maybe val)@. It records
-- the provenance of the assertions regardless of whether the value is present.
--
-- TODO: get rid of What4's PartExpr in favor of this
data PartialExpr (ext :: Type)
                 (e   :: CrucibleType -> Type)
                 (bt  :: CrucibleType) =
  PartialExpr
    { _classifier :: AssertionClassifierTree ext e
    , _value      :: Maybe (e bt)
    }
  deriving (Generic, Typeable)

deriving instance ( Data (e bt)
                  , Data (e BoolType)
                  , Data (AssertionClassifier ext e)
                  , Typeable e
                  , Typeable ext
                  , Typeable bt
                  ) =>
                  (Data (PartialExpr ext e bt))

deriving instance ( Eq (e bt)
                  , Eq (e BoolType)
                  , Eq (AssertionClassifier ext e)
                  ) =>
                  (Eq (PartialExpr ext e bt))

deriving instance ( Ord (e bt)
                  , Ord (e BoolType)
                  , Ord (AssertionClassifier ext e)
                  ) =>
                  (Ord (PartialExpr ext e bt))

deriving instance ( Show (e bt)
                  , Show (e BoolType)
                  , Show (AssertionClassifier ext e)
                  ) =>
                  (Show (PartialExpr ext e bt))

-- -----------------------------------------------------------------------
-- *** Lenses

classifier :: Simple Lens (PartialExpr ext e ty) (AssertionClassifierTree ext e)
classifier = lens _classifier (\s v -> s { _classifier = v})

value :: Simple Lens (PartialExpr ext e ty) (Maybe (e ty))
value = lens _value (\s v -> s { _value = v })

-- -----------------------------------------------------------------------
-- *** Instances

instance ( TestEqualityC (AssertionClassifier ext)
         )
         => TestEqualityFC (PartialExpr ext) where
  testEqualityFC :: forall f. (forall x y. f x -> f y -> (Maybe (x :~: y))) ->
                              (forall x y. PartialExpr ext f x
                                        -> PartialExpr ext f y
                                        -> (Maybe (x :~: y)))
  testEqualityFC subterms (PartialExpr class1 val1) (PartialExpr class2 val2) =
    let justSubterms x y = isJust (subterms x y)
    in join (subterms <$> val1 <*> val2) <*
         guard (liftEq2 justSubterms (testEqualityC subterms) class1 class2)

instance ( OrdC (AssertionClassifier ext)
         , TestEqualityC (AssertionClassifier ext)
         )
         => OrdFC (PartialExpr ext) where
  compareFC subterms (PartialExpr class1 val1) (PartialExpr class2 val2) =
    let demote s x y = toOrdering (s x y)
    in
      case (val1, val2) of
        (Just _, Nothing)  -> LTF
        (Nothing, Just _)  -> GTF
        (Nothing, Nothing) ->
          case liftCompare2
                  (demote subterms) (compareC subterms) class1 class2 of
            LT -> LTF
            GT -> GTF
            EQ -> -- This is safe as long as the 'compareC' is doing a nontrivial
                  -- comparison, i.e. actually using 'subterms'
                  unsafeCoerce EQF
        (Just v1, Just v2) ->
          case subterms v1 v2 of
            LTF -> LTF
            GTF -> GTF
            EQF ->
              case liftCompare2
                     (demote subterms) (compareC subterms) class1 class2 of
                LT -> LTF
                GT -> GTF
                EQ -> EQF

instance ( FunctorF (AssertionClassifier ext)
         )
         => FunctorFC (PartialExpr ext) where
  fmapFC :: forall f g. (forall x. f x -> g x) ->
                        (forall x. PartialExpr ext f x -> PartialExpr ext g x)
  fmapFC trans v =
    PartialExpr
      (bimap trans (fmapF trans) (v ^. classifier))
      (fmap trans (v ^. value))

instance ( TraversableF (AssertionClassifier ext)
         ) =>
         FoldableFC (PartialExpr ext) where
  foldMapFC = foldMapFCDefault

instance ( TraversableF (AssertionClassifier ext)
         ) =>
         TraversableFC (PartialExpr ext) where
  traverseFC :: forall f g m. Applicative m
             => (forall x. f x -> m (g x))
             -> (forall x. PartialExpr ext f x -> m (PartialExpr ext g x))
  traverseFC traverseSubterm (PartialExpr cls val) =
    PartialExpr
    <$> bitraverse traverseSubterm (traverseF traverseSubterm) cls
    <*> traverse traverseSubterm val

-- -----------------------------------------------------------------------
-- ** HasStructuredAssertions

-- | The two key operations on safety assertions are to collapse them into symbolic
-- predicates which can be added to the proof obligations, and to explain to the
-- user why the assertion was made.
--
-- For the sake of consistency, such explanations should contain the word \"should\",
-- e.g. \"the pointer should fall in a live allocation.\"
class HasStructuredAssertions (ext :: Type) where
  toPredicate :: (MonadIO io, IsExprBuilder sym, IsSymInterface sym)
              => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> sym
              -> AssertionClassifier ext (RegValue' sym)
              -> io (Pred sym)

  -- | This is in this class because a given syntax extension might have a more
  -- efficient implementation, e.g. by realizing that one part of an 'And'
  -- encompasses another. Same goes for 'explainTree'.
  treeToPredicate :: (MonadIO io, IsExprBuilder sym, IsSymInterface sym)
                  => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
                  -> sym
                  -> AssertionClassifierTree ext (RegValue' sym)
                  -> io (Pred sym)
  treeToPredicate proxyExt sym tree =
    liftIO $ collapseAT sym (toPredicate proxyExt sym) (pure . unRV) tree

  -- | Offer a one-line summary of what the assertion is about
  explain     :: proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> AssertionClassifier ext e
              -> Doc

  -- | Explain an assertion in detail, including all relevant data.
  detail      :: (IsExprBuilder sym, IsExpr (SymExpr sym))
              => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> AssertionClassifier ext (RegValue' sym)
              -> Doc
  detail proxyExt _proxySym = explain proxyExt

  explainTree :: (IsExprBuilder sym, IsExpr (SymExpr sym))
              => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> AssertionClassifierTree ext (RegValue' sym)
              -> Doc
  explainTree proxyExt proxySym =
    cataAT (explain proxyExt)
      (\factors ->
         "All of "
         <$$> indent 2 (vcat (toList factors)))
      (\summands ->
         "Any of "
         <$$> indent 2 (vcat (toList summands)))
      (\cond doc1 doc2 ->
         "If " <+> printSymExpr (unRV cond) <$$>
          vcat [ "then " <$$> indent 2 doc1
               , "else " <$$> indent 2 doc2
               ])

-- | Take a partial value and assert its safety
assertSafe :: ( MonadIO io
              , IsSymInterface sym
              , HasStructuredAssertions ext
              )
           => proxy ext
           -> sym
           -> PartialExpr ext (RegValue' sym) bt
           -> io (Maybe (RegValue sym bt))
assertSafe proxyExt sym (PartialExpr tree a) = do
  pred <- treeToPredicate proxyExt sym tree
  -- TODO: Should SimErrorReason have another constructor for this?
  liftIO $ assert sym pred $ AssertFailureSimError $
    show $ explainTree proxyExt (Just sym) tree
  pure (unRV <$> a)

-- TODO: a method that descends into an AssertionTree, asserting e.g. the
-- conjuncts separately and reporting on their success or failure individually,
-- within the context of a larger assertion i.e. "The following assertion
-- failed: _. It was part of the larger assertion _."

-- -----------------------------------------------------------------------
-- ** The empty safety assertion

-- | The empty safety assertion extension, which adds no new possible assertions.
data NoAssertionClassifier :: (CrucibleType -> Type) -> Type
  deriving (Data, Eq, Generic, Ord, Read, Show, Typeable)

isoVoid :: Simple Iso Void (NoAssertionClassifier e)
isoVoid = iso (\case) (\case)

type instance AssertionClassifier () = NoAssertionClassifier

instance EqF           NoAssertionClassifier where eqF _           = \case
instance OrdF          NoAssertionClassifier where compareF _      = \case
instance TestEqualityC NoAssertionClassifier where testEqualityC _ = \case
instance OrdC          NoAssertionClassifier where compareC _      = \case
instance HashableF     NoAssertionClassifier where hashWithSaltF _ = \case
instance ShowF         NoAssertionClassifier where showsPrecF _    = \case
instance FunctorF      NoAssertionClassifier where fmapF _         = \case
instance FoldableF     NoAssertionClassifier where foldMapF _      = \case
instance TraversableF  NoAssertionClassifier where traverseF _     = \case
instance TestEquality  NoAssertionClassifier where testEquality _  = \case

instance HasStructuredAssertions () where
  explain _       = \case
  toPredicate _ _ = \case
