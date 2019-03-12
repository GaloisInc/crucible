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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.CFG.Extension.Safety
( AssertionClassifier
, AssertionClassifierTree
, PartialExpr(..)
, pattern PartialExp
, classifier
, value
, HasStructuredAssertions(..)
, assertSafe
, NoAssertionClassifier
) where

import Prelude hiding (pred)

import GHC.Generics (Generic)
import Control.Applicative ((<*))
import Control.Lens ((^.), (&), (.~))
import Control.Lens (Simple, Lens, lens)
import Control.Lens.Wrapped
import Control.Monad (guard)
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
import Text.PrettyPrint.ANSI.Leijen (Doc)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Data.Parameterized.Classes (EqF(..), OrdF(..), HashableF(..), ShowF(..))
import Data.Parameterized.Classes (OrderingF(..), toOrdering)
import Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import Data.Parameterized.TraversableF
import Data.Parameterized.TraversableFC

import Lang.Crucible.Backend (assert, IsSymInterface)
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Simulator.RegValue (RegValue'(..))
import Lang.Crucible.Types

import What4.Interface (SymExpr, IsExpr, IsExprBuilder, Pred, printSymExpr)
import What4.Partial
import What4.Partial.AssertionTree

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

-- | A value packaged with a predicate expressing its partiality
newtype PartialExpr (ext :: Type)
                    (e   :: CrucibleType -> Type)
                    (bt  :: CrucibleType) =
  PartialExpr { _unPartialExpr :: Partial (AssertionClassifierTree ext e) (e bt) }
  deriving (Generic, Typeable)

-- | A simply-bidirectional pattern for deconstructing a 'PartialExpr' into the
-- underlying 'Partial'.
pattern PartialExp :: AssertionClassifierTree ext e -> e bt -> PartialExpr ext e bt
pattern PartialExp p v = PartialExpr (Partial p v)

{-# COMPLETE PartialExp #-}

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

instance Wrapped (PartialExpr ext e bt)

-- -----------------------------------------------------------------------
-- *** Lenses

-- | TODO: Should use 'Control.Lens.Wrapped' here somehow?
unPartialExpr :: Simple Lens (PartialExpr ext e ty) (Partial (AssertionClassifierTree ext e) (e ty))
unPartialExpr = lens _unPartialExpr (\_ v -> PartialExpr v)

classifier :: Simple Lens (PartialExpr ext e ty) (AssertionClassifierTree ext e)
classifier = lens (^. unPartialExpr . partialPred)
                  (\pexp tree -> pexp & unPartialExpr . partialPred .~ tree)

value :: Simple Lens (PartialExpr ext e ty) (e ty)
value = lens (^. unPartialExpr . partialValue)
             (\pexp val -> pexp & unPartialExpr . partialValue .~ val)

-- -----------------------------------------------------------------------
-- *** Instances

instance ( TestEqualityC (AssertionClassifier ext)
         )
         => TestEqualityFC (PartialExpr ext) where
  testEqualityFC :: forall f. (forall x y. f x -> f y -> (Maybe (x :~: y))) ->
                              (forall x y. PartialExpr ext f x
                                        -> PartialExpr ext f y
                                        -> (Maybe (x :~: y)))
  testEqualityFC subterms (PartialExp class1 val1) (PartialExp class2 val2) =
    let justSubterms x y = isJust (subterms x y)
    in subterms val1 val2 <*
         guard (liftEq2 justSubterms (testEqualityC subterms) class1 class2)

instance ( OrdC (AssertionClassifier ext)
         , TestEqualityC (AssertionClassifier ext)
         )
         => OrdFC (PartialExpr ext) where
  compareFC subterms (PartialExp class1 val1) (PartialExp class2 val2) =
    let demote s x y = toOrdering (s x y)
    in
      case subterms val1 val2 of
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
    PartialExp
      (bimap trans (fmapF trans) (v ^. classifier))
      (trans (v ^. value))

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
  traverseFC traverseSubterm (PartialExp cls val) =
    PartialExp
    <$> bitraverse traverseSubterm (traverseF traverseSubterm) cls
    <*> traverseSubterm val

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
    cataAT (detail proxyExt proxySym) -- may want to use 'explain'
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
           -> Partial (AssertionClassifierTree ext (RegValue' sym)) a
           -> io a
assertSafe proxyExt sym (Partial tree a) = do
  pred <- treeToPredicate proxyExt sym tree
  -- TODO: Should SimErrorReason have another constructor for this?
  let rsn = AssertFailureSimError (show (explainTree proxyExt (Just sym) tree))
  liftIO $ assert sym pred rsn
  pure a

-- TODO: a method that descends into an AssertionTree, asserting e.g. the
-- conjuncts separately and reporting on their success or failure individually,
-- within the context of a larger assertion i.e. "The following assertion
-- failed: _. It was part of the larger assertion _."

-- -----------------------------------------------------------------------
-- ** The empty safety assertion

-- | The empty safety assertion extension, which adds no new possible assertions.
data NoAssertionClassifier :: (CrucibleType -> Type) -> Type
  deriving (Data, Eq, Generic, Ord, Read, Show, Typeable)

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
