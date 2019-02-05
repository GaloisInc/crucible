{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
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
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import           Prelude hiding (pred)

import           GHC.Generics (Generic)

import           Control.Applicative ((<*))
import           Control.Lens ((^.), (&), (%~))
import           Control.Lens (Simple(..), Lens, lens)
import           Control.Monad (guard, join)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Data (Data)
import           Data.Functor.Compose (Compose(..))
import           Data.Kind (Type)
import           Data.Maybe (isJust)
import           Data.Type.Equality (TestEquality(..))
import           Data.Typeable (Typeable)
import           Data.Void (Void)
import           Text.PrettyPrint.ANSI.Leijen (Doc)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import           Data.Parameterized.Compose ()
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.Backend (assert, IsSymInterface)
import           Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import           Lang.Crucible.Simulator.RegValue (RegValue')
import           Lang.Crucible.Types

import           What4.Interface (SymExpr, IsExpr, IsExprBuilder, Pred, printSymExpr)
import           What4.Partial

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
                  ) => (Data (PartialExpr ext e bt))
deriving instance ( Eq (e bt)
                  , Eq (e BoolType)
                  , Eq (AssertionClassifier ext e)
                  ) => (Eq (PartialExpr ext e bt))
deriving instance ( Ord (e bt)
                  , Ord (e BoolType)
                  , Ord (AssertionClassifier ext e)
                  ) => (Ord (PartialExpr ext e bt))
deriving instance ( Show (e bt)
                  , Show (e BoolType)
                  , Show (AssertionClassifier ext e)
                  ) => (Show (PartialExpr ext e bt))

-- -----------------------------------------------------------------------
-- *** Lenses

classifier :: Simple Lens (PartialExpr ext e ty) (AssertionClassifierTree ext e)
classifier = lens _classifier (\s v -> s { _classifier = v})

value :: Simple Lens (PartialExpr ext e ty) (Maybe (e ty))
value = lens _value (\s v -> s { _value = v })

-- -----------------------------------------------------------------------
-- *** Instances

-- instance EqF f => Eq (f a) where
--   (==) = eqF

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
         guard (eqAssertionTree justSubterms (testEqualityC subterms) class1 class2)

-- instance ( OrdF (AssertionClassifier ext)
--          )
--          => OrdFC (PartialExpr ext) where
--   compareFC subterms =

instance ( FunctorF (AssertionClassifier ext)
         )
         => FunctorFC (PartialExpr ext) where
  fmapFC :: forall f g. (forall x. f x -> g x) ->
                        (forall x. PartialExpr ext f x -> PartialExpr ext g x)
  fmapFC trans v =
    PartialExpr
      (mapIte trans (fmap (fmapF trans) (v ^. classifier)))
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
  traverseFC traverseSubterm = undefined

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
              -> AssertionClassifierTree ext (RegValue' sym)
              -> io (Pred sym)

  -- -- | This is in this class because a given syntax extension might have a more
  -- -- efficient implementation, e.g. by realizing that one part of an 'And'
  -- -- encompasses another. Same goes for 'explainTree'.
  -- treeToPredicate :: (MonadIO io, IsExprBuilder sym, IsSymInterface sym)
  --                 => proxy ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
  --                 -> sym
  --                 -> AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))
  --                 -> io (Pred sym)
  -- treeToPredicate proxyExt sym =
  --   liftIO . W4P.collapseAT sym (toPredicate proxyExt sym) id

  -- | Offer a one-line summary of what the assertion is about
  explain     :: (IsExprBuilder sym, IsExpr (SymExpr sym))
              => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
              -> AssertionClassifierTree ext e
              -> Doc

  -- -- | Explain an assertion in detail, including all relevant data.
  -- detail      :: (IsExprBuilder sym, IsExpr (SymExpr sym))
  --             => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
  --             -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
  --             -> SafetyAssertion ext (SymExpr sym)
  --             -> Doc
  -- detail = explain

  -- explainTree :: (IsExprBuilder sym, IsExpr (SymExpr sym))
  --             => proxy1 ext -- ^ Avoid ambiguous types, can use "Data.Proxy"
  --             -> proxy2 sym -- ^ Avoid ambiguous types, can use "Data.Proxy"
  --             -> AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))
  --             -> Doc
  -- explainTree proxyExt proxySym =
  --   W4P.cataAT
  --     (explain proxyExt proxySym) -- detail would be too much information
  --     (\factors ->
  --        "All of "
  --        <$$> indent 2 (vcat (toList factors)))
  --     (\summands ->
  --        "Any of "
  --        <$$> indent 2 (vcat (toList summands)))
  --     (\cond doc1 doc2 ->
  --        "If " <+> printSymExpr cond <$$>
  --         vcat [ "then " <$$> indent 2 doc1
  --              , "else " <$$> indent 2 doc2
  --              ])

-- | Take a partial value and assert its safety
-- assertSafe :: ( MonadIO io
--               , IsSymInterface sym
--               , HasSafetyAssertions ext
--               )
--            => proxy ext
--            -> sym
--            -> W4P.PartExpr (AssertionTree (Pred sym) (SafetyAssertion ext (SymExpr sym))) a
--            -> io (Maybe a)
-- assertSafe _proxyExt _sym W4P.Unassigned = pure Nothing
-- assertSafe proxyExt sym (W4P.PE tree a) = do
--   pred <- treeToPredicate proxyExt sym tree
--   -- TODO: Should SimErrorReason have another constructor for this?
--   liftIO $ assert sym pred $ AssertFailureSimError $
--     show $ explainTree proxyExt (Just sym) tree
--   pure (Just a)

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
-- traverseSafetyAssertion :: forall ext f g baseTy proxy m.
--      (TraversableFC (SafetyAssertion ext), Applicative m)
--   => proxy ext
--   -> (forall (u :: CrucibleType). f u -> m (g u))
--   -> SafetyAssertion ext (Compose f BaseToType) baseTy
--   -> m (SafetyAssertion ext (Compose g BaseToType) baseTy)
-- traverseSafetyAssertion _proxy f sa =
--   let mkF :: forall  (f :: k -> *) (g :: k -> *) (h :: j -> k) m. Functor m
--           => (forall (u :: k). f u -> m (g u))
--           -> (forall (u :: j). Compose f h u -> m (Compose g h u))
--       mkF f (Compose v) = Compose <$> (f v)
--   in -- Instantiate @s@ as @SafetyAssertion ext@ and @h@ as @BaseToType@
--      traverseFC (mkF f) sa

{-
traverseSafetyAssertion :: forall ext f g baseTy proxy m.
     (TraversableFC (SafetyAssertion ext), Applicative m)
  => proxy ext
  -> (forall (u :: CrucibleType). f u -> m (g u))
  -> SafetyAssertion ext (Compose f BaseToType) baseTy
  -> m (SafetyAssertion ext (Compose g BaseToType) baseTy)
traverseSafetyAssertion _proxy =
  let
    mkF :: forall  (f :: k -> *) (g :: k -> *) (h :: j -> k) m. Functor m
        => (forall (u :: k). f u -> m (g u))
        -> (forall (u :: j). Compose f h u -> m (Compose g h u))
    mkF f (Compose v) = Compose <$> (f v)
    t :: forall s (f :: k -> *) (g :: k -> *) (h :: l -> k) m.
          ( TraversableFC s
          , Applicative m
          )
      => (forall (u :: k). f u -> m (g u))
      -> s (Compose f h)
      -> m (s (Compose g h))
    t f v = traverseF (mkF f) v
  in -- Instantiate @s@ as @SafetyAssertion ext@ and @h@ as @BaseToType@
     -- TODO: are the above at all generally useful? an instance of anything?
     t
-}

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

absurdTree :: (v -> Void)
           -> AssertionTree x v
           -> a
absurdTree = undefined

instance HasStructuredAssertions () where
  explain _ _     = absurdTree (\case)
  toPredicate _ _ = absurdTree (\case)
  -- toValue _       = \case

