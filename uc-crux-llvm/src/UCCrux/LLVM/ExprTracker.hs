{-
Module       : UCCrux.LLVM.ExprTracker
Description  : Track sources of annotated symbolic expressions
Copyright    : (c) Galois, Inc 2022
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.ExprTracker
  ( TypedSelector(..),
    ExprTracker,
    empty,
    insert,
    lookup,
    union
  )
where

import           Prelude hiding (lookup)

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Classes (OrdF)
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Interface as What4

import           Data.Map (Map)
import qualified Data.Map as Map

import           UCCrux.LLVM.Cursor (Selector, SomeInSelector(..))
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr)

-- | A 'Selector' together with the type of value it points to.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data TypedSelector m (argTypes :: Ctx (FullType m)) (ft :: FullType m)
  = TypedSelector
      { tsType :: FullTypeRepr m ft,
        tsSelector :: SomeInSelector m argTypes ft
      }

-- | Track the origins of What4 expressions.
--
-- This map tracks where a given expression originated from, i.e. whether it was
-- generated as part of an argument of global variable, and if so, where in said
-- value it resides (via a 'Selector'). This is used by
-- 'UCCrux.LLVM.Classify.classifyBadBehavior' to deduce new preconditions and
-- attach constraints in the right place.
--
-- For example, if the error is an OOB write and classification looks up the
-- pointer in this map and it appears in an argument, it will attach a
-- precondition that that part of the argument gets allocated with more
-- space. If it looks up the pointer and it's not in this map, it's not clear
-- how this error could be prevented, and the error will be unclassified.
--
-- This is implemented as a @'Map' ('Some' _) ('Some' _)@ instead of a @MapF@
-- because the relationship between the 'What4.BaseType' and the 'FullType'
-- isn't one-to-one. For example, a 'Selector' may point to a pointer value,
-- which can have an annotated block number (natural) or offset (bitvector).
newtype ExprTracker m sym argTypes =
  ExprTracker
    { getExprTracker ::
        Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m argTypes))
    }

empty :: ExprTracker m sym argTypes
empty = ExprTracker Map.empty

-- | Insert an annotation and the 'Selector' for the annotated value into the
-- tracker
insert ::
  OrdF (What4.SymAnnotation sym) =>
  -- | Annotation on the value
  What4.SymAnnotation sym bt ->
  -- | Path to this value
  Selector m argTypes inTy atTy ->
  -- | Type of the annotated value
  FullTypeRepr m atTy ->
  ExprTracker m sym argTypes ->
  ExprTracker m sym argTypes
insert ann s ftRepr =
  ExprTracker .
    Map.insert (Some ann) (Some (TypedSelector ftRepr (SomeInSelector s))) .
    getExprTracker

-- | Find the origin and type of a symbolic expression
lookup ::
  OrdF (What4.SymAnnotation sym) =>
  -- | Annotation on the value
  What4.SymAnnotation sym bt ->
  ExprTracker m sym argTypes ->
  Maybe (Some (TypedSelector m argTypes))
lookup ann = Map.lookup (Some ann) . getExprTracker

-- | Union of two 'ExprTracker's.
--
-- At runtime, the keys are nonces. They'll never clash, so the bias of the
-- union is unimportant (technically, it's left-biased).
union ::
  OrdF (What4.SymAnnotation sym) =>
  ExprTracker m sym argTypes ->
  ExprTracker m sym argTypes ->
  ExprTracker m sym argTypes
union et1 et2 = ExprTracker (Map.union (getExprTracker et1) (getExprTracker et2))
