-----------------------------------------------------------------------
-- |
-- Module           : What4.LabeledPred
-- Description      : Predicates with some metadata (a tag or label).
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- Predicates alone do not record their semantic content, thus it is often
-- useful to attach some sort of descriptor to them.
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module What4.LabeledPred
  ( LabeledPred(..)
  , labeledPred
  , labeledPredMsg
  , partitionByPreds
  , partitionLabeledPreds
  ) where

import Control.Lens
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Data (Data)
import Data.Coerce (coerce)
import Data.Data (Typeable)
import Data.Eq.Deriving (deriveEq1, deriveEq2)
import Data.Foldable (Foldable, foldrM)
import Data.Ord.Deriving (deriveOrd1, deriveOrd2)
import GHC.Generics (Generic, Generic1)
import Text.Show.Deriving (deriveShow1, deriveShow2)

import What4.Interface (IsExprBuilder, Pred, asConstantPred)

-- | Information about an assertion that was previously made.
data LabeledPred pred msg
   = LabeledPred
     { -- | Predicate that was asserted.
       _labeledPred    :: !pred
       -- | Message added when assumption/assertion was made.
     , _labeledPredMsg :: !msg
     }
   deriving (Eq, Data, Functor, Generic, Generic1, Ord, Typeable)

$(deriveBifunctor     ''LabeledPred)
$(deriveBifoldable    ''LabeledPred)
$(deriveBitraversable ''LabeledPred)
$(deriveEq1           ''LabeledPred)
$(deriveEq2           ''LabeledPred)
$(deriveOrd1          ''LabeledPred)
$(deriveOrd2          ''LabeledPred)
$(deriveShow1         ''LabeledPred)
$(deriveShow2         ''LabeledPred)

-- | Predicate that was asserted.
labeledPred :: Lens (LabeledPred pred msg) (LabeledPred pred' msg) pred pred'
labeledPred = lens _labeledPred (\s v -> s { _labeledPred = v })

-- | Message added when assumption/assertion was made.
labeledPredMsg :: Lens (LabeledPred pred msg) (LabeledPred pred msg') msg msg'
labeledPredMsg = lens _labeledPredMsg (\s v -> s { _labeledPredMsg = v })

-- | Partition datastructures containing predicates by their possibly concrete
--   values.
--
--   The output format is (constantly true, constantly false, unknown/symbolic).
partitionByPredsM ::
  (Monad m, Foldable t, IsExprBuilder sym) =>
  proxy sym {- ^ avoid \"ambiguous type variable\" errors -}->
  (a -> m (Pred sym)) ->
  t a ->
  m ([a], [a], [a])
partitionByPredsM _proxy getPred xs =
  let step x (true, false, unknown) = getPred x <&> \p ->
        case asConstantPred p of
          Just True  -> (x:true, false, unknown)
          Just False -> (true, x:false, unknown)
          Nothing    -> (true, false, x:unknown)
  in foldrM step ([], [], []) xs

-- | Partition datastructures containing predicates by their possibly concrete
--   values.
--
--   The output format is (constantly true, constantly false, unknown/symbolic).
partitionByPreds ::
  (Foldable t, IsExprBuilder sym) =>
  proxy sym {- ^ avoid \"ambiguous type variable\" errors -}->
  (a -> Pred sym) ->
  t a ->
  ([a], [a], [a])
partitionByPreds proxy getPred xs =
  runIdentity (partitionByPredsM proxy (coerce getPred) xs)

-- | Partition labeled predicates by their possibly concrete values.
--
--   The output format is (constantly true, constantly false, unknown/symbolic).
partitionLabeledPreds ::
  (Foldable t, IsExprBuilder sym) =>
  proxy sym {- ^ avoid \"ambiguous type variable\" errors -}->
  t (LabeledPred (Pred sym) msg) ->
  ([LabeledPred (Pred sym) msg], [LabeledPred (Pred sym) msg], [LabeledPred (Pred sym) msg])
partitionLabeledPreds proxy = partitionByPreds proxy (view labeledPred)
