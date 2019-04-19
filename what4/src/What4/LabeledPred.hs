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
import Data.Data (Typeable)
import Data.Eq.Deriving (deriveEq1, deriveEq2)
import Data.Foldable (Foldable(foldr))
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
partitionByPreds ::
  (Foldable t, IsExprBuilder sym) =>
  proxy sym {- ^ avoid \"ambiguous type variable\" errors -}->
  (a -> Pred sym) ->
  t a ->
  ([a], [a], [a])
partitionByPreds _proxy getPred xs =
  let step p (true, false, unknown) =
        case asConstantPred (getPred p) of
          Just True  -> (p:true, false, unknown)
          Just False -> (true, p:false, unknown)
          Nothing    -> (true, false, p:unknown)
  in foldr step ([], [], []) xs

-- | Partition labeled predicates by their possibly concrete values.
--
--   The output format is (constantly true, constantly false, unknown/symbolic).
partitionLabeledPreds ::
  (Foldable t, IsExprBuilder sym) =>
  proxy sym {- ^ avoid \"ambiguous type variable\" errors -}->
  t (LabeledPred (Pred sym) msg) ->
  ([LabeledPred (Pred sym) msg], [LabeledPred (Pred sym) msg], [LabeledPred (Pred sym) msg])
partitionLabeledPreds proxy = partitionByPreds proxy (view labeledPred)
