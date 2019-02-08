{-|
Module           : What4.WordMap
Copyright        : (c) Galois, Inc 2014-2018
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.WordMap
  (
    WordMap(..)
  , emptyWordMap
  , muxWordMap
  , insertWordMap
  , lookupWordMap
  ) where

import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx

import What4.BaseTypes
import What4.Interface
import What4.Partial (PartExpr, pattern PE, pattern Unassigned) -- TODO(langston): use PartialWithErr

-----------------------------------------------------------------------
-- WordMap operations

-- | A @WordMap@ represents a finite partial map from bitvectors of width @w@
--   to elements of type @tp@.
data WordMap sym w tp =
     SimpleWordMap !(SymExpr sym
                       (BaseArrayType (EmptyCtx ::> BaseBVType w) BaseBoolType))
                   !(SymExpr sym
                       (BaseArrayType (EmptyCtx ::> BaseBVType w) tp))

-- | Create a word map where every element is undefined.
emptyWordMap :: (IsExprBuilder sym, 1 <= w)
             => sym
             -> NatRepr w
             -> BaseTypeRepr a
             -> IO (WordMap sym w a)
emptyWordMap sym w tp = do
  let idxRepr = Ctx.singleton (BaseBVRepr w)
  SimpleWordMap <$> constantArray sym idxRepr (falsePred sym)
                <*> baseDefaultValue sym (BaseArrayRepr idxRepr tp)

-- | Compute a pointwise if-then-else operation on the elements of two word maps.
muxWordMap :: IsExprBuilder sym
           => sym
           -> NatRepr w
           -> BaseTypeRepr a
           -> (Pred sym
               -> WordMap sym w a
               -> WordMap sym w a
               -> IO (WordMap sym w a))
muxWordMap sym _w _tp p (SimpleWordMap bs1 xs1) (SimpleWordMap bs2 xs2) = do
  SimpleWordMap <$> arrayIte sym p bs1 bs2
                <*> arrayIte sym p xs1 xs2

-- | Update a word map at the given index.
insertWordMap :: IsExprBuilder sym
              => sym
              -> NatRepr w
              -> BaseTypeRepr a
              -> SymBV sym w {- ^ index -}
              -> SymExpr sym a {- ^ new value -}
              -> WordMap sym w a {- ^ word map to update -}
              -> IO (WordMap sym w a)
insertWordMap sym _w _ idx v (SimpleWordMap bs xs) = do
  let i = Ctx.singleton idx
  SimpleWordMap <$> arrayUpdate sym bs i (truePred sym)
                <*> arrayUpdate sym xs i v

-- | Lookup the value of an index in a word map.
lookupWordMap :: IsExprBuilder sym
              => sym
              -> NatRepr w
              -> BaseTypeRepr a
              -> SymBV sym w {- ^ index -}
              -> WordMap sym w a
              -> IO (PartExpr (Pred sym) (SymExpr sym a))
lookupWordMap sym _w _tp idx (SimpleWordMap bs xs) = do
  let i = Ctx.singleton idx
  p <- arrayLookup sym bs i
  case asConstantPred p of
    Just False -> return Unassigned
    _ -> PE p <$> arrayLookup sym xs i
