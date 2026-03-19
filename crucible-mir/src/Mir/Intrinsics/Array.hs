{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Mir.Intrinsics.Array where

import GHC.TypeLits (type (<=))

import Data.Parameterized.Context
  ( Assignment,
    EmptyCtx,
    pattern Empty,
    pattern (:>),
    type (::>),
  )
import Data.Parameterized.NatRepr (NatRepr)
import Data.Type.Equality (testEquality, pattern Refl)

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Types
  ( BaseBVType,
    BaseTypeRepr,
    SymbolicArrayType,
    TypeRepr (SymbolicArrayRepr),
  )

import What4.Interface (bvZero, constantArray)

import Mir.Intrinsics.Size (BaseUsizeType, pattern BaseUsizeRepr)


-- Aliases for working with the custom Array type, which is backed by an SMT
-- array at the Crucible level.
type UsizeArrayType btp = SymbolicArrayType (EmptyCtx ::> BaseUsizeType) btp

pattern UsizeArrayRepr :: () => tp' ~ UsizeArrayType btp => BaseTypeRepr btp -> TypeRepr tp'
pattern UsizeArrayRepr btp <-
    SymbolicArrayRepr (testEquality (Empty :> BaseUsizeRepr) -> Just Refl) btp
  where UsizeArrayRepr btp = SymbolicArrayRepr (Empty :> BaseUsizeRepr) btp


arrayZeroedIO ::
    (IsSymInterface sym, 1 <= w) =>
    sym ->
    Assignment BaseTypeRepr (idxs ::> idx) ->
    NatRepr w ->
    IO (RegValue sym (SymbolicArrayType (idxs ::> idx) (BaseBVType w)))
arrayZeroedIO sym idxs w = do
    zero <- bvZero sym w
    constantArray sym idxs zero
