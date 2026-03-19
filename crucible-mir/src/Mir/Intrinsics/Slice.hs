{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Mir.Intrinsics.Slice where

import Data.Parameterized.Context
  ( AssignView (AssignEmpty, AssignExtend),
    EmptyCtx,
    i1of2,
    i2of2,
    viewAssign,
    pattern Empty,
    pattern (:>),
    type (::>),
  )

import Lang.Crucible.CFG.Expr (App (..))
import Lang.Crucible.CFG.Reg (Expr (App))
import Lang.Crucible.Syntax (getStruct)
import Lang.Crucible.Types
  ( CtxRepr,
    StructType,
    TypeRepr (..),
  )

import Mir.Intrinsics.Reference (MirReferenceType, pattern MirReferenceRepr)
import Mir.Intrinsics.Size (UsizeType, pattern UsizeRepr)
import Mir.Intrinsics.Syntax (MIR)

--------------------------------------------------------------------------------
-- ** Slices

-- A Slice is a sequence of values plus an index to the first element
-- and a length.

type MirSlice = StructType (EmptyCtx ::>
                            MirReferenceType ::> -- first element
                            UsizeType)       --- length

pattern MirSliceRepr :: () => tp ~ MirSlice => TypeRepr tp
pattern MirSliceRepr <- StructRepr
     (viewAssign -> AssignExtend (viewAssign -> AssignExtend (viewAssign -> AssignEmpty)
         MirReferenceRepr)
         UsizeRepr)
 where MirSliceRepr = StructRepr (Empty :> MirReferenceRepr :> UsizeRepr)

mirSliceCtxRepr :: CtxRepr (EmptyCtx ::>
                            MirReferenceType ::>
                            UsizeType)
mirSliceCtxRepr = (Empty :> MirReferenceRepr :> UsizeRepr)

mkSlice ::
    Expr MIR s MirReferenceType ->
    Expr MIR s UsizeType ->
    Expr MIR s MirSlice
mkSlice vec len = App $ MkStruct mirSliceCtxRepr $
    Empty :> vec :> len


getSlicePtr :: Expr MIR s MirSlice -> Expr MIR s MirReferenceType
getSlicePtr e = getStruct i1of2 e

getSliceLen :: Expr MIR s MirSlice -> Expr MIR s UsizeType
getSliceLen e = getStruct i2of2 e
