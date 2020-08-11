{-|
Module      : Lang.Crucible.Go.Encodings
Description : Crucible encodings of Go types.
Maintainer  : abagnall@galois.com
Stability   : experimental

Some Go types are represented by compound crucible data structures
(e.g., a slice is a struct containing a pointer to an array along with
three nats). This file defines the crucible encodings for such types.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Encodings where

import           Data.Parameterized.Context as Ctx

import           Lang.Crucible.Types

vectorElementRepr :: TypeRepr (VectorType tp) -> TypeRepr tp
vectorElementRepr (VectorRepr repr) = repr

-- | Arrays are vector references (because they are mutable).
type ArrayType tp = ReferenceType (VectorType tp)

arrayElementRepr :: TypeRepr (ArrayType tp) -> TypeRepr tp
arrayElementRepr repr = case repr of
  ReferenceRepr (VectorRepr repr') -> repr'

pattern ArrayRepr :: TypeRepr tp -> TypeRepr (ArrayType tp)
pattern ArrayRepr repr = ReferenceRepr (VectorRepr repr)

-- | An array offset is an assignable location within an array. It's
-- represented by a reference to a vector and a nat offset value.
type ArrayOffsetCtx tp = EmptyCtx ::> ArrayType tp ::> NatType
type ArrayOffset tp = StructType (ArrayOffsetCtx tp)

pattern ArrayOffsetCtxRepr :: TypeRepr tp -> CtxRepr (ArrayOffsetCtx tp)
pattern ArrayOffsetCtxRepr repr = Empty :> ArrayRepr repr :> NatRepr

pattern ArrayOffsetRepr :: TypeRepr tp -> TypeRepr (ArrayOffset tp)
pattern ArrayOffsetRepr repr = StructRepr (ArrayOffsetCtxRepr repr)

-- | A pointer is either:
-- 1) nil
-- 2) a reference
-- 3) an array offset
-- As with all nil-able types, wrap the type of non-nil pointers in a
-- Maybe type.
-- TODO: globals. There doesn't appear to be an Expr form for
-- globals. An expression for reading a global is easy but what about
-- writing? The only way I see for writing to a global is with a
-- statement which I don't think can be embedded in an expression..
type PointerCtx tp = EmptyCtx ::> ReferenceType tp ::> ArrayOffset tp
type NonNilPointerType tp = VariantType (PointerCtx tp)
type PointerType tp = MaybeType (NonNilPointerType tp)

pattern PointerCtxRepr :: TypeRepr tp -> CtxRepr (PointerCtx tp)
pattern PointerCtxRepr repr <-
  Empty :> ReferenceRepr repr :> ArrayOffsetRepr (_ :: TypeRepr tp)
  where
    PointerCtxRepr repr =
      Ctx.empty :> ReferenceRepr repr :> ArrayOffsetRepr repr

pattern NonNilPointerRepr :: TypeRepr tp -> TypeRepr (NonNilPointerType tp)
pattern NonNilPointerRepr repr = VariantRepr (PointerCtxRepr repr)

pattern PointerRepr :: TypeRepr tp -> TypeRepr (PointerType tp)
pattern PointerRepr repr = MaybeRepr (NonNilPointerRepr repr)

nonNilPointerElementRepr :: TypeRepr (NonNilPointerType tp) -> TypeRepr tp
nonNilPointerElementRepr repr = case repr of
  NonNilPointerRepr repr' -> repr'

pointerElementRepr :: TypeRepr (PointerType tp) -> TypeRepr tp
pointerElementRepr repr = case repr of
  MaybeRepr repr -> nonNilPointerElementRepr repr

-- | A slice is represented by a pointer to an array and three nats:
-- 1) begin of slice range
-- 2) end of slice range
-- 3) capacity
type SliceCtx tp =
  EmptyCtx ::> PointerType (ArrayType tp) ::> NatType ::> NatType ::> NatType
type NonNilSliceType tp = StructType (SliceCtx tp)
type SliceType tp = MaybeType (NonNilSliceType tp)

pattern SliceCtxRepr :: TypeRepr tp -> CtxRepr (SliceCtx tp)
pattern SliceCtxRepr repr =
  Empty :> PointerRepr (ArrayRepr repr) :> NatRepr :> NatRepr :> NatRepr

pattern NonNilSliceRepr :: TypeRepr tp -> TypeRepr (NonNilSliceType tp)
pattern NonNilSliceRepr repr = StructRepr (SliceCtxRepr repr)

pattern SliceRepr :: TypeRepr tp -> TypeRepr (SliceType tp)
pattern SliceRepr repr = MaybeRepr (StructRepr (SliceCtxRepr repr))

sliceElementRepr :: TypeRepr (SliceType tp) -> TypeRepr tp
sliceElementRepr repr = case repr of
  SliceRepr repr' -> repr'
