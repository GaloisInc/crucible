{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Encodings where

import           Data.Parameterized.Context as Ctx

import           Lang.Crucible.Types

-- | Arrays are vector references (because they are mutable).
type ArrayType tp = ReferenceType (VectorType tp)

arrayRepr :: TypeRepr tp -> TypeRepr (ArrayType tp)
arrayRepr repr = ReferenceRepr (VectorRepr repr)

arrayElementRepr :: TypeRepr (ArrayType tp) -> TypeRepr tp
arrayElementRepr repr = case repr of
  ReferenceRepr (VectorRepr repr') -> repr'

pattern ArrayRepr :: TypeRepr tp -> TypeRepr (ArrayType tp)
pattern ArrayRepr repr = ReferenceRepr (VectorRepr repr)

-- | An array offset is an assignable location within an array. It's
-- represented by a reference to a vector and a nat offset value.
type ArrayOffsetCtx tp = EmptyCtx ::> ArrayType tp ::> NatType
type ArrayOffset tp = StructType (ArrayOffsetCtx tp)

arrayOffsetCtxRepr :: TypeRepr tp -> CtxRepr (ArrayOffsetCtx tp)
arrayOffsetCtxRepr repr = Ctx.empty :> arrayRepr repr :> NatRepr

pattern ArrayOffsetCtxRepr :: TypeRepr tp -> CtxRepr (ArrayOffsetCtx tp)
pattern ArrayOffsetCtxRepr repr = Empty :> ArrayRepr repr :> NatRepr

arrayOffsetRepr :: TypeRepr tp -> TypeRepr (ArrayOffset tp)
arrayOffsetRepr repr = StructRepr (arrayOffsetCtxRepr repr)

pattern ArrayOffsetRepr :: TypeRepr tp -> TypeRepr (ArrayOffset tp)
pattern ArrayOffsetRepr repr = StructRepr (ArrayOffsetCtxRepr repr)

-- | A pointer is either:
-- 1) a reference
-- 2) an array offset
-- TODO: globals. There doesn't appear to be an Expr form for
-- globals. An expression for reading a global is easy but what about
-- writing? The only way I see for writing to a global is with a
-- statement which I don't think can be embedded in an expression..
type PointerCtx tp = EmptyCtx ::> ReferenceType tp ::> ArrayOffset tp
type PointerType tp = VariantType (PointerCtx tp)

pointerCtxRepr :: TypeRepr tp -> CtxRepr (PointerCtx tp)
pointerCtxRepr repr = Ctx.empty :> ReferenceRepr repr :> arrayOffsetRepr repr

pattern PointerCtxRepr :: TypeRepr tp -> TypeRepr tp -> CtxRepr (PointerCtx tp)
pattern PointerCtxRepr repr1 repr2 =
  Empty :> ReferenceRepr repr1 :> ArrayOffsetRepr repr2

pointerRepr :: TypeRepr tp -> TypeRepr (PointerType tp)
pointerRepr repr = VariantRepr $ pointerCtxRepr repr

pattern PointerRepr :: TypeRepr tp -> TypeRepr tp -> TypeRepr (PointerType tp)
pattern PointerRepr repr1 repr2 = VariantRepr (PointerCtxRepr repr1 repr2)

pointerElementRepr :: TypeRepr (PointerType tp) -> TypeRepr tp
pointerElementRepr repr = case repr of
  PointerRepr repr1 _repr2 -> repr1

-- | A slice is represented by an array pointer and three nats:
-- 1) begin of slice range
-- 2) end of slice range
-- 3) capacity
type SliceCtx tp =
  EmptyCtx ::> PointerType (ArrayType tp) ::> NatType ::> NatType ::> NatType
type SliceType tp = StructType (SliceCtx tp)

sliceCtxRepr :: TypeRepr tp -> CtxRepr (SliceCtx tp)
sliceCtxRepr repr =
  Empty :> pointerRepr (arrayRepr repr) :> NatRepr :> NatRepr :> NatRepr

pattern SliceCtxRepr :: TypeRepr tp -> TypeRepr tp -> CtxRepr (SliceCtx tp)
pattern SliceCtxRepr repr1 repr2 =
  Empty :> PointerRepr (ArrayRepr repr1) (ArrayRepr repr2) :>
  NatRepr :> NatRepr :> NatRepr

sliceRepr :: TypeRepr tp -> TypeRepr (SliceType tp)
sliceRepr repr = StructRepr $ sliceCtxRepr repr

pattern SliceRepr :: TypeRepr tp -> TypeRepr tp -> TypeRepr (SliceType tp)
pattern SliceRepr repr1 repr2 = StructRepr (SliceCtxRepr repr1 repr2)
