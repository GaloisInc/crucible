{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

-- TODO(#1786): refine exports, if necessary
module Mir.Intrinsics.Enum
  ( RustEnumType,
    RustEnumFields,
    SomeRustEnumRepr (..),
    pattern RustEnumFieldsRepr,
    pattern RustEnumRepr,
    mkRustEnum,
    rustEnumDiscriminant,
    rustEnumVariant,
  )
where

import Data.Parameterized.Context
  ( EmptyCtx,
    i1of2,
    i2of2,
    pattern Empty,
    pattern (:>),
    type (::>),
  )

import Lang.Crucible.CFG.Expr (App (..))
import Lang.Crucible.Types (CtxRepr, StructType, TypeRepr (..), VariantType)


-- Rust enum representation

-- A Rust enum, whose variants have the types listed in `ctx`.
type RustEnumType discrTp variantsCtx = StructType (RustEnumFields discrTp variantsCtx)
type RustEnumFields discrTp variantsCtx = EmptyCtx ::> discrTp ::> VariantType variantsCtx

data SomeRustEnumRepr where
  SomeRustEnumRepr ::
    !(TypeRepr discrTp) ->
    !(CtxRepr variantsCtx) ->
    SomeRustEnumRepr

pattern RustEnumFieldsRepr :: () => ctx ~ RustEnumFields discrTp variantsCtx => TypeRepr discrTp -> CtxRepr variantsCtx -> CtxRepr ctx
pattern RustEnumFieldsRepr discrTp variantsCtx = Empty :> discrTp :> VariantRepr variantsCtx
pattern RustEnumRepr :: () => tp ~ RustEnumType discrTp variantsCtx => TypeRepr discrTp -> CtxRepr variantsCtx -> TypeRepr tp
pattern RustEnumRepr discrTp variantsCtx = StructRepr (RustEnumFieldsRepr discrTp variantsCtx)

mkRustEnum :: TypeRepr discrTp -> CtxRepr variantsCtx -> f discrTp -> f (VariantType variantsCtx) -> App ext f (RustEnumType discrTp variantsCtx)
mkRustEnum discrTp variantsCtx discr variant = MkStruct (RustEnumFieldsRepr discrTp variantsCtx) (Empty :> discr :> variant)

rustEnumDiscriminant :: TypeRepr discrTp -> f (RustEnumType discrTp variantsCtx) -> App ext f discrTp
rustEnumDiscriminant discrTp e = GetStruct e i1of2 discrTp

rustEnumVariant :: CtxRepr variantsCtx -> f (RustEnumType discrTp variantsCtx) -> App ext f (VariantType variantsCtx)
rustEnumVariant variantsCtx e = GetStruct e i2of2 (VariantRepr variantsCtx)
