{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module Mir.Intrinsics.Dyn where

import Data.Parameterized.Context
  ( Assignment,
    EmptyCtx,
    Index,
    baseIndex,
    incSize,
    lastIndex,
    skipIndex,
    zeroSize,
    (::>),
    pattern Empty,
    pattern (:>),
  )

import Lang.Crucible.Types (AnyType, StructType, TypeRepr (..))

import Mir.Intrinsics.Reference (MirReferenceType, pattern MirReferenceRepr)

-- | The 'MirReferenceType' is the data pointer - either an immutable or mutable
-- reference. The 'AnyType' is the vtable. See @Note [Erase vtable types]@.
type DynRefType = StructType (EmptyCtx ::> MirReferenceType ::> AnyType)

dynRefDataIndex :: Index (EmptyCtx ::> MirReferenceType ::> AnyType) MirReferenceType
dynRefDataIndex = skipIndex baseIndex

dynRefVtableIndex :: Index (EmptyCtx ::> MirReferenceType ::> AnyType) AnyType
dynRefVtableIndex = lastIndex (incSize $ incSize zeroSize)

pattern DynRefCtx :: () => (ctx ~ EmptyCtx ::> MirReferenceType ::> AnyType) => Assignment TypeRepr ctx
pattern DynRefCtx = Empty :> MirReferenceRepr :> AnyRepr

-- | The representation for a @&dyn Tr@/@&mut dyn Tr@. Both use the same
-- representation: a pair of a data value (which is either @&Ty@ or @&mut Ty@)
-- and a vtable. The vtable is type-erased (`AnyRepr`); see @Note [Erase vtable
-- types]@ in "Mir.Intrinsics". See also `DynRefCtx`.
pattern DynRefRepr :: () => (tp ~ DynRefType) => TypeRepr tp
pattern DynRefRepr = StructRepr DynRefCtx

{-
Note [Erase vtable types]
~~~~~~~~~~~~~~~~~~~~~~~~~
DynRefType erases the type of a trait object's vtable using Crucible's Any
type. Note that the vtable type is known statically, which makes the choice to
use Any here somewhat unusual. The main reason why we need Any is because
vtable types can potentially be recursive. For instance, consider the
std::error::Error trait:

  trait Error {
      fn cause(&self) -> Option<&dyn Error>;
  }

Now suppose that we want to translate the type `&dyn Error` to Crucible. The
vtable for a trait object of this type will have a field for the `cause`
method, and this field's type will recursively mention `&dyn Error`. We have to
be careful when translating this, because we might run this risk of infinitely
recursing.

Using the Any type is one way to break the recursion. Rather than translating
all of a vtable's field types upfront, we instead just represent the entire
vtable type as Any. Later, when making a virtual call, we check dynamically (at
simulation time) that the Any's underlying type actually matches the expected
vtable type, which allows us to unfold the vtable type definition once (and
only once, to avoid infinitely recursing).

An alternative approach would be to use Crucible's RecursiveType instead of
Any. It is unclear if this is worth the effort, however, as we would have to
invent a new symbol for each vtable type. Moreover, the amount of machinery
needed to roll/unroll recursive types is similar to the machinery needed to
pack/unpack Any types.
-}
