-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Types
-- Description      : This module exports the types used in Crucible
--                    expressions.
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module exports the types used in Crucible expressions.
--
-- These types are largely used as indexes to various GADTs and type
-- families as a way to let the GHC typechecker help us keep expressions
-- of the embedded CFG language apart.
--
-- In addition, we provide a value-level reification of the type
-- indices that can be examined by pattern matching, called 'TypeRepr'.
-- The 'KnownRepr' class computes the value-level representation
-- of a given type index, when the type is known at compile time.
-- Similar setups exist for other components of the type system:
-- bitvector data and type contexts.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Types
  ( -- * CrucibleType data kind
    type CrucibleType
    -- ** Constructors for kind CrucibleType
  , AnyType
  , UnitType
  , BoolType
  , ConcreteType
  , NatType
  , IntegerType
  , RealValType
  , ComplexRealType
  , BVType
  , FloatType
  , CharType
  , StringType
  , FunctionHandleType
  , MaybeType
  , RecursiveType
  , IntrinsicType
  , VectorType
  , StructType
  , VariantType
  , ReferenceType
  , WordMapType
  , IntWidthType
  , UIntWidthType
  , MultiDimArrayType
  , SymbolicMultiDimArrayType
  , MatlabIntType
  , MatlabUIntType
  , MatlabIntArrayType
  , MatlabUIntArrayType
  , MatlabSymbolicIntArrayType
  , MatlabSymbolicUIntArrayType

  , StringMapType
  , SymbolicArrayType

    -- * FloatInfo data kind
  , FloatInfo(..)
  , FloatInfoRepr(..)
    -- * IsRecursiveType
  , IsRecursiveType(..)

    -- * Base type injection
  , BaseToType
  , baseToType

  , AsBaseType(..)
  , asBaseType

    -- * Other stuff
  , CtxRepr

  , IntWidth(..)
  , UIntWidth(..)

  , pattern KnownBV

    -- * Derived constructors for kind CrucibleType
  , StructFieldsType
  , CplxArrayType
  , RealArrayType
  , LogicArrayType
  , IntegerArrayType
  , SymLogicArrayType
  , SymNatArrayType
  , SymIntegerArrayType
  , SymRealArrayType
  , SymCplxArrayType
  , CharArrayType
  , MultiDimArrayIndexType
  , ArrayDimType

    -- * Representation of Crucible types
  , TypeRepr(..)
    -- * Concrete types
  , TypeableType(..)
  , TypeableValue(..)

    -- * Re-exports
  , type Data.Parameterized.Ctx.Ctx
  , Data.Parameterized.Ctx.EmptyCtx
  , (Data.Parameterized.Ctx.::>)

  , module Data.Parameterized.NatRepr
  , module Data.Parameterized.SymbolRepr
  , module Lang.Crucible.BaseTypes
  ) where

import           Data.Hashable
import           Data.Maybe
import           Data.Type.Equality
import           Data.Typeable
import           GHC.Fingerprint.Type
import           GHC.TypeLits
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.TH.GADT as U
import           Text.PrettyPrint.ANSI.Leijen

import           Lang.Crucible.BaseTypes

------------------------------------------------------------------------
-- IntWidth

-- | A positive width.
data IntWidth where
  IntWidth :: (1 <= w) => NatRepr w -> IntWidth

instance Eq IntWidth where
  IntWidth x == IntWidth y = isJust (testEquality x y)

instance Show IntWidth where
  show (IntWidth x) = show x

------------------------------------------------------------------------
-- UIntWidth

-- | A positive width.
data UIntWidth where
  UIntWidth :: (1 <= w) => NatRepr w -> UIntWidth

instance Eq UIntWidth where
  UIntWidth x == UIntWidth y = isJust (testEquality x y)

instance Show UIntWidth where
  show (UIntWidth x) = show x

-------------------------------------------------------------------------
-- Concrete types

-- | Representation of a Haskell type that can be used as a 'ConcreteType'.
data TypeableType (a :: *) where
  TypeableType :: (Typeable a, Eq a, Ord a, Show a) => TypeableType a

-- | A value of 'ConcreteType'.
data TypeableValue (a :: *) where
  TypeableValue :: (Typeable a, Eq a, Ord a, Show a) => a -> TypeableValue a

------------------------------------------------------------------------
-- Crucible types


-- | This data kind describes the styles of floating-point values understood
--   by recent LLVM bitcode formats.  This consist of the standard IEEE 754-2008
--   binary floating point formats, as well as the X86 extended 80-bit format
--   and the double-double format.
data FloatInfo where
  HalfFloat         :: FloatInfo  --  16 bit binary IEEE754
  SingleFloat       :: FloatInfo  --  32 bit binary IEEE754
  DoubleFloat       :: FloatInfo  --  64 bit binary IEEE754
  QuadFloat         :: FloatInfo  -- 128 bit binary IEEE754
  X86_80Float       :: FloatInfo  -- X86 80-bit extended floats
  DoubleDoubleFloat :: FloatInfo -- 2 64-bit floats fused in the "double-double" style

type HalfFloat   = 'HalfFloat
type SingleFloat = 'SingleFloat
type DoubleFloat = 'DoubleFloat
type QuadFloat   = 'QuadFloat
type X86_80Float = 'X86_80Float
type DoubleDoubleFloat = 'DoubleDoubleFloat

-- | A family of value-level representatives for floating-point types.
data FloatInfoRepr (flt::FloatInfo) where
   HalfFloatRepr         :: FloatInfoRepr HalfFloat
   SingleFloatRepr       :: FloatInfoRepr SingleFloat
   DoubleFloatRepr       :: FloatInfoRepr DoubleFloat
   QuadFloatRepr         :: FloatInfoRepr QuadFloat
   X86_80FloatRepr       :: FloatInfoRepr X86_80Float
   DoubleDoubleFloatRepr :: FloatInfoRepr DoubleDoubleFloat

-- | This typeclass is used to register recursive Crucible types
--   with the compiler.  This class defines, for a given symbol,
--   both the type-level and the representative-level unrolling
--   of a named recursive type.  Parameter @nm@ has kind 'Symbol'.
class IsRecursiveType (nm::Symbol) where
  type UnrollType nm (ctx :: Ctx CrucibleType) :: CrucibleType
  unrollType :: SymbolRepr nm -> CtxRepr ctx -> TypeRepr (UnrollType nm ctx)

type CtxRepr = Ctx.Assignment TypeRepr

-- | This data kind describes the types of values and expressions that
--   can occur in Crucible CFGs.  Sometimes these correspond to objects that
--   exist in source-level programs, and some correspond only to intermediate
--   values introduced in translations.
data CrucibleType where
   -- An injection of all base types into crucible types
   BaseToType :: BaseType -> CrucibleType

   -- A dynamic type that can contain values of any type.
   AnyType :: CrucibleType

   -- A Crucible type that lifts an arbitrary Haskell type, provided
   -- it supplies Typeable, Eq, Ord and Show instances.
   -- Values of concrete types do not support nontrivial symbolic path merging.
   ConcreteType :: a -> CrucibleType

   -- A type containing a single value "Unit"
   UnitType :: CrucibleType
   -- A type index for floating point numbers
   FloatType :: FloatInfo -> CrucibleType
   -- A single character, as a 16-bit wide char.
   CharType :: CrucibleType
   -- A sequence of Unicode characters.
   StringType :: CrucibleType
   -- A function handle taking a context of formal arguments and a return type
   FunctionHandleType :: Ctx CrucibleType -> CrucibleType -> CrucibleType

   -- The Maybe type lifted into crucible expressions
   MaybeType :: CrucibleType -> CrucibleType
   -- A finite (one-dimensional) sequence of values
   VectorType :: CrucibleType -> CrucibleType
   -- A structure is an aggregate type consisting of a sequence of values.
   -- The type of each value is known statically.
   StructType :: Ctx CrucibleType -> CrucibleType

   -- The type of mutable reference cells.
   ReferenceType :: CrucibleType -> CrucibleType

   -- A variant is a disjoint union of the types listed in the context.
   VariantType :: Ctx CrucibleType -> CrucibleType

   -- A finite map from bitvector values to the given crucible type.
   -- The nat index gives the width of the bitvector values used to index
   -- the map.
   WordMapType :: Nat -> BaseType -> CrucibleType

   -- A concrete positive integer value.
   IntWidthType :: CrucibleType
   -- A value describing the width of an unsigned bitvector.
   -- This is a nonnegative integer value.
   UIntWidthType :: CrucibleType

   -- Named recursive types, named by the given symbol.  To use recursive types
   -- you must provide an instances of the IsRecursiveType class that gives
   -- the unfolding of this recursive type.  The RollRecursive and UnrollRecursive
   -- operations witness the isomorphism between a recursive type and its one-step
   -- unrolling.  Similar to Haskell's newtype, recursive types to not necessarly
   -- have to mention the recursive type being defined; in which case, the type
   -- is simply a new named type which is isomorphic to its definition.
   RecursiveType :: Symbol -> Ctx CrucibleType -> CrucibleType


   -- Named intrinsic types.  Intrinsic types are a way to extend the crucible
   -- type system after-the-fact and add new type implementations.
   -- Core crucible provides no operations on intrinsic types; they must be provided
   -- as built-in override functions.  See the `IntrinsicClass` typeclass
   -- and the `Intrinsic` type family defined in "Lang.Crucible.Simulator.Intrinsics".
   --
   -- The context of crucible types are type arguments to the intrinsic type.
   IntrinsicType :: Symbol -> Ctx CrucibleType -> CrucibleType

   -- A multidimensional array of values.  These arrays are "external" arrays
   -- that exist only in the simulator.  Array dimensions are not tracked statically,
   -- but the array dimensions of external arrays must be concrete values.
   MultiDimArrayType :: CrucibleType -> CrucibleType

   -- A multidimensional array of values.  These arrays are "internal" arrays
   -- that are represented directly in the vocabulary of underlying solvers.
   -- Array dimensions are not tracked statically, and may be symbolic.
   -- However, the types that can be stored in symbolic arrays are limited
   -- to the types that can be represented internally to the solver.
   SymbolicMultiDimArrayType :: BaseType -> CrucibleType

   -- The type of signed MATLAB bitvector integers of unknown size
   -- with 2's complement arithmetic.  These must have width at least
   -- 1. Overflowing operations are clamped to the maximum or minimum
   -- value of the bitvector's range.
   MatlabIntType :: CrucibleType

   -- The type of unsigned MATLAB bitvector integers of unknown size,
   -- using standard binary arithmetic.  Overflowing operations are
   -- clamped to the maximum or minimum value of the bitvector's
   -- range.
   MatlabUIntType :: CrucibleType

   -- Multidimensional array of signed MATLAB bitvector integers.
   -- Every integer in the array has the same width.
   MatlabIntArrayType :: CrucibleType
   -- Multidimensional array of unsigned MATLAB bitvector integers.
   -- Every integer in the array has the same width.
   MatlabUIntArrayType :: CrucibleType

   MatlabSymbolicIntArrayType :: CrucibleType

   MatlabSymbolicUIntArrayType :: CrucibleType

   -- A partial map from strings to values.
   StringMapType :: CrucibleType -> CrucibleType

type BaseToType      = 'BaseToType                -- ^ @:: 'BaseType' -> 'CrucibleType'@.
type BoolType        = BaseToType BaseBoolType    -- ^ @:: 'CrucibleType'@.
type BVType w        = BaseToType (BaseBVType w)  -- ^ @:: 'Nat' -> 'CrucibleType'@.
type ComplexRealType = BaseToType BaseComplexType -- ^ @:: 'CrucibleType'@.
type IntegerType     = BaseToType BaseIntegerType -- ^ @:: 'CrucibleType'@.
type NatType         = BaseToType BaseNatType     -- ^ @:: 'CrucibleType'@.
type RealValType     = BaseToType BaseRealType    -- ^ @:: 'CrucibleType'@.
type SymbolicArrayType idx xs = BaseToType (BaseArrayType idx xs) -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType' -> 'CrucibleType'@.
type SymbolicStructType flds = BaseToType (BaseStructType flds) -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'CrucibleType'@.

-- | A dynamic type that can contain values of any type.
type AnyType  = 'AnyType  -- ^ @:: 'CrucibleType'@.

-- | A single character, as a 16-bit wide char.
type CharType = 'CharType -- ^ @:: 'CrucibleType'@.

-- | A Crucible type that lifts an arbitrary Haskell type, provided it
-- supplies 'Typeable', 'Eq', 'Ord' and 'Show' instances. Values of
-- concrete types do not support nontrivial symbolic path merging.
type ConcreteType = 'ConcreteType -- ^ @:: a -> 'CrucibleType'@.

-- | A type index for floating point numbers.
type FloatType    = 'FloatType    -- ^ @:: 'FloatInfo' -> 'CrucibleType'@.

-- | A function handle taking a context of formal arguments and a return type.
type FunctionHandleType = 'FunctionHandleType -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType' -> 'CrucibleType'@.

-- | A concrete positive integer value.
type IntWidthType = 'IntWidthType -- ^ @:: 'CrucibleType'@.

-- | Named recursive types, named by the given symbol. To use
-- recursive types you must provide an instance of the
-- 'IsRecursiveType' class that gives the unfolding of this recursive
-- type. The 'Lang.Crucible.Core.RollRecursive' and
-- 'Lang.Crucible.Core.UnrollRecursive' operations witness the
-- isomorphism between a recursive type and its one-step unrolling.
-- Similar to Haskell's @newtype@, recursive types to not necessarily
-- have to mention the recursive type being defined; in which case,
-- the type is simply a new named type which is isomorphic to its
-- definition.
type RecursiveType = 'RecursiveType -- ^ @:: 'Symbol' -> 'CrucibleType'@.

-- | Named intrinsic types. Intrinsic types are a way to extend the
-- Crucible type system after-the-fact and add new type
-- implementations. Core Crucible provides no operations on intrinsic
-- types; they must be provided as built-in override functions. See
-- the 'Lang.Crucible.Simulator.Intrinsics.IntrinsicClass' typeclass
-- and the 'Lang.Crucible.Simulator.Intrinsics.Intrinsic' type family
-- defined in "Lang.Crucible.Simulator.Intrinsics".
type IntrinsicType ctx = 'IntrinsicType ctx -- ^ @:: 'Symbol' -> 'Ctx CrucibleType' -> 'CrucibleType'@.

-- | The type of mutable reference cells.
type ReferenceType = 'ReferenceType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | Multidimensional array of signed MATLAB bitvector integers. Every
-- integer in the array has the same width.
type MatlabIntArrayType    = 'MatlabIntArrayType  -- ^ @:: 'CrucibleType'@.

-- | The type of unsigned MATLAB bitvector integers of unknown size,
-- using standard binary arithmetic. Overflowing operations are
-- clamped to the maximum or minimum value of the bitvector's range.
type MatlabIntType         = 'MatlabIntType       -- ^ @:: 'CrucibleType'@.

-- | Multidimensional array of unsigned MATLAB bitvector integers.
-- Every integer in the array has the same width.
type MatlabUIntArrayType   = 'MatlabUIntArrayType -- ^ @:: 'CrucibleType'@.

-- | The type of unsigned MATLAB bitvector integers of unknown size,
-- using standard binary arithmetic. Overflowing operations are
-- clamped to the maximum or minimum value of the bitvector's range.
type MatlabUIntType        = 'MatlabUIntType      -- ^ @:: 'CrucibleType'@.
type MatlabSymbolicIntArrayType = 'MatlabSymbolicIntArrayType -- ^ @:: 'CrucibleType'@.
type MatlabSymbolicUIntArrayType = 'MatlabSymbolicUIntArrayType -- ^ @:: 'CrucibleType'@.

-- | The 'Maybe' type lifted into Crucible expressions.
type MaybeType = 'MaybeType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A multidimensional array of values. These arrays are "external"
-- arrays that exist only in the simulator. Array dimensions are not
-- tracked statically, but the array dimensions of external arrays
-- must be concrete values.
type MultiDimArrayType = 'MultiDimArrayType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A partial map from strings to values.
type StringMapType = 'StringMapType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A sequence of Unicode characters.
type StringType = 'StringType -- ^ @:: 'CrucibleType'@.

-- | A structure is an aggregate type consisting of a sequence of
-- values. The type of each value is known statically.
type StructType = 'StructType -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType'@.

-- | A multidimensional array of values. These arrays are "internal"
-- arrays that are represented directly in the vocabulary of
-- underlying solvers. Array dimensions are not tracked statically,
-- and may be symbolic. However, the types that can be stored in
-- symbolic arrays are limited to the types that can be represented
-- internally to the solver.
type SymbolicMultiDimArrayType = 'SymbolicMultiDimArrayType -- ^ @:: 'BaseType' -> 'CrucibleType'@.

-- | A value describing the width of an unsigned bitvector. This is a
-- non-negative integer value.
type UIntWidthType = 'UIntWidthType -- ^ @:: 'CrucibleType'@.

-- | A type containing a single value "Unit".
type UnitType      = 'UnitType      -- ^ @:: 'CrucibleType'@.

-- | A variant is a disjoint union of the types listed in the context.
type VariantType   = 'VariantType   -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType'@.

-- | A finite (one-dimensional) sequence of values.
type VectorType    = 'VectorType    -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A finite map from bitvector values to the given Crucible type.
-- The 'Nat' index gives the width of the bitvector values used to
-- index the map.
type WordMapType   = 'WordMapType   -- ^ @:: 'Nat' -> 'BaseType' -> 'CrucibleType'@.

-- | A type for a collection of the names of a structure.
type StructFieldsType = VectorType StringType

type CplxArrayType = MultiDimArrayType ComplexRealType
type RealArrayType = MultiDimArrayType RealValType
type IntegerArrayType = MultiDimArrayType IntegerType
type LogicArrayType = MultiDimArrayType BoolType
type CharArrayType = MultiDimArrayType CharType
type MultiDimArrayIndexType = MultiDimArrayType (VectorType NatType)
type ArrayDimType = VectorType NatType

type SymLogicArrayType   = SymbolicMultiDimArrayType BaseBoolType
type SymNatArrayType     = SymbolicMultiDimArrayType BaseNatType
type SymIntegerArrayType = SymbolicMultiDimArrayType BaseIntegerType
type SymRealArrayType    = SymbolicMultiDimArrayType BaseRealType
type SymCplxArrayType    = SymbolicMultiDimArrayType BaseComplexType


----------------------------------------------------------------
-- Base Type Injection

baseToType :: BaseTypeRepr bt -> TypeRepr (BaseToType bt)
baseToType bt =
  case bt of
    BaseBoolRepr -> BoolRepr
    BaseIntegerRepr -> IntegerRepr
    BaseNatRepr -> NatRepr
    BaseRealRepr -> RealValRepr
    BaseBVRepr w -> BVRepr w
    BaseComplexRepr -> ComplexRealRepr
    BaseArrayRepr idx xs -> SymbolicArrayRepr idx xs
    BaseStructRepr flds -> SymbolicStructRepr flds

data AsBaseType tp where
  AsBaseType  :: tp ~ BaseToType bt => BaseTypeRepr bt -> AsBaseType tp
  NotBaseType :: AsBaseType tp

asBaseType :: TypeRepr tp -> AsBaseType tp
asBaseType tp =
  case tp of
    BoolRepr -> AsBaseType BaseBoolRepr
    IntegerRepr -> AsBaseType BaseIntegerRepr
    NatRepr -> AsBaseType BaseNatRepr
    RealValRepr -> AsBaseType BaseRealRepr
    BVRepr w -> AsBaseType (BaseBVRepr w)
    ComplexRealRepr -> AsBaseType BaseComplexRepr
    SymbolicArrayRepr idx xs ->
      AsBaseType (BaseArrayRepr idx xs)
    SymbolicStructRepr flds -> AsBaseType (BaseStructRepr flds)
    _ -> NotBaseType

----------------------------------------------------------------
-- Type representatives

-- | A family of representatives for Crucible types. Parameter @tp@
-- has kind 'CrucibleType'.
data TypeRepr (tp::CrucibleType) where
   AnyRepr :: TypeRepr AnyType
   ConcreteRepr :: TypeableType a -> TypeRepr (ConcreteType a)
   UnitRepr :: TypeRepr UnitType
   BoolRepr :: TypeRepr BoolType
   NatRepr  :: TypeRepr NatType
   IntegerRepr :: TypeRepr IntegerType
   RealValRepr :: TypeRepr RealValType
   ComplexRealRepr :: TypeRepr ComplexRealType
   BVRepr :: (1 <= n) => !(NatRepr n) -> TypeRepr (BVType n)
   IntrinsicRepr :: !(SymbolRepr nm)
                 -> !(CtxRepr ctx)
                 -> TypeRepr (IntrinsicType nm ctx)
   RecursiveRepr :: IsRecursiveType nm
                 => SymbolRepr nm
                 -> CtxRepr ctx
                 -> TypeRepr (RecursiveType nm ctx)
   FloatRepr :: !(FloatInfoRepr flt) -> TypeRepr (FloatType flt)
   CharRepr :: TypeRepr CharType
   StringRepr :: TypeRepr StringType
   FunctionHandleRepr :: !(CtxRepr ctx)
                      -> !(TypeRepr ret)
                      -> TypeRepr (FunctionHandleType ctx ret)

   MaybeRepr   :: !(TypeRepr tp) -> TypeRepr (MaybeType   tp)
   VectorRepr  :: !(TypeRepr tp) -> TypeRepr (VectorType  tp)
   StructRepr  :: !(CtxRepr ctx) -> TypeRepr (StructType  ctx)
   VariantRepr :: !(CtxRepr ctx) -> TypeRepr (VariantType ctx)
   ReferenceRepr :: TypeRepr a -> TypeRepr (ReferenceType a)

   WordMapRepr :: (1 <= n)
               => !(NatRepr n)
               -> !(BaseTypeRepr tp)
               -> TypeRepr (WordMapType n tp)

   IntWidthRepr  :: TypeRepr IntWidthType
   UIntWidthRepr :: TypeRepr UIntWidthType

   StringMapRepr :: !(TypeRepr tp) -> TypeRepr (StringMapType tp)

   SymbolicArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx::>tp))
                     -> !(BaseTypeRepr t)
                     -> TypeRepr (SymbolicArrayType (idx::>tp) t)

   -- A reference to a symbolic struct.
   SymbolicStructRepr :: Ctx.Assignment BaseTypeRepr ctx
                      -> TypeRepr (SymbolicStructType ctx)

   MultiDimArrayRepr :: !(TypeRepr tp) -> TypeRepr (MultiDimArrayType tp)
   SymbolicMultiDimArrayRepr :: !(BaseTypeRepr bt) -> TypeRepr (SymbolicMultiDimArrayType bt)

   MatlabIntRepr  :: TypeRepr MatlabIntType
   MatlabUIntRepr :: TypeRepr MatlabUIntType

   MatlabIntArrayRepr  :: TypeRepr MatlabIntArrayType
   MatlabUIntArrayRepr :: TypeRepr MatlabUIntArrayType
   MatlabSymbolicIntArrayRepr :: TypeRepr MatlabSymbolicIntArrayType
   MatlabSymbolicUIntArrayRepr :: TypeRepr MatlabSymbolicUIntArrayType

------------------------------------------------------------------------------
-- Representable class instances

instance KnownRepr FloatInfoRepr HalfFloat         where knownRepr = HalfFloatRepr
instance KnownRepr FloatInfoRepr SingleFloat       where knownRepr = SingleFloatRepr
instance KnownRepr FloatInfoRepr DoubleFloat       where knownRepr = DoubleFloatRepr
instance KnownRepr FloatInfoRepr QuadFloat         where knownRepr = QuadFloatRepr
instance KnownRepr FloatInfoRepr X86_80Float       where knownRepr = X86_80FloatRepr
instance KnownRepr FloatInfoRepr DoubleDoubleFloat where knownRepr = DoubleDoubleFloatRepr

instance KnownRepr TypeRepr AnyType             where knownRepr = AnyRepr
instance KnownRepr TypeRepr UnitType            where knownRepr = UnitRepr
instance KnownRepr TypeRepr CharType            where knownRepr = CharRepr
instance KnownRepr TypeRepr IntWidthType        where knownRepr = IntWidthRepr
instance KnownRepr TypeRepr UIntWidthType       where knownRepr = UIntWidthRepr
instance KnownRepr TypeRepr StringType          where knownRepr = StringRepr
instance KnownRepr TypeRepr MatlabIntType       where knownRepr = MatlabIntRepr
instance KnownRepr TypeRepr MatlabUIntType      where knownRepr = MatlabUIntRepr
instance KnownRepr TypeRepr MatlabIntArrayType  where knownRepr = MatlabIntArrayRepr
instance KnownRepr TypeRepr MatlabUIntArrayType where knownRepr = MatlabUIntArrayRepr
instance KnownRepr TypeRepr MatlabSymbolicIntArrayType where
  knownRepr = MatlabSymbolicIntArrayRepr
instance KnownRepr TypeRepr MatlabSymbolicUIntArrayType where
  knownRepr = MatlabSymbolicUIntArrayRepr

instance (Eq a, Ord a, Typeable a, Show a) => KnownRepr TypeRepr (ConcreteType a) where
  knownRepr = ConcreteRepr TypeableType

instance KnownRepr BaseTypeRepr bt => KnownRepr TypeRepr (BaseToType bt) where
  knownRepr = baseToType knownRepr

instance KnownCtx TypeRepr ctx => KnownRepr TypeRepr (StructType ctx) where
  knownRepr = StructRepr knownRepr

instance KnownCtx TypeRepr ctx => KnownRepr TypeRepr (VariantType ctx) where
  knownRepr = VariantRepr knownRepr

instance KnownRepr TypeRepr a => KnownRepr TypeRepr (ReferenceType a) where
  knownRepr = ReferenceRepr knownRepr

instance (KnownSymbol s, KnownCtx TypeRepr ctx) => KnownRepr TypeRepr (IntrinsicType s ctx) where
  knownRepr = IntrinsicRepr knownSymbol knownRepr

instance (KnownSymbol s, KnownCtx TypeRepr ctx, IsRecursiveType s) => KnownRepr TypeRepr (RecursiveType s ctx) where
  knownRepr = RecursiveRepr knownSymbol knownRepr

instance (1 <= w, KnownNat w, KnownRepr BaseTypeRepr tp)
      => KnownRepr TypeRepr (WordMapType w tp) where
  knownRepr = WordMapRepr (knownNat :: NatRepr w) (knownRepr :: BaseTypeRepr tp)

instance (KnownCtx TypeRepr ctx, KnownRepr TypeRepr ret)
      => KnownRepr TypeRepr (FunctionHandleType ctx ret) where
  knownRepr = FunctionHandleRepr knownRepr knownRepr

instance KnownRepr FloatInfoRepr flt => KnownRepr TypeRepr (FloatType flt) where
  knownRepr = FloatRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (VectorType tp) where
  knownRepr = VectorRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (MaybeType tp) where
  knownRepr = MaybeRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (StringMapType tp) where
  knownRepr = StringMapRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (MultiDimArrayType tp) where
  knownRepr = MultiDimArrayRepr knownRepr

instance KnownRepr BaseTypeRepr bt => KnownRepr TypeRepr (SymbolicMultiDimArrayType bt) where
  knownRepr = SymbolicMultiDimArrayRepr knownRepr


-- | Pattern synonym specifying bitvector TypeReprs.  Intended to be use
--   with type applications, e.g., @KnownBV \@32@.
pattern KnownBV :: forall n. (1 <= n, KnownNat n) => TypeRepr (BVType n)
pattern KnownBV <- BVRepr (testEquality (knownRepr :: NatRepr n) -> Just Refl)
  where KnownBV = knownRepr

------------------------------------------------------------------------
-- Misc typeclass instances

-- Force TypeRepr, etc. to be in context for next slice.
$(return [])

instance HashableF FloatInfoRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (FloatInfoRepr flt) where
  hashWithSalt = $(U.structuralHash [t|FloatInfoRepr|])

instance HashableF TypeRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (TypeRepr ty) where
  hashWithSalt = $(U.structuralHash [t|TypeRepr|])

instance Show (FloatInfoRepr flt) where
  showsPrec = $(U.structuralShowsPrec [t|FloatInfoRepr|])
instance ShowF FloatInfoRepr

instance Pretty (TypeRepr tp) where
  pretty = text . show

instance Show (TypeRepr tp) where
  showsPrec = $(U.structuralShowsPrec [t|TypeRepr|])
instance ShowF TypeRepr


instance TestEquality FloatInfoRepr where
  testEquality = $(U.structuralTypeEquality [t|FloatInfoRepr|] [])
instance OrdF FloatInfoRepr where
  compareF = $(U.structuralTypeOrd [t|FloatInfoRepr|] [])

instance TestEquality TypeableType where
  testEquality TypeableType TypeableType = eqT
instance OrdF TypeableType where
  compareF (TypeableType ::TypeableType x) (TypeableType :: TypeableType y) =
    case eqT of
      Just (Refl :: x :~: y) -> EQF
      _ -> case compare (typeRep (Proxy :: Proxy x)) (typeRep (Proxy :: Proxy y)) of
             LT -> LTF
             GT -> GTF
             EQ -> error "compareF for TypeableType: eqT disagrees with compare"
instance Hashable (TypeableType x) where
  hashWithSalt s (TypeableType :: TypeableType x) =
    case typeRepFingerprint (typeRep (Proxy :: Proxy x)) of
      Fingerprint f1 f2 -> hashWithSalt (hashWithSalt s f1) f2

instance Show (TypeableType x) where
  show TypeableType = show $ typeRep (Proxy :: Proxy x)

instance Eq (TypeableValue a) where
  TypeableValue a == TypeableValue b = a == b
instance Ord (TypeableValue a) where
  compare (TypeableValue a) (TypeableValue b) = compare a b

instance Show (TypeableValue a) where
  show (TypeableValue a) = show a
instance ShowF TypeableValue

instance TestEquality TypeableValue where
  testEquality (TypeableValue x :: TypeableValue xty) (TypeableValue y :: TypeableValue yty) =
    case eqT of
      Just (Refl :: xty :~: yty) ->
        if x == y then Just Refl else Nothing
      Nothing -> Nothing
instance OrdF TypeableValue where
  compareF (TypeableValue x :: TypeableValue xty) (TypeableValue y :: TypeableValue yty) =
    case eqT of
      Just (Refl :: xty :~: yty) ->
        case compare x y of
          EQ -> EQF
          LT -> LTF
          GT -> GTF
      _ -> case compare (typeRep (Proxy :: Proxy xty)) (typeRep (Proxy :: Proxy yty)) of
             LT -> LTF
             GT -> GTF
             EQ -> error "compareF for TypeableValue: eqT disagrees with compare"


instance TestEquality TypeRepr where
  testEquality = $(U.structuralTypeEquality [t|TypeRepr|]
                   [ (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|SymbolRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|FloatInfoRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|CtxRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|BaseTypeRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|TypeRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|TypeableType|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
                     , [|testEquality|])
                   ]
                  )

instance OrdF TypeRepr where
  compareF = $(U.structuralTypeOrd [t|TypeRepr|]
                   [ (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|SymbolRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|FloatInfoRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|BaseTypeRepr|])  U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|TypeRepr|])      U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|CtxRepr|])      U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|TypeableType|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
                     , [|compareF|])
                   ]
                  )
