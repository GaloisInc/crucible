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

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DefaultSignatures #-}




module Lang.Crucible.Types
  ( -- * CrucibleType data kind
    type CrucibleType
    -- ** Constructors for kind CrucibleType
  , AnyType
  , UnitType
  , BoolType
  , NatType
  , IntegerType
  , RealValType
  , SymbolicStructType
  , ComplexRealType
  , BVType
  , FloatType
  , IEEEFloatType
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

  , StringMapType
  , SymbolicArrayType

    -- * Parameterized types
  , VarType
  , PolyFnType
  , Closed(..)
  , Instantiate
  , InstantiateF(..)
  , InstantiateFC(..)
  , InstantiateType(..)
  , composeInstantiateAxiom
  , closedInstantiate
  , closedInstantiateF
  , closedInstantiateFC

  -- ** Evidence for closedness
  , assumeClosed
  , checkClosed
  , checkClosedCtx

    -- * IsRecursiveType
  , IsRecursiveType(..)

    -- * Base type injection
  , BaseToType
  , baseToType

  , AsBaseType(..)
  , asBaseType

    -- * Other stuff
  , CtxRepr
  , pattern KnownBV

    -- * Representation of Crucible types
  , TypeRepr(..)

    -- * Re-exports
  , module Data.Parameterized.Ctx
  , module Data.Parameterized.NatRepr
  , module Data.Parameterized.SymbolRepr
  , module What4.BaseTypes
  , FloatInfo
  , HalfFloat
  , SingleFloat
  , DoubleFloat
  , QuadFloat
  , X86_80Float
  , DoubleDoubleFloat
  , FloatInfoRepr(..)
  , FloatInfoToBitWidth
  , floatInfoToBVTypeRepr
  ) where

import           Data.Constraint (Dict(..))
import           Data.Hashable
import           Data.Kind
import           Data.Type.Equality
import           GHC.TypeLits
import           Data.Type.Bool
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.TH.GADT as U
import           Text.PrettyPrint.ANSI.Leijen

import           What4.BaseTypes
import           What4.InterpretedFloatingPoint



-- GHC.TypeLits is under-powered, plus other axioms
import           Unsafe.Coerce (unsafeCoerce)

------------------------------------------------------------------------
-- Crucible types


-- | This typeclass is used to register recursive Crucible types
--   with the compiler.  This class defines, for a given symbol,
--   both the type-level and the representative-level unrolling
--   of a named recursive type.
--
--   The symbol constitutes a unique compile-time identifier for the
--   recursive type, allowing recursive types to be unrolled at run
--   time without requiring dynamic checks.
--
--   Parameter @nm@ has kind 'Symbol'.
--
--   If polymorphism is required, then 'eqInstUnroll' must be defined
--   to prove that the rhs of the UnrollType does not include any type
--   variables that were not already present in the ctx argument.
--   (This is equivalent to the constraint "Closed (UnrollType nm)" but
--   we cannot partially apply a type family.)
--   Languages that do not use polymorphism can use the default instance
class IsRecursiveType (nm::Symbol) where
  type UnrollType nm (ctx :: Ctx CrucibleType) :: CrucibleType
  unrollType   :: SymbolRepr nm -> CtxRepr ctx -> TypeRepr (UnrollType nm ctx)

  eqInstUnroll :: proxy subst
               -> Instantiate subst (UnrollType nm ctx) :~: UnrollType nm (Instantiate subst ctx)
  eqInstUnroll _ = error "eqInstUnroll: use of instantiate requires proof"

type CtxRepr = Ctx.Assignment TypeRepr

-- | This data kind describes the types of values and expressions that
--   can occur in Crucible CFGs.
data CrucibleType where
   -- | An injection of solver interface types into Crucible types
   BaseToType :: BaseType -> CrucibleType

   -- | A dynamic type that can contain values of any type.
   AnyType :: CrucibleType

   -- | A type containing a single value "Unit"
   UnitType :: CrucibleType
   -- | A type index for floating point numbers, whose interpretation
   --   depends on the symbolic backend.
   FloatType :: FloatInfo -> CrucibleType
   -- | A single character, as a 16-bit wide char.
   CharType :: CrucibleType
   -- | A function handle taking a context of formal arguments and a return type
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

   -- Named recursive types, named by the given symbol.  To use recursive types
   -- you must provide an instances of the IsRecursiveType class that gives
   -- the unfolding of this recursive type.  The RollRecursive and UnrollRecursive
   -- operations witness the isomorphism between a recursive type and its one-step
   -- unrolling.  Similar to Haskell's newtype, recursive types do not necessarily
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

   -- A partial map from strings to values.
   StringMapType :: CrucibleType -> CrucibleType


   -- A type variable, represented as an index and quantified by an enclosing 'PolyFnType'
   VarType :: Nat -> CrucibleType
   
   -- A polymorphic function type consisting of a list of argument types and a result type.
   -- Must be instantiated before use. Binds *all* type variables in the argument and
   -- result types.
   PolyFnType :: Ctx CrucibleType -> CrucibleType -> CrucibleType

type BaseToType      = 'BaseToType                -- ^ @:: 'BaseType' -> 'CrucibleType'@.
type BoolType        = BaseToType BaseBoolType    -- ^ @:: 'CrucibleType'@.
type BVType w        = BaseToType (BaseBVType w)  -- ^ @:: 'Nat' -> 'CrucibleType'@.
type ComplexRealType = BaseToType BaseComplexType -- ^ @:: 'CrucibleType'@.
type IntegerType     = BaseToType BaseIntegerType -- ^ @:: 'CrucibleType'@.
type StringType      = BaseToType BaseStringType  -- ^ @:: 'CrucibleType'@.
type NatType         = BaseToType BaseNatType     -- ^ @:: 'CrucibleType'@.
type RealValType     = BaseToType BaseRealType    -- ^ @:: 'CrucibleType'@.
type IEEEFloatType p = BaseToType (BaseFloatType p) -- ^ @:: FloatPrecision -> CrucibleType@

type SymbolicArrayType idx xs = BaseToType (BaseArrayType idx xs) -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType' -> 'CrucibleType'@.
type SymbolicStructType flds = BaseToType (BaseStructType flds) -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'CrucibleType'@.


-- | A dynamic type that can contain values of any type.
type AnyType  = 'AnyType  -- ^ @:: 'CrucibleType'@.

-- | A single character, as a 16-bit wide char.
type CharType = 'CharType -- ^ @:: 'CrucibleType'@.

-- | A type index for floating point numbers, whose interpretation
--   depends on the symbolic backend.
type FloatType    = 'FloatType    -- ^ @:: 'FloatInfo' -> 'CrucibleType'@.


-- | A function handle taking a context of formal arguments and a return type.
type FunctionHandleType = 'FunctionHandleType -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType' -> 'CrucibleType'@.

-- | Named recursive types, named by the given symbol. To use
-- recursive types you must provide an instance of the
-- 'IsRecursiveType' class that gives the unfolding of this recursive
-- type. The 'Lang.Crucible.CFG.Expr.RollRecursive' and
-- 'Lang.Crucible.CFG.Expr.UnrollRecursive' operations witness the
-- isomorphism between a recursive type and its one-step unrolling.
-- Similar to Haskell's @newtype@, recursive types do not necessarily
-- have to mention the recursive type being defined; in which case,
-- the type is simply a new named type which is isomorphic to its
-- definition.
type RecursiveType = 'RecursiveType -- ^ @:: 'Symbol' -> 'Ctx' 'CrucibleType' -> 'CrucibleType'@.

-- | Named intrinsic types. Intrinsic types are a way to extend the
-- Crucible type system after-the-fact and add new type
-- implementations. Core Crucible provides no operations on intrinsic
-- types; they must be provided as built-in override functions. See
-- the 'Lang.Crucible.Simulator.Intrinsics.IntrinsicClass' typeclass
-- and the 'Lang.Crucible.Simulator.Intrinsics.Intrinsic' type family
-- defined in "Lang.Crucible.Simulator.Intrinsics".
type IntrinsicType ctx = 'IntrinsicType ctx -- ^ @:: 'Symbol' -> 'Ctx' 'CrucibleType' -> 'CrucibleType'@.

-- | The type of mutable reference cells.
type ReferenceType = 'ReferenceType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | The 'Maybe' type lifted into Crucible expressions.
type MaybeType = 'MaybeType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A partial map from strings to values.
type StringMapType = 'StringMapType -- ^ @:: 'CrucibleType' -> 'CrucibleType'@.

-- | A structure is an aggregate type consisting of a sequence of
-- values. The type of each value is known statically.
type StructType = 'StructType -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType'@.

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

-- | A type variable, represented as an index
type VarType       = 'VarType -- ^ @:: 'Nat' -> 'CrucubleType'@

-- | A polymorphic function type
type PolyFnType      = 'PolyFnType  -- ^ @:: 'Ctx' 'CrucibleType' -> 'CrucibleType' -> 'CrucibleType'@.

----------------------------------------------------------------
-- Base Type Injection

baseToType :: BaseTypeRepr bt -> TypeRepr (BaseToType bt)
baseToType bt =
  case bt of
    BaseBoolRepr -> BoolRepr
    BaseIntegerRepr -> IntegerRepr
    BaseNatRepr -> NatRepr
    BaseRealRepr -> RealValRepr
    BaseStringRepr -> StringRepr
    BaseBVRepr w -> BVRepr w
    BaseComplexRepr -> ComplexRealRepr
    BaseArrayRepr idx xs -> SymbolicArrayRepr idx xs
    BaseStructRepr flds -> SymbolicStructRepr flds
    BaseFloatRepr ps -> IEEEFloatRepr ps

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
    StringRepr -> AsBaseType BaseStringRepr
    BVRepr w -> AsBaseType (BaseBVRepr w)
    ComplexRealRepr -> AsBaseType BaseComplexRepr
    SymbolicArrayRepr idx xs ->
      AsBaseType (BaseArrayRepr idx xs)
    IEEEFloatRepr ps ->
      AsBaseType (BaseFloatRepr ps)
    SymbolicStructRepr flds -> AsBaseType (BaseStructRepr flds)
    _ -> NotBaseType


    




----------------------------------------------------------------
-- Type representatives

-- | A family of representatives for Crucible types. Parameter @tp@
-- has kind 'CrucibleType'.
data TypeRepr (tp::CrucibleType) where
   AnyRepr :: TypeRepr AnyType
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
   IEEEFloatRepr :: !(FloatPrecisionRepr ps) -> TypeRepr (IEEEFloatType ps)
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

   StringMapRepr :: !(TypeRepr tp) -> TypeRepr (StringMapType tp)

   SymbolicArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx::>tp))
                     -> !(BaseTypeRepr t)
                     -> TypeRepr (SymbolicArrayType (idx::>tp) t)

   -- A reference to a symbolic struct.
   SymbolicStructRepr :: Ctx.Assignment BaseTypeRepr ctx
                      -> TypeRepr (SymbolicStructType ctx)
   
   VarRepr :: !(NatRepr n) -> TypeRepr (VarType n)
   PolyFnRepr :: !(CtxRepr args) -> !(TypeRepr ret) -> TypeRepr (PolyFnType args ret)
------------------------------------------------------------------------------
-- Representable class instances

instance KnownRepr TypeRepr AnyType             where knownRepr = AnyRepr
instance KnownRepr TypeRepr UnitType            where knownRepr = UnitRepr
instance KnownRepr TypeRepr CharType            where knownRepr = CharRepr

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

instance KnownRepr FloatPrecisionRepr ps => KnownRepr TypeRepr (IEEEFloatType ps) where
  knownRepr = IEEEFloatRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (VectorType tp) where
  knownRepr = VectorRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (MaybeType tp) where
  knownRepr = MaybeRepr knownRepr

instance KnownRepr TypeRepr tp => KnownRepr TypeRepr (StringMapType tp) where
  knownRepr = StringMapRepr knownRepr

instance KnownNat w => KnownRepr TypeRepr (VarType w) where
  knownRepr = VarRepr knownRepr

instance (KnownRepr CtxRepr args, KnownRepr TypeRepr ret)
      => KnownRepr TypeRepr (PolyFnType args ret) where
  knownRepr = PolyFnRepr knownRepr knownRepr
  

-- | Pattern synonym specifying bitvector TypeReprs.  Intended to be use
--   with type applications, e.g., @KnownBV \@32@.
pattern KnownBV :: forall n. (1 <= n, KnownNat n) => TypeRepr (BVType n)
pattern KnownBV <- BVRepr (testEquality (knownRepr :: NatRepr n) -> Just Refl)
  where KnownBV = knownRepr


------------------------------------------------------------------------
-- | Classes and type families for polymorphism

-- | Type-level substitution function.
-- Uses a Ctx of types to replace the type variables 0 .. n occurring in a type-level
-- expression.
-- This is an open type family that is homeomorphic on most arguments
-- The only exception is for CrucibleTypes, see InstantiateCT
--
-- NOTE: it is tempting to make this a closed type family that dispatches to
-- InstantiateCT when k is CrucibleType and is defined homeomorphically elsewhere.
-- This would remove many instances of the form
--    type instance Instantiate subst T = T
-- However, this approach doesn't work for (ext :: Type). We don't know that
-- all of the potential ext types do not contain CrucibleType as a subterm, so
-- GHC cannot reduce (Instantiate subst ext) = ext.
-- Using GHC-8.6 quantified constraints, we might be able to express this 
-- restriction, but I have not tried it. Until that time, if your code doesn't
-- type check, add an instance like the above.
type family Instantiate  (subst :: Ctx CrucibleType) (v :: k) :: k

-- | Class of types and types that support instantiation
class InstantiateType (ty :: Type) where
  instantiate :: CtxRepr subst -> ty -> Instantiate subst ty

-- | Defines instantiation for SyntaxExtension (must create an instance of this
-- class, but instance can be trivial if polymorphism is not used.
class InstantiateF (t :: k -> Type) where
  instantiateF :: CtxRepr subst -> t a -> (Instantiate subst t) (Instantiate subst a)
  instantiateF _ _ = error "instantiateF: must be defined to use polymorphism"

-- | Also for syntax extensions
class InstantiateFC (t :: (k -> Type) -> l -> Type) where
  instantiateFC :: InstantiateF a => CtxRepr subst -> t a b -> Instantiate subst (t a b)
  instantiateFC _ _ = error "instantiateFC: must be defined to use polymorphism"

-- | Types that do not contain any free type variables. If they are closed
-- then we know that instantiation does nothing.
-- The proxy allows us to specify the 'subst' argument without using a type
-- application.
class Closed (t :: k) where
  closed :: proxy subst -> Instantiate subst t :~: t
  closed = error "closed: must define closed to use instantiation"
  

-- Types that are statically known to be closed can benefit from the following
-- default definitions for InstantiateType, InstantiateF and InstantiateFC

closedInstantiate :: forall ty subst. Closed ty => CtxRepr subst -> ty -> Instantiate subst ty
closedInstantiate subst | Refl <- closed @_ @ty subst = id
   -- NOTE: closed is polykinded so first specified type argument is the kind of ty

closedInstantiateF :: forall t0 a subst. (Closed t0, Closed a)
  => CtxRepr subst -> t0 a -> (Instantiate subst t0) (Instantiate subst a)
closedInstantiateF s | Refl <- closed @_ @t0 s, Refl <- closed @_ @a s = id
  
closedInstantiateFC :: forall t0 a b subst. (Closed t0, Closed a, Closed b, InstantiateF a)
  => CtxRepr subst -> t0 a b -> (Instantiate subst t0) (Instantiate subst a) (Instantiate subst b)
closedInstantiateFC s | Refl <- closed @_ @t0 s, Refl <- closed @_ @a s, Refl <- closed @_ @b s = id
  
------------------------------------------------------------------------
------------------------------------------------------------------------
-- Force TypeRepr, etc. to be in context for next slice.
$(return [])

------------------------------------------------------------------------
-- Misc typeclass instances


instance HashableF TypeRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (TypeRepr ty) where
  hashWithSalt = $(U.structuralHash [t|TypeRepr|])

instance Pretty (TypeRepr tp) where
  pretty = text . show

instance Show (TypeRepr tp) where
  showsPrec = $(U.structuralShowsPrec [t|TypeRepr|])
instance ShowF TypeRepr


instance TestEquality TypeRepr where
  testEquality = $(U.structuralTypeEquality [t|TypeRepr|]
                   [ (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|SymbolRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|FloatInfoRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|FloatPrecisionRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|CtxRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|BaseTypeRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.ConType [t|TypeRepr|]) U.AnyType, [|testEquality|])
                   , (U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
                     , [|testEquality|])
                   ]
                  )

instance OrdF TypeRepr where
  compareF = $(U.structuralTypeOrd [t|TypeRepr|]
                   [ (U.TypeApp (U.ConType [t|NatRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|SymbolRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|FloatInfoRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|FloatPrecisionRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|BaseTypeRepr|])  U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|TypeRepr|])      U.AnyType, [|compareF|])
                   , (U.TypeApp (U.ConType [t|CtxRepr|])      U.AnyType, [|compareF|])
                   , (U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
                     , [|compareF|])
                   ]
                  )


----------------------------------------------------------------
-- "Closed" instances

instance Closed (b :: BaseType) where
  closed _ = unsafeCoerce Refl -- don't want to do a runtime case analysis
instance Closed (ctx :: Ctx BaseType) where
  closed _ = unsafeCoerce Refl  -- don't want to do induction over the list

-- k = Type
instance Closed (BaseTypeRepr b :: Type) where
  closed p | Refl <- closed @_ @b p = Refl 
instance Closed () where closed _ = Refl
  
-- k = CrucibleType  
instance Closed (BaseToType b) where closed _ = Refl
instance Closed AnyType where closed _ = Refl
instance Closed UnitType where closed _ = Refl
instance Closed CharType where closed _ = Refl
instance Closed (FloatType fi) where closed _ = Refl
instance (Closed args, Closed ret) => Closed (FunctionHandleType args ret)
  where
    closed p | Refl <- closed @_ @args p, Refl <- closed @_ @ret p = Refl
instance (Closed ty) => Closed (MaybeType ty)
  where
    closed p | Refl <- closed @_ @ty p = Refl
instance (Closed ty) => Closed (VectorType ty)
  where
    closed p | Refl <- closed @_ @ty p = Refl
instance (Closed ctx) => Closed (StructType ctx)
  where
    closed p | Refl <- closed @_ @ctx p = Refl
instance (Closed ty) => Closed (ReferenceType ty)
  where
    closed p | Refl <- closed @_ @ty p = Refl
instance (Closed ctx) => Closed (VariantType ctx)
  where
    closed p | Refl <- closed @_ @ctx p = Refl
instance (Closed (WordMapType n b)) where closed _ = Refl
instance (Closed ctx) => Closed (RecursiveType sym ctx)
  where
    closed p | Refl <- closed @_ @ctx p = Refl
instance (Closed ctx) => Closed (IntrinsicType sym ctx)
  where
    closed p | Refl <- closed @_ @ctx p = Refl
instance (Closed ty)  => Closed (StringMapType ty) 
  where
    closed p | Refl <- closed @_ @ty p = Refl
instance (Closed (PolyFnType args ret)) where closed _ = Refl
instance (Closed EmptyCtx) where closed _ = Refl
instance (Closed ty, Closed ctx) => Closed (ctx ::> ty)
 where
    closed p | Refl <- closed @_ @ctx p, Refl <- closed @_ @ty p = Refl
         

newtype Gift a r = Gift (Closed a => r)

-- | "assume" that a type is closed, without evidence
assumeClosed :: forall a b. (Closed a => b) -> b
assumeClosed k = unsafeCoerce (Gift k :: Gift a b)
                       (error "No instance of Closed provided")

-- | Attempt to construct evidence that a context is closed, assuming
-- the invariant that type variables are well-scoped.
checkClosedCtx :: CtxRepr ts -> Maybe (Dict (Closed ts))
checkClosedCtx ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Just Dict
    Ctx.AssignExtend ts t ->
      do Dict <- checkClosedCtx ts
         Dict <- checkClosed t
         Just Dict

-- | Attempt to construct evidence that a type is closed, assuming
-- the invariant that type variables are well-scoped.
checkClosed :: TypeRepr t -> Maybe (Dict (Closed t))
checkClosed AnyRepr = Just Dict
checkClosed UnitRepr = Just Dict
checkClosed BoolRepr = Just Dict
checkClosed NatRepr = Just Dict
checkClosed IntegerRepr = Just Dict
checkClosed RealValRepr = Just Dict
checkClosed ComplexRealRepr = Just Dict
checkClosed (BVRepr _) = Just Dict
checkClosed (IntrinsicRepr _ args) =
  do Dict <- checkClosedCtx args
     Just Dict
checkClosed (RecursiveRepr _ ctx) =
  do Dict <- checkClosedCtx ctx
     Just Dict
checkClosed (FloatRepr _) = Just Dict
checkClosed (IEEEFloatRepr _) = Just Dict
checkClosed CharRepr = Just Dict
checkClosed StringRepr = Just Dict
checkClosed (FunctionHandleRepr args ret) =
  do Dict <- checkClosedCtx args
     Dict <- checkClosed ret
     Just Dict
checkClosed (MaybeRepr t) =
  do Dict <- checkClosed t
     Just Dict
checkClosed (VectorRepr t) =
  do Dict <- checkClosed t
     Just Dict
checkClosed (StructRepr fields) =
  do Dict <- checkClosedCtx fields
     Just Dict
checkClosed (VariantRepr cases) =
  do Dict <- checkClosedCtx cases
     Just Dict
checkClosed (ReferenceRepr t) =
  do Dict <- checkClosed t
     Just Dict
checkClosed (WordMapRepr _ _) = Just Dict
checkClosed (StringMapRepr t) =
  do Dict <- checkClosed t
     Just Dict
checkClosed (SymbolicArrayRepr _ _) = Just Dict
checkClosed (SymbolicStructRepr _) = Just Dict
checkClosed (VarRepr _) = Nothing
checkClosed (PolyFnRepr _ _) = Just Dict -- Can this possibly be right?


--------------------------------------------------------------------------------
-- Instantiate/InstantiateType/InstantiateF/InstantiateFC instances

-- This is a property of the Instantiate type family. However, Haskell's type system
-- is too weak to prove it automatically. (And we don't want to run any proofs either.)
-- Maybe a quantified constraint would help?
composeInstantiateAxiom :: forall subst subst1 x.
  Instantiate subst (Instantiate subst1 x) :~: Instantiate (Instantiate subst subst1) x
composeInstantiateAxiom = unsafeCoerce Refl



type instance Instantiate subst (v :: CrucibleType) = InstantiateCT subst v
type family InstantiateCT (subst :: Ctx CrucibleType) (v :: CrucibleType) :: CrucibleType where
  InstantiateCT subst (BaseToType b) = BaseToType b
  InstantiateCT subst AnyType  = AnyType
  InstantiateCT subst UnitType = UnitType
  InstantiateCT subst (FloatType fi) = FloatType fi
  InstantiateCT subst CharType = CharType
  InstantiateCT subst (FunctionHandleType args ret) =
     FunctionHandleType (Instantiate subst args ) (Instantiate subst ret)
  InstantiateCT subst (MaybeType ty) = MaybeType (Instantiate subst ty )
  InstantiateCT subst (VectorType ty) = VectorType (Instantiate subst ty)
  InstantiateCT subst (StructType ctx) = StructType (Instantiate subst ctx)
  InstantiateCT subst (ReferenceType ty) = ReferenceType (Instantiate subst ty)
  InstantiateCT subst (VariantType ctx) = VariantType (Instantiate subst ctx)
  InstantiateCT subst (WordMapType n b) = WordMapType n b
  InstantiateCT subst (RecursiveType sym ctx) = RecursiveType sym (Instantiate subst ctx)
  InstantiateCT subst (IntrinsicType sym ctx) = IntrinsicType sym (Instantiate subst ctx)
  InstantiateCT subst (StringMapType ty) = StringMapType (Instantiate subst ty)
  InstantiateCT subst (VarType i) = LookupVarType i subst (VarType i)
  InstantiateCT subst (PolyFnType args ret) = PolyFnType args ret
-- helper definition for VarType instance
type family LookupVarType (n :: Nat) (subst :: Ctx CrucibleType) (def :: CrucibleType) :: CrucibleType where
  LookupVarType n (ctx ::> ty) def = If (n <=? 0) ty (LookupVarType (n - 1) ctx def)
  LookupVarType n EmptyCtx     def = def
  

-- TypeCon apps

instance (InstantiateF t) => InstantiateType (t a) where
  instantiate = instantiateF
instance (InstantiateFC t, InstantiateF a) => InstantiateF (t a) where
  instantiateF = instantiateFC

-- k = Type (needed for trivial syntax extensions)
type instance Instantiate subst () = ()
type instance Instantiate subst (a b :: Type) = Instantiate subst a (Instantiate subst b)
type instance Instantiate subst (a b :: k -> Type) = Instantiate subst a (Instantiate subst b)
type instance Instantiate subst (a b :: k -> l -> Type) = Instantiate subst a (Instantiate subst b)


-- Ctx & Assignment

-- k = (k' -> Type) -> Ctx k' -> Type
type instance Instantiate subst Ctx.Assignment = Ctx.Assignment

-- k = Ctx k'
type instance Instantiate subst EmptyCtx = EmptyCtx
type instance Instantiate subst (ctx ::> ty) = Instantiate subst ctx ::> Instantiate subst ty

-- Ctx.Assignment :: (k -> Type) -> Ctx k -> Type
instance InstantiateFC Ctx.Assignment where
  instantiateFC _subst Ctx.Empty = Ctx.Empty
  instantiateFC subst (ctx Ctx.:> ty) = instantiate subst ctx Ctx.:> instantiate subst ty


-- Ctx.Index :: Ctx k -> CrucibleType -> Type
-- Ctx.Index is just a number
type instance Instantiate subst Ctx.Index = Ctx.Index 
instance InstantiateF (Ctx.Index ctx) where
  instantiateF _subst idx = unsafeCoerce idx



-- BaseTypeRepr
type instance Instantiate subst BaseTypeRepr = BaseTypeRepr
instance InstantiateF BaseTypeRepr where
  instantiateF subst (r :: BaseTypeRepr bt)
    | Refl <- closed @_ @bt subst
    = r


-- k = CrucibleType


-- TypeRepr
type instance Instantiate subst TypeRepr = TypeRepr 
instance InstantiateF TypeRepr where
  instantiateF = instantiateRepr
  
instantiateRepr :: CtxRepr subst -> TypeRepr ty -> TypeRepr (Instantiate subst ty)
instantiateRepr _subst BoolRepr = BoolRepr
instantiateRepr _subst NatRepr = NatRepr
instantiateRepr _subst IntegerRepr = IntegerRepr
instantiateRepr _ubst RealValRepr = RealValRepr
instantiateRepr _subst StringRepr = StringRepr
instantiateRepr _subst (BVRepr w) = BVRepr w
instantiateRepr _subst ComplexRealRepr = ComplexRealRepr 
instantiateRepr _subst (SymbolicArrayRepr idx w) = SymbolicArrayRepr idx w
instantiateRepr _subst (SymbolicStructRepr flds) = SymbolicStructRepr flds
instantiateRepr _subst (IEEEFloatRepr ps) = IEEEFloatRepr ps
instantiateRepr _subst AnyRepr  = AnyRepr
instantiateRepr _subst UnitRepr = UnitRepr
instantiateRepr _subst (FloatRepr fi) = FloatRepr fi
instantiateRepr _subst CharRepr = CharRepr
instantiateRepr subst (FunctionHandleRepr args ret) =
    FunctionHandleRepr (instantiate subst args ) (instantiateRepr subst ret)
instantiateRepr subst (MaybeRepr ty) =
    MaybeRepr (instantiateRepr subst ty )
instantiateRepr subst (VectorRepr ty) = VectorRepr (instantiateRepr subst ty)
instantiateRepr subst (StructRepr ctx) = StructRepr (instantiate subst ctx)
instantiateRepr subst (ReferenceRepr ty) = ReferenceRepr (instantiateRepr subst ty)
instantiateRepr subst (VariantRepr ctx) = VariantRepr (instantiate subst ctx)
instantiateRepr _subst (WordMapRepr n b) = WordMapRepr n b
instantiateRepr subst (RecursiveRepr sym0 ctx) = RecursiveRepr sym0 (instantiate subst ctx)
instantiateRepr subst (IntrinsicRepr sym0 ctx) = IntrinsicRepr sym0 (instantiate subst ctx)
instantiateRepr subst (StringMapRepr ty) = StringMapRepr (instantiateRepr subst ty)
instantiateRepr subst (VarRepr i) = lookupVarRepr i subst (VarRepr i)
instantiateRepr _subst (PolyFnRepr args ty) = PolyFnRepr args ty


-- NOTE: We need the equality below to typecheck lookupVarRepr.
-- 
-- However, TypeNatSolver cannot prove this equality, even though all
-- of the pieces that we need are available --- something about
-- putting them together with the type family LookupVarType above.
--
-- Furthermore, we cannot actually use this axiom in the definition of
-- lookupVarRepr because the datatype IsZeroNat does not allow
-- binding the type variable that is the predecessor of n (e.g.
-- through a Proxy argument). As we cannot name this type variable, we
-- cannot invoke the axiom.

{- 
axiom1 :: forall n ctx ty .
   (LookupVarType (n + 1) (ctx ::> ty) :~: LookupVarType n ctx)
axiom1 = Refl
-}

-- I am commenting these out so that we don't need to add 
-- {-# OPTIONS_GHC -fplugin TypeNatSolver #-}
-- to the top of this file and 
-- type-nat-solver package to crucible.cabal, and
-- dependencies/type-nat-solver/ to cabal.project, and
-- git submodule add https://github.com/yav/type-nat-solver
{-
axiom2 :: forall n. (n + 1) - 1 :~: n
axiom2 = Refl

axiom3 :: forall n. ((n + 1) <=? 0) :~: 'False
axiom3 = Refl
-}

-- see comments above for justification for [unsafeCoerce] in this function
lookupVarRepr :: NatRepr i -> CtxRepr ctx -> TypeRepr def -> TypeRepr (LookupVarType i ctx def)
lookupVarRepr n ((ctx :: CtxRepr ctx) Ctx.:> (ty::TypeRepr ty)) def =
  case isZeroNat n of
    ZeroNat    -> ty
    NonZeroNat ->
      --  (LookupVarType (n + 1) (ctx ::> ty) :~: LookupVarType n ctx)
      unsafeCoerce (lookupVarRepr (predNat n) ctx def)
lookupVarRepr _n Ctx.Empty def = def
