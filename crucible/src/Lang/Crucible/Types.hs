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
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE TypeInType #-}

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
  , Closed
  , ClosedK(..)
  , Instantiate
  , Liftn
  , liftn
  , InstantiateF(..)
  , InstantiateFC(..)
  , InstantiateType(..)
  , composeInstantiateAxiom
  , swapMkSubstAxiom
  , closedInstantiate
  , closedInstantiateF
  , closedInstantiateFC

  -- ** Substitutions
  , Substitution
  , SubstRepr
  , Compose
  , compose
  , MkSubst
  , mkSubst

  -- ** Peano numbers
  , Peano
  , PeanoView(..)
  , peanoView
  , PeanoRepr(..)

  -- ** Evidence for closedness
  , Dict(..)
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

import           Data.Proxy(Proxy(..))
import           Data.Constraint (Dict(..))
import           Data.Hashable
import           Data.Kind
import           Data.Type.Equality

import           GHC.TypeLits
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Peano
import           Data.Parameterized.SymbolRepr
import qualified Data.Parameterized.TH.GADT as U
import           Text.PrettyPrint.ANSI.Leijen

import           Lang.Crucible.Substitution

import           What4.BaseTypes
import           What4.InterpretedFloatingPoint


import           Unsafe.Coerce (unsafeCoerce)

------------------------------------------------------------------------
-- Crucible types

type Closed    = ClosedK CrucibleType
type SubstRepr = SubstReprK CrucibleType
type Substitution = SubstK CrucibleType

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
--   Languages that do not use polymorphism may use the default instance
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
   VarType :: Peano -> CrucibleType
   
   -- A polymorphic function type consisting of a number of bound variables (n),
   -- a list of argument types and a result type.
   -- Must be instantiated before use. Binds n variables in the argument and
   -- result types.
   PolyFnType :: Peano -> Ctx CrucibleType -> CrucibleType -> CrucibleType

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
   
   VarRepr :: !(PeanoRepr n) -> TypeRepr (VarType n)
   PolyFnRepr :: !(PeanoRepr n) ->  !(CtxRepr args) -> !(TypeRepr ret) -> TypeRepr (PolyFnType n args ret)

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

instance KnownRepr PeanoRepr w => KnownRepr TypeRepr (VarType w) where
  knownRepr = VarRepr knownRepr

instance (KnownRepr PeanoRepr n, KnownRepr CtxRepr args, KnownRepr TypeRepr ret)
      => KnownRepr TypeRepr (PolyFnType n args ret) where
  knownRepr = PolyFnRepr knownRepr knownRepr knownRepr
  

-- | Pattern synonym specifying bitvector TypeReprs.  Intended to be use
--   with type applications, e.g., @KnownBV \@32@.
pattern KnownBV :: forall n. (1 <= n, KnownNat n) => TypeRepr (BVType n)
pattern KnownBV <- BVRepr (testEquality (knownRepr :: NatRepr n) -> Just Refl)
  where KnownBV = knownRepr

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
                   , (U.TypeApp (U.ConType [t|PeanoRepr|]) U.AnyType, [|testEquality|])
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
                   , (U.TypeApp (U.ConType [t|PeanoRepr|]) U.AnyType, [|compareF|])
                   , (U.TypeApp (U.TypeApp (U.ConType [t|Ctx.Assignment|]) U.AnyType) U.AnyType
                     , [|compareF|])
                   ]
                  )

----------------------------------------------------------------
-- "Closed" instances

instance ClosedK CrucibleType (b :: BaseType) where
  closed _ _ = unsafeCoerce Refl -- don't want to do a runtime case analysis

instance ClosedK CrucibleType (ctx :: Ctx BaseType) where
  closed _ _ = unsafeCoerce Refl  -- don't want to do induction over the list

-- k = Type
instance ClosedK CrucibleType (BaseTypeRepr b :: Type) where
  closed _ p | Refl <- closed (Proxy :: Proxy b) p = Refl 

-- k = CrucibleType  
instance ClosedK CrucibleType (BaseToType b) where closed _ _ = Refl
instance ClosedK CrucibleType AnyType where closed _ _ = Refl
instance ClosedK CrucibleType UnitType where closed _ _ = Refl
instance ClosedK CrucibleType CharType where closed _ _ = Refl
instance ClosedK CrucibleType (FloatType fi) where closed _ _ = Refl

instance (Closed args, Closed ret) => ClosedK CrucibleType (FunctionHandleType args ret)
  where
    closed __ p1 | Refl <- closed (Proxy :: Proxy args) p1, Refl <- closed (Proxy :: Proxy ret) p1 = Refl


instance (Closed ty) => ClosedK CrucibleType (MaybeType ty)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ty) p1 = Refl
    
instance (Closed ty) => ClosedK CrucibleType (VectorType ty)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ty) p1 = Refl
    
instance (Closed ctx) => ClosedK CrucibleType (StructType ctx)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ctx) p1 = Refl

instance (Closed ty) => ClosedK CrucibleType (ReferenceType ty)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ty) p1 = Refl

instance (Closed ctx) => ClosedK CrucibleType (VariantType ctx)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ctx) p1 = Refl
    
instance (ClosedK CrucibleType (WordMapType n b)) where closed _ _ = Refl

instance (ClosedK CrucibleType ctx) => ClosedK CrucibleType (RecursiveType sym ctx)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ctx) p1 = Refl
    
instance (ClosedK CrucibleType ctx) => ClosedK CrucibleType (IntrinsicType sym ctx)
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ctx) p1 = Refl
    
instance (ClosedK CrucibleType ty)  => ClosedK CrucibleType (StringMapType ty) 
  where
    closed _ p1 | Refl <- closed (Proxy :: Proxy ty) p1 = Refl
-- note: No instance for PolyFnType
-- we would need to index the type class with the binding level
-- to do this.


newtype Gift a r = Gift (Closed a => r)

-- | "assume" that a type is closed, without evidence
assumeClosed :: forall a b. (Closed a => b) -> b
assumeClosed k = unsafeCoerce (Gift k :: Gift a b)
                       (error "No instance of Closed provided")


-- | Attempt to construct evidence that a context is closed, assuming
-- the invariant that type variables are well-scoped.

checkClosedCtx :: CtxRepr ts -> Maybe (Dict (ClosedK CrucibleType ts))
checkClosedCtx = checkClosedAssignment checkClosed 


-- | Attempt to construct evidence that a type is closed, assuming
-- the invariant that type variables are well-scoped.
checkClosed :: TypeRepr t -> Maybe (Dict (ClosedK CrucibleType t))
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
checkClosed (PolyFnRepr _ _ _) = Nothing -- conservative!!! 


--------------------------------------------------------------------------------
-- Instantiate/InstantiateType/InstantiateF/InstantiateFC instances

-- This is a property of the Instantiate type family. However, Haskell's type system
-- is too weak to prove it automatically. (And we don't want to run any proofs either.)
-- I have proven it in Coq.
composeInstantiateAxiom :: forall subst2 subst1 x.
  Instantiate subst1 (Instantiate subst2 x) :~:
  Instantiate (Compose subst1 subst2) x
composeInstantiateAxiom = unsafeCoerce Refl

-- We need this property in Expr.hs to show that type substitution in the case
-- of type instantiation type checks. It allows us to commute the
-- instantiation of the polymorphic function with the substitution. 
swapMkSubstAxiom :: forall sub k targs x.
  -- (CtxSize targs ~ k) =>   -- TODO: add this constraint
  Instantiate sub (Instantiate (MkSubst targs) x) :~: 
  Instantiate (MkSubst (Instantiate sub targs)) (Instantiate (Liftn k sub) x) 
swapMkSubstAxiom = unsafeCoerce Refl


-- BaseTypeRepr
type instance Instantiate subst BaseTypeRepr = BaseTypeRepr 
instance InstantiateType CrucibleType (BaseTypeRepr ty) where
  instantiate subst (r :: BaseTypeRepr bt)
    | Refl <- closed (Proxy :: Proxy bt) subst
    = r

type instance Instantiate subst (v :: CrucibleType) = InstantiateCT subst v
  
type family InstantiateCT (subst :: Substitution) (v :: CrucibleType) :: CrucibleType where
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
  InstantiateCT subst (WordMapType n0 b) = WordMapType n0 b
  InstantiateCT subst (RecursiveType sym ctx) = RecursiveType sym (Instantiate subst ctx)
  InstantiateCT subst (IntrinsicType sym ctx) = IntrinsicType sym (Instantiate subst ctx)
  InstantiateCT subst (StringMapType ty) = StringMapType (Instantiate subst ty)
  InstantiateCT subst (VarType k) = SubstVar subst k
  InstantiateCT subst (PolyFnType k args ret) =
    PolyFnType k (Instantiate (Liftn k subst) args) (Instantiate (Liftn k subst) ret)
  
instance Term CrucibleType where
  type MkVar CrucibleType = VarType
  type Repr  CrucibleType = TypeRepr
  varRepr    = VarRepr
    
  axiomSubstVar _ _ = Refl

  instantiateRepr _subst BoolRepr = BoolRepr
  instantiateRepr _subst NatRepr = NatRepr
  instantiateRepr _subst IntegerRepr = IntegerRepr
  instantiateRepr _subst RealValRepr = RealValRepr
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
  instantiateRepr subst (VarRepr k) = substVar subst k
  instantiateRepr subst (PolyFnRepr k args ty) =
    PolyFnRepr k (instantiate (liftn k subst) args)
                 (instantiate (liftn k subst) ty)

type instance Instantiate subst TypeRepr = TypeRepr
instance InstantiateF CrucibleType TypeRepr where
  instantiateF = instantiateRepr
