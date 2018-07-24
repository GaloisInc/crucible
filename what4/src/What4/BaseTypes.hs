-----------------------------------------------------------------------
-- |
-- Module           : What4.BaseTypes
-- Description      : This module exports the types used in solver expressions.
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module exports the types used in solver expressions.
--
-- These types are largely used as indexes to various GADTs and type
-- families as a way to let the GHC typechecker help us keep expressions
-- used by solvers apart.
--
-- In addition, we provide a value-level reification of the type
-- indices that can be examined by pattern matching, called 'BaseTypeRepr'.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds#-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module What4.BaseTypes
  ( -- * BaseType data kind
    type BaseType
    -- ** Constructors for kind BaseType
  , BaseBoolType
  , BaseIntegerType
  , BaseNatType
  , BaseRealType
  , BaseStringType
  , BaseBVType
  , BaseFloatType
  , BaseComplexType
  , BaseStructType
  , BaseArrayType
    -- * FloatInfo data kind
  , type FloatInfo
    -- ** Constructors for kind FloatInfo
  , HalfFloat
  , SingleFloat
  , DoubleFloat
  , QuadFloat
  , X86_80Float
  , DoubleDoubleFloat
    -- * Representations of base types
  , BaseTypeRepr(..)
  , FloatInfoRepr(..)
  , arrayTypeIndices
  , arrayTypeResult
  , module Data.Parameterized.NatRepr

    -- * KnownRepr
  , KnownRepr(..)  -- Re-export from 'Data.Parameterized.Classes'
  , KnownCtx
  ) where


import           Data.Hashable
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen

--------------------------------------------------------------------------------
-- KnownCtx

-- | A Context where all the argument types are 'KnownRepr' instances
type KnownCtx f = KnownRepr (Ctx.Assignment f)

------------------------------------------------------------------------
-- BaseType

-- | This data kind enumerates the Crucible solver interface types,
-- which are types that may be represented symbolically.
data BaseType
     -- | @BaseBoolType@ denotes Boolean values.
   = BaseBoolType
     -- | @BaseNatType@ denotes a natural number.
   | BaseNatType
     -- | @BaseIntegerType@ denotes an integer.
   | BaseIntegerType
     -- | @BaseRealType@ denotes a real number.
   | BaseRealType
     -- | @BaseBVType n@ denotes a bitvector with @n@-bits.
   | BaseBVType GHC.TypeLits.Nat
     -- | @BaseFloatType fi@ denotes a floating point number in @fi@ format.
   | BaseFloatType FloatInfo
     -- | @BaseStringType@ denotes a sequence of Unicode codepoints
   | BaseStringType
     -- | @BaseComplexType@ denotes a complex number with real components.
   | BaseComplexType
     -- | @BaseStructType tps@ denotes a sequence of values with types @tps@.
   | BaseStructType (Ctx.Ctx BaseType)
     -- | @BaseArrayType itps rtp@ denotes a function mapping indices @itps@
     -- to values of type @rtp@.
     --
     -- It does not have bounds as one would normally expect from an
     -- array in a programming language, but the solver does provide
     -- operations for doing pointwise updates.
   | BaseArrayType  (Ctx.Ctx BaseType) BaseType

type BaseBoolType    = 'BaseBoolType    -- ^ @:: 'BaseType'@.
type BaseIntegerType = 'BaseIntegerType -- ^ @:: 'BaseType'@.
type BaseNatType     = 'BaseNatType     -- ^ @:: 'BaseType'@.
type BaseRealType    = 'BaseRealType    -- ^ @:: 'BaseType'@.
type BaseBVType      = 'BaseBVType      -- ^ @:: 'GHC.TypeLits.Nat' -> 'BaseType'@.
type BaseFloatType   = 'BaseFloatType   -- ^ @:: 'FloatInfo' -> 'BaseType'@.
type BaseStringType  = 'BaseStringType  -- ^ @:: 'BaseType'@.
type BaseComplexType = 'BaseComplexType -- ^ @:: 'BaseType'@.
type BaseStructType  = 'BaseStructType  -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType'@.
type BaseArrayType   = 'BaseArrayType   -- ^ @:: 'Ctx.Ctx' 'BaseType' -> 'BaseType' -> 'BaseType'@.

-- | This data kind describes the types of floating-point formats.
-- This consist of the standard IEEE 754-2008 binary floating point formats,
-- as well as the X86 extended 80-bit format and the double-double format.
data FloatInfo where
  HalfFloat         :: FloatInfo  --  16 bit binary IEEE754
  SingleFloat       :: FloatInfo  --  32 bit binary IEEE754
  DoubleFloat       :: FloatInfo  --  64 bit binary IEEE754
  QuadFloat         :: FloatInfo  -- 128 bit binary IEEE754
  X86_80Float       :: FloatInfo  -- X86 80-bit extended floats
  DoubleDoubleFloat :: FloatInfo  -- two 64-bit floats fused in the "double-double" style

type HalfFloat   = 'HalfFloat   -- ^  16 bit binary IEEE754.
type SingleFloat = 'SingleFloat -- ^  32 bit binary IEEE754.
type DoubleFloat = 'DoubleFloat -- ^  64 bit binary IEEE754.
type QuadFloat   = 'QuadFloat   -- ^ 128 bit binary IEEE754.
type X86_80Float = 'X86_80Float -- ^ X86 80-bit extended floats.
type DoubleDoubleFloat = 'DoubleDoubleFloat -- ^ Two 64-bit floats fused in the "double-double" style.

------------------------------------------------------------------------
-- BaseTypeRepr

-- | A runtime representation of a solver interface type. Parameter @bt@
-- has kind 'BaseType'.
data BaseTypeRepr (bt::BaseType) :: * where
   BaseBoolRepr :: BaseTypeRepr BaseBoolType
   BaseBVRepr   :: (1 <= w) => !(NatRepr w) -> BaseTypeRepr (BaseBVType w)
   BaseNatRepr  :: BaseTypeRepr BaseNatType
   BaseIntegerRepr :: BaseTypeRepr BaseIntegerType
   BaseRealRepr    :: BaseTypeRepr BaseRealType
   BaseFloatRepr   :: !(FloatInfoRepr fi) -> BaseTypeRepr (BaseFloatType fi)
   BaseStringRepr  :: BaseTypeRepr BaseStringType
   BaseComplexRepr :: BaseTypeRepr BaseComplexType

   -- The representation of a struct type.
   BaseStructRepr :: !(Ctx.Assignment BaseTypeRepr ctx)
                  -> BaseTypeRepr (BaseStructType ctx)

   BaseArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx Ctx.::> tp))
                 -> !(BaseTypeRepr xs)
                 -> BaseTypeRepr (BaseArrayType (idx Ctx.::> tp) xs)

-- | A family of value-level representatives for floating-point types.
data FloatInfoRepr (fi::FloatInfo) where
  HalfFloatRepr         :: FloatInfoRepr HalfFloat
  SingleFloatRepr       :: FloatInfoRepr SingleFloat
  DoubleFloatRepr       :: FloatInfoRepr DoubleFloat
  QuadFloatRepr         :: FloatInfoRepr QuadFloat
  X86_80FloatRepr       :: FloatInfoRepr X86_80Float
  DoubleDoubleFloatRepr :: FloatInfoRepr DoubleDoubleFloat

-- | Return the type of the indices for an array type.
arrayTypeIndices :: BaseTypeRepr (BaseArrayType idx tp)
                 -> Ctx.Assignment BaseTypeRepr idx
arrayTypeIndices (BaseArrayRepr i _) = i

-- | Return the result type of an array type.
arrayTypeResult :: BaseTypeRepr (BaseArrayType idx tp) -> BaseTypeRepr tp
arrayTypeResult (BaseArrayRepr _ rtp) = rtp

instance KnownRepr BaseTypeRepr BaseBoolType where
  knownRepr = BaseBoolRepr
instance KnownRepr BaseTypeRepr BaseIntegerType where
  knownRepr = BaseIntegerRepr
instance KnownRepr BaseTypeRepr BaseNatType where
  knownRepr = BaseNatRepr
instance KnownRepr BaseTypeRepr BaseRealType where
  knownRepr = BaseRealRepr
instance KnownRepr BaseTypeRepr BaseStringType where
  knownRepr = BaseStringRepr
instance (1 <= w, KnownNat w) => KnownRepr BaseTypeRepr (BaseBVType w) where
  knownRepr = BaseBVRepr knownNat
instance KnownRepr FloatInfoRepr fi => KnownRepr BaseTypeRepr (BaseFloatType fi) where
  knownRepr = BaseFloatRepr knownRepr
instance KnownRepr BaseTypeRepr BaseComplexType where
  knownRepr = BaseComplexRepr

instance KnownRepr FloatInfoRepr HalfFloat         where knownRepr = HalfFloatRepr
instance KnownRepr FloatInfoRepr SingleFloat       where knownRepr = SingleFloatRepr
instance KnownRepr FloatInfoRepr DoubleFloat       where knownRepr = DoubleFloatRepr
instance KnownRepr FloatInfoRepr QuadFloat         where knownRepr = QuadFloatRepr
instance KnownRepr FloatInfoRepr X86_80Float       where knownRepr = X86_80FloatRepr
instance KnownRepr FloatInfoRepr DoubleDoubleFloat where knownRepr = DoubleDoubleFloatRepr

instance KnownRepr (Ctx.Assignment BaseTypeRepr) ctx
      => KnownRepr BaseTypeRepr (BaseStructType ctx) where
  knownRepr = BaseStructRepr knownRepr

instance ( KnownRepr (Ctx.Assignment BaseTypeRepr) idx
         , KnownRepr BaseTypeRepr tp
         , KnownRepr BaseTypeRepr t
         )
      => KnownRepr BaseTypeRepr (BaseArrayType (idx Ctx.::> tp) t) where
  knownRepr = BaseArrayRepr knownRepr knownRepr

-- Force BaseTypeRepr, etc. to be in context for next slice.
$(return [])

instance HashableF BaseTypeRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (BaseTypeRepr bt) where
  hashWithSalt = $(structuralHash [t|BaseTypeRepr|])

instance HashableF FloatInfoRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (FloatInfoRepr fi) where
  hashWithSalt = $(structuralHash [t|FloatInfoRepr|])

instance Pretty (BaseTypeRepr bt) where
  pretty = text . show
instance Show (BaseTypeRepr bt) where
  showsPrec = $(structuralShowsPrec [t|BaseTypeRepr|])
instance ShowF BaseTypeRepr

instance Pretty (FloatInfoRepr fi) where
  pretty = text . show
instance Show (FloatInfoRepr fi) where
  showsPrec = $(structuralShowsPrec [t|FloatInfoRepr|])
instance ShowF FloatInfoRepr

instance TestEquality BaseTypeRepr where
  testEquality = $(structuralTypeEquality [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|FloatInfoRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
                   , ( TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|testEquality|]
                     )
                   ]
                  )

instance OrdF BaseTypeRepr where
  compareF = $(structuralTypeOrd [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|FloatInfoRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )

instance TestEquality FloatInfoRepr where
  testEquality = $(structuralTypeEquality [t|FloatInfoRepr|] [])
instance OrdF FloatInfoRepr where
  compareF = $(structuralTypeOrd [t|FloatInfoRepr|] [])