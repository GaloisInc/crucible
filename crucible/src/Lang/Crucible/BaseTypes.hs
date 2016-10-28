-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.BaseTypes
-- Description      : This module exports the types used in solver expressions.
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- This module exports the types used in solver expressions.
--
-- These types are largely used as indexes to various GADTs and type
-- families as a way to let the GHC typechecker help us keep expressions
-- used by solvers apart.
--
-- In addition, we provide a value-level reification of the type
-- indices that can be examinied by pattern matching, called BaseTypeRepr.
--
-- Base types are essentially a subset of the wider class of crucible
-- types (defined in "Lang.Crucible.Types").
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
module Lang.Crucible.BaseTypes
  ( type BaseType
  , BaseBoolType
  , BaseIntegerType
  , BaseNatType
  , BaseRealType
  , BaseBVType
  , BaseComplexType
  , BaseStructType
  , BaseArrayType
  , BaseTypeRepr(..)
  , arrayTypeIndices
  , arrayTypeResult
  , module Data.Parameterized.NatRepr
  , KnownRepr(..)
  , KnownCtx
  ) where


import           Data.Hashable
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen

------------------------------------------------------------------------
-- KnownRepr

class KnownRepr (f :: k -> *) (ctx :: k) where
  knownRepr :: f ctx

instance (KnownRepr (Ctx.Assignment f) ctx, KnownRepr f bt)
      => KnownRepr (Ctx.Assignment f) (ctx Ctx.::> bt) where
  knownRepr = knownRepr Ctx.%> knownRepr

instance KnownRepr (Ctx.Assignment f) Ctx.EmptyCtx where
  knownRepr = Ctx.empty

-- | A Context where all the argument types are 'KnownRepr' instances.
type KnownCtx f = KnownRepr (Ctx.Assignment f)

------------------------------------------------------------------------
-- BaseType

-- | A type for the solver.
data BaseType
   = BaseBoolType
   | BaseIntegerType
   | BaseNatType
   | BaseRealType
   | BaseBVType GHC.TypeLits.Nat
   | BaseComplexType
     -- An aggregate type containing a sequence of values of the
     -- given types.
   | BaseStructType (Ctx.Ctx BaseType)
   | BaseArrayType  (Ctx.Ctx BaseType) BaseType

type BaseBoolType    = 'BaseBoolType
type BaseIntegerType = 'BaseIntegerType
type BaseNatType     = 'BaseNatType
type BaseRealType    = 'BaseRealType
type BaseBVType      = 'BaseBVType
type BaseComplexType = 'BaseComplexType
type BaseStructType  = 'BaseStructType
type BaseArrayType   = 'BaseArrayType

------------------------------------------------------------------------
-- BaseTypeRepr

-- | A runtime representation of a solver base type.
data BaseTypeRepr (bt::BaseType) :: * where
   BaseBoolRepr :: BaseTypeRepr BaseBoolType
   BaseBVRepr   :: (1 <= w) => !(NatRepr w) -> BaseTypeRepr (BaseBVType w)
   BaseNatRepr  :: BaseTypeRepr BaseNatType
   BaseIntegerRepr :: BaseTypeRepr BaseIntegerType
   BaseRealRepr    :: BaseTypeRepr BaseRealType
   BaseComplexRepr :: BaseTypeRepr BaseComplexType

   -- The representation of a struct type.
   BaseStructRepr :: !(Ctx.Assignment BaseTypeRepr ctx)
                  -> BaseTypeRepr (BaseStructType ctx)

   BaseArrayRepr :: !(Ctx.Assignment BaseTypeRepr (idx Ctx.::> tp))
                 -> !(BaseTypeRepr xs)
                 -> BaseTypeRepr (BaseArrayType (idx Ctx.::> tp) xs)

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
instance (1 <= w, KnownNat w) => KnownRepr BaseTypeRepr (BaseBVType w) where
  knownRepr = BaseBVRepr knownNat
instance KnownRepr BaseTypeRepr BaseComplexType where
  knownRepr = BaseComplexRepr

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

instance Pretty (BaseTypeRepr bt) where
  pretty = text . show
instance Show (BaseTypeRepr bt) where
  showsPrec = $(structuralShowsPrec [t|BaseTypeRepr|])
instance ShowF BaseTypeRepr where
  showF = show

instance TestEquality BaseTypeRepr where
  testEquality = $(structuralTypeEquality [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
                   , ( TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|testEquality|]
                     )
                   ]
                  )

instance OrdF BaseTypeRepr where
  compareF = $(structuralTypeOrd [t|BaseTypeRepr|]
                   [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|compareF|])
                   , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|compareF|])
                   , (TypeApp (TypeApp (ConType [t|Ctx.Assignment|]) AnyType) AnyType
                     , [|compareF|]
                     )
                   ]
                  )
