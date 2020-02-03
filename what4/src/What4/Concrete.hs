-----------------------------------------------------------------------
-- |
-- Module           : What4.Concrete
-- Description      : Concrete values of base types
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines a representation of concrete values of base
-- types.  These are values in fully-evaluated form that do not depend
-- on any symbolic constants.
-----------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Concrete
  (
    -- * Concrete values
    ConcreteVal(..)
  , concreteType
  , ppConcrete

    -- * Concrete projections
  , fromConcreteBool
  , fromConcreteNat
  , fromConcreteInteger
  , fromConcreteReal
  , fromConcreteString
  , fromConcreteUnsignedBV
  , fromConcreteSignedBV
  , fromConcreteComplex
  ) where

import           Data.List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Numeric as N
import           Numeric.Natural
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Data.Parameterized.Classes
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC

import           What4.BaseTypes
import           What4.Utils.Complex
import           What4.Utils.StringLiteral

-- | A data type for representing the concrete values of base types.
data ConcreteVal tp where
  ConcreteBool    :: Bool -> ConcreteVal BaseBoolType
  ConcreteNat     :: Natural -> ConcreteVal BaseNatType
  ConcreteInteger :: Integer -> ConcreteVal BaseIntegerType
  ConcreteReal    :: Rational -> ConcreteVal BaseRealType
  ConcreteString  :: StringLiteral si -> ConcreteVal (BaseStringType si)
  ConcreteComplex :: Complex Rational -> ConcreteVal BaseComplexType
  ConcreteBV      ::
    (1 <= w) =>
    NatRepr w {- Width of the bitvector -} ->
    Integer   {- Unsigned value of the bitvector -} ->
    ConcreteVal (BaseBVType w)
  ConcreteStruct  :: Ctx.Assignment ConcreteVal ctx -> ConcreteVal (BaseStructType ctx)
  ConcreteArray   ::
    Ctx.Assignment BaseTypeRepr (idx ::> i) {- Type representatives for the index tuple -} ->
    ConcreteVal b {- A default value -} ->
    Map (Ctx.Assignment ConcreteVal (idx ::> i)) (ConcreteVal b) {- A collection of point-updates -} ->
    ConcreteVal (BaseArrayType (idx ::> i) b)

deriving instance ShowF ConcreteVal
deriving instance Show (ConcreteVal tp)

fromConcreteBool :: ConcreteVal BaseBoolType -> Bool
fromConcreteBool (ConcreteBool x) = x

fromConcreteNat :: ConcreteVal BaseNatType -> Natural
fromConcreteNat (ConcreteNat x) = x

fromConcreteInteger :: ConcreteVal BaseIntegerType -> Integer
fromConcreteInteger (ConcreteInteger x) = x

fromConcreteReal :: ConcreteVal BaseRealType -> Rational
fromConcreteReal (ConcreteReal x) = x

fromConcreteComplex :: ConcreteVal BaseComplexType -> Complex Rational
fromConcreteComplex (ConcreteComplex x) = x

fromConcreteString :: ConcreteVal (BaseStringType si) -> StringLiteral si
fromConcreteString (ConcreteString x) = x

fromConcreteUnsignedBV :: ConcreteVal (BaseBVType w) -> Integer
fromConcreteUnsignedBV (ConcreteBV _w x) = x

fromConcreteSignedBV :: ConcreteVal (BaseBVType w) -> Integer
fromConcreteSignedBV (ConcreteBV w x) = toSigned w x

-- | Compute the type representative for a concrete value.
concreteType :: ConcreteVal tp -> BaseTypeRepr tp
concreteType = \case
  ConcreteBool{}     -> BaseBoolRepr
  ConcreteNat{}      -> BaseNatRepr
  ConcreteInteger{}  -> BaseIntegerRepr
  ConcreteReal{}     -> BaseRealRepr
  ConcreteString s   -> BaseStringRepr (stringLiteralInfo s)
  ConcreteComplex{}  -> BaseComplexRepr
  ConcreteBV w _     -> BaseBVRepr w
  ConcreteStruct xs  -> BaseStructRepr (fmapFC concreteType xs)
  ConcreteArray idxTy def _ -> BaseArrayRepr idxTy (concreteType def)

$(return [])

instance TestEquality ConcreteVal where
  testEquality = $(structuralTypeEquality [t|ConcreteVal|]
     [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType, [|testEqualityFC testEquality|])
     , (ConType [t|ConcreteVal|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|StringLiteral|] `TypeApp` AnyType, [|testEquality|])
     , (ConType [t|Map|] `TypeApp` AnyType `TypeApp` AnyType, [|\x y -> if x == y then Just Refl else Nothing|])
     ])

instance Eq (ConcreteVal tp) where
  x==y = isJust (testEquality x y)

instance OrdF ConcreteVal where
  compareF = $(structuralTypeOrd [t|ConcreteVal|]
     [ (ConType [t|NatRepr|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType, [|compareFC compareF|])
     , (ConType [t|ConcreteVal|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|StringLiteral|] `TypeApp` AnyType, [|compareF|])
     , (ConType [t|Map|] `TypeApp` AnyType `TypeApp` AnyType, [|\x y -> fromOrdering (compare x y)|])
     ])

instance Ord (ConcreteVal tp) where
  compare x y = toOrdering (compareF x y)

-- | Pretty-print a concrete value
ppConcrete :: ConcreteVal tp -> PP.Doc
ppConcrete = \case
  ConcreteBool x -> PP.text (show x)
  ConcreteNat x -> PP.text (show x)
  ConcreteInteger x -> PP.text (show x)
  ConcreteReal x -> PP.text (show x)
  ConcreteString x -> PP.text (show x)
  ConcreteBV w x -> PP.text ("0x" ++ (N.showHex x (":[" ++ show w ++ "]")))
  ConcreteComplex (r :+ i) -> PP.text "complex(" PP.<> PP.text (show r) PP.<> PP.text ", " PP.<> PP.text (show i) PP.<> PP.text ")"
  ConcreteStruct xs -> PP.text "struct(" PP.<> PP.cat (intersperse PP.comma (toListFC ppConcrete xs)) PP.<> PP.text ")"
  ConcreteArray _ def xs0 -> go (Map.toAscList xs0) (PP.text "constArray(" PP.<> ppConcrete def PP.<> PP.text ")")
    where
    go  [] doc = doc
    go ((i,x):xs) doc = ppUpd i x (go xs doc)

    ppUpd i x doc =
       PP.text "update(" PP.<> PP.cat (intersperse PP.comma (toListFC ppConcrete i))
                         PP.<> PP.comma
                         PP.<> ppConcrete x
                         PP.<> PP.comma
                         PP.<> doc
                         PP.<> PP.text ")"
