{- |
Module           : Lang.Crucible.CFG.Expr
Description      : Expression syntax definitions
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Define the syntax of Crucible expressions.  Expressions represent
side-effect free computations that result in terms.  The same
expression language is used both for registerized CFGs ("Lang.Crucible.CFG.Reg")
and for the core SSA-form CFGs ("Lang.Crucible.CFG.Core").

Evaluation of expressions is defined in module "Lang.Crucible.Simulator.Evaluation".
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- This option is here because, without it, GHC takes an extremely
-- long time (forever?) to compile this module with profiling enabled.
-- The SpecConstr optimization appears to be the culprit, and this
-- option disables it.  Perhaps we only need to disable this
-- optimization on profiling builds?
{-# OPTIONS_GHC -fno-spec-constr #-}

module Lang.Crucible.CFG.Expr
  ( -- * App
    App(..)
  , mapApp
  , foldApp
  , traverseApp
  , pattern BoolEq
  , pattern NatEq
  , pattern IntEq
  , pattern RealEq
  , pattern BVEq

  , pattern BoolIte
  , pattern NatIte
  , pattern IntIte
  , pattern RealIte
  , pattern BVIte
    -- * Base terms
  , BaseTerm(..)
  , module Lang.Crucible.CFG.Extension
  , RoundingMode(..)
  ) where

import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Text (Text)
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableFC

import           What4.Interface (RoundingMode(..))

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Utils.PrettyPrint
import qualified Lang.Crucible.Utils.Structural as U


import Unsafe.Coerce(unsafeCoerce)
------------------------------------------------------------------------
-- BaseTerm

-- | Base terms represent the subset of expressions
--   of base types, packaged together with a run-time
--   representation of their type.
data BaseTerm (f :: CrucibleType -> *) (tp :: BaseType)
   = BaseTerm { baseTermType :: !(BaseTypeRepr tp)
              , baseTermVal  :: !(f (BaseToType tp))
              }

instance TestEqualityFC BaseTerm where
  testEqualityFC testF (BaseTerm _ x) (BaseTerm _ y) = do
    Refl <- testF x y
    return Refl
instance TestEquality f => TestEquality (BaseTerm f) where
  testEquality = testEqualityFC testEquality

instance OrdFC BaseTerm where
  compareFC cmpF (BaseTerm _ x) (BaseTerm _ y) = do
    case cmpF x y of
      LTF -> LTF
      GTF -> GTF
      EQF -> EQF
instance OrdF f => OrdF (BaseTerm f) where
  compareF = compareFC compareF

instance FunctorFC BaseTerm where
  fmapFC = fmapFCDefault

instance FoldableFC BaseTerm where
  foldMapFC = foldMapFCDefault

instance TraversableFC BaseTerm where
  traverseFC f (BaseTerm tp x) = BaseTerm tp <$> f x

type instance Instantiate subst BaseTerm = BaseTerm
instance InstantiateF a => InstantiateType (BaseTerm a ctx) where
  instantiate subst (BaseTerm (btr :: BaseTypeRepr btr) val)
    | Refl <- closedType @(BaseTypeRepr btr) subst =
    BaseTerm btr (instantiate subst val)

------------------------------------------------------------------------
-- App

-- | Equality on booleans
pattern BoolEq :: () => (tp ~ BoolType) => f BoolType -> f BoolType -> App ext f tp
pattern BoolEq x y = BaseIsEq BaseBoolRepr x y

-- | Equality on natural numbers.
pattern NatEq :: () => (tp ~ BoolType) => f NatType -> f NatType -> App ext f tp
pattern NatEq x y = BaseIsEq BaseNatRepr x y

-- | Equality on integers
pattern IntEq :: () => (tp ~ BoolType) => f IntegerType -> f IntegerType -> App ext f tp
pattern IntEq x y = BaseIsEq BaseIntegerRepr x y

-- | Equality on real numbers.
pattern RealEq :: () => (tp ~ BoolType) => f RealValType -> f RealValType -> App ext f tp
pattern RealEq x y = BaseIsEq BaseRealRepr x y

-- | Equality on bitvectors
pattern BVEq :: () => (1 <= w, tp ~ BoolType) => NatRepr w -> f (BVType w) -> f (BVType w) -> App ext f tp
pattern BVEq w x y = BaseIsEq (BaseBVRepr w) x y


-- | Return first or second value depending on condition.
pattern BoolIte :: () => (tp ~ BoolType) => f BoolType -> f tp -> f tp -> App ext f tp
pattern BoolIte c x y = BaseIte BaseBoolRepr c x y

-- | Return first or second value depending on condition.
pattern NatIte :: () => (tp ~ NatType) => f BoolType -> f tp -> f tp -> App ext f tp
pattern NatIte c x y = BaseIte BaseNatRepr c x y

-- | Return first or second value depending on condition.
pattern IntIte :: () => (tp ~ IntegerType) => f BoolType -> f tp -> f tp -> App ext f tp
pattern IntIte c x y = BaseIte BaseIntegerRepr c x y

-- | Return first or second number depending on condition.
pattern RealIte :: () => (tp ~ RealValType) => f BoolType -> f tp -> f tp -> App ext f tp
pattern RealIte c x y = BaseIte BaseRealRepr c x y

-- | Return first or second value depending on condition.
pattern BVIte :: () => (1 <= w, tp ~ BVType w) => f BoolType -> NatRepr w -> f tp -> f tp -> App ext f tp
pattern BVIte c w x y = BaseIte (BaseBVRepr w) c x y

-- | The main Crucible expression datastructure, defined as a
-- multisorted algebra. Type @'App' ext f tp@ encodes the top-level
-- application of a Crucible expression. The parameter @ext@ is used
-- to indicate which syntax extension is being used via the
-- @ExprExtension@ type family.  The type parameter @tp@ is a
-- type index that indicates the Crucible type of the values denoted
-- by the given expression form. Parameter @f@ is used everywhere a
-- recursive sub-expression would go.  Uses of the 'App' type will
-- tie the knot through this parameter.
data App (ext :: *) (f :: CrucibleType -> *) (tp :: CrucibleType) where

  ----------------------------------------------------------------------
  -- Syntax Extension

  ExtensionApp :: !(ExprExtension ext f tp) -> App ext f tp

  ----------------------------------------------------------------------
  -- Polymorphic

  -- | Return true if two base types are equal.
  BaseIsEq :: !(BaseTypeRepr tp)
           -> !(f (BaseToType tp))
           -> !(f (BaseToType tp))
           -> App ext f BoolType

  -- | Select one or other
  BaseIte :: !(BaseTypeRepr tp)
          -> !(f BoolType)
          -> !(f (BaseToType tp))
          -> !(f (BaseToType tp))
          -> App ext f (BaseToType tp)

  ----------------------------------------------------------------------
  -- ()

  EmptyApp :: App ext f UnitType

  ----------------------------------------------------------------------
  -- Any

  -- Build an ANY type package.
  PackAny :: !(TypeRepr tp)
          -> !(f tp)
          -> App ext f AnyType

  -- Attempt to open an ANY type. Return the contained
  -- value if it has the given type; otherwise return Nothing.
  UnpackAny :: !(TypeRepr tp)
            -> !(f AnyType)
            -> App ext f (MaybeType tp)

  ---------------------------------------------------------------------
  -- Bool

  BoolLit :: !Bool -> App ext f BoolType

  Not :: !(f BoolType)
      -> App ext f BoolType

  And :: !(f BoolType)
      -> !(f BoolType)
      -> App ext f BoolType
  Or  :: !(f BoolType)
      -> !(f BoolType)
      -> App ext f BoolType

  -- Exclusive or of Boolean values.
  BoolXor :: !(f BoolType)
          -> !(f BoolType)
          -> App ext f BoolType

  ----------------------------------------------------------------------
  -- Nat

  -- @NatLit n@ returns the value n.
  NatLit :: !Natural -> App ext f NatType
  -- Less than on natural numbers.
  NatLt :: !(f NatType) -> !(f NatType) -> App ext f BoolType
  -- Less than or equal on natural numbers.
  NatLe :: !(f NatType) -> !(f NatType) -> App ext f BoolType
  -- Add two natural numbers.
  NatAdd :: !(f NatType) -> !(f NatType) -> App ext f NatType
  -- @NatSub x y@ equals @x - y@.
  -- The result is undefined if the @x@ is less than @y@.
  NatSub :: !(f NatType) -> !(f NatType) -> App ext f NatType
  -- Multiply two natural numbers.
  NatMul :: !(f NatType) -> !(f NatType) -> App ext f NatType
  -- Divide two natural numbers.  Undefined if the divisor is 0.
  NatDiv :: !(f NatType) -> !(f NatType) -> App ext f NatType
  -- Modular reduction on natural numbers. Undefined if the modulus is 0.
  NatMod :: !(f NatType) -> !(f NatType) -> App ext f NatType

  ----------------------------------------------------------------------
  -- Integer

  -- Create a singleton real array from a numeric literal.
  IntLit :: !Integer -> App ext f IntegerType
  -- Less-than test on integers
  IntLt :: !(f IntegerType) -> !(f IntegerType) -> App ext f BoolType
  -- Less-than-or-equal test on integers
  IntLe :: !(f IntegerType) -> !(f IntegerType) -> App ext f BoolType
  -- Negation of an integer value
  IntNeg :: !(f IntegerType) -> App ext f IntegerType
  -- Add two integers.
  IntAdd :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Subtract one integer from another.
  IntSub :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Multiply two integers.
  IntMul :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Divide two integers.  Undefined if the divisor is 0.
  IntDiv :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Modular reduction on integers.  Undefined if the modulus is 0.
  IntMod :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Integer absolute value
  IntAbs :: !(f IntegerType) -> App ext f IntegerType

  ----------------------------------------------------------------------
  -- RealVal

  -- A real constant
  RationalLit :: !Rational -> App ext f RealValType

  RealLt :: !(f RealValType) -> !(f RealValType) -> App ext f BoolType
  RealLe :: !(f RealValType) -> !(f RealValType) -> App ext f BoolType
  -- Negate a real number
  RealNeg :: !(f RealValType) -> App ext f RealValType
  -- Add two natural numbers.
  RealAdd :: !(f RealValType) -> !(f RealValType) -> App ext f RealValType
  -- Subtract one number from another.
  RealSub :: !(f RealValType) -> !(f RealValType) -> App ext f RealValType
  -- Multiple two numbers.
  RealMul :: !(f RealValType) -> !(f RealValType) -> App ext f RealValType
  -- Divide two numbers.
  RealDiv :: !(f RealValType) -> !(f RealValType) -> App ext f RealValType
  -- Compute the "real modulus", which is @x - y * floor(x ./ y)@ when
  -- @y@ is not zero and @x@ when @y@ is zero.
  RealMod :: !(f RealValType) -> !(f RealValType) -> App ext f RealValType

  -- Return true if real value is integer.
  RealIsInteger :: !(f RealValType) -> App ext f BoolType

  ----------------------------------------------------------------------
  -- Float

  -- Floating point constants
  FloatLit :: !Float -> App ext f (FloatType SingleFloat)
  DoubleLit :: !Double -> App ext f (FloatType DoubleFloat)
  FloatNaN :: !(FloatInfoRepr fi) -> App ext f (FloatType fi)
  FloatPInf :: !(FloatInfoRepr fi) -> App ext f (FloatType fi)
  FloatNInf :: !(FloatInfoRepr fi) -> App ext f (FloatType fi)
  FloatPZero :: !(FloatInfoRepr fi) -> App ext f (FloatType fi)
  FloatNZero :: !(FloatInfoRepr fi) -> App ext f (FloatType fi)

  -- Arithmetic operations
  FloatNeg
    :: !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatAbs
    :: !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatSqrt
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)

  FloatAdd
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatSub
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatMul
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatDiv
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  -- Foating-point remainder of the two operands
  FloatRem
    :: !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatMin
    :: !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatMax
    :: !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)
  FloatFMA
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)

  -- Comparison operations
  FloatEq :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatFpEq :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatGt :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatGe :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatLt :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatLe :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatNe :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType
  FloatFpNe :: !(f (FloatType fi)) -> !(f (FloatType fi)) -> App ext f BoolType

  FloatIte
    :: !(FloatInfoRepr fi)
    -> !(f BoolType)
    -> !(f (FloatType fi))
    -> !(f (FloatType fi))
    -> App ext f (FloatType fi)

  -- Conversion operations
  FloatCast
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (FloatType fi'))
    -> App ext f (FloatType fi)
  FloatFromBinary
    :: !(FloatInfoRepr fi)
    -> !(f (BVType (FloatInfoToBitWidth fi)))
    -> App ext f (FloatType fi)
  FloatToBinary
    :: (1 <= FloatInfoToBitWidth fi)
    => !(FloatInfoRepr fi)
    -> !(f (FloatType fi))
    -> App ext f (BVType (FloatInfoToBitWidth fi))
  FloatFromBV
    :: (1 <= w)
    => !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (BVType w))
    -> App ext f (FloatType fi)
  FloatFromSBV
    :: (1 <= w)
    => !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f (BVType w))
    -> App ext f (FloatType fi)
  FloatFromReal
    :: !(FloatInfoRepr fi)
    -> !RoundingMode
    -> !(f RealValType)
    -> App ext f (FloatType fi)
  FloatToBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> App ext f (BVType w)
  FloatToSBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(f (FloatType fi))
    -> App ext f (BVType w)
  FloatToReal :: !(f (FloatType fi)) -> App ext f RealValType

  -- Classification operations
  FloatIsNaN :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsInfinite :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsZero :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsPositive :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsNegative :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsSubnormal :: !(f (FloatType fi)) -> App ext f BoolType
  FloatIsNormal :: !(f (FloatType fi)) -> App ext f BoolType

  ----------------------------------------------------------------------
  -- Maybe

  JustValue :: !(TypeRepr tp)
            -> !(f tp)
            -> App ext f (MaybeType tp)

  NothingValue :: !(TypeRepr tp) -> App ext f (MaybeType tp)

  -- This is a partial operation with given a maybe value returns the
  -- value if is defined and otherwise fails with the given error message.
  --
  -- This operation should be used instead of pattern matching on a maybe
  -- when you do not want an explicit error message being printed, but rather
  -- want to assert that the value is defined.
  FromJustValue :: !(TypeRepr tp)
                -> !(f (MaybeType tp))
                -> !(f StringType)
                -> App ext f tp


  ----------------------------------------------------------------------
  -- Side conditions
  AddSideCondition :: BaseTypeRepr bt
                   -> !(f (BoolType))
                   -> String
                   -> !(f (BaseToType bt))
                   -> App ext f (BaseToType bt)

  ----------------------------------------------------------------------
  -- Recursive Types
  RollRecursive :: IsRecursiveType nm
                => !(SymbolRepr nm)
                -> !(CtxRepr ctx)
                -> !(f (UnrollType nm ctx))
                -> App ext f (RecursiveType nm ctx)

  UnrollRecursive
                :: IsRecursiveType nm
                => !(SymbolRepr nm)
                -> !(CtxRepr ctx)
                -> !(f (RecursiveType nm ctx))
                -> App ext f (UnrollType nm ctx)

  ----------------------------------------------------------------------
  -- Vector

  -- Vector literal.
  VectorLit :: !(TypeRepr tp) -> !(Vector (f tp)) -> App ext f (VectorType tp)

  -- Create an vector of constants.
  VectorReplicate :: !(TypeRepr tp)
                  -> !(f NatType)
                  -> !(f tp)
                  -> App ext f (VectorType tp)

  -- Return true if vector is empty.
  VectorIsEmpty :: !(f (VectorType tp))
                -> App ext f BoolType

  -- Size of vector
  VectorSize :: !(f (VectorType tp)) -> App ext f NatType

  -- Return value stored in given entry.
  VectorGetEntry :: !(TypeRepr tp)
                 -> !(f (VectorType tp))
                 -> !(f NatType)
                 -> App ext f tp

  -- Update vector at given entry.
  VectorSetEntry :: !(TypeRepr tp)
                 -> !(f (VectorType tp))
                 -> !(f NatType)
                 -> !(f tp)
                 -> App ext f (VectorType tp)

  -- Cons an element onto the front of the vector
  VectorCons :: !(TypeRepr tp)
             -> !(f tp)
             -> !(f (VectorType tp))
             -> App ext f (VectorType tp)

  ----------------------------------------------------------------------
  -- Handle

  HandleLit :: !(FnHandle args ret)
            -> App ext f (FunctionHandleType args ret)

  -- Create a closure that captures the last argument.
  Closure :: Closed tp =>
             !(CtxRepr args)
          -> !(TypeRepr ret)
          -> !(f (FunctionHandleType (args::>tp) ret))
          -> !(TypeRepr tp)
          -> !(f tp)
          -> App ext f (FunctionHandleType args ret)


  ------------------------------------------------------------------------
  -- Polymorphism

  -- Generalize the type of a function handle
  PolyHandleLit   :: !(FnHandle args ret) -> App ext f (PolyFnType args ret)

  -- Instantiate the type of polymorphic function handle
  PolyInstantiate :: !(TypeRepr (PolyFnType args ret))
                   -> !(f (PolyFnType args ret))
                   -> !(CtxRepr subst)
                   -> App ext f (Instantiate subst (FunctionHandleType args ret))

  ----------------------------------------------------------------------
  -- Conversions

  -- @NatToInteger@ convert a natural number to an integer.
  NatToInteger :: !(f NatType) -> App ext f IntegerType

  -- @IntegerToReal@ convert an integer to a real.
  IntegerToReal :: !(f IntegerType) -> App ext f RealValType

  -- @RealRound@ rounds the real number value toward the nearest integer.
  -- Ties are rounded away from 0.
  RealRound :: !(f RealValType) -> App ext f IntegerType

  -- @RealRound@ computes the largest integer less-or-equal to the given real number.
  RealFloor :: !(f RealValType) -> App ext f IntegerType

  -- @RealCeil@ computes the smallest integer greater-or-equal to the given real number.
  RealCeil :: !(f RealValType) -> App ext f IntegerType

  -- @IntegerToBV@ converts an integer value to a bitvector.  This operations computes
  -- the unique bitvector whose value is congruent to the input value modulo @2^w@.
  IntegerToBV :: (1 <= w) => NatRepr w -> !(f IntegerType) -> App ext f (BVType w)

  -- @RealToNat@ convert a non-negative real integer to natural number.
  -- This is partial, and requires that the input be a non-negative real
  -- integer.
  RealToNat :: !(f RealValType) -> App ext f NatType

  ----------------------------------------------------------------------
  -- ComplexReal

  -- Create complex number from two real numbers.
  Complex :: !(f RealValType) -> !(f RealValType) -> App ext f ComplexRealType
  RealPart :: !(f ComplexRealType) -> App ext f RealValType
  ImagPart :: !(f ComplexRealType) -> App ext f RealValType

  ----------------------------------------------------------------------
  -- BV

  -- generate an "undefined" bitvector value
  BVUndef :: (1 <= w) => NatRepr w -> App ext f (BVType w)

  BVLit :: (1 <= w) => NatRepr w -> Integer -> App ext f (BVType w)

  -- concatenate two bitvectors
  BVConcat :: (1 <= u, 1 <= v, 1 <= u+v)
           => !(NatRepr u)
           -> !(NatRepr v)
           -> !(f (BVType u))       -- Most significant bits
           -> !(f (BVType v))       -- Least significant bits
           -> App ext f (BVType (u+v))

  -- BVSelect idx n bv choses bits [idx, .. , idx+n-1] from bitvector bv.
  -- The resulting bitvector will have width n.
  -- Index 0 denotes the least-significant bit.
  BVSelect :: (1 <= w, 1 <= len, idx + len <= w)
           => !(NatRepr idx)
           -> !(NatRepr len)
           -> !(NatRepr w)
           -> !(f (BVType w))
           -> App ext f (BVType len)

  BVTrunc :: (1 <= r, r+1 <= w)
          => !(NatRepr r)
          -> !(NatRepr w)
          -> !(f (BVType w))
          -> App ext f (BVType r)

  BVZext :: (1 <= w, 1 <= r, w+1 <= r)
         => !(NatRepr r)
         -> !(NatRepr w)
         -> !(f (BVType w))
         -> App ext f (BVType r)

  BVSext :: (1 <= w, 1 <= r, w+1 <= r)
         => !(NatRepr r)
         -> !(NatRepr w)
         -> !(f (BVType w))
         -> App ext f (BVType r)

  -- Complement bits in bitvector.
  BVNot :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVAnd :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVOr  :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVXor :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVNeg :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVAdd :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVSub :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVMul :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f (BVType w)

  BVUdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App ext f (BVType w)

  -- | This performs signed division.  The result is truncated to zero.
  --
  -- TODO: Document semantics when divisor is zero and case of
  -- minSigned w / -1 = minSigned w.
  BVSdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App ext f (BVType w)

  BVUrem :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App ext f (BVType w)

  BVSrem :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App ext f (BVType w)

  BVUle :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f BoolType

  BVUlt :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f BoolType

  BVSle :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f BoolType

  BVSlt :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f BoolType

  -- True if the unsigned addition of the two given bitvectors
  -- has a carry-out; that is, if the unsigned addition overflows.
  BVCarry :: (1 <= w)
          => !(NatRepr w)
          -> !(f (BVType w))
          -> !(f (BVType w))
          -> App ext f BoolType

  -- True if the signed addition of the two given bitvectors
  -- has a signed overflow condition.
  BVSCarry :: (1 <= w)
           => !(NatRepr w)
           -> !(f (BVType w))
           -> !(f (BVType w))
           -> App ext f BoolType

  -- True if the signed subtraction of the two given bitvectors
  -- has a signed overflow condition.
  BVSBorrow :: (1 <= w)
            => !(NatRepr w)
            -> !(f (BVType w))
            -> !(f (BVType w))
            -> App ext f BoolType

  -- Perform a left-shift
  BVShl :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w)) -- Value to shift
        -> !(f (BVType w)) -- The shift amount as an unsigned integer.
        -> App ext f (BVType w)

  -- Perform a logical shift right
  BVLshr :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w)) -- Value to shift
         -> !(f (BVType w)) -- The shift amount as an unsigned integer.
         -> App ext f (BVType w)

  -- Perform a signed shift right (if the
  BVAshr :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w)) -- Value to shift
         -> !(f (BVType w)) -- The shift amount as an unsigned integer.
         -> App ext f (BVType w)

  -- Given a Boolean, returns one if Boolean is True and zero otherwise.
  BoolToBV :: (1 <= w)
           => !(NatRepr w)
           -> !(f BoolType)
           -> App ext f (BVType w)

  -- Return the unsigned value of the given bitvector as an integer
  BvToInteger :: (1 <= w)
              => !(NatRepr w)
              -> !(f (BVType w))
              -> App ext f IntegerType

  -- Return the signed value of the given bitvector as an integer
  SbvToInteger :: (1 <= w)
               => !(NatRepr w)
               -> !(f (BVType w))
               -> App ext f IntegerType

  -- Return the unsigned value of the given bitvector as a nat
  BvToNat :: (1 <= w)
          => !(NatRepr w)
          -> !(f (BVType w))
          -> App ext f NatType

  BVNonzero :: (1 <= w)
            => !(NatRepr w)
            -> !(f (BVType w))
            -> App ext f BoolType

  ----------------------------------------------------------------------
  -- WordMap

  EmptyWordMap :: (1 <= w)
               => !(NatRepr w)
               -> !(BaseTypeRepr tp)
               -> App ext f (WordMapType w tp)

  InsertWordMap :: (1 <= w)
                => !(NatRepr w)
                -> !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (BaseToType tp))
                -> !(f (WordMapType w tp))
                -> App ext f (WordMapType w tp)

  LookupWordMap :: (1 <= w)
                => !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (WordMapType w tp))
                -> App ext f (BaseToType tp)

  LookupWordMapWithDefault
                :: (1 <= w)
                => !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (WordMapType w tp))
                -> !(f (BaseToType tp))
                -> App ext f (BaseToType tp)

  ----------------------------------------------------------------------
  -- Variants

  InjectVariant :: !(CtxRepr ctx)
            -> !(Ctx.Index ctx tp)
            -> !(f tp)
            -> App ext f (VariantType ctx)

  ProjectVariant :: !(CtxRepr ctx)
                 -> !(Ctx.Index ctx tp)
                 -> !(f (VariantType ctx))
                 -> App ext f (MaybeType tp)

  ----------------------------------------------------------------------
  -- Struct

  MkStruct :: !(CtxRepr ctx)
           -> !(Ctx.Assignment f ctx)
           -> App ext f (StructType ctx)

  GetStruct :: !(f (StructType ctx))
            -> !(Ctx.Index ctx tp)
            -> !(TypeRepr tp)
            -> App ext f tp

  SetStruct :: !(CtxRepr ctx)
            -> !(f (StructType ctx))
            -> !(Ctx.Index ctx tp)
            -> !(f tp)
            -> App ext f (StructType ctx)

  ----------------------------------------------------------------------
  -- StringMapType

  -- Initialize the ident value map to the given value.
  EmptyStringMap :: !(TypeRepr tp)
                 -> App ext f (StringMapType tp)

  -- Lookup the value of a string in a string map.
  LookupStringMapEntry :: !(TypeRepr tp)
                       -> !(f (StringMapType tp))
                       -> !(f StringType)
                       -> App ext f (MaybeType tp)

  -- Update the name of the ident value map with the given value.
  InsertStringMapEntry :: !(TypeRepr tp)
                       -> !(f (StringMapType tp))
                       -> !(f StringType)
                       -> !(f (MaybeType tp))
                       -> App ext f (StringMapType tp)

  ----------------------------------------------------------------------
  -- String

  TextLit :: !Text
          -> App ext f StringType

  ShowValue :: !(BaseTypeRepr bt)
            -> !(f (BaseToType bt))
            -> App ext f StringType

  AppendString :: !(f StringType)
               -> !(f StringType)
               -> App ext f StringType


  ----------------------------------------------------------------------
  -- Arrays (supporting symbolic operations)

  SymArrayLookup   :: !(BaseTypeRepr b)
                   -> !(f (SymbolicArrayType (idx ::> tp) b))
                   -> !(Ctx.Assignment (BaseTerm f) (idx ::> tp))
                   -> App ext f (BaseToType b)

  SymArrayUpdate   :: !(BaseTypeRepr b)
                   -> !(f (SymbolicArrayType (idx ::> itp) b))
                   -> !(Ctx.Assignment (BaseTerm f) (idx ::> itp))
                   -> !(f (BaseToType b))
                   -> App ext f (SymbolicArrayType (idx ::> itp) b)

  ------------------------------------------------------------------------
  -- Introspection

  -- Returns true if the given value is a concrete value, false otherwise.
  -- This is primarily intended to assist with issuing warnings and such
  -- when a value is expected to be concrete.  This primitive could be
  -- used for evil; try to avoid the temptation.
  IsConcrete :: !(BaseTypeRepr b)
             -> f (BaseToType b)
             -> App ext f BoolType

  ------------------------------------------------------------------------
  -- References

  -- Check whether two references are equal.
  ReferenceEq :: !(TypeRepr tp)
              -> !(f (ReferenceType tp))
              -> !(f (ReferenceType tp))
              -> App ext f BoolType

 

  




-- | Compute a run-time representation of the type of an application.
instance TypeApp (ExprExtension ext) => TypeApp (App ext) where
  -- appType :: App ext f tp -> TypeRepr tp
  appType a0 =
   case a0 of
    BaseIsEq{} -> knownRepr
    BaseIte tp _ _ _ -> baseToType tp
    ---------------------------------------------------------------------
    -- Extension
    ExtensionApp x -> appType x

    ----------------------------------------------------------------------
    -- ()
    EmptyApp -> knownRepr
    ----------------------------------------------------------------------
    -- Any
    PackAny{} -> knownRepr
    UnpackAny tp _ -> MaybeRepr tp
    ----------------------------------------------------------------------
    -- Bool
    BoolLit{} -> knownRepr
    Not{} -> knownRepr
    And{} -> knownRepr
    Or{} -> knownRepr
    BoolXor{} -> knownRepr
    ----------------------------------------------------------------------
    -- Nat
    NatLit{} -> knownRepr
    NatLt{} -> knownRepr
    NatLe{} -> knownRepr
    NatAdd{} -> knownRepr
    NatSub{} -> knownRepr
    NatMul{} -> knownRepr
    NatDiv{} -> knownRepr
    NatMod{} -> knownRepr

    ----------------------------------------------------------------------
    -- Integer
    IntLit{} -> knownRepr
    IntLt{} -> knownRepr
    IntLe{} -> knownRepr
    IntNeg{} -> knownRepr
    IntAdd{} -> knownRepr
    IntSub{} -> knownRepr
    IntMul{} -> knownRepr
    IntDiv{} -> knownRepr
    IntMod{} -> knownRepr
    IntAbs{} -> knownRepr

    ----------------------------------------------------------------------
    -- RealVal
    RationalLit{} -> knownRepr
    RealAdd{} -> knownRepr
    RealSub{} -> knownRepr
    RealMul{} -> knownRepr
    RealDiv{} -> knownRepr
    RealMod{} -> knownRepr
    RealNeg{} -> knownRepr
    RealLe{} -> knownRepr
    RealLt{} -> knownRepr
    RealIsInteger{} -> knownRepr

    ----------------------------------------------------------------------
    -- Float
    FloatLit{} -> knownRepr
    DoubleLit{} -> knownRepr
    FloatNaN fi -> FloatRepr fi
    FloatPInf fi -> FloatRepr fi
    FloatNInf fi -> FloatRepr fi
    FloatPZero fi -> FloatRepr fi
    FloatNZero fi -> FloatRepr fi
    FloatNeg fi _ -> FloatRepr fi
    FloatAbs fi _ -> FloatRepr fi
    FloatSqrt fi _ _ -> FloatRepr fi
    FloatAdd fi _ _ _ -> FloatRepr fi
    FloatSub fi _ _ _ -> FloatRepr fi
    FloatMul fi _ _ _ -> FloatRepr fi
    FloatDiv fi _ _ _ -> FloatRepr fi
    FloatRem fi _ _ -> FloatRepr fi
    FloatMin fi _ _ -> FloatRepr fi
    FloatMax fi _ _ -> FloatRepr fi
    FloatFMA fi _ _ _ _ -> FloatRepr fi
    FloatEq{} -> knownRepr
    FloatFpEq{} -> knownRepr
    FloatLt{} -> knownRepr
    FloatLe{} -> knownRepr
    FloatGt{} -> knownRepr
    FloatGe{} -> knownRepr
    FloatNe{} -> knownRepr
    FloatFpNe{} -> knownRepr
    FloatIte fi _ _ _ -> FloatRepr fi
    FloatCast fi _ _ -> FloatRepr fi
    FloatFromBinary fi _ -> FloatRepr fi
    FloatToBinary fi _ -> case floatInfoToBVTypeRepr fi of
      BaseBVRepr w -> BVRepr w
    FloatFromBV fi _ _ -> FloatRepr fi
    FloatFromSBV fi _ _ -> FloatRepr fi
    FloatFromReal fi _ _ -> FloatRepr fi
    FloatToBV w _ _ -> BVRepr w
    FloatToSBV w _ _ -> BVRepr w
    FloatToReal{} -> knownRepr
    FloatIsNaN{} -> knownRepr
    FloatIsInfinite{} -> knownRepr
    FloatIsZero{} -> knownRepr
    FloatIsPositive{} -> knownRepr
    FloatIsNegative{} -> knownRepr
    FloatIsSubnormal{} -> knownRepr
    FloatIsNormal{} -> knownRepr

    ----------------------------------------------------------------------
    -- Maybe

    JustValue tp _ -> MaybeRepr tp
    NothingValue tp -> MaybeRepr tp
    FromJustValue tp _ _ -> tp

    ----------------------------------------------------------------------
    -- Side conditions
    AddSideCondition tp _ _ _ -> baseToType tp

    ----------------------------------------------------------------------
    -- Recursive Types

    RollRecursive nm ctx _ -> RecursiveRepr nm ctx
    UnrollRecursive nm ctx _ -> unrollType nm ctx

    ----------------------------------------------------------------------
    -- Vector
    VectorIsEmpty{}          -> knownRepr
    VectorSize{}             -> knownRepr
    VectorLit       tp _     -> VectorRepr tp
    VectorReplicate tp _ _   -> VectorRepr tp
    VectorGetEntry  tp _ _   -> tp
    VectorSetEntry  tp _ _ _ -> VectorRepr tp
    VectorCons      tp _ _   -> VectorRepr tp

    ----------------------------------------------------------------------
    -- SymbolicArrayType

    SymArrayLookup b _ _ -> baseToType b
    SymArrayUpdate b _ idx _ ->
      baseToType (BaseArrayRepr (fmapFC baseTermType idx) b)

    ----------------------------------------------------------------------
    -- WordMap
    EmptyWordMap w tp -> WordMapRepr w tp
    InsertWordMap w tp _ _ _ -> WordMapRepr w tp
    LookupWordMap tp _ _ -> baseToType tp
    LookupWordMapWithDefault tp _ _ _ -> baseToType tp

    ----------------------------------------------------------------------
    -- Handle

    HandleLit h -> handleType h
    Closure a r _ _ _ ->
      FunctionHandleRepr a r

    ----------------------------------------------------------------------
    -- Polymorphic functions
    
    PolyHandleLit h -> PolyFnRepr (handleArgTypes h) (handleReturnType h)
    PolyInstantiate (PolyFnRepr args tp) _ subst ->
      FunctionHandleRepr (instantiateCtxRepr subst args)
                         (instantiateRepr subst tp)


    ----------------------------------------------------------------------
    -- Conversions
    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    RealToNat{} -> knownRepr
    RealRound{} -> knownRepr
    RealFloor{} -> knownRepr
    RealCeil{} -> knownRepr
    IntegerToBV w _ -> BVRepr w

    ----------------------------------------------------------------------
    -- ComplexReal
    Complex{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    ----------------------------------------------------------------------
    -- BV
    BVUndef w -> BVRepr w
    BVLit w _ -> BVRepr w
    BVTrunc w _ _ -> BVRepr w
    BVZext w _ _ -> BVRepr w
    BVSext w _ _ -> BVRepr w

    BVNot w _ -> BVRepr w
    BVAnd w _ _ -> BVRepr w
    BVOr  w _ _ -> BVRepr w
    BVXor  w _ _ -> BVRepr w
    BVNeg w _ -> BVRepr w
    BVAdd w _ _ -> BVRepr w
    BVSub w _ _ -> BVRepr w
    BVMul w _ _ -> BVRepr w
    BVUdiv w _ _ -> BVRepr w
    BVSdiv w _ _ -> BVRepr w
    BVUrem w _ _ -> BVRepr w
    BVSrem w _ _ -> BVRepr w
    BVUle{} -> knownRepr
    BVUlt{} -> knownRepr
    BVSle{} -> knownRepr
    BVSlt{} -> knownRepr
    BVCarry{} -> knownRepr
    BVSCarry{} -> knownRepr
    BVSBorrow{} -> knownRepr
    BVShl w _ _ -> BVRepr w
    BVLshr w _ _ -> BVRepr w
    BVAshr w _ _ -> BVRepr w

    BoolToBV w _ -> BVRepr w
    BvToNat{} -> knownRepr
    BvToInteger{} -> knownRepr
    SbvToInteger{} -> knownRepr
    BVNonzero{} -> knownRepr
    BVSelect _ n _ _ -> BVRepr n
    BVConcat w1 w2 _ _ -> BVRepr (addNat w1 w2)

    ----------------------------------------------------------------------
    -- Struct

    MkStruct ctx _ -> StructRepr ctx
    GetStruct _ _ tp -> tp
    SetStruct ctx _ _ _ -> StructRepr ctx

    ----------------------------------------------------------------------
    -- Variants

    InjectVariant ctx _ _ -> VariantRepr ctx
    ProjectVariant ctx idx _ -> MaybeRepr (ctx Ctx.! idx)

    ----------------------------------------------------------------------
    -- StringMap
    EmptyStringMap tp             -> StringMapRepr tp
    LookupStringMapEntry tp _ _   -> MaybeRepr tp
    InsertStringMapEntry tp _ _ _ -> StringMapRepr tp

    ----------------------------------------------------------------------
    -- String

    TextLit{} -> knownRepr
    ShowValue{} -> knownRepr
    AppendString{} -> knownRepr

    ------------------------------------------------------------------------
    -- Introspection

    IsConcrete _ _ -> knownRepr

    ------------------------------------------------------------------------
    -- References

    ReferenceEq{} -> knownRepr


----------------------------------------------------------------------------
-- Utility operations

testFnHandle :: FnHandle a1 r1 -> FnHandle a2 r2 -> Maybe (FnHandle a1 r1 :~: FnHandle a2 r2)
testFnHandle x y = do
  Refl <- testEquality (handleID x) (handleID y)
  return $! Refl

compareFnHandle :: FnHandle a1 r1
                -> FnHandle a2 r2
                -> OrderingF (FnHandle a1 r1) (FnHandle a2 r2)
compareFnHandle x y = do
  case compareF (handleID x) (handleID y) of
    LTF -> LTF
    GTF -> GTF
    EQF -> EQF

testVector :: (forall x y. f x -> f y -> Maybe (x :~: y))
           -> Vector (f tp) -> Vector (f tp) -> Maybe (Int :~: Int)
testVector testF x y = do
  case V.zipWithM_ testF x y of
    Just () -> Just Refl
    Nothing -> Nothing

compareVector :: forall f tp. (forall x y. f x -> f y -> OrderingF x y)
              -> Vector (f tp) -> Vector (f tp) -> OrderingF Int Int
compareVector cmpF x y
    | V.length x < V.length y = LTF
    | V.length x > V.length y = GTF
    | otherwise = V.foldr go EQF (V.zip x y)
  where go :: forall z. (f z, f z) -> OrderingF Int Int -> OrderingF Int Int
        go (u,v) r =
          case cmpF u v of
            LTF -> LTF
            GTF -> GTF
            EQF -> r

-- Force app to be in context.
$(return [])

------------------------------------------------------------------------
-- Pretty printing

ppBaseTermAssignment :: (forall u . f u -> Doc)
                     -> Ctx.Assignment (BaseTerm f) ctx
                     -> Doc
ppBaseTermAssignment pp v = brackets (commas (toListFC (pp . baseTermVal) v))

instance PrettyApp (ExprExtension ext) => PrettyApp (App ext) where
  --ppApp :: (forall a . f a -> Doc) -> App ext f b -> Doc
  ppApp = $(U.structuralPretty [t|App|]
          [ ( U.ConType [t|Ctx.Assignment|]
              `U.TypeApp` (U.ConType [t|BaseTerm|] `U.TypeApp` U.DataArg 1)
              `U.TypeApp` U.AnyType
            , [| ppBaseTermAssignment |]
            )
          , (U.ConType [t|ExprExtension|] `U.TypeApp`
                  U.DataArg 0 `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType,
              [| ppApp |]
            )
          , ( U.ConType [t|Vector|] `U.TypeApp` U.AnyType
            , [| \pp v -> brackets (commas (fmap pp v)) |]
            )
          ])

------------------------------------------------------------------------
-- TraverseApp (requires TemplateHaskell)

traverseBaseTerm :: Applicative m
                  => (forall tp . f tp -> m (g tp))
                  -> Ctx.Assignment (BaseTerm f) x
                  -> m (Ctx.Assignment (BaseTerm g) x)
traverseBaseTerm f = traverseFC (traverseFC f)

-- | Traversal that performs the given action on each immediate
-- subterm of an application. Used for the 'TraversableFC' instance.
traverseApp :: (TraversableFC (ExprExtension ext), Applicative m)
            => (forall u . f u -> m (g u))
            -> App ext f tp -> m (App ext g tp)
traverseApp =
  $(U.structuralTraversal [t|App|]
     [
       ( U.ConType [t|Ctx.Assignment|] `U.TypeApp` (U.DataArg 1) `U.TypeApp` U.AnyType
       , [|traverseFC|]
       )
     , (U.ConType [t|ExprExtension|] `U.TypeApp`
             U.DataArg 0 `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType,
         [| traverseFC |]
       )
     , ( U.ConType [t|Ctx.Assignment|]
         `U.TypeApp` (U.ConType [t|BaseTerm|] `U.TypeApp` (U.DataArg 1))
         `U.TypeApp` U.AnyType
       , [| traverseBaseTerm |]
       )
     ])

------------------------------------------------------------------------------
-- Parameterized Eq and Ord instances

instance TestEqualityFC (ExprExtension ext) => TestEqualityFC (App ext) where
  testEqualityFC testSubterm
      = $(U.structuralTypeEquality [t|App|]
                   [ (U.DataArg 1                   `U.TypeApp` U.AnyType, [|testSubterm|])
                   , (U.ConType [t|ExprExtension|] `U.TypeApp`
                           U.DataArg 0 `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType,
                       [|testEqualityFC testSubterm|]
                     )
                   , (U.ConType [t|NatRepr |]       `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|SymbolRepr |]    `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|TypeRepr|]       `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|BaseTypeRepr|]  `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|FloatInfoRepr|]  `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|Ctx.Assignment|] `U.TypeApp`
                         (U.ConType [t|BaseTerm|] `U.TypeApp` U.AnyType) `U.TypeApp` U.AnyType
                     , [| testEqualityFC (testEqualityFC testSubterm) |]
                     )
                   , (U.ConType [t|Ctx.Assignment|] `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType
                     , [| testEqualityFC testSubterm |]
                     )
                   , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType
                     , [| testEquality |]
                     )
                   , (U.ConType [t|Ctx.Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|FnHandle|]  `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testFnHandle|])
                   , (U.ConType [t|Vector|]    `U.TypeApp` U.AnyType, [|testVector testSubterm|])
                   ]
                  )

instance (TestEqualityFC (ExprExtension ext), TestEquality f) => TestEquality (App ext f) where
  testEquality = testEqualityFC testEquality

instance OrdFC (ExprExtension ext) => OrdFC (App ext) where
  compareFC compareSubterm
        = $(U.structuralTypeOrd [t|App|]
                   [ (U.DataArg 1            `U.TypeApp` U.AnyType, [|compareSubterm|])
                   , (U.ConType [t|ExprExtension|] `U.TypeApp`
                           U.DataArg 0 `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType,
                       [|compareFC compareSubterm|]
                     )
                   , (U.ConType [t|NatRepr |] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|SymbolRepr |] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|BaseTypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|FloatInfoRepr|] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|Ctx.Assignment|] `U.TypeApp`
                         (U.ConType [t|BaseTerm|] `U.TypeApp` U.AnyType) `U.TypeApp` U.AnyType
                     , [| compareFC (compareFC compareSubterm) |]
                     )
                   , (U.ConType [t|Ctx.Assignment|] `U.TypeApp` U.DataArg 1 `U.TypeApp` U.AnyType
                     , [| compareFC compareSubterm |]
                     )
                   , ( U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType
                     , [| compareF |]
                     )
                   , (U.ConType [t|Ctx.Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|FnHandle|]  `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareFnHandle|])
                   , (U.ConType [t|Vector|]    `U.TypeApp` U.AnyType, [|compareVector compareSubterm|])
                   ]
                  )
instance (OrdFC (ExprExtension ext), OrdF f) => OrdF (App ext f) where
  compareF = compareFC compareF

-------------------------------------------------------------------------------------
-- Traversals and such

instance TraversableFC (ExprExtension ext) => FunctorFC (App ext) where
  fmapFC = fmapFCDefault

instance TraversableFC (ExprExtension ext) => FoldableFC (App ext) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (ExprExtension ext) => TraversableFC (App ext) where
  traverseFC = traverseApp

-- | Fold over an application.
foldApp :: TraversableFC (ExprExtension ext)
        => (forall x . f x -> r -> r)
        -> r
        -> App ext f tp
        -> r
foldApp f0 r0 a = execState (traverseApp (go f0) a) r0
  where go f v = v <$ modify (f v)

-- | Map a Crucible-type-preserving function over the immediate
-- subterms of an application.
mapApp :: TraversableFC (ExprExtension ext)
       => (forall u . f u -> g u) -> App ext f tp -> App ext g tp
mapApp f a = runIdentity (traverseApp (pure . f) a)

-------------------------------------------------------------------------------------
-- Type Instantiation

-- App :: Type -> (CrucibleType -> Type) -> CrucibleType -> Type
type instance Instantiate subst App = App  
instance (IsSyntaxExtension ext) => InstantiateFC (App ext) where
   instantiateFC (subst :: CtxRepr subst) app 
      | Refl <- closedType @ext subst,
        Refl <- closedFC @_ @_ @(ExprExtension ext) subst =
      case app of
          ExtensionApp ext -> ExtensionApp (instantiate subst ext)
          
          BaseIsEq bty r1 r2 -> BaseIsEq bty (instantiate subst r1) (instantiate subst r2)
          BaseIte bty r1 r2 r3 -> BaseIte bty (instantiate subst r1)
            (instantiate subst r2) (instantiate subst r3)
          EmptyApp -> EmptyApp
          PackAny ty reg   -> PackAny (instantiateRepr subst ty) (instantiate subst reg)
          UnpackAny ty reg -> UnpackAny (instantiateRepr subst ty) (instantiate subst reg)
          BoolLit b -> BoolLit b
          Not r1 -> Not (instantiate subst r1)
          And r1 r2 -> And (instantiate subst r1) (instantiate subst r2)
          Or r1 r2 -> Or (instantiate subst r1) (instantiate subst r2)
          BoolXor r1 r2 -> BoolXor (instantiate subst r1) (instantiate subst r2)
          NatLit n -> NatLit n
          NatLt  r1 r2 -> NatLt  (instantiate subst r1) (instantiate subst r2)
          NatLe  r1 r2 -> NatLe  (instantiate subst r1) (instantiate subst r2)
          NatAdd r1 r2 -> NatAdd (instantiate subst r1) (instantiate subst r2)
          NatSub r1 r2 -> NatSub (instantiate subst r1) (instantiate subst r2)
          NatMul r1 r2 -> NatMul (instantiate subst r1) (instantiate subst r2)
          NatDiv r1 r2 -> NatDiv (instantiate subst r1) (instantiate subst r2)
          NatMod r1 r2 -> NatMod (instantiate subst r1) (instantiate subst r2)

          IntLit n -> IntLit n
          IntLt  r1 r2 -> IntLt  (instantiate subst r1) (instantiate subst r2)
          IntLe  r1 r2 -> IntLe  (instantiate subst r1) (instantiate subst r2)
          IntNeg r1    -> IntNeg (instantiate subst r1)
          IntAdd r1 r2 -> IntAdd (instantiate subst r1) (instantiate subst r2)
          IntSub r1 r2 -> IntSub (instantiate subst r1) (instantiate subst r2)
          IntMul r1 r2 -> IntMul (instantiate subst r1) (instantiate subst r2)
          IntDiv r1 r2 -> IntDiv (instantiate subst r1) (instantiate subst r2)
          IntMod r1 r2 -> IntMod (instantiate subst r1) (instantiate subst r2)
          IntAbs r1    -> IntAbs (instantiate subst r1)

          RationalLit n -> RationalLit n
          RealLt  r1 r2 -> RealLt  (instantiate subst r1) (instantiate subst r2)
          RealLe  r1 r2 -> RealLe  (instantiate subst r1) (instantiate subst r2)
          RealNeg r1    -> RealNeg (instantiate subst r1)
          RealAdd r1 r2 -> RealAdd (instantiate subst r1) (instantiate subst r2)
          RealSub r1 r2 -> RealSub (instantiate subst r1) (instantiate subst r2)
          RealMul r1 r2 -> RealMul (instantiate subst r1) (instantiate subst r2)
          RealDiv r1 r2 -> RealDiv (instantiate subst r1) (instantiate subst r2)
          RealMod r1 r2 -> RealMod (instantiate subst r1) (instantiate subst r2)
          RealIsInteger r1 -> RealIsInteger (instantiate subst r1)

          FloatLit n    -> FloatLit n
          DoubleLit d   -> DoubleLit d
          FloatNaN fi   -> FloatNaN fi
          FloatPInf fi  -> FloatPInf fi
          FloatNInf fi  -> FloatNInf fi
          FloatPZero fi -> FloatPZero fi
          FloatNZero fi -> FloatNZero fi

          FloatNeg fi r1    -> FloatNeg fi (instantiate subst r1)
          FloatAbs fi r1    -> FloatAbs fi (instantiate subst r1)
          FloatSqrt fi rm r1  -> FloatSqrt fi rm (instantiate subst r1)
          FloatAdd fi rm r1 r2 -> FloatAdd fi rm (instantiate subst r1) (instantiate subst r2)
          FloatSub fi rm r1 r2 -> FloatSub fi rm (instantiate subst r1) (instantiate subst r2)
          FloatMul fi rm r1 r2 -> FloatMul fi rm (instantiate subst r1) (instantiate subst r2)
          FloatDiv fi rm r1 r2 -> FloatDiv fi rm (instantiate subst r1) (instantiate subst r2)
          FloatRem fi r1 r2 -> FloatRem fi (instantiate subst r1) (instantiate subst r2)
          FloatMin fi r1 r2 -> FloatMin fi (instantiate subst r1) (instantiate subst r2)
          FloatMax fi r1 r2 -> FloatMax fi (instantiate subst r1) (instantiate subst r2)
          FloatFMA fi rm r1 r2 r3 -> FloatFMA fi rm (instantiate subst r1) (instantiate subst r2) (instantiate subst r3)

          FloatEq  r1 r2 -> FloatEq  (instantiate subst r1) (instantiate subst r2)
          FloatFpEq  r1 r2 -> FloatFpEq  (instantiate subst r1) (instantiate subst r2)          
          FloatGt  r1 r2 -> FloatGt  (instantiate subst r1) (instantiate subst r2)
          FloatGe  r1 r2 -> FloatGe  (instantiate subst r1) (instantiate subst r2)
          FloatLt  r1 r2 -> FloatLt  (instantiate subst r1) (instantiate subst r2)
          FloatLe  r1 r2 -> FloatLe  (instantiate subst r1) (instantiate subst r2)
          FloatNe  r1 r2 -> FloatNe  (instantiate subst r1) (instantiate subst r2)
          FloatFpNe  r1 r2 -> FloatFpNe  (instantiate subst r1) (instantiate subst r2)          

          FloatIte fi r1 r2 r3 -> FloatIte fi (instantiate subst r1) (instantiate subst r2) (instantiate subst r3)
          

          -- TODO: more floats

          JustValue ty r1 -> JustValue (instantiateRepr subst ty) (instantiate subst r1)
          NothingValue ty -> NothingValue (instantiateRepr subst ty) 
          FromJustValue ty r1 r2 -> FromJustValue (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)

          AddSideCondition bty r1 s r2 -> AddSideCondition bty (instantiate subst r1) s (instantiate subst r2)

          RollRecursive (sr :: SymbolRepr nm) (ctr :: CtxRepr ctx) r1
            | Refl <- eqInstUnroll @nm @_ @_ @ctx subst -> RollRecursive sr (instantiate subst ctr) (instantiate subst r1)
          UnrollRecursive (sr :: SymbolRepr nm) (ctr :: CtxRepr ctx) r1
            | Refl <- eqInstUnroll @nm @_ @_ @ctx subst -> UnrollRecursive sr (instantiate subst ctr) (instantiate subst r1)

          VectorLit ty v1 -> VectorLit  (instantiateRepr subst ty) (V.map (instantiate subst) v1)
          VectorReplicate ty r1 r2 -> VectorReplicate (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)
          VectorIsEmpty r1 -> VectorIsEmpty (instantiate subst r1)
          VectorSize r1 -> VectorSize (instantiate subst r1)
          VectorGetEntry ty r1 r2 -> VectorGetEntry (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)
          VectorSetEntry ty r1 r2 r3 ->
            VectorSetEntry  (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2) (instantiate subst r3)
          VectorCons ty r1 r2 ->
            VectorCons  (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)


          HandleLit fh ->
            -- We need a precondition that bare function handle literals in expressions do not contain any type parameters
            -- If this is true, we know that
            --    (Instantiate subst (FunctionHandleType args ret) ~ FunctionHandleType args ret)
            -- maybe we want to add a ClosedType constraint to the HandleLit constructor?
            unsafeCoerce (HandleLit fh)

          Closure argTy retTy r1 (tp :: TypeRepr tp) r2
            | Refl <- closed @tp subst
            ->
              Closure (instantiateCtxRepr subst argTy)
                      (instantiateRepr subst retTy)
                      (instantiate subst r1) (instantiate subst tp) (instantiate subst r2)

          PolyHandleLit fh -> PolyHandleLit fh

          PolyInstantiate (ty :: TypeRepr (PolyFnType args ret)) r1 (targs :: CtxRepr targs) 
            | Refl <- composeInstantiateAxiom @subst @targs @ret,
              Refl <- composeInstantiateAxiom @subst @targs @args 
            ->
              PolyInstantiate ty (instantiate subst r1) (instantiateCtxRepr subst targs)


          NatToInteger r1 -> NatToInteger (instantiate subst r1)
          IntegerToReal r1 -> IntegerToReal (instantiate subst r1)
          RealRound r1 -> RealRound (instantiate subst r1)
          RealFloor r1 -> RealFloor (instantiate subst r1)
          RealCeil r1 -> RealCeil (instantiate subst r1)
          IntegerToBV n r1 -> IntegerToBV n (instantiate subst r1)
          RealToNat r1 -> RealToNat (instantiate subst r1)

          Complex r1 r2 -> Complex (instantiate subst r1) (instantiate subst r2)
          RealPart r1 -> RealPart (instantiate subst r1)
          ImagPart r1 -> ImagPart (instantiate subst r1)


          -- bv
          BVUndef nr -> BVUndef nr
          BVLit nr i -> BVLit nr i
          BVConcat n1 n2 r1 r2 -> BVConcat n1 n2 (instantiate subst r1) (instantiate subst r2)
          BVSelect n1 n2 n3 r1 -> BVSelect n1 n2 n3 (instantiate subst r1)
          BVTrunc n1 n2 r1 -> BVTrunc n1 n2 (instantiate subst r1)

          -- more BV

          InjectVariant ctx idx r1 -> InjectVariant (instantiateCtxRepr subst ctx) (instantiate subst idx)
            (instantiate subst r1)
          ProjectVariant ctx idx r1 -> ProjectVariant (instantiateCtxRepr subst ctx) (instantiate subst idx)
            (instantiate subst r1) 

          MkStruct ctx args -> MkStruct (instantiateCtxRepr subst ctx) (instantiate subst args)
          GetStruct r1 idx ty -> GetStruct (instantiate subst r1) (instantiate subst idx) (instantiateRepr subst ty)
          SetStruct ctx r1 idx r2 -> SetStruct (instantiateCtxRepr subst ctx) (instantiate subst r1)
            (instantiate subst idx) (instantiate subst r2)

          EmptyStringMap ty -> EmptyStringMap (instantiateRepr subst ty)
          LookupStringMapEntry ty r1 r2 -> LookupStringMapEntry (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)
          InsertStringMapEntry ty r1 r2 r3 -> InsertStringMapEntry (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2) (instantiate subst r3)


          TextLit t -> TextLit t
          ShowValue btr r1 -> ShowValue btr (instantiate subst r1)
          AppendString r1 r2 -> AppendString (instantiate subst r1) (instantiate subst r2)

          -- Sym Arrays
{-          SymArrayLookup :: forall (b :: BaseType) (f :: CrucibleType
                                                         -> *) (idx :: Ctx
                                                                         BaseType) (tp :: BaseType) ext.
                            BaseTypeRepr b
                            -> f (SymbolicArrayType (idx ::> tp) b)
                            -> Ctx.Assignment (BaseTerm f) (idx ::> tp)
                            -> App ext f (BaseToType b), -}

          SymArrayLookup (br :: BaseTypeRepr br) r1 (ctx :: Ctx.Assignment (BaseTerm f) (idx ::> tp))
            | Refl <- closedBT @br subst,
              Refl <- closedBT @tp subst
            -> undefined -- SymArrayLookup br (instantiate subst r1) (instantiate subst ctx)
          SymArrayUpdate (br :: BaseTypeRepr br) r1 ctx r2
            | Refl <- closedBT @br subst
            -> undefined -- SymArrayUpdate br (instantiate subst r1) (instantiate subst ctx) (instantiate subst r2)

          IsConcrete btr r1 -> IsConcrete btr (instantiate subst r1)

          ReferenceEq ty r1 r2 -> ReferenceEq (instantiateRepr subst ty) (instantiate subst r1) (instantiate subst r2)
