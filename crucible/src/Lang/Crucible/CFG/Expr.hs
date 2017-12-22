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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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
    -- * Base terms
  , BaseTerm(..)
  , module Lang.Crucible.CFG.Extension
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

import           Lang.MATLAB.CharVector (CharVector)
import           Lang.MATLAB.MatlabChar
import           Lang.MATLAB.Utils.PrettyPrint

import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types
import           Lang.Crucible.FunctionHandle
import qualified Lang.Crucible.Utils.Structural as U

------------------------------------------------------------------------
-- BaseTerm

-- | Base terms represent the subset of expressions
--   of base types, packaged together with a run-time
--   representation of their type.
data BaseTerm (f :: CrucibleType -> *) tp
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

------------------------------------------------------------------------
-- App

-- | The main Crucible expression datastructure, defined as a
-- multisorted algebra. Type @'App' f tp@ encodes the top-level
-- application of a Crucible expression. The type parameter @tp@ is a
-- type index that indicates the Crucible type of the values denoted
-- by the given expression form. Parameter @f@ is used everywhere a
-- recursive sub-expression would go.  Uses of the 'App' type will
-- tie the knot through this parameter.
data App (ext :: *) (f :: CrucibleType -> *) (tp :: CrucibleType) where

  ----------------------------------------------------------------------
  -- Syntax Extension 

  ExtensionApp :: !(ExprExtension ext f tp) -> App ext f tp

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

  ----------------------------------------------------------------------
  -- Concrete

  -- Constructs a literal of concrete type
  ConcreteLit :: !(TypeableValue a)
              -> App ext f (ConcreteType a)

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

  -- Exclusive or of Boolean values.
  BoolIte :: !(f BoolType)
          -> !(f BoolType)
          -> !(f BoolType)
          -> App ext f BoolType

  ----------------------------------------------------------------------
  -- Nat

  -- @NatLit n@ returns the value n.
  NatLit :: !Natural -> App ext f NatType
  -- Equality on natural numbers.
  NatEq :: !(f NatType) -> !(f NatType) -> App ext f BoolType
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

  ----------------------------------------------------------------------
  -- Integer

  -- Create a singleton real array from a numeric literal.
  IntLit :: !Integer -> App ext f IntegerType
  -- Add two integers.
  IntAdd :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Subtract one integer from another.
  IntSub :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType
  -- Multiple two integers.
  IntMul :: !(f IntegerType) -> !(f IntegerType) -> App ext f IntegerType

  IntEq :: !(f IntegerType) -> !(f IntegerType) -> App ext f BoolType
  IntLt :: !(f IntegerType) -> !(f IntegerType) -> App ext f BoolType

  ----------------------------------------------------------------------
  -- RealVal

  -- A real constant
  RationalLit :: !Rational -> App ext f RealValType

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

  -- Return first or second number depending on condition.
  RealIte :: !(f BoolType) -> !(f RealValType) -> !(f RealValType) -> App ext f RealValType

  RealEq :: !(f RealValType) -> !(f RealValType) -> App ext f BoolType
  RealLt :: !(f RealValType) -> !(f RealValType) -> App ext f BoolType
  -- Return true if real value is integer.
  RealIsInteger :: !(f RealValType) -> App ext f BoolType

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

  -----------------------------
  -- SymbolicMultiDimArray


  MatlabSymArrayDim :: !(f (SymbolicMultiDimArrayType tp))
                      -> App ext f ArrayDimType

  -- Create an array of containing a single value.
  MatlabSymArrayReplicate :: !(BaseTypeRepr tp)
                          -> !(f ArrayDimType)
                          -> !(f (BaseToType tp))
                          -> App ext f (SymbolicMultiDimArrayType tp)

  -- Get value in array at index.
  MatlabSymArrayLookup :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType  bt))
                       -> !(f (VectorType NatType))
                       -> App ext f (BaseToType bt)

  -- Set value of array at index.
  MatlabSymArrayUpdate :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType  bt))
                       -> !(f (VectorType NatType))
                       -> !(f (BaseToType bt))
                       -> App ext f (SymbolicMultiDimArrayType bt)
  -- Project array as a single scalar value if it is one.
  MatlabSymArrayAsSingleton :: !(BaseTypeRepr bt)
                            -> !(f (SymbolicMultiDimArrayType bt))
                            -> App ext f (MaybeType (BaseToType bt))

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the given default value.
  MatlabSymArrayResize :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType bt))
                       -> !(f ArrayDimType)
                       -> !(f (BaseToType bt)) -- The default value.
                       -> App ext f (SymbolicMultiDimArrayType bt)

  -- Index array at the given indices.
  -- This function is not defined outside the array bounds.
  MatlabSymIndexArray :: !(BaseTypeRepr tp)
                      -> !(f (SymbolicMultiDimArrayType tp))
                      -> !(f MultiDimArrayIndexType)
                      -> App ext f (MultiDimArrayType (BaseToType tp))

  -- Index a symbolic multidim array at the given symbolic indices.
  MatlabSymArraySymIndex :: !(BaseTypeRepr tp)
                         -> !(f (SymbolicMultiDimArrayType tp))
                         -> !(V.Vector (f (SymbolicMultiDimArrayType BaseNatType)))
                         -> App ext f (SymbolicMultiDimArrayType tp)

  -- Convert a MATLAB symbolic array into a MATLAB external
  -- multidimensional-array.
  MatlabSymArrayExternalize
                :: !(BaseTypeRepr tp)
                -> !(f (SymbolicMultiDimArrayType tp))
                -> App ext f (MultiDimArrayType (BaseToType tp))

  -- Convert a MATLAB external multidimensional array into a
  -- symbolic array.
  MatlabArrayInternalize
                :: !(BaseTypeRepr tp)
                -> !(f (MultiDimArrayType (BaseToType tp)))
                -> App ext f (SymbolicMultiDimArrayType tp)

  --------------------------------------------------------------------
  -- MultiDimArray

  -- Empty array
  ArrayEmpty :: !(TypeRepr tp) -> App ext f (MultiDimArrayType tp)
  -- Create an array of constants.
  ArrayReplicate :: !(TypeRepr tp)
                 -> !(f ArrayDimType)
                 -> !(f tp)
                 -> App ext f (MultiDimArrayType tp)
  -- Return dimension of array.
  ArrayDim   :: !(f (MultiDimArrayType tp))
             -> App ext f ArrayDimType

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the given default value.
  ArrayResize :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f ArrayDimType)
              -> !(f tp) -- Default value
              -> App ext f (MultiDimArrayType tp)
  -- Get value in array at 1-based index of vectors.
  ArrayLookup :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f (VectorType NatType))
              -> App ext f tp
  -- Set value of array at index.
  ArrayUpdate :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f (VectorType NatType))
              -> !(f tp)
              -> App ext f (MultiDimArrayType tp)
  -- Project array as a single scalar value if it is one.
  ArrayAsSingleton :: !(TypeRepr tp)
                   -> !(f (MultiDimArrayType tp))
                   -> App ext f (MaybeType tp)

  -- Index array at the given indices.
  -- This function is not defined outside the array bounds.
  IndexArray :: !(TypeRepr tp)
             -> !(f (MultiDimArrayType tp))
             -> !(f MultiDimArrayIndexType)
             -> App ext f (MultiDimArrayType  tp)
  -- Get value in array at a single specific index.
  -- Not defined when evaluated if the cell entry is out of range,
  -- or expression contains multiple indices.
  ArrayEntry :: !(TypeRepr tp)
             -> !(f (MultiDimArrayType tp))
             -> !(f (VectorType NatType))
             -> App ext f tp

  -- @ArrayProduct _ v@ converts a vector of multidimensional arrays into
  -- a multidimensional array of vectors.
  ArrayProduct :: !(TypeRepr tp)
               -> !(Vector (f (MultiDimArrayType tp)))
               -> App ext f (MultiDimArrayType (VectorType tp))

  -- Return the vector associated with a multi-dimensional array
  MultiDimArrayToVec :: !(TypeRepr tp)
                     -> !(f (MultiDimArrayType tp))
                     -> App ext f (VectorType tp)

  -- Index an external multidim array at the given symbolic indices.
  MatlabExtArraySymIndex :: !(TypeRepr tp)
                         -> !(f (MultiDimArrayType tp))
                         -> !(V.Vector (f (SymbolicMultiDimArrayType BaseNatType)))
                         -> App ext f (MultiDimArrayType tp)

  ----------------------------------------------------------------------
  -- Conversion to vector based indexing.

  -- @CplxVecToIndex@ converts the vector to a vector of natural numbers.
  --
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  CplxVecToNat :: !(f (VectorType ComplexRealType))
                 -> App ext f (VectorType NatType)

  -- @LogicVecToIndex@ converts the vector of predicates to a vector of
  -- natural numbers.
  --
  -- The resulting vector contains the 1-based index of each true
  -- value in the vector.
  LogicVecToIndex :: !(f (VectorType BoolType))
                  -> App ext f (VectorType NatType)

  -- @MatlabCharVecToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabCharVecToNat :: !(f (VectorType CharType))
                     -> App ext f (VectorType NatType)

  -- @MatlabIntArrayToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabIntArrayToNat :: !(f MatlabIntArrayType)
                      -> App ext f (VectorType NatType)

  -- @MatlabUIntArrayToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabUIntArrayToNat :: !(f MatlabUIntArrayType)
                       -> App ext f (VectorType NatType)

  ----------------------------------------------------------------------
  -- Handle

  HandleLit :: !(FnHandle args ret)
            -> App ext f (FunctionHandleType args ret)

  -- Create a closure that captures the last argument.
  Closure :: !(CtxRepr args)
          -> !(TypeRepr ret)
          -> !(f (FunctionHandleType (args::>tp) ret))
          -> !(TypeRepr tp)
          -> !(f tp)
          -> App ext f (FunctionHandleType args ret)

  ----------------------------------------------------------------------
  -- PosNat

  -- EnumTo n creates a column array with n columns containing values 1 to n.
  EnumTo :: !(f NatType)
         -> App ext f (MultiDimArrayType NatType)

  ----------------------------------------------------------------------
  -- Conversions

  -- @NatToInteger@ convert a natural number to an integer.
  NatToInteger :: !(f NatType) -> App ext f IntegerType

  -- @IntegerToReal@ convert an integer to a real.
  IntegerToReal :: !(f IntegerType) -> App ext f RealValType

  -- @RealToNat@ convert a non-negative real integer to natural number.
  -- This is partial, and requires that the input be a non-negative real
  -- integer.
  RealToNat :: !(f RealValType)
            -> App ext f NatType

  ----------------------------------------------------------------------
  -- ComplexReal

  -- Create complex number from two real numbers.
  Complex :: !(f RealValType) -> !(f RealValType) -> App ext f ComplexRealType
  RealPart :: !(f ComplexRealType) -> App ext f RealValType
  ImagPart :: !(f ComplexRealType) -> App ext f RealValType

  ----------------------------------------------------------------------
  -- MatlabChar

  MatlabCharLit :: !MatlabChar
                -> App ext f CharType

  -- Compare of two characters are equal.
  MatlabCharEq :: !(f CharType)
               -> !(f CharType)
               -> App ext f BoolType

  -- Convert a Matlab character (16-bit word) to a natural number.
  -- This is total.
  MatlabCharToNat :: !(f CharType) -> App ext f NatType

  ----------------------------------------------------------------------
  -- CplxArrayType

  -- Compare real arrays (arrays with different dimensions are not equal).
  CplxArrayEq  :: !(f CplxArrayType)
               -> !(f CplxArrayType)
               -> App ext f BoolType
  -- Return true if all entries in array are real values (i.e. have 0 in imaginary part).
  CplxArrayIsReal :: !(f CplxArrayType) -> App ext f BoolType


  CplxArrayToRealArray :: !(f CplxArrayType)
                       -> App ext f RealArrayType

  CharArrayToIntegerArray  :: !(f (CharArrayType))
                          -> App ext f IntegerArrayType
  LogicArrayToIntegerArray :: !(f (LogicArrayType))
                          -> App ext f IntegerArrayType
  IntArrayToIntegerArray :: !(f (MatlabIntArrayType))
                          -> App ext f IntegerArrayType
  UIntArrayToIntegerArray :: !(f (MatlabUIntArrayType))
                          -> App ext f IntegerArrayType

  -- Converts a real array to an integer array.
  --
  -- Result is undefined if real values are not integers.
  RealArrayToIntegerArray :: !(f RealArrayType)
                       -> App ext f IntegerArrayType

  CplxArrayToIntegerArray :: !(f CplxArrayType)
                       -> App ext f IntegerArrayType

  RealArrayToCplxArray  :: !(f RealArrayType)
                        -> App ext f CplxArrayType
  IntegerArrayToCplxArray :: !(f IntegerArrayType)
                          -> App ext f CplxArrayType
  IntArrayToCplxArray   :: !(f MatlabIntArrayType)
                        -> App ext f CplxArrayType
  UIntArrayToCplxArray  :: !(f MatlabUIntArrayType)
                        -> App ext f CplxArrayType
  LogicArrayToCplxArray :: !(f LogicArrayType)
                        -> App ext f CplxArrayType
  CharArrayToCplxArray  :: !(f CharArrayType)
                        -> App ext f CplxArrayType
  CplxArrayAsPosNat :: !(f CplxArrayType)
                      -> App ext f (MaybeType (MultiDimArrayType NatType))

  ----------------------------------------------------------------------
  -- IntWidth

  -- Return width of int array.
  IntArrayWidth  :: !(f MatlabIntArrayType)
                 -> App ext f IntWidthType

  ----------------------------------------------------------------------
  -- MatlabInt

  -- Create an expression from a constant.
  MatlabIntLit :: (1 <= n) => NatRepr n -> Integer -> App ext f MatlabIntType
  -- Check if two values are equal.
  MatlabIntEq :: !(f MatlabIntType) -> !(f MatlabIntType) -> App ext f BoolType
  -- Check if one value is less than another.
  MatlabIntLt :: !(f MatlabIntType) -> !(f MatlabIntType) -> App ext f BoolType
  -- Check is value is positive.
  MatlabIntIsPos :: !(f MatlabIntType) -> App ext f BoolType
  -- Convert to a natural number.
  -- Undefined on negative numbers.
  MatlabIntToNat :: !(f MatlabIntType) -> App ext f NatType

  ----------------------------------------------------------------------
  -- IntArrayType

  -- Create empty int array with same width as input type.
  MatlabIntArrayEmpty :: !(f IntWidthType)
                      -> App ext f MatlabIntArrayType
  -- Create a single element array.
  MatlabIntArraySingleton :: !(f MatlabIntType)
                          -> App ext f MatlabIntArrayType
  MatlabIntArrayDim :: !(f MatlabIntArrayType)
                    -> App ext f ArrayDimType

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabIntArrayResize :: !(f MatlabIntArrayType)
                       -> !(f ArrayDimType)
                       -> App ext f MatlabIntArrayType
  MatlabIntArrayLookup :: !(f MatlabIntArrayType)
                       -> !(f (VectorType NatType))
                       -> App ext f MatlabIntType
  MatlabIntArrayUpdate :: !(f MatlabIntArrayType)
                       -> !(f (VectorType NatType))
                       -> !(f MatlabIntType)
                       -> App ext f MatlabIntArrayType
  MatlabIntArrayAsSingleton :: !(f MatlabIntArrayType)
                      -> App ext f (MaybeType MatlabIntType)
  MatlabIntArrayIndex :: !(f MatlabIntArrayType)
                      -> !(f MultiDimArrayIndexType)
                      -> App ext f MatlabIntArrayType
  -- Compare int arrays (arrays with different dimensions are not equal).
  MatlabIntArrayEq   :: !(f MatlabIntArrayType)
                     -> !(f MatlabIntArrayType)
                     -> App ext f BoolType
  MatlabIntArrayAsPosNat :: !(f MatlabIntArrayType)
                           -> App ext f (MaybeType (MultiDimArrayType NatType))

  CplxArrayToMatlabInt :: !(f CplxArrayType)
                       -> !(f IntWidthType)
                       -> App ext f MatlabIntArrayType
  MatlabIntArraySetWidth  :: !(f MatlabIntArrayType)
                          -> !(f IntWidthType)
                          -> App ext f MatlabIntArrayType
  MatlabUIntArrayToInt :: !(f MatlabUIntArrayType)
                       -> !(f IntWidthType)
                       -> App ext f MatlabIntArrayType
  LogicArrayToMatlabInt :: !(f LogicArrayType)
                        -> !(f IntWidthType)
                        -> App ext f MatlabIntArrayType
  CharArrayToMatlabInt :: !(f CharArrayType)
                       -> !(f IntWidthType)
                       -> App ext f MatlabIntArrayType

  ----------------------------------------------------------------------
  -- UIntWidth

  -- Return width of uint array.
  UIntArrayWidth :: !(f MatlabUIntArrayType)
                 -> App ext f UIntWidthType

  ----------------------------------------------------------------------
  -- MatlabUInt

  -- Create an expression from a constant.
  MatlabUIntLit :: (1 <= n) => NatRepr n -> Integer -> App ext f MatlabUIntType
  -- Check if two values are equal.
  MatlabUIntEq :: !(f MatlabUIntType) -> !(f MatlabUIntType) -> App ext f BoolType
  -- Check if one value is less than another.
  MatlabUIntLt :: !(f MatlabUIntType) -> !(f MatlabUIntType) -> App ext f BoolType
  -- Check is value is positive.
  MatlabUIntIsPos :: !(f MatlabUIntType) -> App ext f BoolType
  -- Convert a MatlabUInt to a natural number.
  MatlabUIntToNat :: !(f MatlabUIntType) -> App ext f NatType


  ----------------------------------------------------------------------
  -- Symbolic (u)int arrays

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabSymIntArrayResize :: !(f MatlabSymbolicIntArrayType)
                          -> !(f ArrayDimType)
                          -> App ext f MatlabSymbolicIntArrayType
  MatlabSymIntArrayLookup :: !(f MatlabSymbolicIntArrayType)
                          -> !(f (VectorType NatType))
                          -> App ext f MatlabIntType
  MatlabSymIntArrayUpdate :: !(f MatlabSymbolicIntArrayType)
                          -> !(f (VectorType NatType))
                          -> !(f MatlabIntType)
                          -> App ext f MatlabSymbolicIntArrayType
  MatlabSymIntArrayAsSingleton :: !(f MatlabSymbolicIntArrayType)
                      -> App ext f (MaybeType MatlabIntType)

  SymIntArrayWidth
             :: !(f MatlabSymbolicIntArrayType)
             -> App ext f IntWidthType

  SymIndexIntArray
             :: !(f (MatlabSymbolicIntArrayType))
             -> !(f MultiDimArrayIndexType)
             -> App ext f MatlabIntArrayType

  MatlabSymbolicIntArrayDim
             :: !(f (MatlabSymbolicIntArrayType))
             -> App ext f (ArrayDimType)

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabSymUIntArrayResize :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f ArrayDimType)
                           -> App ext f MatlabSymbolicUIntArrayType
  MatlabSymUIntArrayLookup :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f (VectorType NatType))
                           -> App ext f MatlabUIntType
  MatlabSymUIntArrayUpdate :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f (VectorType NatType))
                           -> !(f MatlabUIntType)
                           -> App ext f MatlabSymbolicUIntArrayType
  MatlabSymUIntArrayAsSingleton :: !(f MatlabSymbolicUIntArrayType)
                      -> App ext f (MaybeType MatlabUIntType)

  SymUIntArrayWidth
             :: !(f MatlabSymbolicUIntArrayType)
             -> App ext f UIntWidthType

  SymIndexUIntArray
             :: !(f (MatlabSymbolicUIntArrayType))
             -> !(f MultiDimArrayIndexType)
             -> App ext f MatlabUIntArrayType

  MatlabSymbolicUIntArrayDim
             :: !(f (MatlabSymbolicUIntArrayType))
             -> App ext f (ArrayDimType)

  SymIntArrayExternalize
                :: !(f MatlabSymbolicIntArrayType)
                -> App ext f MatlabIntArrayType

  SymUIntArrayExternalize
                :: !(f MatlabSymbolicUIntArrayType)
                -> App ext f MatlabUIntArrayType

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

  BVEq  :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App ext f BoolType

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

  BVIte :: (1 <= w)
        => !(f BoolType)
        -> !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
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
  -- UIntArrayType

  -- Create empty uint array with same width as input type.
  MatlabUIntArrayEmpty :: !(f UIntWidthType)
                       -> App ext f MatlabUIntArrayType
  -- Create a single element array.
  MatlabUIntArraySingleton :: !(f MatlabUIntType)
                           -> App ext f MatlabUIntArrayType
  MatlabUIntArrayDim :: !(f MatlabUIntArrayType)
                     -> App ext f ArrayDimType

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabUIntArrayResize :: !(f MatlabUIntArrayType)
                        -> !(f ArrayDimType)
                        -> App ext f MatlabUIntArrayType
  -- Index uint array at index.
  MatlabUIntArrayLookup :: !(f MatlabUIntArrayType)
                        -> !(f (VectorType NatType))
                        -> App ext f MatlabUIntType
  -- Set value of array at index.
  MatlabUIntArrayUpdate :: !(f MatlabUIntArrayType)
                        -> !(f (VectorType NatType))
                        -> !(f MatlabUIntType)
                        -> App ext f MatlabUIntArrayType
  MatlabUIntArrayAsSingleton :: !(f MatlabUIntArrayType)
                             -> App ext f (MaybeType MatlabUIntType)
  MatlabUIntArrayIndex :: !(f MatlabUIntArrayType)
                       -> !(f MultiDimArrayIndexType)
                       -> App ext f MatlabUIntArrayType
  -- Compare uint arrays (arrays with different dimensions are not equal).
  MatlabUIntArrayEq :: !(f MatlabUIntArrayType)
                    -> !(f MatlabUIntArrayType)
                    -> App ext f BoolType
  MatlabUIntArrayAsPosNat :: !(f MatlabUIntArrayType)
                            -> App ext f (MaybeType (MultiDimArrayType NatType))
  CplxArrayToMatlabUInt :: !(f CplxArrayType)
                        -> !(f UIntWidthType)
                        -> App ext f MatlabUIntArrayType
  MatlabIntArrayToUInt :: !(f MatlabIntArrayType)
                       -> !(f UIntWidthType)
                       -> App ext f MatlabUIntArrayType
  MatlabUIntArraySetWidth :: !(f MatlabUIntArrayType)
                          -> !(f UIntWidthType)
                          -> App ext f MatlabUIntArrayType
  LogicArrayToMatlabUInt :: !(f LogicArrayType)
                         -> !(f UIntWidthType)
                         -> App ext f MatlabUIntArrayType
  CharArrayToMatlabUInt :: !(f CharArrayType)
                        -> !(f UIntWidthType)
                        -> App ext f MatlabUIntArrayType

  ----------------------------------------------------------------------
  -- LogicArrayType

  -- Compare Boolean arrays (arrays with different dimensions are not equal).
  LogicArrayEq :: !(f LogicArrayType)
               -> !(f LogicArrayType)
               -> App ext f BoolType
  LogicArrayToIndices :: !(f LogicArrayType)
                      -> App ext f (MultiDimArrayType NatType)
  CplxArrayToLogic :: !(f CplxArrayType)
                   -> App ext f LogicArrayType
  IntegerArrayToLogic :: !(f IntegerArrayType)
                      -> App ext f LogicArrayType
  RealArrayToLogic :: !(f RealArrayType)
                      -> App ext f LogicArrayType
  MatlabIntArrayToLogic :: !(f MatlabIntArrayType)
                        -> App ext f LogicArrayType
  MatlabUIntArrayToLogic :: !(f MatlabUIntArrayType)
                         -> App ext f LogicArrayType
  -- Return true if all entries in array are true.
  AllEntriesAreTrue :: !(f LogicArrayType)
                    -> App ext f BoolType

  ----------------------------------------------------------------------
  -- CharArrayType

  -- A character array literal (also called a string).
  CharVectorLit :: !CharVector
                -> App ext f CharArrayType

  IntegerArrayEq :: !(f (IntegerArrayType))
                 -> !(f (IntegerArrayType))
                 -> App ext f BoolType
  RealArrayEq :: !(f (RealArrayType))
              -> !(f (RealArrayType))
              -> App ext f BoolType

  -- Compare char arrays (arrays with different dimensions are not equal).
  CharArrayEq :: !(f CharArrayType)
              -> !(f CharArrayType)
              -> App ext f BoolType
  CplxArrayToChar :: !(f CplxArrayType)
                  -> App ext f CharArrayType
  CharArrayAsPosNat :: !(f CharArrayType)
                      -> App ext f (MaybeType (MultiDimArrayType NatType))
  CharArrayToLogic :: !(f CharArrayType)
                   -> App ext f LogicArrayType

  ----------------------------------------------------------------------
  -- StructFields

  -- Empty set of struct fields.
  EmptyStructFields :: App ext f (VectorType StringType)

  -- Return true if fields are equal.
  FieldsEq :: !(f (VectorType StringType))
           -> !(f (VectorType StringType))
           -> App ext f BoolType

  -- Return true if field is in set.
  HasField :: !(f StringType)
           -> !(f (VectorType StringType))
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


-- | Compute a run-time representation of the type of an application.
instance TypeApp (ExprExtension ext) => TypeApp (App ext) where
  -- appType :: App ext f tp -> TypeRepr tp
  appType a0 =
   case a0 of
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
    -- Concrete
    ConcreteLit (TypeableValue _) -> ConcreteRepr TypeableType
    ----------------------------------------------------------------------
    -- Bool
    BoolLit{} -> knownRepr
    Not{} -> knownRepr
    And{} -> knownRepr
    Or{} -> knownRepr
    BoolXor{} -> knownRepr
    BoolIte{} -> knownRepr
    ----------------------------------------------------------------------
    -- Nat
    NatLit{} -> knownRepr
    NatEq{} -> knownRepr
    NatLt{} -> knownRepr
    NatLe{} -> knownRepr
    NatAdd{} -> knownRepr
    NatSub{} -> knownRepr
    NatMul{} -> knownRepr
    ----------------------------------------------------------------------
    -- Integer
    IntLit{} -> knownRepr
    IntAdd{} -> knownRepr
    IntSub{} -> knownRepr
    IntMul{} -> knownRepr
    IntEq{} -> knownRepr
    IntLt{} -> knownRepr

    ----------------------------------------------------------------------
    -- RealVal
    RationalLit{} -> knownRepr
    RealAdd{} -> knownRepr
    RealSub{} -> knownRepr
    RealMul{} -> knownRepr
    RealDiv{} -> knownRepr
    RealMod{} -> knownRepr
    RealIte{} -> knownRepr
    RealEq{} -> knownRepr
    RealLt{} -> knownRepr
    RealIsInteger{} -> knownRepr

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
    -- SymbolicMultiDimArray

    MatlabSymArrayDim{}            -> knownRepr
    MatlabSymArrayReplicate bt _ _ -> SymbolicMultiDimArrayRepr bt
    MatlabSymArrayLookup bt _ _    -> baseToType bt
    MatlabSymArrayUpdate bt _ _ _  -> SymbolicMultiDimArrayRepr bt
    MatlabSymArrayAsSingleton bt _ -> MaybeRepr (baseToType bt)
    MatlabSymArrayResize bt _ _ _  -> SymbolicMultiDimArrayRepr bt
    MatlabSymIndexArray bt _ _     -> MultiDimArrayRepr (baseToType bt)
    MatlabSymArraySymIndex bt _ _  -> SymbolicMultiDimArrayRepr bt
    MatlabSymArrayExternalize bt _ -> MultiDimArrayRepr (baseToType bt)
    MatlabArrayInternalize bt _    -> SymbolicMultiDimArrayRepr bt

    ----------------------------------------------------------------------
    -- SymbolicArrayType

    SymArrayLookup b _ _ -> baseToType b
    SymArrayUpdate b _ idx _ ->
      baseToType (BaseArrayRepr (fmapFC baseTermType idx) b)

    ----------------------------------------------------------------------
    -- Symbolic (u)int arrays

    SymIntArrayWidth{} -> knownRepr
    SymUIntArrayWidth{} -> knownRepr
    SymIndexIntArray{} -> knownRepr
    SymIndexUIntArray{} -> knownRepr
    MatlabSymbolicIntArrayDim{}     -> knownRepr
    MatlabSymIntArrayResize{}       -> knownRepr
    MatlabSymIntArrayLookup{}       -> knownRepr
    MatlabSymIntArrayUpdate{}       -> knownRepr
    MatlabSymIntArrayAsSingleton{}  -> knownRepr
    MatlabSymbolicUIntArrayDim{}    -> knownRepr
    MatlabSymUIntArrayResize{}      -> knownRepr
    MatlabSymUIntArrayLookup{}      -> knownRepr
    MatlabSymUIntArrayUpdate{}      -> knownRepr
    MatlabSymUIntArrayAsSingleton{} -> knownRepr

    SymIntArrayExternalize{} -> knownRepr
    SymUIntArrayExternalize{} -> knownRepr

    ----------------------------------------------------------------------
    -- MultiDimArray

    ArrayEmpty tp -> MultiDimArrayRepr tp
    ArrayReplicate tp _ _ -> MultiDimArrayRepr tp
    ArrayDim{} -> knownRepr
    ArrayResize tp _ _ _ -> MultiDimArrayRepr tp
    ArrayLookup tp _ _   -> tp
    ArrayUpdate tp _ _ _ -> MultiDimArrayRepr tp
    ArrayAsSingleton tp _ -> MaybeRepr tp
    IndexArray tp _ _ -> MultiDimArrayRepr tp
    ArrayEntry tp _ _ -> tp
    ArrayProduct tp _ -> MultiDimArrayRepr (VectorRepr tp)
    MultiDimArrayToVec tp _ -> VectorRepr tp
    MatlabExtArraySymIndex bt _ _ -> MultiDimArrayRepr bt

    ----------------------------------------------------------------------
    -- Vector based indexing

    CplxVecToNat{}  -> knownRepr
    LogicVecToIndex{} -> knownRepr
    MatlabCharVecToNat{}   -> knownRepr
    MatlabIntArrayToNat{}  -> knownRepr
    MatlabUIntArrayToNat{} -> knownRepr

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
    -- PosNat

    EnumTo{} -> knownRepr

    ----------------------------------------------------------------------
    -- Conversions
    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    RealToNat{} -> knownRepr

    ----------------------------------------------------------------------
    -- ComplexReal
    Complex{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    ----------------------------------------------------------------------
    -- MatlabChar
    MatlabCharLit{} -> knownRepr
    MatlabCharEq{} -> knownRepr
    MatlabCharToNat{} -> knownRepr

    ----------------------------------------------------------------------
    -- CplxArrayType
    CplxArrayEq{} -> knownRepr

    CplxArrayIsReal{} -> knownRepr
    IntArrayToCplxArray{} -> knownRepr
    UIntArrayToCplxArray{} -> knownRepr
    RealArrayToCplxArray{} -> knownRepr
    IntegerArrayToCplxArray{} -> knownRepr
    LogicArrayToCplxArray{} -> knownRepr
    CharArrayToCplxArray{} -> knownRepr
    CplxArrayAsPosNat{} -> knownRepr

    CplxArrayToRealArray{} -> knownRepr

    ---------------------------------------------------------------------
    -- IntegerArrayType
    CharArrayToIntegerArray{} -> knownRepr
    LogicArrayToIntegerArray{} -> knownRepr
    IntArrayToIntegerArray{} -> knownRepr
    UIntArrayToIntegerArray{} -> knownRepr
    RealArrayToIntegerArray{} -> knownRepr
    CplxArrayToIntegerArray{} -> knownRepr

    ----------------------------------------------------------------------
    -- IntWidth

    IntArrayWidth{} -> knownRepr

    ----------------------------------------------------------------------
    -- MatlabInt
    MatlabIntLit{} -> knownRepr
    MatlabIntEq{} -> knownRepr
    MatlabIntLt{} -> knownRepr
    MatlabIntIsPos{} -> knownRepr
    MatlabIntToNat{} -> knownRepr

    ----------------------------------------------------------------------
    -- IntArrayType
    MatlabIntArrayEmpty{} -> knownRepr
    MatlabIntArraySingleton{} -> knownRepr
    MatlabIntArrayDim{} -> knownRepr
    MatlabIntArrayResize{} -> knownRepr
    MatlabIntArrayLookup{} -> knownRepr
    MatlabIntArrayUpdate{} -> knownRepr
    MatlabIntArrayAsSingleton{} -> knownRepr
    MatlabIntArrayIndex{} -> knownRepr
    MatlabIntArrayEq{} -> knownRepr
    MatlabIntArrayAsPosNat{} -> knownRepr
    CplxArrayToMatlabInt{} -> knownRepr
    MatlabIntArraySetWidth{} -> knownRepr
    MatlabUIntArrayToInt{} -> knownRepr
    LogicArrayToMatlabInt{} -> knownRepr
    CharArrayToMatlabInt{} -> knownRepr

    ----------------------------------------------------------------------
    -- UIntWidth
    UIntArrayWidth{} -> knownRepr

    ----------------------------------------------------------------------
    -- MatlabUInt
    MatlabUIntLit{} -> knownRepr
    MatlabUIntEq{} -> knownRepr
    MatlabUIntLt{} -> knownRepr
    MatlabUIntIsPos{} -> knownRepr
    MatlabUIntToNat{} -> knownRepr


    ----------------------------------------------------------------------
    -- BV
    BVUndef w -> BVRepr w
    BVLit w _ -> BVRepr w
    BVTrunc w _ _ -> BVRepr w
    BVZext w _ _ -> BVRepr w
    BVSext w _ _ -> BVRepr w

    BVEq{} -> knownRepr
    BVNot w _ -> BVRepr w
    BVAnd w _ _ -> BVRepr w
    BVOr  w _ _ -> BVRepr w
    BVXor  w _ _ -> BVRepr w
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
    BVIte _ w _ _ -> BVRepr w

    BoolToBV w _ -> BVRepr w
    BvToNat{} -> knownRepr
    BvToInteger{} -> knownRepr
    SbvToInteger{} -> knownRepr
    BVNonzero{} -> knownRepr
    BVSelect _ n _ _ -> BVRepr n
    BVConcat w1 w2 _ _ -> BVRepr (addNat w1 w2)

    ----------------------------------------------------------------------
    -- UIntArrayType

    MatlabUIntArrayEmpty{} -> knownRepr
    MatlabUIntArraySingleton{} -> knownRepr
    MatlabUIntArrayDim{} -> knownRepr
    MatlabUIntArrayResize{} -> knownRepr
    MatlabUIntArrayLookup{} -> knownRepr
    MatlabUIntArrayUpdate{} -> knownRepr
    MatlabUIntArrayAsSingleton{} -> knownRepr
    MatlabUIntArrayIndex{} -> knownRepr
    MatlabUIntArrayEq{} -> knownRepr
    MatlabUIntArrayAsPosNat{} -> knownRepr
    CplxArrayToMatlabUInt{} -> knownRepr
    MatlabIntArrayToUInt{} -> knownRepr
    MatlabUIntArraySetWidth{} -> knownRepr
    LogicArrayToMatlabUInt{} -> knownRepr
    CharArrayToMatlabUInt{} -> knownRepr

    ----------------------------------------------------------------------
    -- LogicArrayType
    LogicArrayEq{} -> knownRepr
    LogicArrayToIndices{} -> knownRepr
    CplxArrayToLogic{} -> knownRepr
    RealArrayToLogic{} -> knownRepr
    IntegerArrayToLogic{} -> knownRepr
    MatlabIntArrayToLogic{} -> knownRepr
    MatlabUIntArrayToLogic{} -> knownRepr
    AllEntriesAreTrue{} -> knownRepr

    ----------------------------------------------------------------------
    -- CharArrayType

    CharVectorLit{} -> knownRepr
    CharArrayEq{} -> knownRepr
    CplxArrayToChar{} -> knownRepr
    CharArrayAsPosNat{} -> knownRepr
    CharArrayToLogic{} -> knownRepr

    IntegerArrayEq{} -> knownRepr
    RealArrayEq{} -> knownRepr

    ----------------------------------------------------------------------
    -- StructFields
    EmptyStructFields{} -> knownRepr
    FieldsEq{} -> knownRepr
    HasField{} -> knownRepr

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
                   , (U.ConType [t|TypeableValue|]  `U.TypeApp` U.AnyType, [|testEquality|])
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
                   , (U.ConType [t|TypeableValue|] `U.TypeApp` U.AnyType, [|compareF|])
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
