{-
Module           : Lang.Crucible.Core
Copyright        : (c) Galois, Inc 2014-2016
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Define a SSA-based control flow graph data structure using a side-effect free
expression syntax.

Unlike usual SSA forms, we do not use phi-functions, but instead rely on an
argument-passing formulation for basic blocks.  In this form, concrete values
are bound to formal parameters instead of using phi-functions that switch
on the place from which you jumped.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
module Lang.Crucible.Core
  ( -- * App
    App(..)
  , appType
  , ppApp
  , mapApp
  , foldApp
  , traverseApp
    -- * Types
  , CharVector
  , module Lang.Crucible.Types
    -- * CFG
  , CFG(..)
  , SomeCFG(..)
  , HasSomeCFG(..)
  , AnyCFG(..)
  , ppCFG
  , cfgArgTypes
  , cfgReturnType
  , CFGPostdom

  , BlockMap
  , getBlock
  , extendBlockMap
  , GlobalVar(..)
  , freshGlobalVar

  , JumpTarget(..)
  , extendJumpTarget
  , jumpTargetID
  , SwitchTarget(..)
  , switchTargetID
  , extendSwitchTarget

  , BlockID(..)
  , extendBlockID
  , extendBlockID'

  , Block(..)
  , blockLoc
  , blockStmts
  , withBlockTermStmt
  , nextBlocks
  , extendBlock

  , StmtSeq(..)
  , firstStmtLoc
  , extendStmtSeq
  , stmtSeqTermStmt
  , Stmt(..)
  , ppStmt
  , MSwitch(..)
  , constMSwitch
  , extendMSwitch
  , zipSwitchWith
  , ppMSwitch

  , TermStmt(..)
  , termStmtNextBlocks
  , extendTermStmt

  , BaseTerm(..)
  , Expr(..)
  , Reg(..)
  , extendReg
  , lastReg
  , module Data.Parameterized.Classes
  , module Data.Parameterized.Some
  , module Lang.Crucible.Utils.ConstK
  ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.State.Strict
import           Control.Monad.ST
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (Pair(..))
import           Data.Parameterized.Nonce.Unsafe
import           Data.Parameterized.Some
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.MATLAB.CharVector (CharVector)
import           Lang.MATLAB.MatlabChar
import           Lang.MATLAB.Utils.Nat (Nat)
import           Lang.MATLAB.Utils.PrettyPrint

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.ConstK
import qualified Lang.Crucible.Utils.Structural as U

#ifdef UNSAFE_OPS
import qualified Data.Coerce
#endif

------------------------------------------------------------------------
-- App

data BaseTerm (f :: CrucibleType -> *) tp
   = BaseTerm { baseTermType :: !(BaseTypeRepr tp)
              , baseTermVal  :: !(f (BaseToType tp))
              }

instance TestEquality f => TestEquality (BaseTerm f) where
  testEquality (BaseTerm _ x) (BaseTerm _ y) = do
    Refl <- testEquality x y
    return Refl

instance OrdF f => OrdF (BaseTerm f) where
  compareF (BaseTerm _ x) (BaseTerm _ y) = do
    case compareF x y of
      LTF -> LTF
      GTF -> GTF
      EQF -> EQF

instance FunctorFC BaseTerm where
  fmapFC = fmapFCDefault

instance FoldableFC BaseTerm where
  foldMapFC = foldMapFCDefault

instance TraversableFC BaseTerm where
  traverseFC f (BaseTerm tp x) = BaseTerm tp <$> f x

-- | The main matlab expression datastructure, defined as a multisorted algebra.
--   The type parameter `f` is used to indicate additional recursive structure;
--   we later tie the knot with the `Expr` datatype, below.
--   The type parameter `tp` is a type index that indicates the matlab type
--   of the values denoted by the given expression form.
data App f (tp :: CrucibleType) where

  ----------------------------------------------------------------------
  -- ()

  EmptyApp :: App f UnitType

  ----------------------------------------------------------------------
  -- Any

  -- Build an ANY type package.
  PackAny :: !(TypeRepr tp)
          -> !(f tp)
          -> App f AnyType

  -- Attempt to open an ANY type. Return the contained
  -- value if it has the given type; otherwise return Nothing.
  UnpackAny :: !(TypeRepr tp)
            -> !(f AnyType)
            -> App f (MaybeType tp)

  ----------------------------------------------------------------------
  -- Concrete

  -- Constructs a literal of concrete type
  ConcreteLit :: !(TypeableValue a)
              -> App f (ConcreteType a)

  ---------------------------------------------------------------------
  -- Bool

  BoolLit :: !Bool -> App f BoolType

  Not :: !(f BoolType)
      -> App f BoolType

  And :: !(f BoolType)
      -> !(f BoolType)
      -> App f BoolType
  Or  :: !(f BoolType)
      -> !(f BoolType)
      -> App f BoolType

  -- Exclusive or of Boolean values.
  BoolXor :: !(f BoolType)
          -> !(f BoolType)
          -> App f BoolType

  -- Exclusive or of Boolean values.
  BoolIte :: !(f BoolType)
          -> !(f BoolType)
          -> !(f BoolType)
          -> App f BoolType

  ----------------------------------------------------------------------
  -- Nat

  -- @NatLit n@ returns the value n.
  NatLit :: !Nat -> App f NatType
  -- Equality on natural numbers.
  NatEq :: !(f NatType) -> !(f NatType) -> App f BoolType
  -- Less than on natural numbers.
  NatLt :: !(f NatType) -> !(f NatType) -> App f BoolType
  -- Less than or equal on natural numbers.
  NatLe :: !(f NatType) -> !(f NatType) -> App f BoolType
  -- Add two natural numbers.
  NatAdd :: !(f NatType) -> !(f NatType) -> App f NatType
  -- @NatSub x y@ equals @x - y@.
  -- The result is undefined if the @x@ is less than @y@.
  NatSub :: !(f NatType) -> !(f NatType) -> App f NatType
  -- Multiple two natural numbers.
  NatMul :: !(f NatType) -> !(f NatType) -> App f NatType

  ----------------------------------------------------------------------
  -- Integer

  -- Create a singleton real array from a numeric literal.
  IntLit :: !Integer -> App f IntegerType
  -- Add two integers.
  IntAdd :: !(f IntegerType) -> !(f IntegerType) -> App f IntegerType
  -- Subtract one integer from another.
  IntSub :: !(f IntegerType) -> !(f IntegerType) -> App f IntegerType
  -- Multiple two integers.
  IntMul :: !(f IntegerType) -> !(f IntegerType) -> App f IntegerType

  IntEq :: !(f IntegerType) -> !(f IntegerType) -> App f BoolType
  IntLt :: !(f IntegerType) -> !(f IntegerType) -> App f BoolType

  ----------------------------------------------------------------------
  -- RealVal

  -- A real constant
  RationalLit :: !Rational -> App f RealValType

  -- Add two natural numbers.
  RealAdd :: !(f RealValType) -> !(f RealValType) -> App f RealValType
  -- Subtract one number from another.
  RealSub :: !(f RealValType) -> !(f RealValType) -> App f RealValType
  -- Multiple two numbers.
  RealMul :: !(f RealValType) -> !(f RealValType) -> App f RealValType
  -- Return first or second number depending on condition.
  RealIte :: !(f BoolType) -> !(f RealValType) -> !(f RealValType) -> App f RealValType

  RealEq :: !(f RealValType) -> !(f RealValType) -> App f BoolType
  RealLt :: !(f RealValType) -> !(f RealValType) -> App f BoolType
  -- Return true if real value is integer.
  RealIsInteger :: !(f RealValType) -> App f BoolType

  ----------------------------------------------------------------------
  -- Maybe

  JustValue :: !(TypeRepr tp)
            -> !(f tp)
            -> App f (MaybeType tp)

  NothingValue :: !(TypeRepr tp) -> App f (MaybeType tp)

  -- This is a partial operation with given a maybe value returns the
  -- value if is defined and otherwise fails with the given error message.
  --
  -- This operation should be used instead of pattern matching on a maybe
  -- when you do not want an explicit error message being printed, but rather
  -- want to assert that the value is defined.
  FromJustValue :: !(TypeRepr tp)
                -> !(f (MaybeType tp))
                -> !(f StringType)
                -> App f tp


  ----------------------------------------------------------------------
  -- Side conditions
  AddSideCondition :: BaseTypeRepr bt
                   -> !(f (BoolType))
                   -> String
                   -> !(f (BaseToType bt))
                   -> App f (BaseToType bt)

  ----------------------------------------------------------------------
  -- Recursive Types
  RollRecursive :: IsRecursiveType nm
                => !(SymbolRepr nm)
                -> !(f (UnrollType nm))
                -> App f (RecursiveType nm)

  UnrollRecursive
                :: IsRecursiveType nm
                => !(SymbolRepr nm)
                -> !(f (RecursiveType nm))
                -> App f (UnrollType nm)

  ----------------------------------------------------------------------
  -- Vector

  -- Vector literal.
  VectorLit :: !(TypeRepr tp) -> !(Vector (f tp)) -> App f (VectorType tp)
  -- Create an vector of constants.
  VectorReplicate :: !(TypeRepr tp)
                  -> !(f NatType)
                  -> !(f tp)
                  -> App f (VectorType tp)
  -- Return true if vector is empty.
  VectorIsEmpty :: !(f (VectorType tp))
                -> App f BoolType
  -- Size of vector
  VectorSize :: !(f (VectorType tp)) -> App f NatType

  -- Return value stored in given entry.
  --
  VectorGetEntry :: !(TypeRepr tp)
                 -> !(f (VectorType tp))
                 -> !(f NatType)
                 -> App f tp
  -- Update vector at given entry.
  VectorSetEntry :: !(TypeRepr tp)
                 -> !(f (VectorType tp))
                 -> !(f NatType)
                 -> !(f tp)
                 -> App f (VectorType tp)


  -----------------------------
  -- SymbolicMultiDimArray


  MatlabSymArrayDim :: !(f (SymbolicMultiDimArrayType tp))
                      -> App f ArrayDimType

  -- Create an array of containing a single value.
  MatlabSymArrayReplicate :: !(BaseTypeRepr tp)
                          -> !(f ArrayDimType)
                          -> !(f (BaseToType tp))
                          -> App f (SymbolicMultiDimArrayType tp)

  -- Get value in array at index.
  MatlabSymArrayLookup :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType  bt))
                       -> !(f (VectorType NatType))
                       -> App f (BaseToType bt)

  -- Set value of array at index.
  MatlabSymArrayUpdate :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType  bt))
                       -> !(f (VectorType NatType))
                       -> !(f (BaseToType bt))
                       -> App f (SymbolicMultiDimArrayType bt)
  -- Project array as a single scalar value if it is one.
  MatlabSymArrayAsSingleton :: !(BaseTypeRepr bt)
                            -> !(f (SymbolicMultiDimArrayType bt))
                            -> App f (MaybeType (BaseToType bt))

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the given default value.
  MatlabSymArrayResize :: !(BaseTypeRepr bt)
                       -> !(f (SymbolicMultiDimArrayType bt))
                       -> !(f ArrayDimType)
                       -> !(f (BaseToType bt)) -- The default value.
                       -> App f (SymbolicMultiDimArrayType bt)

  -- Index array at the given indices.
  -- This function is not defined outside the array bounds.
  MatlabSymIndexArray :: !(BaseTypeRepr tp)
                      -> !(f (SymbolicMultiDimArrayType tp))
                      -> !(f MultiDimArrayIndexType)
                      -> App f (MultiDimArrayType (BaseToType tp))

  -- Index a symbolic multidim array at the given symbolic indices.
  MatlabSymArraySymIndex :: !(BaseTypeRepr tp)
                         -> !(f (SymbolicMultiDimArrayType tp))
                         -> !(V.Vector (f (SymbolicMultiDimArrayType BaseNatType)))
                         -> App f (SymbolicMultiDimArrayType tp)

  -- Convert a MATLAB symbolic array into a MATLAB external
  -- multidimensional-array.
  MatlabSymArrayExternalize
                :: !(BaseTypeRepr tp)
                -> !(f (SymbolicMultiDimArrayType tp))
                -> App f (MultiDimArrayType (BaseToType tp))

  -- Convert a MATLAB external multidimensional array into a
  -- symbolic array.
  MatlabArrayInternalize
                :: !(BaseTypeRepr tp)
                -> !(f (MultiDimArrayType (BaseToType tp)))
                -> App f (SymbolicMultiDimArrayType tp)

  --------------------------------------------------------------------
  -- MultiDimArray

  -- Empty array
  ArrayEmpty :: !(TypeRepr tp) -> App f (MultiDimArrayType tp)
  -- Create an array of constants.
  ArrayReplicate :: !(TypeRepr tp)
                 -> !(f ArrayDimType)
                 -> !(f tp)
                 -> App f (MultiDimArrayType tp)
  -- Return dimension of array.
  ArrayDim   :: !(f (MultiDimArrayType tp))
             -> App f ArrayDimType

  -- | This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the given default value.
  ArrayResize :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f ArrayDimType)
              -> !(f tp) -- Default value
              -> App f (MultiDimArrayType tp)
  -- Get value in array at 1-based index of vectors.
  ArrayLookup :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f (VectorType NatType))
              -> App f tp
  -- Set value of array at index.
  ArrayUpdate :: !(TypeRepr tp)
              -> !(f (MultiDimArrayType tp))
              -> !(f (VectorType NatType))
              -> !(f tp)
              -> App f (MultiDimArrayType tp)
  -- Project array as a single scalar value if it is one.
  ArrayAsSingleton :: !(TypeRepr tp)
                   -> !(f (MultiDimArrayType tp))
                   -> App f (MaybeType tp)

  -- Index array at the given indices.
  -- This function is not defined outside the array bounds.
  IndexArray :: !(TypeRepr tp)
             -> !(f (MultiDimArrayType tp))
             -> !(f MultiDimArrayIndexType)
             -> App f (MultiDimArrayType  tp)
  -- Get value in array at a single specific index.
  -- Not defined when evaluated if the cell entry is out of range,
  -- or expression contains multiple indices.
  ArrayEntry :: !(TypeRepr tp)
             -> !(f (MultiDimArrayType tp))
             -> !(f (VectorType NatType))
             -> App f tp

  -- @ArrayProduct _ v@ converts a vector of multidimensional arrays into
  -- a multidimensional array of vectors.
  ArrayProduct :: !(TypeRepr tp)
               -> !(Vector (f (MultiDimArrayType tp)))
               -> App f (MultiDimArrayType (VectorType tp))

  -- Return the vector associated with a multi-dimensional array
  MultiDimArrayToVec :: !(TypeRepr tp)
                     -> !(f (MultiDimArrayType tp))
                     -> App f (VectorType tp)

  -- Index an external multidim array at the given symbolic indices.
  MatlabExtArraySymIndex :: !(TypeRepr tp)
                         -> !(f (MultiDimArrayType tp))
                         -> !(V.Vector (f (SymbolicMultiDimArrayType BaseNatType)))
                         -> App f (MultiDimArrayType tp)

  ----------------------------------------------------------------------
  -- Conversion to vector based indexing.

  -- @CplxVecToIndex@ converts the vector to a vector of natural numbers.
  --
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  CplxVecToNat :: !(f (VectorType ComplexRealType))
                 -> App f (VectorType NatType)

  -- @LogicVecToIndex@ converts the vector of predicates to a vector of
  -- natural numbers.
  --
  -- The resulting vector contains the 1-based index of each true
  -- value in the vector.
  LogicVecToIndex :: !(f (VectorType BoolType))
                  -> App f (VectorType NatType)

  -- @MatlabCharVecToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabCharVecToNat :: !(f (VectorType CharType))
                     -> App f (VectorType NatType)

  -- @MatlabIntArrayToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabIntArrayToNat :: !(f MatlabIntArrayType)
                      -> App f (VectorType NatType)

  -- @MatlabUIntArrayToIndex@ converts the vector to a vector of natural numbers.
  -- This is partial, and requires that all values in the array are
  -- non-negative integers.
  MatlabUIntArrayToNat :: !(f MatlabUIntArrayType)
                       -> App f (VectorType NatType)

  ----------------------------------------------------------------------
  -- Handle

  HandleLit :: !(FnHandle args ret)
            -> App f (FunctionHandleType args ret)

  -- Create a closure that captures the last argument.
  Closure :: !(CtxRepr args)
          -> !(TypeRepr ret)
          -> !(f (FunctionHandleType (args::>tp) ret))
          -> !(TypeRepr tp)
          -> !(f tp)
          -> App f (FunctionHandleType args ret)

  ----------------------------------------------------------------------
  -- PosNat

  -- EnumTo n creates a column array with n columns containing values 1 to n.
  EnumTo :: !(f NatType)
         -> App f (MultiDimArrayType NatType)

  ----------------------------------------------------------------------
  -- Conversions

  -- @NatToInteger@ convert a natural number to an integer.
  NatToInteger :: !(f NatType) -> App f IntegerType

  -- @IntegerToReal@ convert an integer to a real.
  IntegerToReal :: !(f IntegerType) -> App f RealValType

  -- @RealToNat@ convert a non-negative real integer to natural number.
  -- This is partial, and requires that the input be a non-negative real
  -- integer.
  RealToNat :: !(f RealValType)
            -> App f NatType

  ----------------------------------------------------------------------
  -- ComplexReal

  -- Create complex number from two real numbers.
  Complex :: !(f RealValType) -> !(f RealValType) -> App f ComplexRealType
  RealPart :: !(f ComplexRealType) -> App f RealValType
  ImagPart :: !(f ComplexRealType) -> App f RealValType

  ----------------------------------------------------------------------
  -- MatlabChar

  MatlabCharLit :: !MatlabChar
                -> App f CharType

  -- Compare of two characters are equal.
  MatlabCharEq :: !(f CharType)
               -> !(f CharType)
               -> App f BoolType

  -- Convert a Matlab character (16-bit word) to a natural number.
  -- This is total.
  MatlabCharToNat :: !(f CharType) -> App f NatType

  ----------------------------------------------------------------------
  -- CplxArrayType

  -- Compare real arrays (arrays with different dimensions are not equal).
  CplxArrayEq  :: !(f CplxArrayType)
               -> !(f CplxArrayType)
               -> App f BoolType
  -- Return true if all entries in array are real values (i.e. have 0 in imaginary part).
  CplxArrayIsReal :: !(f CplxArrayType) -> App f BoolType


  CplxArrayToRealArray :: !(f CplxArrayType)
                       -> App f RealArrayType

  CharArrayToIntegerArray  :: !(f (CharArrayType))
                          -> App f IntegerArrayType
  LogicArrayToIntegerArray :: !(f (LogicArrayType))
                          -> App f IntegerArrayType
  IntArrayToIntegerArray :: !(f (MatlabIntArrayType))
                          -> App f IntegerArrayType
  UIntArrayToIntegerArray :: !(f (MatlabUIntArrayType))
                          -> App f IntegerArrayType

  -- | Converts a real array to an integer array.
  --
  -- Result is undefined if real values are not integers.
  RealArrayToIntegerArray :: !(f RealArrayType)
                       -> App f IntegerArrayType

  CplxArrayToIntegerArray :: !(f CplxArrayType)
                       -> App f IntegerArrayType

  RealArrayToCplxArray  :: !(f RealArrayType)
                        -> App f CplxArrayType
  IntegerArrayToCplxArray :: !(f IntegerArrayType)
                          -> App f CplxArrayType
  IntArrayToCplxArray   :: !(f MatlabIntArrayType)
                        -> App f CplxArrayType
  UIntArrayToCplxArray  :: !(f MatlabUIntArrayType)
                        -> App f CplxArrayType
  LogicArrayToCplxArray :: !(f LogicArrayType)
                        -> App f CplxArrayType
  CharArrayToCplxArray  :: !(f CharArrayType)
                        -> App f CplxArrayType
  CplxArrayAsPosNat :: !(f CplxArrayType)
                      -> App f (MaybeType (MultiDimArrayType NatType))

  ----------------------------------------------------------------------
  -- IntWidth

  -- Return width of int array.
  IntArrayWidth  :: !(f MatlabIntArrayType)
                 -> App f IntWidthType

  ----------------------------------------------------------------------
  -- MatlabInt

  -- Create an expression from a constant.
  MatlabIntLit :: (1 <= n) => NatRepr n -> Integer -> App f MatlabIntType
  -- Check if two values are equal.
  MatlabIntEq :: !(f MatlabIntType) -> !(f MatlabIntType) -> App f BoolType
  -- Check if one value is less than another.
  MatlabIntLt :: !(f MatlabIntType) -> !(f MatlabIntType) -> App f BoolType
  -- Check is value is positive.
  MatlabIntIsPos :: !(f MatlabIntType) -> App f BoolType
  -- Convert to a natural number.
  -- Undefined on negative numbers.
  MatlabIntToNat :: !(f MatlabIntType) -> App f NatType

  ----------------------------------------------------------------------
  -- IntArrayType

  -- Create empty int array with same width as input type.
  MatlabIntArrayEmpty :: !(f IntWidthType)
                      -> App f MatlabIntArrayType
  -- Create a single element array.
  MatlabIntArraySingleton :: !(f MatlabIntType)
                          -> App f MatlabIntArrayType
  MatlabIntArrayDim :: !(f MatlabIntArrayType)
                    -> App f ArrayDimType

  -- | This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabIntArrayResize :: !(f MatlabIntArrayType)
                       -> !(f ArrayDimType)
                       -> App f MatlabIntArrayType
  MatlabIntArrayLookup :: !(f MatlabIntArrayType)
                       -> !(f (VectorType NatType))
                       -> App f MatlabIntType
  MatlabIntArrayUpdate :: !(f MatlabIntArrayType)
                       -> !(f (VectorType NatType))
                       -> !(f MatlabIntType)
                       -> App f MatlabIntArrayType
  MatlabIntArrayAsSingleton :: !(f MatlabIntArrayType)
                      -> App f (MaybeType MatlabIntType)
  MatlabIntArrayIndex :: !(f MatlabIntArrayType)
                      -> !(f MultiDimArrayIndexType)
                      -> App f MatlabIntArrayType
  -- Compare int arrays (arrays with different dimensions are not equal).
  MatlabIntArrayEq   :: !(f MatlabIntArrayType)
                     -> !(f MatlabIntArrayType)
                     -> App f BoolType
  MatlabIntArrayAsPosNat :: !(f MatlabIntArrayType)
                           -> App f (MaybeType (MultiDimArrayType NatType))

  CplxArrayToMatlabInt :: !(f CplxArrayType)
                       -> !(f IntWidthType)
                       -> App f MatlabIntArrayType
  MatlabIntArraySetWidth  :: !(f MatlabIntArrayType)
                          -> !(f IntWidthType)
                          -> App f MatlabIntArrayType
  MatlabUIntArrayToInt :: !(f MatlabUIntArrayType)
                       -> !(f IntWidthType)
                       -> App f MatlabIntArrayType
  LogicArrayToMatlabInt :: !(f LogicArrayType)
                        -> !(f IntWidthType)
                        -> App f MatlabIntArrayType
  CharArrayToMatlabInt :: !(f CharArrayType)
                       -> !(f IntWidthType)
                       -> App f MatlabIntArrayType

  ----------------------------------------------------------------------
  -- UIntWidth

  -- Return width of uint array.
  UIntArrayWidth :: !(f MatlabUIntArrayType)
                 -> App f UIntWidthType

  ----------------------------------------------------------------------
  -- MatlabUInt

  -- Create an expression from a constant.
  MatlabUIntLit :: (1 <= n) => NatRepr n -> Integer -> App f MatlabUIntType
  -- Check if two values are equal.
  MatlabUIntEq :: !(f MatlabUIntType) -> !(f MatlabUIntType) -> App f BoolType
  -- Check if one value is less than another.
  MatlabUIntLt :: !(f MatlabUIntType) -> !(f MatlabUIntType) -> App f BoolType
  -- Check is value is positive.
  MatlabUIntIsPos :: !(f MatlabUIntType) -> App f BoolType
  -- Convert a MatlabUInt to a natural number.
  MatlabUIntToNat :: !(f MatlabUIntType) -> App f NatType


  ----------------------------------------------------------------------
  -- Symbolic (u)int arrays

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabSymIntArrayResize :: !(f MatlabSymbolicIntArrayType)
                          -> !(f ArrayDimType)
                          -> App f MatlabSymbolicIntArrayType
  MatlabSymIntArrayLookup :: !(f MatlabSymbolicIntArrayType)
                          -> !(f (VectorType NatType))
                          -> App f MatlabIntType
  MatlabSymIntArrayUpdate :: !(f MatlabSymbolicIntArrayType)
                          -> !(f (VectorType NatType))
                          -> !(f MatlabIntType)
                          -> App f MatlabSymbolicIntArrayType
  MatlabSymIntArrayAsSingleton :: !(f MatlabSymbolicIntArrayType)
                      -> App f (MaybeType MatlabIntType)

  SymIntArrayWidth
             :: !(f MatlabSymbolicIntArrayType)
             -> App f IntWidthType

  SymIndexIntArray
             :: !(f (MatlabSymbolicIntArrayType))
             -> !(f MultiDimArrayIndexType)
             -> App f MatlabIntArrayType

  MatlabSymbolicIntArrayDim
             :: !(f (MatlabSymbolicIntArrayType))
             -> App f (ArrayDimType)

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabSymUIntArrayResize :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f ArrayDimType)
                           -> App f MatlabSymbolicUIntArrayType
  MatlabSymUIntArrayLookup :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f (VectorType NatType))
                           -> App f MatlabUIntType
  MatlabSymUIntArrayUpdate :: !(f MatlabSymbolicUIntArrayType)
                           -> !(f (VectorType NatType))
                           -> !(f MatlabUIntType)
                           -> App f MatlabSymbolicUIntArrayType
  MatlabSymUIntArrayAsSingleton :: !(f MatlabSymbolicUIntArrayType)
                      -> App f (MaybeType MatlabUIntType)

  SymUIntArrayWidth
             :: !(f MatlabSymbolicUIntArrayType)
             -> App f UIntWidthType

  SymIndexUIntArray
             :: !(f (MatlabSymbolicUIntArrayType))
             -> !(f MultiDimArrayIndexType)
             -> App f MatlabUIntArrayType

  MatlabSymbolicUIntArrayDim
             :: !(f (MatlabSymbolicUIntArrayType))
             -> App f (ArrayDimType)

  SymIntArrayExternalize
                :: !(f MatlabSymbolicIntArrayType)
                -> App f MatlabIntArrayType

  SymUIntArrayExternalize
                :: !(f MatlabSymbolicUIntArrayType)
                -> App f MatlabUIntArrayType

  ----------------------------------------------------------------------
  -- BV

  -- generate an "undefined" bitvector value
  BVUndef :: (1 <= w) => NatRepr w -> App f (BVType w)

  BVLit :: (1 <= w) => NatRepr w -> Integer -> App f (BVType w)

  -- concatenate two bitvectors
  BVConcat :: (1 <= u, 1 <= v, 1 <= u+v)
           => !(NatRepr u)
           -> !(NatRepr v)
           -> !(f (BVType u))       -- Most significant bits
           -> !(f (BVType v))       -- Least significant bits
           -> App f (BVType (u+v))

  -- BVSelect idx n bv choses bits [idx, .. , idx+n-1] from bitvector bv.
  -- The resulting bitvector will have width n.
  -- Index 0 denotes the least-significant bit.
  BVSelect :: (1 <= w, 1 <= len, idx + len <= w)
           => !(NatRepr idx)
           -> !(NatRepr len)
           -> !(NatRepr w)
           -> !(f (BVType w))
           -> App f (BVType len)

  BVTrunc :: (1 <= r, r+1 <= w)
          => !(NatRepr r)
          -> !(NatRepr w)
          -> !(f (BVType w))
          -> App f (BVType r)

  BVZext :: (1 <= w, 1 <= r, w+1 <= r)
         => !(NatRepr r)
         -> !(NatRepr w)
         -> !(f (BVType w))
         -> App f (BVType r)

  BVSext :: (1 <= w, 1 <= r, w+1 <= r)
         => !(NatRepr r)
         -> !(NatRepr w)
         -> !(f (BVType w))
         -> App f (BVType r)

  BVEq  :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f BoolType

  -- Complement bits in bitvector.
  BVNot :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> App f (BVType w)

  BVAnd :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVOr  :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVXor :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVAdd :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVSub :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVMul :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BVUdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App f (BVType w)

  BVSdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App f (BVType w)

  BVUrem :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App f (BVType w)

  BVSrem :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w))
         -> !(f (BVType w))
         -> App f (BVType w)

  BVUle :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f BoolType

  BVUlt :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f BoolType

  BVSle :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f BoolType

  BVSlt :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f BoolType

  -- True if the unsigned addition of the two given bitvectors
  -- has a carry-out; that is, if the unsigned addition overflows.
  BVCarry :: (1 <= w)
          => !(NatRepr w)
          -> !(f (BVType w))
          -> !(f (BVType w))
          -> App f BoolType

  -- True if the signed addition of the two given bitvectors
  -- has a signed overflow condition.
  BVSCarry :: (1 <= w)
           => !(NatRepr w)
           -> !(f (BVType w))
           -> !(f (BVType w))
           -> App f BoolType

  -- True if the signed subtraction of the two given bitvectors
  -- has a signed overflow condition.
  BVSBorrow :: (1 <= w)
            => !(NatRepr w)
            -> !(f (BVType w))
            -> !(f (BVType w))
            -> App f BoolType

  -- Perform a left-shift
  BVShl :: (1 <= w)
        => !(NatRepr w)
        -> !(f (BVType w)) -- Value to shift
        -> !(f (BVType w)) -- The shift amount as an unsigned integer.
        -> App f (BVType w)

  -- Perform a logical shift right
  BVLshr :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w)) -- Value to shift
         -> !(f (BVType w)) -- The shift amount as an unsigned integer.
         -> App f (BVType w)

  -- Perform a signed shift right (if the
  BVAshr :: (1 <= w)
         => !(NatRepr w)
         -> !(f (BVType w)) -- Value to shift
         -> !(f (BVType w)) -- The shift amount as an unsigned integer.
         -> App f (BVType w)

  BVIte :: (1 <= w)
        => !(f BoolType)
        -> !(NatRepr w)
        -> !(f (BVType w))
        -> !(f (BVType w))
        -> App f (BVType w)

  BoolToBV :: (1 <= w)
           => !(NatRepr w)
           -> !(f BoolType)
           -> App f (BVType w)

  -- Return the unsigned value of the given bitvector as a nat
  BvToNat :: (1 <= w)
          => !(NatRepr w)
          -> !(f (BVType w))
          -> App f NatType

  BVNonzero :: (1 <= w)
            => !(NatRepr w)
            -> !(f (BVType w))
            -> App f BoolType

  ----------------------------------------------------------------------
  -- UIntArrayType

  -- Create empty uint array with same width as input type.
  MatlabUIntArrayEmpty :: !(f UIntWidthType)
                       -> App f MatlabUIntArrayType
  -- Create a single element array.
  MatlabUIntArraySingleton :: !(f MatlabUIntType)
                           -> App f MatlabUIntArrayType
  MatlabUIntArrayDim :: !(f MatlabUIntArrayType)
                     -> App f ArrayDimType

  -- This resizes the array to given dimensions.
  --
  -- The new dimensions can be assumed to be not smaller than the current array
  -- dimensions in each index.  When resizing the array, the new dimensions
  -- all have the value of 0.
  MatlabUIntArrayResize :: !(f MatlabUIntArrayType)
                        -> !(f ArrayDimType)
                        -> App f MatlabUIntArrayType
  -- Index uint array at index.
  MatlabUIntArrayLookup :: !(f MatlabUIntArrayType)
                        -> !(f (VectorType NatType))
                        -> App f MatlabUIntType
  -- Set value of array at index.
  MatlabUIntArrayUpdate :: !(f MatlabUIntArrayType)
                        -> !(f (VectorType NatType))
                        -> !(f MatlabUIntType)
                        -> App f MatlabUIntArrayType
  MatlabUIntArrayAsSingleton :: !(f MatlabUIntArrayType)
                             -> App f (MaybeType MatlabUIntType)
  MatlabUIntArrayIndex :: !(f MatlabUIntArrayType)
                       -> !(f MultiDimArrayIndexType)
                       -> App f MatlabUIntArrayType
  -- Compare uint arrays (arrays with different dimensions are not equal).
  MatlabUIntArrayEq :: !(f MatlabUIntArrayType)
                    -> !(f MatlabUIntArrayType)
                    -> App f BoolType
  MatlabUIntArrayAsPosNat :: !(f MatlabUIntArrayType)
                            -> App f (MaybeType (MultiDimArrayType NatType))
  CplxArrayToMatlabUInt :: !(f CplxArrayType)
                        -> !(f UIntWidthType)
                        -> App f MatlabUIntArrayType
  MatlabIntArrayToUInt :: !(f MatlabIntArrayType)
                       -> !(f UIntWidthType)
                       -> App f MatlabUIntArrayType
  MatlabUIntArraySetWidth :: !(f MatlabUIntArrayType)
                          -> !(f UIntWidthType)
                          -> App f MatlabUIntArrayType
  LogicArrayToMatlabUInt :: !(f LogicArrayType)
                         -> !(f UIntWidthType)
                         -> App f MatlabUIntArrayType
  CharArrayToMatlabUInt :: !(f CharArrayType)
                        -> !(f UIntWidthType)
                        -> App f MatlabUIntArrayType

  ----------------------------------------------------------------------
  -- LogicArrayType

  -- Compare Boolean arrays (arrays with different dimensions are not equal).
  LogicArrayEq :: !(f LogicArrayType)
               -> !(f LogicArrayType)
               -> App f BoolType
  LogicArrayToIndices :: !(f LogicArrayType)
                      -> App f (MultiDimArrayType NatType)
  CplxArrayToLogic :: !(f CplxArrayType)
                   -> App f LogicArrayType
  IntegerArrayToLogic :: !(f IntegerArrayType)
                      -> App f LogicArrayType
  RealArrayToLogic :: !(f RealArrayType)
                      -> App f LogicArrayType
  MatlabIntArrayToLogic :: !(f MatlabIntArrayType)
                        -> App f LogicArrayType
  MatlabUIntArrayToLogic :: !(f MatlabUIntArrayType)
                         -> App f LogicArrayType
  -- Return true if all entries in array are true.
  AllEntriesAreTrue :: !(f LogicArrayType)
                    -> App f BoolType

  ----------------------------------------------------------------------
  -- CharArrayType

  -- A character array literal (also called a string).
  CharVectorLit :: !CharVector
                -> App f CharArrayType

  IntegerArrayEq :: !(f (IntegerArrayType))
                 -> !(f (IntegerArrayType))
                 -> App f BoolType
  RealArrayEq :: !(f (RealArrayType))
              -> !(f (RealArrayType))
              -> App f BoolType

  -- Compare char arrays (arrays with different dimensions are not equal).
  CharArrayEq :: !(f CharArrayType)
              -> !(f CharArrayType)
              -> App f BoolType
  CplxArrayToChar :: !(f CplxArrayType)
                  -> App f CharArrayType
  CharArrayAsPosNat :: !(f CharArrayType)
                      -> App f (MaybeType (MultiDimArrayType NatType))
  CharArrayToLogic :: !(f CharArrayType)
                   -> App f LogicArrayType

  ----------------------------------------------------------------------
  -- CellArrayType

  -- Update cell array at a single specific index.
  -- Throws error when evaluated if the cell entry is out of range,
  -- or expression contains multiple indices.
  UpdateCellEntry :: !(f CellArrayType)
                  -> !(f (VectorType NatType))
                  -> !(f MatlabValueType)
                  -> App f CellArrayType

  -- Return arguments after vector in a cell array.
  GetVarArgs :: !(f (VectorType MatlabValueType))
             -> !Nat
             -> App f CellArrayType

  ----------------------------------------------------------------------
  -- StructFields

  -- Empty set of struct fields.
  EmptyStructFields :: App f (VectorType StringType)

  -- Return true if fields are equal.
  FieldsEq :: !(f (VectorType StringType))
           -> !(f (VectorType StringType))
           -> App f BoolType

  -- Return true if field is in set.
  HasField :: !(f StringType)
           -> !(f (VectorType StringType))
           -> App f BoolType

  ----------------------------------------------------------------------
  -- MatlabValue

  CplxArrayToMatlab :: !(f CplxArrayType)
                    -> App f MatlabValueType
  MatlabIntArrayToMatlab :: !(f MatlabIntArrayType)
                         -> App f MatlabValueType
  MatlabUIntArrayToMatlab :: !(f MatlabUIntArrayType)
                          -> App f MatlabValueType
  LogicArrayToMatlab :: !(f LogicArrayType)
                     -> App f MatlabValueType
  SymLogicArrayToMatlab :: !(f SymLogicArrayType)
                     -> App f MatlabValueType
  SymRealArrayToMatlab :: !(f SymRealArrayType)
                       -> App f MatlabValueType
  SymCplxArrayToMatlab :: !(f SymCplxArrayType)
                     -> App f MatlabValueType
  SymIntArrayToMatlab :: !(f MatlabSymbolicIntArrayType)
                      -> App f MatlabValueType
  SymUIntArrayToMatlab :: !(f MatlabSymbolicUIntArrayType)
                      -> App f MatlabValueType
  CharArrayToMatlab :: !(f CharArrayType)
                    -> App f MatlabValueType
  CellArrayToMatlab :: !(f CellArrayType)
                 -> App f MatlabValueType
  MatlabStructArrayToMatlab :: !(f MatlabStructArrayType)
                            -> App f MatlabValueType
  MatlabObjectArrayToMatlab :: !(f MatlabObjectArrayType)
                            -> App f MatlabValueType
  HandleToMatlab :: !(f MatlabHandleType)
                 -> App f MatlabValueType

  ----------------------------------------------------------------------
  -- WordMap

  EmptyWordMap :: (1 <= w)
               => !(NatRepr w)
               -> !(BaseTypeRepr tp)
               -> App f (WordMapType w tp)

  InsertWordMap :: (1 <= w)
                => !(NatRepr w)
                -> !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (BaseToType tp))
                -> !(f (WordMapType w tp))
                -> App f (WordMapType w tp)

  LookupWordMap :: (1 <= w)
                => !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (WordMapType w tp))
                -> App f (BaseToType tp)

  LookupWordMapWithDefault
                :: (1 <= w)
                => !(BaseTypeRepr tp)
                -> !(f (BVType w))
                -> !(f (WordMapType w tp))
                -> !(f (BaseToType tp))
                -> App f (BaseToType tp)

  ----------------------------------------------------------------------
  -- Variants

  InjectVariant :: !(CtxRepr ctx)
            -> !(Ctx.Index ctx tp)
            -> !(f tp)
            -> App f (VariantType ctx)

  ----------------------------------------------------------------------
  -- Struct

  MkStruct :: !(CtxRepr ctx)
           -> !(Ctx.Assignment f ctx)
           -> App f (StructType ctx)

  GetStruct :: !(f (StructType ctx))
            -> !(Ctx.Index ctx tp)
            -> !(TypeRepr tp)
            -> App f tp

  SetStruct :: !(CtxRepr ctx)
            -> !(f (StructType ctx))
            -> !(Ctx.Index ctx tp)
            -> !(f tp)
            -> App f (StructType ctx)

  ----------------------------------------------------------------------
  -- StringMapType

  -- Initialize the ident value map to the given value.
  EmptyStringMap :: !(TypeRepr tp)
                 -> App f (StringMapType tp)

  -- Lookup the value of a string in a string map.
  LookupStringMapEntry :: !(TypeRepr tp)
                       -> !(f (StringMapType tp))
                       -> !(f StringType)
                       -> App f (MaybeType tp)

  -- Update the name of the ident value map with the given value.
  InsertStringMapEntry :: !(TypeRepr tp)
                       -> !(f (StringMapType tp))
                       -> !(f StringType)
                       -> !(f (MaybeType tp))
                       -> App f (StringMapType tp)

  ----------------------------------------------------------------------
  -- String

  TextLit :: !Text
          -> App f StringType

  -- Assignment statement "nm = v"
  AssignmentText :: !(f StringType)
                 -> !(f MatlabValueType)
                 -> App f StringType

  ShowValue :: !(BaseTypeRepr bt)
            -> !(f (BaseToType bt))
            -> App f StringType

  ----------------------------------------------------------------------
  -- Arrays (supporting symbolic operations)

  SymArrayLookup   :: !(BaseTypeRepr b)
                   -> !(f (SymbolicArrayType (idx ::> tp) b))
                   -> !(Ctx.Assignment (BaseTerm f) (idx ::> tp))
                   -> App f (BaseToType b)

  SymArrayUpdate   :: !(BaseTypeRepr b)
                   -> !(f (SymbolicArrayType (idx ::> itp) b))
                   -> !(Ctx.Assignment (BaseTerm f) (idx ::> itp))
                   -> !(f (BaseToType b))
                   -> App f (SymbolicArrayType (idx ::> itp) b)

  ------------------------------------------------------------------------
  -- Introspection

  -- Returns true if the given value is a concrete value, false otherwise.
  -- This is primarily intended to assist with issuing warnings and such
  -- when a value is expected to be concrete.  This primitive could be
  -- used for evil; try to avoid the temptation.
  IsConcrete :: !(BaseTypeRepr b)
             -> f (BaseToType b)
             -> App f BoolType


appType :: App f tp -> TypeRepr tp
appType a0 =
  case a0 of
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

    RollRecursive nm _ -> RecursiveRepr nm
    UnrollRecursive nm _ -> unrollType nm

    ----------------------------------------------------------------------
    -- Vector
    VectorLit tp _ -> VectorRepr tp
    VectorReplicate tp _ _ -> VectorRepr tp
    VectorIsEmpty{} -> knownRepr
    VectorSize{} -> knownRepr
    VectorGetEntry tp _ _ -> tp
    VectorSetEntry tp _ _ _ -> VectorRepr tp

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
    -- CellArrayType
    UpdateCellEntry{} -> knownRepr
    GetVarArgs{} -> knownRepr

    ----------------------------------------------------------------------
    -- StructFields
    EmptyStructFields{} -> knownRepr
    FieldsEq{} -> knownRepr
    HasField{} -> knownRepr

    ----------------------------------------------------------------------
    -- MatlabValue

    --GetFieldName{} -> knownRepr
    CplxArrayToMatlab{} -> knownRepr
    MatlabIntArrayToMatlab{} -> knownRepr
    MatlabUIntArrayToMatlab{} -> knownRepr
    LogicArrayToMatlab{} -> knownRepr
    SymLogicArrayToMatlab{} -> knownRepr
    SymRealArrayToMatlab{} -> knownRepr
    SymCplxArrayToMatlab{} -> knownRepr
    SymIntArrayToMatlab{} -> knownRepr
    SymUIntArrayToMatlab{} -> knownRepr
    CharArrayToMatlab{} -> knownRepr
    CellArrayToMatlab{} -> knownRepr
    MatlabStructArrayToMatlab{} -> knownRepr
    MatlabObjectArrayToMatlab{} -> knownRepr
    HandleToMatlab{} -> knownRepr

    ----------------------------------------------------------------------
    -- Struct

    MkStruct ctx _ -> StructRepr ctx
    GetStruct _ _ tp -> tp
    SetStruct ctx _ _ _ -> StructRepr ctx

    ----------------------------------------------------------------------
    -- Variants

    InjectVariant ctx _ _ -> VariantRepr ctx

    ----------------------------------------------------------------------
    -- StringMap
    EmptyStringMap tp             -> StringMapRepr tp
    LookupStringMapEntry tp _ _   -> MaybeRepr tp
    InsertStringMapEntry tp _ _ _ -> StringMapRepr tp

    ----------------------------------------------------------------------
    -- String

    TextLit{} -> knownRepr
    AssignmentText{} -> knownRepr
    ShowValue{} -> knownRepr

    ----------------------------------------------------------------------
    -- Array
--    SymArrayConstant dom ran _   -> SymbolicArrayRepr dom ran
--    SymArrayLookup _dom ran _ _  -> baseToType ran
--    SymArrayUpdate dom ran _ _ _ -> SymbolicArrayRepr dom ran
--    SymArrayEq _ _ _ _ -> knownRepr

    ------------------------------------------------------------------------
    -- Introspection

    IsConcrete _ _ -> knownRepr

------------------------------------------------------------------------
-- Reg

-- | A temporary register identifier introduced during translation.
--   These are unique to the current function.  The `ctx` parameter
--   is a context containing the types of all the temporary registers
--   currently in scope, and the `tp` parameter indicates the type
--   of this register (which necessarily appears somewhere in `ctx`)
newtype Reg (ctx :: Ctx CrucibleType) (tp :: CrucibleType) = Reg { regIndex :: Ctx.Index ctx tp }
  deriving (Eq, TestEquality, Ord, OrdF)

instance Show (Reg ctx tp) where
  show (Reg i) = '$' : show (Ctx.indexVal i)

instance ShowF (Reg ctx) where
  showF x = show x

instance Pretty (Reg ctx tp) where
  pretty = text.show

instance Ctx.ApplyEmbedding' Reg where
  applyEmbedding' ctxe r = Reg $ Ctx.applyEmbedding' ctxe (regIndex r)

instance Ctx.ExtendContext' Reg where
  extendContext' diff r = Reg $ Ctx.extendContext' diff (regIndex r)

-- | Finds the value of the most-recently introduced register in scope.
lastReg :: Ctx.KnownContext ctx => Reg (ctx ::> tp) tp
lastReg = Reg (Ctx.nextIndex Ctx.knownSize)

-- | Extend the set of registers in scope for a given register value
--   without changing its index or type.
extendReg :: Reg ctx tp -> Reg (ctx ::> r) tp
extendReg = Reg . Ctx.extendIndex . regIndex

#ifdef UNSAFE_OPS
instance CoerceableF (Reg ctx) where
  coerceF x = Data.Coerce.coerce x
#endif

------------------------------------------------------------------------
-- Expr

-- | An expression is just an App applied to some registers.
newtype Expr (ctx :: Ctx CrucibleType) (tp :: CrucibleType)
      = App (App (Reg ctx) tp)

instance IsString (Expr ctx StringType) where
  fromString  = App . TextLit . fromString

ppAssignment :: Ctx.Assignment (Reg ctx) args -> [Doc]
ppAssignment = toListFC pretty

------------------------------------------------------------------------
-- GlobalRef

-- | A reference to a global variable.
data GlobalVar tp
   = GlobalVar { globalNonce :: {-# UNPACK #-} !(Nonce tp)
               , globalName  :: !Text
               , globalType  :: !(TypeRepr tp)
               }

instance TestEquality GlobalVar where
  x `testEquality` y = globalNonce x `testEquality` globalNonce y

instance OrdF GlobalVar where
  x `compareF` y = globalNonce x `compareF` globalNonce y

instance Show (GlobalVar tp) where
  show = Text.unpack . globalName

instance Pretty (GlobalVar tp) where
  pretty  = text . show


freshGlobalVar :: HandleAllocator s
               -> Text
               -> TypeRepr tp
               -> ST s (GlobalVar tp)
freshGlobalVar halloc nm tp = do
  nonce <- freshNonce (haCounter halloc)
  return GlobalVar
         { globalNonce = nonce
         , globalName  = nm
         , globalType  = tp
         }

------------------------------------------------------------------------
-- BlockID

-- | A `BlockID` uniquely identifies a block in a control-flow graph.
--   Each block has an associated context, indicating the formal arguments
--   it expects to find in registers from its calling locations.
newtype BlockID (blocks :: Ctx (Ctx CrucibleType)) (tp :: Ctx CrucibleType)
      = BlockID { blockIDIndex :: Ctx.Index blocks tp }
  deriving ( Eq, Ord)

instance TestEquality (BlockID blocks) where
  testEquality (BlockID x) (BlockID y) = testEquality x y

instance OrdF (BlockID blocks) where
  compareF (BlockID x) (BlockID y) = compareF x y

instance Pretty (BlockID blocks tp) where
  pretty (BlockID i) = char '%' <> int (Ctx.indexVal i)

instance Show (BlockID blocks ctx) where
  show (BlockID i) = '%' : show (Ctx.indexVal i)

instance ShowF (BlockID blocks) where
  showF x = show x

extendBlockID :: Ctx.KnownDiff l r => BlockID l tp -> BlockID r tp
extendBlockID = BlockID . Ctx.extendIndex . blockIDIndex

extendBlockID' :: Ctx.Diff l r -> BlockID l tp -> BlockID r tp
extendBlockID' e = BlockID . Ctx.extendIndex' e . blockIDIndex

------------------------------------------------------------------------
-- JumpTarget

-- | Target for jump and branch statements
data JumpTarget blocks ctx where
     JumpTarget :: !(BlockID blocks args)            -- BlockID to jump to
                -> !(CtxRepr args)                   -- expected argument types
                -> !(Ctx.Assignment (Reg ctx) args) -- jump target actual arguments
                -> JumpTarget blocks ctx

instance Pretty (JumpTarget blocks ctx) where
  pretty (JumpTarget tgt _ a) = pretty tgt <> parens (commas (ppAssignment a))

jumpTargetID :: JumpTarget blocks ctx -> Some (BlockID blocks)
jumpTargetID (JumpTarget tgt _ _) = Some tgt

extendJumpTarget :: Ctx.Diff blocks' blocks -> JumpTarget blocks' ctx -> JumpTarget blocks ctx
extendJumpTarget diff (JumpTarget b tps a) = JumpTarget (extendBlockID' diff b) tps a

instance Ctx.ApplyEmbedding (JumpTarget blocks) where
  applyEmbedding ctxe (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (Ctx.applyEmbedding' ctxe) args)

instance Ctx.ExtendContext (JumpTarget blocks) where
  extendContext diff (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (Ctx.extendContext' diff) args)



------------------------------------------------------------------------
-- SwitchTarget

-- | Target for a switch statement.
data SwitchTarget blocks ctx tp where
  SwitchTarget :: !(BlockID blocks (args ::> tp))   -- BlockID to jump to
               -> !(CtxRepr args)                   -- expected argument types
               -> !(Ctx.Assignment (Reg ctx) args) -- switch target actual arguments
               -> SwitchTarget blocks ctx tp

switchTargetID :: SwitchTarget blocks ctx tp -> Some (BlockID blocks)
switchTargetID (SwitchTarget tgt _ _) = Some tgt

ppCase :: String -> SwitchTarget blocks ctx tp -> Doc
ppCase nm (SwitchTarget tgt _ a) =
  text nm <+> text "->" <+> pretty tgt <> parens (commas (ppAssignment a))

extendSwitchTarget :: Ctx.Diff blocks' blocks
                   -> SwitchTarget blocks' ctx tp
                   -> SwitchTarget blocks ctx tp
extendSwitchTarget diff (SwitchTarget b tps a) =
    SwitchTarget (extendBlockID' diff b) tps a

instance Ctx.ApplyEmbedding' (SwitchTarget blocks) where
  applyEmbedding' ctxe (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (Ctx.applyEmbedding' ctxe) args)

instance Ctx.ExtendContext' (SwitchTarget blocks) where
  extendContext' diff (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (Ctx.extendContext' diff) args)



------------------------------------------------------------------------
-- MSwitch

-- | Data structure for a type-case switch.  A switch is used to
--   unpack an arbitrary matlab value, jumping to one of the given
--   switch targets, depending on the runtime type of a value to be examined.
data MSwitch tgt
   = MSwitch { matchRealArray      :: tgt CplxArrayType
             , matchIntArray       :: tgt MatlabIntArrayType
             , matchUIntArray      :: tgt MatlabUIntArrayType
             , matchLogicArray     :: tgt LogicArrayType
             , matchCharArray      :: tgt CharArrayType
             , matchCellArray      :: tgt CellArrayType
             , matchStructArray    :: tgt MatlabStructArrayType
             , matchHandle         :: tgt MatlabHandleType
             , matchSymLogicArray  :: tgt SymLogicArrayType
             , matchSymRealArray   :: tgt SymRealArrayType
             , matchSymCplxArray   :: tgt SymCplxArrayType
             , matchSymIntArray    :: tgt MatlabSymbolicIntArrayType
             , matchSymUIntArray   :: tgt MatlabSymbolicUIntArrayType
             , matchObjectArray    :: tgt MatlabObjectArrayType
             }

constMSwitch :: (forall tp . tgt tp) -> MSwitch tgt
constMSwitch v =
  MSwitch { matchRealArray      = v
          , matchIntArray       = v
          , matchUIntArray      = v
          , matchLogicArray     = v
          , matchCharArray      = v
          , matchCellArray      = v
          , matchStructArray    = v
          , matchHandle         = v
          , matchSymLogicArray  = v
          , matchSymRealArray   = v
          , matchSymCplxArray   = v
          , matchSymIntArray    = v
          , matchSymUIntArray   = v
          , matchObjectArray    = v
          }

instance ShowF tgt => Show (MSwitch tgt) where
  show (MSwitch {..}) =
     unwords [ "(MSwitch"
             , showF matchRealArray
             , showF matchIntArray
             , showF matchUIntArray
             , showF matchLogicArray
             , showF matchCharArray
             , showF matchCellArray
             , showF matchStructArray
             , showF matchHandle
             , showF matchSymLogicArray
             , showF matchSymRealArray
             , showF matchSymCplxArray
             , showF matchSymIntArray
             , showF matchSymUIntArray
             , showF matchObjectArray
             , ")"]

instance FunctorF MSwitch where
  fmapF = fmapFDefault

instance FoldableF MSwitch where
  foldMapF = foldMapFDefault

instance TraversableF MSwitch where
  traverseF f m = do
    MSwitch
      <$> f (matchRealArray m)
      <*> f (matchIntArray m)
      <*> f (matchUIntArray m)
      <*> f (matchLogicArray m)
      <*> f (matchCharArray m)
      <*> f (matchCellArray m)
      <*> f (matchStructArray m)
      <*> f (matchHandle m)
      <*> f (matchSymLogicArray m)
      <*> f (matchSymRealArray m)
      <*> f (matchSymCplxArray m)
      <*> f (matchSymIntArray m)
      <*> f (matchSymUIntArray m)
      <*> f (matchObjectArray m)

zipSwitchWith :: (forall tp. f tp -> g tp -> h tp) -> MSwitch f -> MSwitch g -> MSwitch h
zipSwitchWith f m1 m2 =
  MSwitch
  { matchRealArray   = f (matchRealArray m1)    (matchRealArray m2)
  , matchIntArray    = f (matchIntArray m1)     (matchIntArray m2)
  , matchUIntArray   = f (matchUIntArray m1)    (matchUIntArray m2)
  , matchLogicArray  = f (matchLogicArray m1)   (matchLogicArray m2)
  , matchCharArray   = f (matchCharArray m1)    (matchCharArray m2)
  , matchCellArray   = f (matchCellArray m1)    (matchCellArray m2)
  , matchStructArray = f (matchStructArray m1)  (matchStructArray m2)
  , matchHandle      = f (matchHandle m1)       (matchHandle m2)
  , matchSymLogicArray = f (matchSymLogicArray m1) (matchSymLogicArray m2)
  , matchSymRealArray  = f (matchSymRealArray m1)  (matchSymRealArray m2)
  , matchSymCplxArray  = f (matchSymCplxArray m1)  (matchSymCplxArray m2)
  , matchSymIntArray   = f (matchSymIntArray m1)   (matchSymIntArray m2)
  , matchSymUIntArray  = f (matchSymUIntArray m1)  (matchSymUIntArray m2)
  , matchObjectArray   = f (matchObjectArray m1)   (matchObjectArray m2)
  }

extendMSwitch :: Ctx.Diff blocks' blocks
              -> MSwitch (SwitchTarget blocks' ctx)
              -> MSwitch (SwitchTarget blocks ctx)
extendMSwitch diff = fmapF (extendSwitchTarget diff)


ppMSwitch :: (forall tp . String -> tgt tp -> Doc) -> MSwitch tgt -> [Doc]
ppMSwitch pp (MSwitch {..})
  = [ pp "R"       matchRealArray
    , pp "I"       matchIntArray
    , pp "U"       matchUIntArray
    , pp "Ch"      matchLogicArray
    , pp "L"       matchCharArray
    , pp "Cell"    matchCellArray
    , pp "S"       matchStructArray
    , pp "H"       matchHandle
    , pp "symL"    matchSymLogicArray
    , pp "symR"    matchSymRealArray
    , pp "symCplx" matchSymCplxArray
    , pp "symI"    matchSymIntArray
    , pp "symU"    matchSymUIntArray
    , pp "O"       matchObjectArray
    ]

------------------------------------------------------------------------
-- Stmt

-- | A sequential statement that does not affect the
-- program location within the current block or leave the current
-- block.
data Stmt (ctx :: Ctx CrucibleType) (ctx' :: Ctx CrucibleType) where
  -- Assign the value of a register
  SetReg :: !(TypeRepr tp)
         -> !(Expr ctx tp)
         -> Stmt ctx (ctx ::> tp)

  -- Statement used for evaluating function calls
  CallHandle :: !(TypeRepr ret)                          -- The type of the return value(s)
             -> !(Reg ctx (FunctionHandleType args ret)) -- The function handle to call
             -> !(CtxRepr args)                          -- The expected types of the arguments
             -> !(Ctx.Assignment (Reg ctx) args)         -- The actual arguments to the call
             -> Stmt ctx (ctx ::> ret)

  -- Print a message out to the console
  Print :: !(Reg ctx StringType) -> Stmt ctx ctx

  -- Read a global variable.
  ReadGlobal :: !(GlobalVar tp)
             -> Stmt ctx (ctx ::> tp)

  -- Write to a global variable.
  WriteGlobal :: !(GlobalVar tp)
              -> !(Reg ctx tp)
              -> Stmt ctx ctx

  -- Allocate a new reference cell
  NewRefCell :: !(TypeRepr tp)
             -> !(Reg ctx tp)
             -> Stmt ctx (ctx ::> ReferenceType tp)

  -- Read the current value of a reference cell
  ReadRefCell :: !(Reg ctx (ReferenceType tp))
              -> Stmt ctx (ctx ::> tp)

  -- Write the current value of a reference cell
  WriteRefCell :: !(Reg ctx (ReferenceType tp))
               -> !(Reg ctx tp)
               -> Stmt ctx ctx

  -- Assert a boolean condition.  If the condition fails, print the given string.
  Assert :: !(Reg ctx BoolType) -> !(Reg ctx StringType) -> Stmt ctx ctx

------------------------------------------------------------------------
-- TermStmt

data TermStmt blocks (ret :: CrucibleType) (ctx :: Ctx CrucibleType) where
  -- Jump to the given jump target
  Jump :: !(JumpTarget blocks ctx)
       -> TermStmt blocks ret ctx

  -- Branch on condition.  If true, jump to the first jump target; otherwise
  -- jump to the second jump target.
  Br :: !(Reg ctx BoolType)
     -> !(JumpTarget blocks ctx)
     -> !(JumpTarget blocks ctx)
     -> TermStmt blocks ret ctx

  -- Switch on whether this is a maybe value.  Jump to the switch target if
  -- the maybe value is a "Some".  Otherwise (if "Nothing"), jump to the jump target.
  MaybeBranch :: !(TypeRepr tp)
              -> !(Reg ctx (MaybeType tp))
              -> !(SwitchTarget blocks ctx tp)
              -> !(JumpTarget blocks ctx)
              -> TermStmt blocks rtp ctx

  -- Switch on a Matlab value.  Examine the runtime type of the given
  -- dynamic expression and jump to the appropriate switch target.
  MSwitchStmt :: !(Reg ctx MatlabValueType)
              -> !(MSwitch (SwitchTarget blocks ctx))
              -> TermStmt blocks ret ctx

  -- Switch on a variant value.  Examine the tag of the variant
  -- and jump to the appropriate switch target.
  VariantElim :: !(CtxRepr varctx)
              -> !(Reg ctx (VariantType varctx))
              -> !(Ctx.Assignment (SwitchTarget blocks ctx) varctx)
              -> TermStmt blocks ret ctx

  -- Return from function, providing the return value(s).
  Return :: !(Reg ctx ret)
         -> TermStmt blocks ret ctx

  -- End block with a tail call.
  TailCall :: !(Reg ctx (FunctionHandleType args ret))
           -> !(CtxRepr args)
           -> !(Ctx.Assignment (Reg ctx) args)
           -> TermStmt blocks ret ctx

  -- Block ends with an error.
  ErrorStmt :: !(Reg ctx StringType) -> TermStmt blocks ret ctx

extendTermStmt :: Ctx.Diff blocks' blocks -> TermStmt blocks' ret ctx -> TermStmt blocks ret ctx
extendTermStmt diff (Jump tgt) = Jump (extendJumpTarget diff tgt)
extendTermStmt diff (Br c x y) = Br c (extendJumpTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (MaybeBranch tp c x y) =
  MaybeBranch tp c (extendSwitchTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (MSwitchStmt e s) =
  MSwitchStmt e (extendMSwitch diff s)
extendTermStmt diff (VariantElim ctx e asgn) =
  VariantElim ctx e (fmapFC (extendSwitchTarget diff) asgn)
extendTermStmt _diff (Return e) = Return e
extendTermStmt _diff (TailCall h tps args) = TailCall h tps args
extendTermStmt _diff (ErrorStmt e) = ErrorStmt e

-- | Return the set of possible next blocks from a TermStmt
termStmtNextBlocks :: TermStmt b ret ctx -> Maybe [Some (BlockID b)]
termStmtNextBlocks s0 =
  case s0 of
    Jump tgt             -> Just [ jumpTargetID tgt ]
    Br          _ x y    -> Just [ jumpTargetID x, jumpTargetID y ]
    MaybeBranch _ _ x y  -> Just [ switchTargetID x, jumpTargetID y ]
    VariantElim _ _ a    -> Just (toListFC switchTargetID a)
    MSwitchStmt _ s      -> Just (toListF switchTargetID s)
    Return      _        -> Nothing
    TailCall    _ _ _    -> Nothing
    ErrorStmt   _        -> Just []

instance Pretty (TermStmt blocks ret ctx) where
 pretty s =
  case s of
    Jump b   -> text "jump" <+> pretty b
    Br e x y -> text "br"  <+> pretty e <+> pretty x <+> pretty y
    MaybeBranch _ e j n ->
      text "maybeBranch" <+> pretty e <+> lbrace <$$>
        indent 2 (
          vcat [ ppCase "Just" j
               , text "Nothing ->" <+> pretty n
               ] <$$>
          rbrace)
    VariantElim _ e asgn ->
      let branches =
              [ f (show i) <> semi
              | i <- [(0::Int) .. ]
              | f <- toListFC (\tgt nm -> ppCase nm tgt) asgn
              ] in
      text "vswitch" <+> pretty e <+> lbrace <$$>
       indent 2 (vcat branches) <$$>
       rbrace
    MSwitchStmt e c ->
      text "switch" <+> pretty e <+> lbrace <$$>
       indent 2 (
         vcat ((<> semi) <$> ppMSwitch ppCase c) <$$>
         rbrace)
    Return e ->
      text "return"
       <+> pretty e
    TailCall h _ args ->
      text "tailCall"
       <+> pretty h
       <+> parens (commas (ppAssignment args))
    ErrorStmt msg ->
      text "error" <+> pretty msg


applyEmbeddingStmt :: forall ctx ctx' sctx.
                      Ctx.CtxEmbedding ctx ctx' -> Stmt ctx sctx
                      -> Pair (Stmt ctx') (Ctx.CtxEmbedding sctx)
applyEmbeddingStmt ctxe stmt =
  case stmt of
    SetReg tp e -> Pair (SetReg tp (Ctx.applyEmbedding' ctxe e))
                        (Ctx.extendEmbeddingBoth ctxe)

    CallHandle ret hdl tys args ->
      Pair (CallHandle ret (reg hdl) tys (fmapFC reg args))
           (Ctx.extendEmbeddingBoth ctxe)

    Print str -> Pair (Print (reg str)) ctxe

    ReadGlobal var -> Pair (ReadGlobal var)
                           (Ctx.extendEmbeddingBoth ctxe)

    WriteGlobal var r -> Pair (WriteGlobal var (reg r)) ctxe
    NewRefCell tp r -> Pair (NewRefCell tp (reg r))
                            (Ctx.extendEmbeddingBoth ctxe)
    ReadRefCell r     -> Pair (ReadRefCell (reg r))
                              (Ctx.extendEmbeddingBoth ctxe)
    WriteRefCell r r' ->  Pair (WriteRefCell (reg r) (reg r')) ctxe
    Assert b str      -> Pair (Assert (reg b) (reg str)) ctxe
  where
    reg :: forall tp. Reg ctx tp -> Reg ctx' tp
    reg = Ctx.applyEmbedding' ctxe


instance Ctx.ApplyEmbedding (TermStmt blocks ret) where
  applyEmbedding :: forall ctx ctx'.
                    Ctx.CtxEmbedding ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  applyEmbedding ctxe term =
    case term of
      Jump jt -> Jump (apC jt)
      Br b jtl jtr -> Br (apC' b) (apC jtl) (apC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (apC' b) (apC' swt) (apC jt)
      MSwitchStmt tm targets     -> MSwitchStmt (apC' tm) (fmapF apC' targets)
      VariantElim repr r targets -> VariantElim repr (apC' r) (fmapFC apC' targets)
      Return r -> Return (apC' r)
      TailCall hdl tys args -> TailCall (apC' hdl) tys (fmapFC apC' args)
      ErrorStmt r -> ErrorStmt (apC' r)
    where
      apC' :: forall f v. Ctx.ApplyEmbedding' f => f ctx v -> f ctx' v
      apC' = Ctx.applyEmbedding' ctxe

      apC :: forall f. Ctx.ApplyEmbedding  f => f ctx -> f ctx'
      apC  = Ctx.applyEmbedding  ctxe

instance Ctx.ExtendContext (TermStmt blocks ret) where
  extendContext :: forall ctx ctx'.
                    Ctx.Diff ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  extendContext diff term =
    case term of
      Jump jt -> Jump (extC jt)
      Br b jtl jtr -> Br (extC' b) (extC jtl) (extC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (extC' b) (extC' swt) (extC jt)
      MSwitchStmt tm targets     -> MSwitchStmt (extC' tm) (fmapF extC' targets)
      VariantElim repr r targets -> VariantElim repr (extC' r) (fmapFC extC' targets)
      Return r -> Return (extC' r)
      TailCall hdl tys args -> TailCall (extC' hdl) tys (fmapFC extC' args)
      ErrorStmt r -> ErrorStmt (extC' r)
    where
      extC' :: forall f v. Ctx.ExtendContext' f => f ctx v -> f ctx' v
      extC' = Ctx.extendContext' diff

      extC :: forall f. Ctx.ExtendContext  f => f ctx -> f ctx'
      extC  = Ctx.extendContext  diff




------------------------------------------------------------------------
-- StmtSeq

-- | A sequence of straight-line program statements that end with
--   a terminating statement (return, jump, etc).
data StmtSeq blocks (ret :: CrucibleType) ctx where
  ConsStmt :: !ProgramLoc
           -> !(Stmt ctx ctx')
           -> !(StmtSeq blocks ret ctx')
           -> StmtSeq blocks ret ctx
  TermStmt :: !ProgramLoc
           -> !(TermStmt blocks ret ctx)
           -> (StmtSeq blocks ret ctx)

-- | Return the location of a statement.
firstStmtLoc :: StmtSeq b r ctx -> ProgramLoc
firstStmtLoc (ConsStmt pl _ _) = pl
firstStmtLoc (TermStmt pl _) = pl

-- | A lens-like operation that gives one access to program location and term statement,
-- and allows the terminal statement to be replaced with an arbitrary sequence of
-- statements.
stmtSeqTermStmt :: Functor f
                => (forall ctx
                    . (ProgramLoc, TermStmt b ret ctx)
                    -> f (StmtSeq b' ret ctx))
                -> StmtSeq b ret args
                -> f (StmtSeq b' ret args)
stmtSeqTermStmt f (ConsStmt l s t) = ConsStmt l s <$> stmtSeqTermStmt f t
stmtSeqTermStmt f (TermStmt p t) = f (p, t)

ppReg :: Ctx.Size ctx -> Doc
ppReg h = text "$" <> int (Ctx.sizeInt h)

nextStmtHeight :: Ctx.Size ctx -> Stmt ctx ctx' -> Ctx.Size ctx'
nextStmtHeight h s =
  case s of
    SetReg{} -> Ctx.incSize h
    CallHandle{} -> Ctx.incSize h
    Print{} -> h
    ReadGlobal{} -> Ctx.incSize h
    WriteGlobal{} -> h
    NewRefCell{} -> Ctx.incSize h
    ReadRefCell{} -> Ctx.incSize h
    WriteRefCell{} -> h
    Assert{} -> h

ppStmt :: Ctx.Size ctx -> Stmt ctx ctx' -> Doc
ppStmt r s =
  case s of
    SetReg _ e -> ppReg r <+> text "=" <+> pretty e
    CallHandle _ h _ args ->
      ppReg r <+> text "= call"
              <+> pretty h <> parens (commas (ppAssignment args))
               <> text ";"
    Print msg -> ppFn "print" [ pretty msg ]
    ReadGlobal v -> text "read" <+> ppReg r <+> pretty v
    WriteGlobal v e -> text "write" <+> pretty v <+> pretty e
    NewRefCell _ e -> ppReg r <+> text "=" <+> ppFn "newref" [ pretty e ]
    ReadRefCell e -> ppReg r <+> text "= !" <> pretty e
    WriteRefCell r1 r2 -> pretty r1 <+> text ":=" <+> pretty r2
    Assert c e -> ppFn "assert" [ pretty c, pretty e]

prefixLineNum :: Bool -> ProgramLoc -> Doc -> Doc
prefixLineNum True pl d = text "%" <+> ppNoFileName (plSourceLoc pl) <$$> d
prefixLineNum False _ d = d

ppStmtSeq :: Bool -> Ctx.Size ctx -> StmtSeq blocks ret ctx -> Doc
ppStmtSeq ppLineNum h (ConsStmt pl s r) =
  prefixLineNum ppLineNum pl (ppStmt h s) <$$>
  ppStmtSeq ppLineNum (nextStmtHeight h s) r
ppStmtSeq ppLineNum _ (TermStmt pl s) =
  prefixLineNum ppLineNum pl (pretty s)


#ifdef UNSAFE_OPS
extendStmtSeq :: Ctx.Diff blocks' blocks -> StmtSeq blocks' ret ctx -> StmtSeq blocks ret ctx
extendStmtSeq _ s = Data.Coerce.coerce s
#else
extendStmtSeq :: Ctx.Diff blocks' blocks -> StmtSeq blocks' ret ctx -> StmtSeq blocks ret ctx
extendStmtSeq diff (ConsStmt p s l) = ConsStmt p s (extendStmtSeq diff l)
extendStmtSeq diff (TermStmt p s) = TermStmt p (extendTermStmt diff s)
#endif


instance Ctx.ApplyEmbedding (StmtSeq blocks ret) where
  applyEmbedding ctxe (ConsStmt loc stmt rest) =
    case applyEmbeddingStmt ctxe stmt of
      Pair stmt' ctxe' -> ConsStmt loc stmt' (Ctx.applyEmbedding ctxe' rest)
  applyEmbedding ctxe (TermStmt loc term) =
    TermStmt loc (Ctx.applyEmbedding ctxe term)



------------------------------------------------------------------------
-- CFGPostdom

type CFGPostdom blocks = Ctx.Assignment (ConstK [Some (BlockID blocks)]) blocks

emptyCFGPostdomInfo :: Ctx.Size blocks -> CFGPostdom blocks
emptyCFGPostdomInfo sz = Ctx.replicate sz (ConstK [])


------------------------------------------------------------------------
-- Block

-- | A basic block within a function.  Note: postdominators are precalculated.
data Block (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType) ctx
   = Block { blockID        :: !(BlockID blocks ctx)
             -- ^ The unique identifier of this block
           , blockInputs    :: !(CtxRepr ctx)
             -- ^ The expected types of the formal arguments to this block
           , _blockStmts    :: !(StmtSeq blocks ret ctx)
             -- ^ The sequence of statements in this block
           }

blockStmts :: Simple Lens (Block b r c) (StmtSeq b r c)
blockStmts = lens _blockStmts (\b s -> b { _blockStmts = s })

-- | Return location of start of block.
blockLoc :: Block blocks ret ctx -> ProgramLoc
blockLoc b = firstStmtLoc (b^.blockStmts)

-- | Get the terminal statement of a basic block.  This is implemented
-- in a CPS style due to the block context.
withBlockTermStmt :: Block blocks ret args
                  -> (forall ctx . ProgramLoc -> TermStmt blocks ret ctx -> r)
                  -> r
withBlockTermStmt b f = getConst (stmtSeqTermStmt (Const . uncurry f) (b^.blockStmts))

nextBlocks :: Block b r a -> [Some (BlockID b)]
nextBlocks b =
  withBlockTermStmt b (\_ s -> fromMaybe [] (termStmtNextBlocks s))


blockInputCount :: Block blocks ret ctx -> Ctx.Size ctx
blockInputCount b = Ctx.size (blockInputs b)

ppBlock :: Bool
           -- ^ Print line numbers.
        -> CFGPostdom blocks
        -> Block blocks ret ctx
           -- ^ Block to print.
        -> Doc
ppBlock ppLineNumbers pda b = do
  let stmts = ppStmtSeq ppLineNumbers (blockInputCount b) (b^.blockStmts)
  let ConstK pd = pda Ctx.! blockIDIndex (blockID b)
  let postdom
        | null pd = text "% no postdom"
        | otherwise = text "% postdom" <+> hsep (viewSome pretty <$> pd)
  pretty (blockID b) <$$> indent 2 (stmts <$$> postdom)

ppBlock' :: Bool
           -- ^ Print line numbers.
          -> Block blocks ret ctx
            -- ^ Block to print.
         -> Doc
ppBlock' ppLineNumbers b = do
  let stmts = ppStmtSeq ppLineNumbers (blockInputCount b) (b^.blockStmts)
  pretty (blockID b) <$$> indent 2 stmts

instance Show (Block blocks ret args) where
  show blk = show $ ppBlock' False blk

instance ShowF (Block blocks ret) where
  showF = show

extendBlock :: Block blocks ret ctx -> Block (blocks ::> new) ret ctx
#ifdef UNSAFE_OPS
extendBlock b = Data.Coerce.coerce b
#else
extendBlock b =
  Block { blockID = extendBlockID (blockID b)
        , blockInputs = blockInputs b
        , _blockStmts = extendStmtSeq Ctx.knownDiff (b^.blockStmts)
        }
#endif

------------------------------------------------------------------------
-- BlockMap

-- | A mapping from block indices to CFG blocks
type BlockMap blocks ret = Ctx.Assignment (Block blocks ret) blocks

getBlock :: BlockID blocks args
         -> BlockMap blocks ret
         -> Block blocks ret args
getBlock (BlockID i) m = m Ctx.! i

extendBlockMap :: Ctx.Assignment (Block blocks ret) b
               -> Ctx.Assignment (Block (blocks ::> args) ret) b
#ifdef UNSAFE_OPS
extendBlockMap = Data.Coerce.coerce
#else
extendBlockMap = fmapFC extendBlock
#endif
------------------------------------------------------------------------
-- CFG

-- | A CFG consists of: a function handle, uniquely identifying the function
--   this CFG implements; a block map, representing the main CFG data structure;
--   the identifier of the function entry point; and the runtime representation
--   of the function return type(s).
data CFG blocks init ret
   = CFG { cfgHandle :: FnHandle init ret
         , cfgBlockMap :: !(BlockMap blocks ret)
         , cfgEntryBlockID :: !(BlockID blocks init)
         }

cfgArgTypes :: CFG blocks init ret -> CtxRepr init
cfgArgTypes g = handleArgTypes (cfgHandle g)

cfgReturnType :: CFG blocks init ret -> TypeRepr ret
cfgReturnType g = handleReturnType (cfgHandle g)

-- | Class for types that embedd a CFG of some sort
class HasSomeCFG f init ret | f -> init, f -> ret where
  getCFG :: f b -> SomeCFG init ret

instance Show (CFG blocks init ret) where
  show g = show (ppCFG True g)

-- | Pretty print CFG
ppCFG :: Bool -- ^ Flag indicates if we should print line numbers
      -> CFG blocks init ret
      -> Doc
ppCFG lineNumbers g = ppCFG' lineNumbers (emptyCFGPostdomInfo sz) g
  where sz = Ctx.size (cfgBlockMap g)

-- | Pretty print CFG with postdom information.
ppCFG' :: Bool -- ^ Flag indicates if we should print line numbers
       -> CFGPostdom blocks
       -> CFG blocks init ret
       -> Doc
ppCFG' lineNumbers pdInfo g = vcat (toListFC (ppBlock lineNumbers pdInfo) (cfgBlockMap g))


-- | Control flow graph with some blocks.
data SomeCFG init ret where
  SomeCFG :: CFG blocks init ret -> SomeCFG init ret

data AnyCFG where
  AnyCFG :: CFG blocks init ret
         -> AnyCFG

-- Force app to be in context.
$(return [])

------------------------------------------------------------------------
-- Pretty printing

ppBaseTermAssignment :: (forall u . f u -> Doc)
                     -> Ctx.Assignment (BaseTerm f) ctx
                     -> Doc
ppBaseTermAssignment pp v = brackets (commas (toListFC (pp . baseTermVal) v))


ppApp :: (forall a . f a -> Doc) -> App f b -> Doc
ppApp = $(U.structuralPretty [t|App|]
          [ ( U.ConType [t|Ctx.Assignment|]
              `U.TypeApp` (U.ConType [t|BaseTerm|] `U.TypeApp` U.DataArg 0)
              `U.TypeApp` U.AnyType
            , [| ppBaseTermAssignment |]
            )
          , ( U.ConType [t|Vector|] `U.TypeApp` U.AnyType
            , [| \pp v -> brackets (commas (fmap pp v)) |]
            )
          ])

instance Pretty (Expr ctx tp) where
  pretty (App a) = ppApp pretty a

------------------------------------------------------------------------
-- TraverseApp (requires TemplateHaskell)

traverseBaseTerm :: Applicative m
                  => (forall tp . f tp -> m (g tp))
                  -> Ctx.Assignment (BaseTerm f) x
                  -> m (Ctx.Assignment (BaseTerm g) x)
traverseBaseTerm f = traverseFC (traverseFC f)

traverseApp :: Applicative m
            => (forall u . f u -> m (g u))
            -> App f tp -> m (App g tp)
traverseApp =
  $(U.structuralTraversal [t|App|]
     [
       ( U.ConType [t|Ctx.Assignment|] `U.TypeApp` (U.DataArg 0) `U.TypeApp` U.AnyType
       , [|traverseFC|]
       )
     , ( U.ConType [t|Ctx.Assignment|]
         `U.TypeApp` (U.ConType [t|BaseTerm|] `U.TypeApp` (U.DataArg 0))
         `U.TypeApp` U.AnyType
       , [| traverseBaseTerm |]
       )
     ])

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

testVector :: TestEquality f => Vector (f tp) -> Vector (f tp) -> Maybe (Int :~: Int)
testVector x y = do
  case V.zipWithM_ testEquality x y of
    Just () -> Just Refl
    Nothing -> Nothing

compareVector :: OrdF f => Vector (f tp) -> Vector (f tp) -> OrderingF Int Int
compareVector x y
    | V.length x < V.length y = LTF
    | V.length x > V.length y = GTF
    | otherwise = V.foldr go EQF (V.zip x y)
  where go :: OrdF f => (f tp, f tp) -> OrderingF Int Int -> OrderingF Int Int
        go (u,v) r =
          case compareF u v of
            LTF -> LTF
            GTF -> GTF
            EQF -> r

instance TestEquality f => TestEquality (App f) where
  testEquality = $(U.structuralTypeEquality [t|App|]
                   [ (U.DataArg 0                   `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|NatRepr |]       `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|SymbolRepr |]    `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|TypeRepr|]       `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|BaseTypeRepr|]  `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|TypeableValue|]  `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|Ctx.Assignment|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType
                     , [| testEquality |]
                     )
                   , (U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType
                     , [| testEquality |]
                     )
                   , (U.ConType [t|Ctx.Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEquality|])
                   , (U.ConType [t|FnHandle|]  `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testFnHandle|])
                   , (U.ConType [t|Vector|]    `U.TypeApp` U.AnyType, [|testVector|])
                   ]
                  )

instance OrdF f => OrdF (App f) where
  compareF = $(U.structuralTypeOrd [t|App|]
                   [ (U.DataArg 0            `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|NatRepr |] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|SymbolRepr |] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|BaseTypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|TypeableValue|] `U.TypeApp` U.AnyType, [|compareF|])
                   , ( U.ConType [t|Ctx.Assignment|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType
                     , [| compareF |]
                     )
                   , ( U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType
                     , [| compareF |]
                     )
                   , (U.ConType [t|Ctx.Index|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareF|])
                   , (U.ConType [t|FnHandle|]  `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareFnHandle|])
                   , (U.ConType [t|Vector|]    `U.TypeApp` U.AnyType, [|compareVector|])
                   ]
                  )

{-
instance OrdF f => OrdF (App f) where
  compareF = $(structuralTypeOrd [t|App|]
                 [ TypeApp (DataArg 0)            U.AnyType
                 ]
              )
-}

instance FunctorFC App where
  fmapFC = fmapFCDefault

instance FoldableFC App where
  foldMapFC = foldMapFCDefault

instance TraversableFC App where
  traverseFC = traverseApp

-- | Fold over an app.
foldApp :: (forall x . f x -> r -> r)
        -> r
        -> App f tp
        -> r
foldApp f0 r0 a = execState (traverseApp (go f0) a) r0
  where go f v = v <$ modify (f v)

mapApp :: (forall u . f u -> g u) -> App f tp -> App g tp
mapApp f a = runIdentity (traverseApp (pure . f) a)


instance Ctx.ApplyEmbedding' Expr where
  applyEmbedding' ctxe (App e) = App (mapApp (Ctx.applyEmbedding' ctxe) e)

instance Ctx.ExtendContext' Expr where
  extendContext' diff (App e) = App (mapApp (Ctx.extendContext' diff) e)
