-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.MatlabValue
-- Description      : Defines a symbolic representation of Matlab simulator values.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
--  Defines a symbolic representation of Matlab simulator values.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.Simulator.MatlabValue
  ( -- * Value type
    Value(..)
  , intValue
  , uintValue
  , valueClass
  , valueDim
  , matlabValueClass
    -- * Objects
  , MatlabObject(..)
  , MatlabObjectArray(..)
  , setObjectProperty
    -- * MatlabHandleInfo
  , MatlabFnVal
  , MatlabHandleInfo(..)
    -- * StructArray
  , MatlabStructArray(..)
  , setStructField
    -- * SomeBVArray
  , SomeBVArray(..)
    -- * Convenience constructors.
  , trueValue
  , falseValue
  , emptyDoubleValue
  , singleReal
  , singleStruct
  , singleHandle
  , boolValue
  , charVectorValue
  , stringValue
    -- * View functions.
  , asRealArray
  , CharArray
  , asCharArray
  , asCharVector
  , asHandle
    -- * Recognizers
  , isRealArray
  , isCharArray
  , isLogicArray
  , isCellArray
  , isStructArray
  , isHandle
    -- * Argument parsing functions.
  , valueAsDim
  , valuesAsDim
  , valueAsSymDim
  , valuesAsSymDim
    -- * Logical operations.
  , structValue
    -- * Pretty printing
  , CanPrintExpr
  , ppPred
  , ppCplx
  , ppSignedBV
  , ppUnsignedBV
  , ppValue
  , ppShortValue
    -- * Utilities
  , conversionErrorMsg
  , cplxArrayValuesAreReal
  , symIntegerArrayToMatlab
  , complexRealAsChar
  , integerAsChar
  , valueDimAsRowVector
  , valueDimN
  , valueDimAt
  , valueDimIsEmpty
  , valueDimIsScalar
  , valueDimIsVector
  , valueDimIs2d
  , valueDimLength
  , valueConcreteDim
  -- * Matlab type represntations
  , MatlabStructVal(..)
  , iteValue
  , matlabStructMuxFn
  , structArrayMuxFn
  , muxMatlabHandle
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Maybe
import           Data.Proxy
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word as Word (Word16)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.MATLAB.CharVector as CV
import           Lang.MATLAB.MultiDimArray (ArrayDim, MultiDimArray)
import qualified Lang.MATLAB.MultiDimArray as MDA
import           Lang.MATLAB.Utils.Nat as Nat
import           Lang.MATLAB.Utils.PrettyPrint

import           Lang.Crucible.MATLAB.Intrinsics.Solver
import           Lang.Crucible.MATLAB.Types
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
  ( SomeBVArray(..)
  , SomeSymbolicBVArray(..)
  , FnVal
  , muxReg
  , muxHandle
  , mdaMuxFn
  , RegValue
  , ValMuxFn
  )
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.Complex
import qualified Lang.Crucible.Utils.SymMultiDimArray as SMDA


------------------------------------------------------------------------
-- Utilities

-- | Error message when converting from one type to another.
conversionErrorMsg :: String -> String -> String
conversionErrorMsg s d =
  "The following error occurred converting from " ++ s ++ " to " ++ d ++ ":\n"

------------------------------------------------------------------------
-- Value

type CharArray = MultiDimArray Word16

-- | A MATLAB value in the simulator.
data Value sym
   = RealArray     !(MultiDimArray (SymCplx sym))
   | SymCplxArray  !(SMDA.SymMultiDimArray (SymExpr sym) BaseComplexType)
   | SymRealArray  !(SMDA.SymMultiDimArray (SymExpr sym) BaseRealType)
   | IntArray      !(SomeBVArray (SymExpr sym))
   | SymIntArray   !(SomeSymbolicBVArray (SymExpr sym))
   | UIntArray     !(SomeBVArray (SymExpr sym))
   | SymUIntArray  !(SomeSymbolicBVArray (SymExpr sym))
   | LogicArray    !(MultiDimArray (Pred sym))
   | SymLogicArray !(SMDA.SymMultiDimArray (SymExpr sym) BaseBoolType)
   | CharArray     !CharArray
   | CellArray     !(MultiDimArray (Value sym))

   | FunctionHandle !(MatlabHandleInfo sym)
     -- ^ @FunctionHandle r c nm@ is an array of function
     -- handles the values must be constant and refer to nm.
   | MatlabStructArray {-# UNPACK #-} !(MatlabStructArray sym)
   | MatlabObjectArray {-# UNPACK #-} !(MatlabObjectArray sym)

intValue :: (1 <= n) => NatRepr n -> MultiDimArray (SymBV sym n) -> Value sym
intValue w a = IntArray $ SomeBVArray w a

uintValue :: (1 <= n) => NatRepr n -> MultiDimArray (SymBV sym n) -> Value sym
uintValue w a = UIntArray $ SomeBVArray w a

type MatlabFnVal sym = FnVal sym MatlabFunctionBaseArgs MatlabFunctionReturnType

-- | Tuple containing a Matlab handle, and information needed for
-- queries about handle.
data MatlabHandleInfo sym
   = MatlabHandleInfo { handleFnVal :: !(MatlabFnVal sym)
                        -- ^ Underlying handle
                      , handleIsBuiltin :: !(Pred sym)
                        -- ^ Whether this handle corresponds to a builtin function
                      , firstReturnValue :: !Text
                        -- ^ Name of first return value
                      , handleNargin :: !(SymInteger sym)
                        -- ^ nargin for handle.
                      }

instance Show (MatlabHandleInfo sym) where
  show = show . handleFnVal

-- | Returns type of value as a string for printing purposes.
valueClass :: Value sym -> String
valueClass (RealArray _)      = "double"
valueClass (IntArray  (SomeBVArray w _))  = "int"  ++ show w
valueClass (UIntArray (SomeBVArray w _)) = "uint" ++ show w
valueClass (LogicArray _)     = "logical"
valueClass (CharArray _)      = "char"
valueClass (CellArray _)      = "cell"
valueClass (MatlabStructArray _)    = "struct"
valueClass (FunctionHandle _) = "function_handle"
valueClass (SymLogicArray _) = "logical (symbolic)"
valueClass (SymRealArray _) = "real (symbolic)"
valueClass (SymCplxArray _) = "complex (symbolic)"
valueClass (SymIntArray (SomeSymbolicBVArray w _)) = "int" ++ show w ++ " (symbolic)"
valueClass (SymUIntArray (SomeSymbolicBVArray w _)) = "uint" ++ show w ++ " (symbolic)"
valueClass (MatlabObjectArray (MkMatlabObjectArray nm _)) = Text.unpack nm

-- | Returns type of value as a string for printing purposes.
-- This different from valueClass in that it uses the standard Matlab name for classes.
matlabValueClass :: Value sym -> String
matlabValueClass (RealArray _)      = "double"
matlabValueClass (IntArray  (SomeBVArray w _))  = "int"  ++ show w
matlabValueClass (UIntArray (SomeBVArray w _)) = "uint" ++ show w
matlabValueClass (LogicArray _)     = "logical"
matlabValueClass (CharArray _)      = "char"
matlabValueClass (CellArray _)      = "cell"
matlabValueClass (MatlabStructArray _)    = "struct"
matlabValueClass (FunctionHandle _) = "function_handle"
matlabValueClass (SymLogicArray _) = "logical"
matlabValueClass (SymRealArray _) = "double"
matlabValueClass (SymCplxArray _) = "double"
matlabValueClass (SymIntArray (SomeSymbolicBVArray w _)) = "int" ++ show w
matlabValueClass (SymUIntArray (SomeSymbolicBVArray w _)) = "uint" ++ show w
matlabValueClass (MatlabObjectArray (MkMatlabObjectArray nm _)) = Text.unpack nm

-- | Compute value dimension as concrete or symbolic
valueDim :: forall sym
          . Value sym
         -> Either MDA.ArrayDim (SMDA.NonEmptyAssignment (SMDA.NatExpr (SymExpr sym)))
valueDim v0 = do
  let concreteDim :: MDA.HasDim a => a -> Either MDA.ArrayDim r
      concreteDim a = Left $! MDA.dim a
  case v0 of
    RealArray  v        -> concreteDim v
    IntArray  v         -> concreteDim v
    UIntArray  v        -> concreteDim v
    LogicArray  v       -> concreteDim v
    CharArray  v        -> concreteDim v
    CellArray  v        -> concreteDim v
    MatlabStructArray v -> concreteDim v
    MatlabObjectArray v -> concreteDim v
    FunctionHandle _    -> concreteDim (MDA.matrixDim 1 1)
    SymLogicArray a     -> Right $! SMDA.dim a
    SymCplxArray a      -> Right $! SMDA.dim a
    SymRealArray a      -> Right $! SMDA.dim a
    SymIntArray  (SomeSymbolicBVArray _ a) -> Right $! SMDA.dim a
    SymUIntArray (SomeSymbolicBVArray _ a) -> Right $! SMDA.dim a

valueConcreteDim :: Value sym -> Maybe MDA.ArrayDim
valueConcreteDim v =
  case valueDim v of
    Left d -> Just d
    Right _ -> Nothing

-- | Pretty print dimensions of value.
ppValueDim :: IsExpr (SymExpr sym) => Value sym -> Doc
ppValueDim v =
  case valueDim v of
    Left d -> MDA.ppDim d
    Right d ->
        encloseSep PP.empty PP.empty (text "*") (pp <$> index_list)
      where sd = SMDA.symDimToVector d
            -- Get indices of dimensions (minimum of 2).
            index_list = [1..max (V.length sd) 2]
            -- Print the dimension at index i
            pp i =
              case sd V.!? (i-1) of
                Nothing -> text "1"
                Just n -> text $! maybe "?" show (asNat n)

-- | If-then-else applied to natural numbers.
natIteM :: IsExprBuilder sym
        => sym -> Pred sym -> IO (SymNat sym) -> IO (SymNat sym) -> IO (SymNat sym)
natIteM sym c mx my =
  case asConstantPred c of
    Nothing -> join $ natIte sym c <$> mx <*> my
    Just True  -> mx
    Just False -> my

-- | Given a vector of natural numbers, this drops trailing 1 values from the
-- vector and returns the resulting number of elements.
symDimLen :: IsExprBuilder sym => sym -> V.Vector (SymNat sym) -> IO (SymNat sym)
symDimLen sym v
  | V.length v <= 2 = natLit sym 2
  | otherwise = do
      p <- natEq sym (V.last v) =<< natLit sym 1
      let n = fromIntegral (V.length v)
      natIteM sym p (symDimLen sym (V.init v)) (natLit sym n)

-- | This returns the dimensions of a value as a vector of natural numbers.
--
-- Indices after the list are assumed to be 1.
valueDimAsRowVector :: IsSymInterface sym
                    => sym -> Value sym -> IO (Value sym)
valueDimAsRowVector sym v =
  case valueDim v of
    Left d -> do
      len_vec <- traverse (mkReal sym) (V.fromList (MDA.asDimList d))
      return $ RealArray (MDA.rowVector len_vec)
    Right d -> do
      let nat_vec = SMDA.symDimToVector d
      len <- symDimLen sym nat_vec
      int_vec <- traverse (integerToReal sym <=< natToInteger sym) nat_vec
      -- Get default value for other entries in array.
      def_value <- realLit sym 1
      SymRealArray <$> SMDA.rowVector sym len int_vec def_value


symIntegerArrayToMatlab :: MatlabSymbolicArrayBuilder sym
                        => sym
                        -> SMDA.SymMultiDimArray (SymExpr sym) BaseIntegerType
                        -> IO (Value sym)
symIntegerArrayToMatlab sym a = do
  f <- mkMatlabSolverFn sym IntegerToRealFn
  SymRealArray <$> SMDA.map sym f a

-- | This returns the dimensions of a value as a vector of natural numbers
-- with the given length.
--
-- Indices after the list are assumed to be 1.
valueDimN :: IsSymInterface sym
          => sym -> Value sym -> Nat -> IO (V.Vector (SymNat sym))
valueDimN sym val n =
  case valueDim val of
    Left  d -> traverse (natLit sym) (V.fromList (MDA.asDimListN n d))
    Right d -> SMDA.mkSymDimN sym n d

-- | Return true if any of the values in the foldable are true.
predAny :: (Foldable t, IsBoolExprBuilder sym, IsPred (Pred sym))
        => sym -> t (IO (Pred sym)) -> IO (Pred sym)
predAny sym v = foldlM f (falsePred sym) v
  where f b m = do
          case asConstantPred b of
            Just True -> return $! truePred sym
            Just False -> m
            Nothing -> orPred sym b =<< m

-- | Return true if any of the values in the foldable are true.
predAll :: (Foldable t, IsBoolExprBuilder sym, IsPred (Pred sym))
        => sym -> t (IO (Pred sym)) -> IO (Pred sym)
predAll sym v = foldlM f (truePred sym) v
  where f b m = do
          case asConstantPred b of
            Just True -> m
            Just False -> return $! falsePred sym
            Nothing -> andPred sym b =<< m

-- | Return maximum natural number.
natMax :: IsExprBuilder sym => sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)
natMax sym x y = do
  p <- natLe sym x y
  natIte sym  p y x

-- | Return maximum natural number.
natMaximum :: (Foldable t, IsExprBuilder sym) => sym -> t (SymNat sym) -> IO (SymNat sym)
natMaximum sym t = do
  z <- natLit sym 0
  foldlM (natMax sym) z t

symDimIsEmpty :: IsExprBuilder sym => sym -> V.Vector (SymNat sym) -> IO (Pred sym)
symDimIsEmpty sym v = do
  z <- natLit sym 0
  predAny sym (natEq sym z <$> v)

-- | This returns 0 if the value is empty, or the length of the
-- longest dimension otherwise.
valueDimLength :: IsExprBuilder sym => sym -> Value sym -> IO (SymNat sym)
valueDimLength sym val =
  case valueDim val of
    Left d -> do
      let l = MDA.asDimList d
      -- Length is zero if any dimension is zero, and the length of
      -- the maximum dimension otherwise.
      let result | any (== 0) l = 0
                 | otherwise = maximum l
      natLit sym result
    Right d -> do
      let v = SMDA.symDimToVector d
      p <- symDimIsEmpty sym v
      natIteM sym p (natLit sym 0) (natMaximum sym v)

-- | Return predicate indicating if value if empty.
valueDimIsEmpty :: IsExprBuilder sym => sym -> Value sym -> IO (Pred sym)
valueDimIsEmpty sym val =
  case valueDim val of
    Left d -> return $! backendPred sym (MDA.null d)
    Right d -> symDimIsEmpty sym (SMDA.symDimToVector d)

symDimIsScalar :: IsExprBuilder sym => sym -> V.Vector (SymNat sym) -> IO (Pred sym)
symDimIsScalar sym v = do
  one <- natLit sym 1
  predAll sym (natEq sym one <$> v)

-- | Return predicate indicating if value is a scalar.
valueDimIsScalar :: IsExprBuilder sym => sym -> Value sym -> IO (Pred sym)
valueDimIsScalar sym val =
  case valueDim val of
    Left d -> return $! backendPred sym (MDA.isSingleton d)
    Right d -> symDimIsScalar sym (SMDA.symDimToVector d)

symDimAt :: IsExprBuilder sym => sym -> V.Vector (SymNat sym) -> Nat -> IO (SymNat sym)
symDimAt sym v n =
  case v V.!? fromIntegral n of
    Just r -> return r
    Nothing -> natLit sym 1

-- | Return number of dimensions at given position.
valueDimAt :: IsExprBuilder sym => sym -> Value sym -> Nat -> IO (SymNat sym)
valueDimAt sym val n =
  case valueDim val of
    Left d -> natLit sym (MDA.dimAt d n)
    Right d -> symDimAt sym (SMDA.symDimToVector d) n

-- | Return true if dimensions have form (x*1) or (1*x)
valueDimIsVector :: IsExprBuilder sym => sym -> Value sym -> IO (Pred sym)
valueDimIsVector sym val =
  case valueDim val of
    Left d -> return $! backendPred sym (MDA.isVector d)
    Right d -> do
      let v = SMDA.symDimToVector d
      one <- natLit sym 1
      r1 <- natEq sym one =<< symDimAt sym v 0
      c1 <- natEq sym one =<< symDimAt sym v 1
      p0 <- orPred sym r1 c1
      p1 <- symDimIsScalar sym (V.drop 2 v)
      andPred sym p0 p1

-- | Return true if dimensions have form (x*1) or (1*x)
valueDimIs2d :: IsExprBuilder sym => sym -> Value sym -> IO (Pred sym)
valueDimIs2d sym val =
  case valueDim val of
    Left d -> return $! backendPred sym (MDA.is2d d)
    Right d -> do
      let v = SMDA.symDimToVector d
      symDimIsScalar sym (V.drop 2 v)

------------------------------------------------------------------------
-- Convenience constructors.

trueValue :: IsBoolExprBuilder sym => sym -> Value sym
trueValue  solver = LogicArray $ MDA.singleton $ truePred solver

falseValue :: IsBoolExprBuilder sym => sym -> Value sym
falseValue solver = LogicArray $ MDA.singleton $ falsePred solver

emptyDoubleValue :: Value sym
emptyDoubleValue = RealArray MDA.empty

singleReal :: SymCplx sym -> Value sym
singleReal = RealArray . MDA.singleton

singleStruct :: [(Text, Value sym)] -> Value sym
singleStruct pairs = MatlabStructArray (StructArr flds (MDA.singleton vals))
  where (flds,vals) = V.unzip (V.fromList pairs)

singleHandle :: MatlabHandleInfo sym
             -> Value sym
singleHandle = FunctionHandle

-- | Create a value from a single Boolean.
boolValue ::  IsBoolExprBuilder sym => sym -> Bool -> Value sym
boolValue solver b = LogicArray $ MDA.singleton $! backendPred solver b

charVectorValue :: CV.CharVector -> Value sym
charVectorValue v = CharArray $ MDA.rowVector $ CV.toVector v

stringValue :: String -> Value sym
stringValue = charVectorValue . CV.fromString

instance IsString (Value sym) where
  fromString = stringValue

------------------------------------------------------------------------
-- StructArray

data MatlabStructArray sym
   = StructArr { structFields :: !(V.Vector Text) -- ^ Names of fields.
               , structValues :: !(MultiDimArray (V.Vector (Value sym)))
               }

instance MDA.HasDim (MatlabStructArray sym) where
  dim a = MDA.dim (structValues a)


-- | Update struct array and return new value.
setStructField :: Monad m
               => MatlabStructArray val -- ^ Struct value
               -> MDA.Index -- ^ Index of struct to assign.
               -> Text      -- ^ Name of field to assign.
               -> Value val -- ^ Value to assign
               -> m (MatlabStructArray val)
setStructField (StructArr nms a) a_idx f v = do
  -- Get number of fields.
  let field_count = V.length nms
  -- Check to see if field is defined.
  case V.elemIndex f nms of
    -- If field is defined, set index.
    Just idx -> assert (idx < V.length fl) $
        case MDA.set a dfl a_idx new_fl of
          Just a' ->
            return $! StructArr nms a'
          Nothing ->
            fail $ "In assignments with a single index, the array cannot be resized."
      where -- Get default value of fields at new index.
            dfl = V.replicate field_count emptyDoubleValue
            -- Get current value of field at index.
            fl = fromMaybe dfl (a MDA.!? a_idx)
            -- Update field value.
            new_fl = fl V.// [(idx,v)]
    -- If field is not defined, create new index for storing it.
    Nothing ->
      case MDA.set new_a dfl a_idx new_fl of
        Just a' ->
          return $! StructArr new_nms a'
        Nothing ->
          fail $ "In assignments with a single index, the array cannot be resized."
      where -- Get new names of fields
            new_nms = nms `V.snoc` f
            -- Get default value of fields at new index.
            dfl = V.replicate (field_count + 1) emptyDoubleValue
            -- Extend all previous fields with new field entry.
            new_a = (`V.snoc` emptyDoubleValue) <$> a
            -- Get current value of field at index.
            fl = fromMaybe (V.replicate field_count emptyDoubleValue) (a MDA.!? a_idx)
            -- Get new field value.
            new_fl = fl `V.snoc` v

------------------------------------------------------------------------
-- View functions

asRealArray :: Monad m => Value sym -> m (MultiDimArray (SymCplx sym))
asRealArray (RealArray a) = return a
asRealArray _ = fail "Expected real array"

asCharArray :: Monad m => Value sym -> m CharArray
asCharArray (CharArray a) = return a
asCharArray _ = fail $ "Expected character array"

asCharVector :: Monad m => Value sym -> m CharVector
asCharVector v = (CV.fromVector . MDA.mdVec) `liftM` asCharArray v

-- | Attempt to parse a value as a function.
asHandle :: Monad m
         => Value sym
         -> m (MatlabHandleInfo sym)
asHandle (FunctionHandle nm) = return nm
asHandle v = fail $ "Expected function handle instead of " ++ valueClass v ++ "."

------------------------------------------------------------------------
-- Recognizers

isRealArray :: Value sym -> Bool
isRealArray RealArray{} = True
isRealArray SymCplxArray{} = True
isRealArray _ = False

isCharArray :: Value sym -> Bool
isCharArray CharArray{} = True
isCharArray _ = False

isLogicArray :: Value sym -> Bool
isLogicArray LogicArray{} = True
isLogicArray SymLogicArray{} = True
isLogicArray _ = False

isCellArray :: Value sym -> Bool
isCellArray CellArray{} = True
isCellArray _ = False

isStructArray :: Value sym -> Bool
isStructArray MatlabStructArray{} = True
isStructArray _ = False

isHandle :: Value sym -> Bool
isHandle FunctionHandle{} = True
isHandle _ = False

------------------------------------------------------------------------
-- Coercion functions

-- | Returns predicate checking that all complex array predicates are real.
cplxArrayValuesAreReal :: (IsExprBuilder sym)
                       => sym
                       -> MultiDimArray (SymCplx sym)
                       -> IO (Pred sym)
cplxArrayValuesAreReal sb a = do
  eqs <- traverse (isReal sb) a
  andAllOf sb folded eqs

integerAsChar :: Integer -> Word16
integerAsChar i = fromInteger ((i `max` 0) `min` (2^(16::Int)-1))

complexRealAsChar :: (Monad m, IsExpr val)
                  => val BaseComplexType
                  -> m Word16
complexRealAsChar v = do
  case cplxExprAsRational v of
    -- Check number is printable.
    Just r | otherwise -> return (integerAsChar (floor r))
    Nothing -> fail "Symbolic value cannot be interpreted as a character."

------------------------------------------------------------------------
-- Parse functions.

valAsRA :: Monad m => Value sym -> m (MultiDimArray (SymCplx sym))
valAsRA (RealArray a) = return a
valAsRA _ = fail "Dimensions should be numeric scalar values."

-- | Interpret the value as a list of dimensions of an array.
valueAsDim :: (Monad m, IsExpr (SymExpr sym))
           => Value sym
           -> m ArrayDim
valueAsDim a0 = do
  a <- valAsRA a0
  r <- mapM cplxExprAsNat (toList a)
  return $ case r of
             [c] -> MDA.matrixDim c c
             _   -> MDA.fromDimList r

-- | Interpret a vector of values as defining dimensions of an array.
valuesAsDim :: (Monad m, IsExpr (SymExpr sym))
            => V.Vector (Value sym)
            -> m ArrayDim
valuesAsDim value_vec =
  case V.toList value_vec of
    [] -> return MDA.singletonDim
    [a0] -> valueAsDim a0
    l -> do
      let valAsDim v0 = do
            a <- valAsRA v0
            v <- case MDA.asSingleton a of
                   Just v -> return v
                   Nothing -> fail "Dimensions should be numeric scalar values."
            cplxExprAsNat v
      r <- mapM valAsDim l
      return $
        case r of
        [c] -> MDA.matrixDim c c
        _   -> MDA.fromDimList r

checkedCplxToNat :: (IsBoolSolver sym, IsExprBuilder sym)
                 => sym -> SymCplx sym -> IO (SymNat sym)
checkedCplxToNat sym v = do
  (r :+ i) <- cplxGetParts sym v
  let msg = "Dimensions should be non-negative integers."
  let z = realZero sym
  addAssertionM sym (realEq    sym i z) msg
  addAssertionM sym (isInteger sym r)   msg
  addAssertionM sym (realLe    sym z r) msg
  integerToNat sym =<< realToInteger sym r

-- | Interpret the value as a list of dimensions of an array.
--
-- We ensure the vector has at least two elements.  This may fail if the vector cannot
-- be interpreted as a row vector of natural numbers.
valueAsSymDim :: (IsBoolSolver sym, IsExprBuilder sym)
              => sym
              -> Value sym
              -> IO (V.Vector (SymNat sym))
valueAsSymDim sym a0 = do
  a <- valAsRA a0
  r <- mapM (checkedCplxToNat sym) a
  when (MDA.isRowVector r == False || MDA.null r) $ do
    fail "Expected dimensions to be a non-empty row vector."
  let v = MDA.mdVec r
  return $
    case () of
      -- If r has a single element 'e', then return the square dimensions 'e x e'
      _ | V.length v == 1 -> v V.++ v
        | otherwise -> v

-- | Interpret a vector of values as defining dimensions of a multidimensional array.
--
-- We ensure the vector has at least two elements.  This may fail if the vector cannot
-- be interpreted as a row vector of natural numbers.
valuesAsSymDim :: forall sym
               .  (IsExprBuilder sym, IsBoolSolver sym)
               => sym
               -> V.Vector (Value sym)
               -> IO (V.Vector (SymNat sym))
valuesAsSymDim sym value_vec
  | V.length value_vec == 0 = do
    one <- natLit sym 1
    return $! V.fromList [ one, one ]
  | V.length value_vec == 1 = do
    valueAsSymDim sym (value_vec V.! 0)
  | otherwise = mapM valAsDim value_vec
 where valAsDim :: Value sym -> IO (SymNat sym)
       valAsDim v0 = do
         a <- valAsRA v0
         case MDA.asSingleton a of
           Just v -> checkedCplxToNat sym v
           Nothing -> fail "Dimensions should be numeric scalar values."

------------------------------------------------------------------------
-- Operations

-- | Get value of specified field in struct.
structValue :: Monad m => MatlabStructArray sym -> Text -> m (Value sym)
structValue a f
  | Just v <- MDA.asSingleton (structValues a) = do
    case V.elemIndex f (structFields a) of
      Just idx -> assert (idx < V.length v) $ do
        return (v V.! idx)
      Nothing -> fail $ "Unknown field " ++ show f ++ " in structure."
  | MDA.null (structValues a) =
      fail "Structure field reference is illegal when structure is empty."
  | otherwise =
      fail "Structure field reference is illegal when structure contains multiple elements."

------------------------------------------------------------------------
-- Pretty printing utilities.

type CanPrintExpr sym =
    ( IsExpr (SymExpr sym)
    , Show (RegValue sym MatlabFunctionHandleType)
    )

-- | Pretty print a predicate value.
ppPred :: IsPred v => v -> String
ppPred v =
  case asConstantPred v of
    Just True  -> "1"
    Just False -> "0"
    Nothing -> "??"

-- | Pretty print a real value.
ppCplx :: IsExpr e => e BaseComplexType -> String
ppCplx v =
  case asComplex v of
    Just r  -> ppComplexFrac r
    Nothing -> "??"

ppUnsignedBV :: IsExpr val => NatRepr w -> val (BaseBVType w) -> String
ppUnsignedBV _ v =
  case asUnsignedBV v of
    Just i  -> show i
    Nothing -> "??"

ppSignedBV :: (IsExpr val, 1 <= w) => NatRepr w -> val (BaseBVType w) -> String
ppSignedBV _ v =
  case asSignedBV v of
    Just i  -> show i
    Nothing -> "??"

-- | Print a complex number using the same rules as Matlab.
ppComplexFrac :: RealFrac a => Complex a -> String
ppComplexFrac (d :+ i)
    | i == 0    = sd
    | d == 0    = si
    | otherwise = sd ++ " + " ++ si
  where sd = ppFrac d
        si = ppFrac i ++ "i"

-- | Pretty print an object array
--
-- Examples:
--
--
ppObjectArray :: CanPrintExpr sym
              => (MatlabObjectArray sym) -> Doc
ppObjectArray a@(MkMatlabObjectArray nm vs)
    | MDA.null vs = text "empty" <+> text (Text.unpack nm)
        <+>     text " object array"
    | Just _ <- MDA.asSingleton vs = text (Text.unpack nm)
        <+>     propText
        PP.<$$> PP.indent 2 (PP.vcat propvals)
    | otherwise = ppValueDim (MatlabObjectArray a)
        <+>     text (Text.unpack nm)
        <+>     text "object array"
        <+>     propText
        PP.<$$> PP.indent 2 (PP.vcat proponly)
  where
    -- first element of MDA; only eval'd in the dimSize >= 1 cases above!
    o   = maybe err id (MDA.mdVec vs V.!? 0)
    pn  = V.toList $ objPropNames o
    pv  = V.toList $ objPropVals  o
    propText = text "with "
               <> (if null pn then text "no " else PP.empty)
               <>  text "properties"
    err = error "impossible: MultiDimArray with size >= 1 has no first element"
    proponly = map (pretty . show) pn
    propvals = [ pretty (Text.unpack p) <> text ": " <> ppShortValue v |
                 (p,v) <- zip pn pv ]


-- | Pretty print an assignment of a value to a variable.
ppValue :: CanPrintExpr sym
        => String     -- ^ Name of variable
        -> Value sym  -- ^ Value to print
        -> Doc
ppValue nm v0 =
  case v0 of
    RealArray a   -> MDA.ppVector nm ppCplx a
    IntArray  (SomeBVArray w a) -> MDA.ppVector nm (ppSignedBV w)  a
    UIntArray (SomeBVArray w a) -> MDA.ppVector nm (ppUnsignedBV w) a
    CharArray a   -> MDA.pp2d ppChar nm a
      where ppv = text . show . CV.fromVector
            ppChar m = vcat $ ppv <$> V.toList (MDA.asRows m)
    LogicArray a -> MDA.ppVector nm ppPred a
    CellArray a ->
      MDA.ppVector nm (\v -> show (ppShortValue v)) a
    SymLogicArray _   -> ppNameEqual nm $ text "??"
    SymRealArray _    -> ppNameEqual nm $ text "??"
    SymCplxArray _    -> ppNameEqual nm $ text "??"
    SymIntArray _     -> ppNameEqual nm $ text "??"
    SymUIntArray _    -> ppNameEqual nm $ text "??"

    MatlabStructArray (StructArr flds a) ->
      let d | V.null flds
            , Just{} <- MDA.asSingleton a =
              text "struct with no fields."
            | Just vals <- MDA.asSingleton a =
              let flds' = padLengths $ V.toList $ (\f -> Text.unpack f ++ ":") <$> flds
               in vcat $ zipWith (\f v -> text f <+> ppShortValue v) flds' (V.toList vals)
            | otherwise = MDA.ppDim (MDA.dim a) <+> text "struct"
       in ppNameEqual nm $ d
    FunctionHandle fnm ->
      ppNameEqual nm $ (char '@' <> text (show fnm))
    MatlabObjectArray a -> ppNameEqual nm (ppObjectArray a)

ppRowVector :: V.Vector String -> Doc
ppRowVector v
  | V.length v == 1 = text (v V.! 0)
  | otherwise =  brackets $ hsep $ text <$> V.toList v

ppShortValue :: CanPrintExpr sym
             => Value sym
             -> Doc
ppShortValue v =
  case v of
    RealArray a
      | Just r <- MDA.asRowVector a -> ppRowVector $ ppCplx <$> r
    IntArray (SomeBVArray w a)
      | Just r <- MDA.asRowVector a ->
        ppRowVector $ (ppSignedBV w)  <$> r
    UIntArray (SomeBVArray w a)
      | Just r <- MDA.asRowVector a ->
        ppRowVector $ (ppUnsignedBV w) <$> r
    CharArray a
      | Just r <- MDA.asRowVector a -> text (show (CV.fromVector r))
    LogicArray a
      | Just r <- MDA.asRowVector a -> ppRowVector $ ppPred <$> r
    FunctionHandle fnm -> char '@' <> ppShow fnm
    CellArray a
      | MDA.null a -> text "{}"
      | Just e <- MDA.asSingleton a -> lbrace <+> ppShortValue e <+> rbrace
    _ -> ppValueDim v <+> text (valueClass v)

------------------------------------------------------------------------
-- IntrinsicClass instance for MatlabHandle
--   A type of matlab function handles.  These consists of a bare funcion handle
--   as well as some additional metadata about the function.

instance IsExprBuilder sym => IntrinsicClass sym "MatlabHandle" where
  type Intrinsic sym "MatlabHandle" = MatlabHandleInfo sym
  muxIntrinsic sym _ = muxMatlabHandle sym

{-# INLINE muxMatlabHandle #-}
muxMatlabHandle :: IsExprBuilder sym
                => sym
                -> Pred sym
                -> MatlabHandleInfo sym
                -> MatlabHandleInfo sym
                -> IO (MatlabHandleInfo sym)
muxMatlabHandle s = \c x y ->
  if firstReturnValue x == firstReturnValue y then do
      h <- muxHandle s c (handleFnVal x) (handleFnVal y)
      return MatlabHandleInfo { handleFnVal = h
                              , handleIsBuiltin = handleIsBuiltin x
                              , firstReturnValue = firstReturnValue x
                              , handleNargin = handleNargin x
                              }
  else
    fail "Cannot merge handles with distinct types."


------------------------------------------------------------------------
-- RegValue instance for Value

instance MatlabSymbolicArrayBuilder sym => IntrinsicClass sym "MatlabValue" where

  type Intrinsic sym "MatlabValue" = Value sym
  muxIntrinsic sym _ = iteValue sym


-- | Ite two values together.
{-# INLINE iteValue #-}
iteValue :: MatlabSymbolicArrayBuilder sym
         => sym
         -> Pred sym
         -> Value sym
         -> Value sym
         -> IO (Value sym)

-- Ite value for all real cases.
iteValue s c   (RealArray x) (RealArray y) =
  RealArray <$> muxReg s (Proxy :: Proxy (MultiDimArrayType ComplexRealType)) c x y
iteValue sym c (RealArray x) (SymCplxArray y) = do
  x' <- SMDA.internalizeArray sym knownRepr x
  SymCplxArray <$> SMDA.muxArray sym c x' y
iteValue sym c (RealArray x) (SymRealArray y) = do
  x' <- SMDA.internalizeArray sym knownRepr x
  f <- mkMatlabSolverFn sym RealToComplexFn
  y' <- SMDA.map sym f y
  SymCplxArray <$> SMDA.muxArray sym c x' y'
iteValue sym c (SymCplxArray x) (RealArray y) = do
  y' <- SMDA.internalizeArray sym knownRepr y
  SymCplxArray <$> SMDA.muxArray sym c x y'
iteValue sym c (SymRealArray x) (RealArray y) = do
  f <- mkMatlabSolverFn sym RealToComplexFn
  x' <- SMDA.map sym f x
  y' <- SMDA.internalizeArray sym knownRepr y
  SymCplxArray <$> SMDA.muxArray sym c x' y'
iteValue sym c (SymCplxArray x) (SymCplxArray y) =
  SymCplxArray <$> SMDA.muxArray sym c x y
iteValue sym c (SymCplxArray x) (SymRealArray y) = do
  f <- mkMatlabSolverFn sym RealToComplexFn
  y' <- SMDA.map sym f y
  SymCplxArray <$> SMDA.muxArray sym c x y'
iteValue sym c (SymRealArray x) (SymCplxArray y) = do
  f <- mkMatlabSolverFn sym RealToComplexFn
  x' <- SMDA.map sym f x
  SymCplxArray <$> SMDA.muxArray sym c x' y
iteValue sym c (SymRealArray x) (SymRealArray y) = do
  SymRealArray <$> SMDA.muxArray sym c x y

iteValue s c (IntArray x) (IntArray y) =
  IntArray <$> muxReg s (Proxy :: Proxy MatlabIntArrayType) c x y
iteValue s c (SymIntArray x) (SymIntArray y) =
  SymIntArray <$> muxReg s (Proxy :: Proxy MatlabSymbolicIntArrayType) c x y

iteValue s c (UIntArray x) (UIntArray y) =
  UIntArray <$> muxReg s (Proxy :: Proxy MatlabUIntArrayType) c x y
iteValue s c (SymUIntArray x) (SymUIntArray y) =
  SymUIntArray <$> muxReg s (Proxy :: Proxy MatlabSymbolicUIntArrayType) c x y

iteValue s c (LogicArray x) (LogicArray y) =
  LogicArray <$> muxReg s (Proxy :: Proxy (MultiDimArrayType BoolType)) c x y
iteValue s c (SymLogicArray x) (SymLogicArray y) =
  SymLogicArray <$> SMDA.muxArray s c x y

iteValue s c (CharArray  x) (CharArray y) =
  CharArray <$> muxReg s (Proxy :: Proxy (MultiDimArrayType CharType)) c x y
iteValue s c (CellArray x) (CellArray y) =
  CellArray <$> mdaMuxFn (iteValue s) c x y
iteValue s c (MatlabStructArray x) (MatlabStructArray y) =
  MatlabStructArray <$> structArrayMuxFn s c x y
iteValue s c (MatlabObjectArray x) (MatlabObjectArray y) =
  MatlabObjectArray <$> objectArrayMuxFn s c x y
iteValue s c (FunctionHandle x) (FunctionHandle y) = do
  FunctionHandle <$> muxMatlabHandle s c x y
iteValue _ _ x y = do
  fail $ "Cannot merge values with classes " ++ valueClass x ++ " and " ++ valueClass y ++ "."

------------------------------------------------------------------------
-- IntrinsicClass instance for MatlabStructArray
--   A type describing arrays of MATLAB structures, where each array element
--   uniformly has the same set of fields.

instance MatlabSymbolicArrayBuilder sym => IntrinsicClass sym "MatlabStructArray" where

  type Intrinsic sym "MatlabStructArray" = MatlabStructArray sym
  muxIntrinsic sym _ = structArrayMuxFn sym


{-# INLINE structArrayMuxFn #-}
structArrayMuxFn :: MatlabSymbolicArrayBuilder sym
                 => sym -> ValMuxFn sym MatlabStructArrayType
structArrayMuxFn s p (StructArr f x) (StructArr g y)
  | MDA.dim x /= MDA.dim y =
    fail "Cannot merge disimilar arrays."
  | f /= g =
    fail "Cannot merge structs with different types."
  | otherwise =
    StructArr f <$> MDA.zipWithM (V.zipWithM (iteValue s p)) x y

------------------------------------------------------------------------
-- IntrinsicClass instance for MatlabStruct
--   A type describing MATLAB structures, which basically consist of (name,value) pairs

data MatlabStructVal sym = MatlabStruct (V.Vector Text) (V.Vector (Value sym))

instance MatlabSymbolicArrayBuilder sym => IntrinsicClass sym "MatlabStruct" where
  type Intrinsic sym "MatlabStruct" = MatlabStructVal sym
  muxIntrinsic sym _ p x y = do
     matlabStructMuxFn sym p x y

{-# INLINE matlabStructMuxFn #-}
matlabStructMuxFn :: MatlabSymbolicArrayBuilder sym
                  => sym
                  -> ValMuxFn sym MatlabStructType
matlabStructMuxFn s p (MatlabStruct f x) (MatlabStruct g y)
  | f /= g = do
    fail "Cannot merge structs with different types."
  | otherwise = do
     MatlabStruct f <$> V.zipWithM (iteValue s p) x y

------------------------------------------------------------------------
-- ObjectArray

-- | A Matlab object value
data MatlabObject sym = MkMatlabObject
  { -- | name of object's class
    objClass :: !Text
    -- | object's properties, stored in the order specified by the class info
  , objPropNames :: !(V.Vector Text)
  , objPropVals  :: !(V.Vector (Value sym))
  }

-- | A Matlab object array. Note that the class name must be kept in addition to
-- the name as part of constituent objects.
data MatlabObjectArray sym = MkMatlabObjectArray
  { -- | name of the class
    objArrayClass  :: !Text
    -- | multidimarray of object values
  , objArrayValues :: !(MultiDimArray (MatlabObject sym))
  }

-- | HasDim instance for 'MatlabObjectArray'
instance MDA.HasDim (MatlabObjectArray sym) where
  dim a = MDA.dim (objArrayValues a)

setObjectProperty
  :: Monad m
  => MatlabObjectArray a  -- ^ object array to update
  -> MDA.Index            -- ^ index of object
  -> Text                 -- ^ name of the property
  -> Value a              -- ^ value to update to
  -> m (MatlabObjectArray a)
setObjectProperty (MkMatlabObjectArray nm objs) idx prop val = do
  -- Get the current object from the selected index
  let Just (MkMatlabObject cnm pnms pvls) = objs MDA.!? idx

  -- Check to see if the property is valid
  case V.elemIndex prop pnms of
    -- If property is not valid, raise an error
    Nothing  -> fail $ "No property " ++ (show prop) ++ " exists for class "
                    ++ (show nm) ++ "."

    -- When property exists, update its value at the given index.
    Just pidx -> do
      -- Replace the property value in the vector at position pidx
      let new_pvls = pvls V.// [(pidx,val)]
      let new_obj  = MkMatlabObject cnm pnms new_pvls
      let resizeErr = "In assignments with a single index, the array cannot be resized."
      let defaultObj = error resizeErr

      -- Update the objs array with the new object
      case MDA.set objs defaultObj idx new_obj of
        Just new_objs ->
          return (MkMatlabObjectArray nm new_objs)
        Nothing       ->
          fail resizeErr

------------------------------------------------------------------------
-- IntrinsicClass instance for 'MatlabObjectArray'

--   A type describing arrays of Matlab objects, where each array element
--   is from the same Matlab class.
instance MatlabSymbolicArrayBuilder sym => IntrinsicClass sym "MatlabObjectArray" where

  type Intrinsic sym "MatlabObjectArray" = MatlabObjectArray sym
  muxIntrinsic sym _ = objectArrayMuxFn sym

{-# INLINE objectArrayMuxFn #-}
objectArrayMuxFn :: MatlabSymbolicArrayBuilder sym
                 => sym -> ValMuxFn sym MatlabObjectArrayType
objectArrayMuxFn s p (MkMatlabObjectArray f x) (MkMatlabObjectArray g y)
  | f /= g =
    fail "Cannot merge objects from different classes."
  | otherwise  =
    MkMatlabObjectArray f <$> mdaMuxFn (matlabObjectMuxFn s) p x y

------------------------------------------------------------------------
-- IntrinsicClass instance for 'MatlabObject'
instance MatlabSymbolicArrayBuilder sym => IntrinsicClass sym "MatlabObject" where
  type Intrinsic sym "MatlabObject" = MatlabObject sym
  muxIntrinsic sym _ p x y = matlabObjectMuxFn sym p x y

-- When objects are from the same class, merge the property values.
{-# INLINE matlabObjectMuxFn #-}
matlabObjectMuxFn :: MatlabSymbolicArrayBuilder sym
                  => sym
                  -> ValMuxFn sym MatlabObjectType
matlabObjectMuxFn s p (MkMatlabObject f ps fpvs) (MkMatlabObject g _ gpvs)
  | f /= g    = fail "Cannot merge objects from different classes."
  | otherwise = MkMatlabObject f ps <$> V.zipWithM (iteValue s p) fpvs gpvs
