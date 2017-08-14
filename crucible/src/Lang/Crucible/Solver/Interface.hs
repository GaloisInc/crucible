{-|
Module           : Lang.Crucible.Solver.Interface
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Defines interface between the simulator and terms that are sent to the
SAT or SMT solver.  The simulator can use a richer set of types, but the
symbolic values must be representable by types supported by this interface.

A solver backend is defined in terms of a type parameter @sym@, which
is the type that tracks whatever state or context is needed by that
particular backend. To instantiate the solver interface, one must
provide several type family definitions and class instances for @sym@:

  [@type 'SymExpr' sym :: 'BaseType' -> *@]
  Type of symbolic expressions.

  [@type 'BoundVar' sym :: 'BaseType' -> *@]
  Representation of bound variables in symbolic expressions.

  [@type 'SymFn' sym :: Ctx BaseType -> BaseType -> *@]
  Representation of symbolic functions.

  [@type 'SymPathState' sym :: *@]
  Representation of symbolic path conditions.

  [@instance 'IsBoolExprBuilder' sym@]
  Functions for building boolean formulas.

  [@instance 'IsExprBuilder' sym@]
  Functions for building expressions of various types.

  [@instance 'IsSymInterface' sym@]
  Functions for building expressions with bound variables and quantifiers.

  [@instance 'IsBoolSolver' sym@]
  Functions for managing path conditions and assertions.

  [@instance 'IsPred' ('SymExpr' sym 'BaseBoolType')@]
  Recognizer for boolean literals.

  [@instance 'IsExpr' ('SymExpr' sym)@]
  Recognizers for various kinds of literal expressions.

  [@instance 'Lang.Crucible.ProgramLoc.HasProgramLoc' ('SymPathState' sym)@]

  [@instance 'OrdF' ('SymExpr' sym)@]

  [@instance 'TestEquality' ('SymExpr' sym)@]

  [@instance 'HashableF' ('SymExpr' sym)@]

-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Solver.Interface
  ( -- * Interface classes
    -- ** IsExpr
    IsExpr(..)
    -- ** IsExprBuilder
  , IsExprBuilder(..)
    -- ** IsSymInterface
  , BoundVar
  , IsSymFn(..)
  , IsSymInterface(..)
    -- * Bound variables
  , SymEncoder(..)
  , ArrayResultWrapper(..)
    -- * Type Aliases
  , SymFn
  , SymNat
  , SymInteger
  , SymReal
  , SymCplx
  , SymStruct
  , SymBV
  , SymArray
    -- * IndexLit
  , IndexLit(..)
  , indexLit
    -- * WordMap
  , WordMap(..)
  , emptyWordMap
  , muxWordMap
  , insertWordMap
  , lookupWordMap
    -- * Utilities
  , mkRational
  , mkReal
  , iteM
  , cplxDiv
  , cplxLog
  , cplxLogBase

  , realExprAsInteger
  , realExprAsNat

  , cplxExprAsRational
  , cplxExprAsNat
  , cplxExprAsInteger

  , rationalAsInteger
  , baseDefaultValue

  , andAllOf
  , predToReal
  , backendPred
  , isNonZero
  , isReal
  , addAssertionM
  , assertIsInteger

  , baseIsConcrete

    -- * Indexing
  , muxIntegerRange

  , module Data.Parameterized.NatRepr
  , module BoolInterface
  , Lang.Crucible.Solver.Symbol.SolverSymbol
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Hashable
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Scientific (Scientific)
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen (Doc)

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.BoolInterface as BoolInterface
import           Lang.Crucible.Solver.Partial (PartExpr(..))
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Solver.WeightedSum (WeightedSum)
import           Lang.Crucible.Utils.Arithmetic
import           Lang.Crucible.Utils.Complex
import           Lang.Crucible.Utils.UnaryBV
import qualified Lang.Crucible.Utils.Hashable as Hash

------------------------------------------------------------------------
-- SymExpr names

-- | Symbolic natural numbers.
type SymNat sym = SymExpr sym BaseNatType

-- | Symbolic integers.
type SymInteger sym = SymExpr sym BaseIntegerType

-- | Symbolic real numbers.
type SymReal sym = SymExpr sym BaseRealType

-- | Symbolic complex numbers.
type SymCplx sym = SymExpr sym BaseComplexType

-- | Symbolic structures.
type SymStruct sym flds = SymExpr sym (BaseStructType flds)

-- | Symbolic arrays.
type SymArray sym idx b = SymExpr sym (BaseArrayType idx b)

-- | Symbolic bitvectors.
type SymBV sym n = SymExpr sym (BaseBVType n)

------------------------------------------------------------------------
-- Type families for the interface.

-- | Type of bound variable associated with symbolic state.
--
-- This type is used by some methods in class 'IsSymInterface'.
type family BoundVar (sym :: *) :: BaseType -> *

------------------------------------------------------------------------
-- IsExpr

class (IsPred (e BaseBoolType)) => IsExpr e where
  -- | Return nat if this is a constant natural number.
  asNat :: e BaseNatType -> Maybe Natural
  asNat _ = Nothing

  -- | Return integer if this is a constant integer.
  asInteger :: e BaseIntegerType -> Maybe Integer
  asInteger _ = Nothing

  -- | Return rational if this is a constant value.
  asRational :: e BaseRealType -> Maybe Rational
  asRational _ = Nothing

  -- | Return complex if this is a constant value.
  asComplex :: e BaseComplexType -> Maybe (Complex Rational)
  asComplex _ = Nothing

  asUnsignedBV :: e (BaseBVType w) -> Maybe Integer
  asUnsignedBV _ = Nothing

  asSignedBV   :: (1 <= w) => e (BaseBVType w) -> Maybe Integer
  asSignedBV _ = Nothing

  -- | Return value if this is an array of constants.
  asConstantArray :: e (BaseArrayType idx bt) -> Maybe (e bt)
  asConstantArray _ = Nothing

  -- | Get type of expression.
  exprType :: e tp -> BaseTypeRepr tp

  bvWidth      :: e (BaseBVType w) -> NatRepr w
  bvWidth e =
    case exprType e of
      BaseBVRepr w -> w

  -- | Print a sym expression for debugging purposes.
  printSymExpr :: e tp -> Doc

------------------------------------------------------------------------
-- IndexLit

-- | This represents a concrete index value, and is used for creating
-- arrays.
data IndexLit idx where
  NatIndexLit :: !Natural -> IndexLit BaseNatType
  BVIndexLit :: (1 <= w) => !(NatRepr w) -> !Integer ->  IndexLit (BaseBVType w)

instance Eq (IndexLit tp) where
  x == y = isJust (testEquality x y)

instance TestEquality IndexLit where
  testEquality (NatIndexLit x) (NatIndexLit y) =
    if x == y then
     Just Refl
     else
     Nothing
  testEquality (BVIndexLit wx x) (BVIndexLit wy y) = do
    Refl <- testEquality wx wy
    if x == y then Just Refl else Nothing
  testEquality _ _ =
    Nothing

instance OrdF IndexLit where
  compareF (NatIndexLit x) (NatIndexLit y) = fromOrdering (compare x y)
  compareF NatIndexLit{} _ = LTF
  compareF _ NatIndexLit{} = GTF
  compareF (BVIndexLit wx x) (BVIndexLit wy y) =
    case compareF wx wy of
      LTF -> LTF
      GTF -> GTF
      EQF -> fromOrdering (compare x y)

instance Hashable (IndexLit tp) where
  hashWithSalt = hashIndexLit
  {-# INLINE hashWithSalt #-}


hashIndexLit :: Int -> IndexLit idx -> Int
s `hashIndexLit` (NatIndexLit i) =
    s `hashWithSalt` (0::Int)
      `hashWithSalt` i
s `hashIndexLit` (BVIndexLit w i) =
    s `hashWithSalt` (1::Int)
      `hashWithSalt` w
      `hashWithSalt` i

instance HashableF IndexLit where
  hashWithSaltF = hashIndexLit

instance Show (IndexLit tp) where
  showsPrec p (NatIndexLit i) s = showsPrec p i s
  showsPrec p (BVIndexLit w i) s = showsPrec p i ("::[" ++ shows w (']' : s))

instance ShowF IndexLit

newtype ArrayResultWrapper f idx tp =
  ArrayResultWrapper { unwrapArrayResult :: f (BaseArrayType idx tp) }

instance TestEquality f => TestEquality (ArrayResultWrapper f idx) where
  testEquality (ArrayResultWrapper x) (ArrayResultWrapper y) = do
    Refl <- testEquality x y
    return Refl

instance HashableF e => HashableF (ArrayResultWrapper e idx) where
  hashWithSaltF s (ArrayResultWrapper v) = hashWithSaltF s v

------------------------------------------------------------------------
-- IsExprBuilder

-- | This class allows the simulator to build symbolic expressions.
--
-- Methods of this class refer to type families @'SymExpr' sym@
-- and @'SymFn' sym@.
class ( IsBoolExprBuilder sym
      , IsExpr (SymExpr sym)
      , HashableF (SymExpr sym)
      ) => IsExprBuilder sym where

  ----------------------------------------------------------------------
  -- Nat operations.

  -- | A natural number literal.
  natLit :: sym -> Natural -> IO (SymNat sym)

  -- | Add two natural numbers.
  natAdd :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | Subtract one number from another.
  --
  -- The result is undefined if this would result in a negative number.
  natSub :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | Multiply one number by another.
  natMul :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | Evaluate a weighted sum of natural number values
  natSum :: sym -> WeightedSum (SymExpr sym) BaseNatType -> IO (SymNat sym)

  -- | 'natDiv sym x y' performs natural division.
  --
  -- The result is undefined if y equals '0'.
  --
  -- 'natDiv' and 'natMod' satisfy the property that given
  --   d <- natDiv sym x y
  --   m <- natMod sym x y
  --
  --  We have that
  --    1. y > 0 => y * d + m = x
  --    2. y > 0 => m < y
  natDiv :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | @natMod sym x y@ returns `x mod y`.
  --
  -- See 'natDiv' for a description of the properties the return
  -- value is expected to satisfy.
  natMod :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)
  natMod sym x y = do
    xi <- natToInteger sym x
    intMod sym xi y

  -- | If-then-else applied to natural numbers.
  natIte :: sym -> Pred sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  natEq :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)

  -- | @natLe sym x y@ returns 'true' if @x <= y@.
  natLe :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)

  natLt :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)
  natLt sym x y = notPred sym =<< natLe sym y x

  -- | Return true if two expressions are equal. The default
  -- implementation dispatches 'eqPred', 'bvEq', 'natEq', 'intEq',
  -- 'realEq', 'cplxEq', 'structEq', or 'arrayEq', depending on the
  -- type.
  isEq :: sym -> SymExpr sym tp -> SymExpr sym tp -> IO (Pred sym)
  isEq sym x y =
    case exprType x of
      BaseBoolRepr     -> eqPred sym x y
      BaseBVRepr{}     -> bvEq sym x y
      BaseNatRepr      -> natEq sym x y
      BaseIntegerRepr  -> intEq sym x y
      BaseRealRepr     -> realEq sym x y
      BaseComplexRepr  -> cplxEq sym x y
      BaseStructRepr{} -> structEq sym x y
      BaseArrayRepr{}  -> arrayEq sym x y

  -- | Take the if-then-else of two expressions. The default
  -- implementation dispatches 'itePred', 'bvIte', 'natIte', 'intIte',
  -- 'realIte', 'cplxIte', 'structIte', or 'arrayIte', depending on
  -- the type.
  baseTypeIte :: sym
              -> Pred sym
              -> SymExpr sym tp
              -> SymExpr sym tp
              -> IO (SymExpr sym tp)
  baseTypeIte sym c x y =
    case exprType x of
      BaseBoolRepr     -> itePred   sym c x y
      BaseBVRepr{}     -> bvIte     sym c x y
      BaseNatRepr      -> natIte    sym c x y
      BaseIntegerRepr  -> intIte    sym c x y
      BaseRealRepr     -> realIte   sym c x y
      BaseComplexRepr  -> cplxIte   sym c x y
      BaseStructRepr{} -> structIte sym c x y
      BaseArrayRepr{}  -> arrayIte  sym c x y

  ----------------------------------------------------------------------
  -- Integer operations

  -- | Create a symbolic integer.
  intLit :: sym -> Integer -> IO (SymInteger sym)

  -- | Negate an integer.
  intNeg :: sym -> SymInteger sym -> IO (SymInteger sym)

  -- | Add two integers.
  intAdd :: sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | Subtract one integer from another.
  intSub :: sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)
  intSub sym x y = intAdd sym x =<< intNeg sym y

  -- | Multiply one integer by another.
  intMul :: sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | Evaluate a weighted sum of integer values
  intSum :: sym -> WeightedSum (SymExpr sym) BaseIntegerType -> IO (SymInteger sym)

  -- | If-then-else applied to integers.
  intIte :: sym -> Pred sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | Integer equality.
  intEq  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)

  -- | Integer less-than-or-equal.
  intLe  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)

  -- | Integer less-than.
  intLt  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)
  intLt sym x y = notPred sym =<< intLe sym y x

  -- | @intMod x y@ returns the value of @x - y * floor(x ./ y)@ when
  -- @y@ is not zero, and undefined when @y@ is zero.
  intMod :: sym -> SymInteger sym -> SymNat sym -> IO (SymNat sym)

  ----------------------------------------------------------------------
  -- Bitvector operations

  -- | Create a bitvector with the given width and value.
  bvLit :: (1 <= w) => sym -> NatRepr w -> Integer -> IO (SymBV sym w)

  -- | Concatenate two bitvectors.
  bvConcat :: (1 <= u, 1 <= v)
           => sym
           -> SymBV sym u  -- ^ most significant bits
           -> SymBV sym v  -- ^ least significant bits
           -> IO (SymBV sym (u+v))

  -- | Select a subsequence from a bitvector.
  bvSelect :: (1 <= n, idx + n <= w)
           => sym
           -> NatRepr idx  -- ^ Starting index, from 0 as least significant bit
           -> NatRepr n    -- ^ Number of bits to take
           -> SymBV sym w  -- ^ Bitvector to select from
           -> IO (SymBV sym n)

  -- | 2's complement negation.
  bvNeg :: (1 <= w)
        => sym
        -> SymBV sym w
        -> IO (SymBV sym w)

  -- | Add two bitvectors.
  bvAdd :: (1 <= w)
        => sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (SymBV sym w)

  -- | Subtract one bitvector from another.
  bvSub :: (1 <= w)
        => sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (SymBV sym w)
  bvSub sym x y = bvAdd sym x =<< bvNeg sym y

  -- | Multiply one bitvector by another.
  bvMul :: (1 <= w)
        => sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (SymBV sym w)

  -- | Unsigned bitvector division.
  bvUdiv :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Unsigned bitvector remainder.
  bvUrem :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Signed bitvector division.
  bvSdiv :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Signed bitvector remainder.
  bvSrem :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | This creates an expression from a unary bitvector.
  bvUnary :: (1 <= w)
          => sym
          -> UnaryBV (Pred sym) w
          -> IO (SymBV sym w)

  -- | Returns true if the corresponding bit in the bitvector is set.
  testBitBV :: (1 <= w)
            => sym
            -> Integer -- ^ Index of bit (0 is the least significant bit)
            -> SymBV sym w
            -> IO (Pred sym)

  -- | Return true if bitvector is negative.
  bvIsNeg :: (1 <= w) => sym -> SymBV sym w -> IO (Pred sym)
  bvIsNeg sym x = bvSlt sym x =<< bvLit sym (bvWidth x) 0

  -- | If-then-else applied to bitvectors.
  bvIte :: (1 <= w)
        => sym
        -> Pred sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (SymBV sym w)

  -- | Return true if bitvectors are equal.
  bvEq  :: (1 <= w)
        => sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (Pred sym)
  bvEq = isEq

  -- | Return true if bitvectors are distinct.
  bvNe  :: (1 <= w)
        => sym
        -> SymBV sym w
        -> SymBV sym w
        -> IO (Pred sym)
  bvNe sym x y = notPred sym =<< bvEq sym x y

  -- | Unsigned less-than.
  bvUlt  :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (Pred sym)

  -- | Unsigned less-than-or-equal.
  bvUle  :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (Pred sym)
  bvUle sym x y = notPred sym =<< bvUlt sym y x

  -- | Unsigned greater-than-or-equal.
  bvUge :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)
  bvUge sym x y = bvUle sym y x

  -- | Unsigned greater-than.
  bvUgt :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)
  bvUgt sym x y = bvUlt sym y x

  -- | Signed less-than.
  bvSlt :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)

  -- | Signed greater-than.
  bvSgt :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)
  bvSgt sym x y = bvSlt sym y x

  -- | Signed less-than-or-equal.
  bvSle :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)
  bvSle sym x y = notPred sym =<< bvSlt sym y x

  -- | Signed greater-than-or-equal.
  bvSge :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (Pred sym)
  bvSge sym x y = notPred sym =<< bvSlt sym x y

  -- | returns true if the given bitvector is non-zero.
  bvIsNonzero :: (1 <= w) => sym -> SymBV sym w -> IO (Pred sym)
  bvIsNonzero sym x = do
     let w = bvWidth x
     zro <- bvLit sym w 0
     notPred sym  =<< bvEq sym x zro

  -- | Left shift.
  bvShl :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)

  -- | Logical right shift.
  bvLshr :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)

  -- | Arithmetic right shift.
  bvAshr :: (1 <= w) => sym -> SymBV sym w -> SymBV sym w -> IO (SymBV sym w)

  -- | Zero-extend a bitvector.
  bvZext :: (1 <= u, u+1 <= r) => sym -> NatRepr r -> SymBV sym u -> IO (SymBV sym r)

  -- | Sign-extend a bitvector.
  bvSext :: (1 <= u, u+1 <= r) => sym -> NatRepr r -> SymBV sym u -> IO (SymBV sym r)

  -- | Truncate a bitvector.
  bvTrunc :: (1 <= r, r+1 <= w) -- Assert result is less than input.
          => sym
          -> NatRepr r
          -> SymBV sym w
          -> IO (SymBV sym r)

  -- | Bitwise logical and.
  bvAndBits :: (1 <= w)
            => sym
            -> SymBV sym w
            -> SymBV sym w
            -> IO (SymBV sym w)

  -- | Bitwise logical or.
  bvOrBits  :: (1 <= w)
            => sym
            -> SymBV sym w
            -> SymBV sym w
            -> IO (SymBV sym w)

  -- | Bitwise logical exclusive or.
  bvXorBits :: (1 <= w)
            => sym
            -> SymBV sym w
            -> SymBV sym w
            -> IO (SymBV sym w)

  -- | Bitwise complement.
  bvNotBits :: (1 <= w) => sym -> SymBV sym w -> IO (SymBV sym w)

  -- | @bvSet sym v i p@ returns a bitvector @v'@ where bit @i@ of @v'@ is set to
  -- @p@, and the bits at the other indices are the same as in @v@.
  bvSet :: forall w
         . (1 <= w)
        => sym         -- ^ Symbolic interface
        -> SymBV sym w -- ^ Bitvector to updaate
        -> Integer     -- ^ 0-based index to set
        -> Pred sym    -- ^ Predicate to set.
        -> IO (SymBV sym w)
  bvSet sym v i p = assert (0 <= i && i < natValue (bvWidth v)) $ do
    let setCase :: IO (SymBV sym w)
        setCase = do
          bvOrBits sym v =<< bvLit sym (bvWidth v) (2^i)
        unsetCase :: IO (SymBV sym w)
        unsetCase = do
          bvAndBits sym v =<< bvLit sym (bvWidth v) (negate (2^i+1))
    iteM bvIte sym p setCase unsetCase

  -- | Return the bitvector of the desired width with all 0 bits;
  --   this is the minimum unsigned integer.
  minUnsignedBV :: (1 <= w) => sym -> NatRepr w -> IO (SymBV sym w)
  minUnsignedBV sym w = bvLit sym w 0

  -- | Return the bitvector of the desired width with all bits set;
  --   this is the maximum unsigned integer.
  maxUnsignedBV :: (1 <= w) => sym -> NatRepr w -> IO (SymBV sym w)
  maxUnsignedBV sym w = bvLit sym w (maxUnsigned w)

  -- | Return the bitvector representing the largest 2's complement
  --   signed integer of the given width.  This consists of all bits
  --   set except the MSB.
  maxSignedBV :: (1 <= w) => sym -> NatRepr w -> IO (SymBV sym w)
  maxSignedBV sym w = bvLit sym w (maxSigned w)

  -- | Return the bitvector representing the smallest 2's complement
  --   signed integer of the given width. This consists of all 0 bits
  --   except the MSB, which is set.
  minSignedBV :: (1 <= w) => sym -> NatRepr w -> IO (SymBV sym w)
  minSignedBV sym w = bvLit sym w (minSigned w)

  -- | Unsigned add with overflow bit.
  addUnsignedOF :: (1 <= w)
                => sym
                -> SymBV sym w
                -> SymBV sym w
                -> IO (Pred sym, SymBV sym w)
  addUnsignedOF sym x y = do
    -- Compute result
    r   <- bvAdd sym x y
            -- Return that this overflows if x input value is greater than result.
    (,) <$> bvUgt sym x r <*> pure r

  -- | Signed add with overflow bit. Overflow is true if positive +
  -- positive = negative, or if negative + negative = positive.
  addSignedOF :: (1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (Pred sym, SymBV sym w)
  addSignedOF sym x y = do
    xy  <- bvAdd sym x y
    sx  <- bvIsNeg sym x
    sy  <- bvIsNeg sym y
    sxy <- bvIsNeg sym xy

    not_sx  <- notPred sym sx
    not_sy  <- notPred sym sy
    not_sxy <- notPred sym sxy

    -- Return this overflowed if the sign bits of sx and sy are equal,
    -- but different from sxy.
    ov1 <- andPred sym not_sxy =<< andPred sym sx sy
    ov2 <- andPred sym sxy =<< andPred sym not_sx not_sy

    ov  <- orPred sym ov1 ov2
    return (ov, xy)

  -- | Signed subtract with overflow bit. Overflow is true if positive
  -- - negative = negative, or if negative - positive = positive.
  subSignedOF :: (1 <= w)
              => sym
              -> SymBV sym w
              -> SymBV sym w
              -> IO (Pred sym, SymBV sym w)
  subSignedOF sym x y = do
       xy  <- bvSub sym x y
       sx  <- bvIsNeg sym x
       sy  <- bvIsNeg sym y
       sxy <- bvIsNeg sym xy
       ov  <- join (pure (andPred sym) <*> xorPred sym sx sxy <*> xorPred sym sx sy)
       return (ov, xy)

  -- | @unsignedWideMultiplyBV sym x y@ multiplies two unsigned 'w' bit numbers 'x' and 'y'.
  --
  -- It returns a pair containing the top 'w' bits as the first element, and the
  -- lower 'w' bits as the second element.
  unsignedWideMultiplyBV :: (1 <= w)
                         => sym
                         -> SymBV sym w
                         -> SymBV sym w
                         -> IO (SymBV sym w, SymBV sym w)
  unsignedWideMultiplyBV sym x y = do
       let w = bvWidth x
       let dbl_w = addNat w w
       -- Add dynamic check to assert w' is positive to work around
       -- Haskell typechecker limitation.
       Just LeqProof <- return (isPosNat dbl_w)
       -- Add dynamic check to assert w+1 <= 2*w.
       Just LeqProof <- return (testLeq (incNat w) dbl_w)
       x'  <- bvZext sym dbl_w x
       y'  <- bvZext sym dbl_w y
       s   <- bvMul sym x' y'
       lo  <- bvTrunc sym w s
       n   <- bvLit sym dbl_w (natValue w)
       hi  <- bvTrunc sym w =<< bvLshr sym s n
       return (hi, lo)

  -- | @signedWideMultiplyBV sym x y@ multiplies two signed 'w' bit numbers 'x' and 'y'.
  --
  -- It returns a pair containing the top 'w' bits as the first element, and the
  -- lower 'w' bits as the second element.
  signedWideMultiplyBV :: (1 <= w)
                       => sym
                       -> SymBV sym w
                       -> SymBV sym w
                       -> IO (SymBV sym w, SymBV sym w)
  signedWideMultiplyBV sym x y = do
       let w = bvWidth x
       let dbl_w = addNat w w
       -- Add dynamic check to assert dbl_w is positive to work around
       -- Haskell typechecker limitation.
       Just LeqProof <- return (isPosNat dbl_w)
       -- Add dynamic check to assert w+1 <= 2*w.
       Just LeqProof <- return (testLeq (incNat w) dbl_w)
       x'  <- bvSext sym dbl_w x
       y'  <- bvSext sym dbl_w y
       s   <- bvMul sym x' y'
       lo  <- bvTrunc sym w s
       n   <- bvLit sym dbl_w (fromIntegral (widthVal w))
       hi  <- bvTrunc sym w =<< bvLshr sym s n
       return (hi, lo)

  ----------------------------------------------------------------------
  -- Struct operations

  -- | Create a struct from an assignment of expressions.
  mkStruct :: sym
           -> Ctx.Assignment (SymExpr sym) flds
           -> IO (SymStruct sym flds)

  -- | Get the value of a specific field in a struct.
  structField :: sym
              -> SymStruct sym flds
              -> Ctx.Index flds tp
              -> IO (SymExpr sym tp)

  -- | Check if two structs are equal.
  structEq  :: forall flds
            .  sym
            -> SymStruct sym flds
            -> SymStruct sym flds
            -> IO (Pred sym)
  structEq sym x y = do
    case exprType x of
      BaseStructRepr fld_types -> do
        let sz = Ctx.size fld_types
        -- Checks to see if the ith struct fields are equal, and all previous entries
        -- are as well.
        let f :: IO (Pred sym) -> Ctx.Index flds tp -> IO (Pred sym)
            f mp i = do
              xi <- structField sym x i
              yi <- structField sym y i
              i_eq <- isEq sym xi yi
              case asConstantPred i_eq of
                Just True -> mp
                Just False -> return (falsePred sym)
                _ ->  andPred sym i_eq =<< mp
        Ctx.forIndex sz f (return (truePred sym))

  -- | Take the if-then-else of two structures.
  structIte :: sym
            -> Pred sym
            -> SymStruct sym flds
            -> SymStruct sym flds
            -> IO (SymStruct sym flds)

  -----------------------------------------------------------------------
  -- Array operations

  -- | Create an array where each element has the same value.
  constantArray :: sym -- Interface
                -> Ctx.Assignment BaseTypeRepr (idx::>tp) -- ^ Index type
                -> SymExpr sym b -- ^ Constant
                -> IO (SymArray sym (idx::>tp) b)

  -- | Create an array from an arbitrary symbolic function.
  --
  -- Arrays created this way can typically not be compared
  -- for equality when provided to the simulator.
  arrayFromFn :: sym
              -> SymFn sym (idx ::> itp) ret
              -> IO (SymArray sym (idx ::> itp) ret)

  -- | Create an array by mapping a function over one or more existing arrays.
  arrayMap :: sym
           -> SymFn sym (ctx::>d) r
           -> Ctx.Assignment (ArrayResultWrapper (SymExpr sym) (idx ::> itp)) (ctx::>d)
           -> IO (SymArray sym (idx ::> itp) r)

  -- | Update an array at a specific location.
  arrayUpdate :: sym
              -> SymArray sym (idx::>tp) b
              -> Ctx.Assignment (SymExpr sym) (idx::>tp)
              -> SymExpr sym b
              -> IO (SymArray sym (idx::>tp) b)

  -- | Return element in array.
  arrayLookup :: sym
              -> SymArray sym (idx::>tp) b
              -> Ctx.Assignment (SymExpr sym) (idx::>tp)
              -> IO (SymExpr sym b)

  -- | Create an array from a map of concrete indices to values.
  --
  -- This is implemented, but designed to be overriden for efficiency.
  arrayFromMap :: sym
               -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
                  -- ^ Types for indices
               -> Hash.Map IndexLit (idx ::> itp) (SymExpr sym) tp
                  -- ^ Value for known indices.
               -> SymExpr sym tp
                  -- ^ Value for other entries.
               -> IO (SymArray sym (idx ::> itp) tp)
  arrayFromMap sym idx_tps m default_value = do
    a0 <- constantArray sym idx_tps default_value
    arrayUpdateAtIdxLits sym m a0

  -- | Update an array at specific concrete indices.
  --
  -- This is implemented, but designed to be overriden for efficiency.
  arrayUpdateAtIdxLits :: sym
                       -> Hash.Map IndexLit (idx ::> itp) (SymExpr sym) tp
                       -- ^ Value for known indices.
                       -> SymArray sym (idx ::> itp) tp
                       -- ^ Value for existing array.
                       -> IO (SymArray sym (idx ::> itp) tp)
  arrayUpdateAtIdxLits sym m a0 = do
    let updateAt a (i,v) = do
          idx <-  traverseFC (indexLit sym) i
          arrayUpdate sym a idx v
    foldlM updateAt a0 (Map.toList (Hash.hashedMap m))

  -- | If-then-else applied to arrays.
  arrayIte :: sym
           -> Pred sym
           -> SymArray sym idx b
           -> SymArray sym idx b
           -> IO (SymArray sym idx b)

  -- | Return true if two arrays are equal.
  --
  -- Note that in the backend, arrays do not have a fixed number of elements, so
  -- this equality requires that arrays are equal on all elements.
  arrayEq :: sym
          -> SymArray sym idx b
          -> SymArray sym idx b
          -> IO (Pred sym)
  arrayEq = isEq

  -- | Return true if all entries in the array are true.
  allTrueEntries :: sym -> SymArray sym idx BaseBoolType -> IO (Pred sym)
  allTrueEntries sym a = do
    case exprType a of
      BaseArrayRepr idx_tps _ ->
        arrayEq sym a =<< constantArray sym idx_tps (truePred sym)

  -- | Return true if the array has the value true at every index satisfying the
  -- given predicate.
  arrayTrueOnEntries
    :: sym
    -> SymFn sym (idx::>itp) BaseBoolType
    -- ^ Predicate that indicates if array should be true.
    -> SymArray sym (idx ::> itp) BaseBoolType
    -> IO (Pred sym)

  ----------------------------------------------------------------------
  -- Lossless (injective) conversions

  -- | Convert a natural number to an integer.
  natToInteger :: sym -> SymNat sym -> IO (SymInteger sym)

  -- | Convert an integer to a real number.
  integerToReal :: sym -> SymInteger sym -> IO (SymReal sym)

  -- | Return the unsigned value of the given bitvector as an integer.
  bvToInteger :: (1 <= w) => sym -> SymBV sym w -> IO (SymInteger sym)

  -- | Return the signed value of the given bitvector as an integer.
  sbvToInteger :: (1 <= w) => sym -> SymBV sym w -> IO (SymInteger sym)

  -- | Return @1@ if the predicate is true; @0@ otherwise.
  predToBV :: (1 <= w) => sym -> Pred sym -> NatRepr w -> IO (SymBV sym w)
  predToBV sym p w = do
    c1 <- bvLit sym w 1
    c0 <- bvLit sym w 0
    bvIte sym p c1 c0

  ----------------------------------------------------------------------
  -- Lossless combinators

  -- | Convert a natural number to a real number.
  natToReal :: sym -> SymNat sym -> IO (SymReal sym)
  natToReal sym = natToInteger sym >=> integerToReal sym

  -- | Convert an unsigned bitvector to a real number.
  uintToReal :: (1 <= w) => sym -> SymBV sym w -> IO (SymReal sym)
  uintToReal sym = bvToInteger sym >=> integerToReal sym

  -- | Convert an signed bitvector to a real number.
  sbvToReal :: (1 <= w) => sym -> SymBV sym w -> IO (SymReal sym)
  sbvToReal sym = sbvToInteger sym >=> integerToReal sym

  ----------------------------------------------------------------------
  -- Lossy (non-injective) conversions

  -- | Round a real number to an integer.
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  realRound :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Round down to the nearest integer that is at most this value.
  realFloor :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Round up to the nearest integer that is at least this value.
  realCeil :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Convert an integer to a signed bitvector.
  --
  -- Result is undefined if integer is outside of range.
  integerToSBV :: (1 <= w) => sym -> SymInteger sym -> NatRepr w -> IO (SymBV sym w)

  -- | Convert an integer to an unsigned bitvector.
  --
  -- Result is undefined if integer is outside of range.
  integerToBV :: (1 <= w) => sym -> SymInteger sym -> NatRepr w -> IO (SymBV sym w)

  ----------------------------------------------------------------------
  -- Lossy (non-injective) combinators

  -- | Convert an integer to a natural number.
  --
  -- For negative integers, the result is undefined.
  integerToNat :: sym -> SymInteger sym -> IO (SymNat sym)

  -- | Convert the unsigned value of a bitvector to a natural.
  --   May fail if the width of the bitvector exceeds the precison
  --   of Haskell 'Int'.
  bvToNat :: (1 <= w) => sym -> SymBV sym w -> IO (SymNat sym)
  bvToNat sym bv = integerToNat sym =<< bvToInteger sym bv


  -- | Convert a real number to an integer.
  --
  -- This should return some value even if the real argument is not a integer,
  -- but the result result may be arbitrarily chosen.
  realToInteger :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Convert a real number to a natural number.
  --
  -- This should return some value even if the real argument is not a natural number,
  -- but the result result may be arbitrarily chosen.
  realToNat :: sym -> SymReal sym -> IO (SymNat sym)
  realToNat sym r = realToInteger sym r >>= integerToNat sym

  -- | Convert a real number to a signed bitvector.
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  realToInt  :: (1 <= w) => sym -> SymReal sym -> NatRepr w -> IO (SymBV sym w)
  realToInt sym r w  = do
    i <- realRound sym r
    clampedIntToSBV sym i w

  -- | Convert an integer to the nearest signed bitvector.
  --
  -- Numbers are rounded to the nearest representable number.
  clampedIntToSBV :: (1 <= w) => sym -> SymInteger sym -> NatRepr w -> IO (SymBV sym w)
  clampedIntToSBV sym i w
    | Just v <- asInteger i = do
      bvLit sym w $ signedClamp w v
    | otherwise = do
      -- Handle case where i < minSigned w
      let min_val = minSigned w
      min_sym <- intLit sym min_val
      is_lt <- intLt sym i min_sym
      iteM bvIte sym is_lt (bvLit sym w min_val) $ do
        -- Handle case where i > maxSigned w
        let max_val = maxSigned w
        max_sym <- intLit sym max_val
        is_gt <- intLt sym max_sym i
        iteM bvIte sym is_gt (bvLit sym w max_val) $ do
          -- Do unclamped conversion.
          integerToSBV sym i w

  -- | Convert an integer to the nearest unsigned bitvector.
  --
  -- Numbers are rounded to the nearest representable number.
  clampedIntToBV :: (1 <= w) => sym -> SymInteger sym -> NatRepr w -> IO (SymBV sym w)
  clampedIntToBV sym i w
    | Just v <- asInteger i = do
      bvLit sym w $ unsignedClamp w v
    | otherwise = do
      -- Handle case where i < 0
      min_sym <- intLit sym 0
      is_lt <- intLt sym i min_sym
      iteM bvIte sym is_lt (bvLit sym w 0) $ do
        -- Handle case where i > maxUnsigned w
        let max_val = maxUnsigned w
        max_sym <- intLit sym max_val
        is_gt <- intLt sym max_sym i
        iteM bvIte sym is_gt (bvLit sym w max_val) $
          -- Do unclamped conversion.
          integerToBV sym i w

  -- | Convert a real number to an unsigned bitvector.
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  -- When the real is negative the result is zero.
  realToUInt :: (1 <= w) => sym -> SymReal sym -> NatRepr w -> IO (SymBV sym w)
  realToUInt sym r w = do
    i <- realRound sym r
    clampedIntToBV sym i w

  ----------------------------------------------------------------------
  -- Bitvector operations.

  -- The width of the output should be at least the width of the
  -- input, but we do not enforce this in the Haskell typechecker,
  -- because it turns out to be painful to do so.

  -- | Convert a signed bitvector to the nearest signed bitvector with
  -- the given width. If the resulting width is smaller, this clamps
  -- the value to min-int or max-int when necessary.
  intSetWidth :: (1 <= m, 1 <= n) => sym -> SymBV sym m -> NatRepr n -> IO (SymBV sym n)
  intSetWidth sym e w = do
    let e_width = bvWidth e
    case w `compareNat` e_width of
      -- Truncate when the width of e is larger than w.
      NatLT _ -> do
        -- Add dynamic check due to limitation in GHC typechecker.
        Just LeqProof <- return (testLeq (incNat w) e_width)
        -- Check if e underflows
        does_underflow <- bvSlt sym e =<< bvLit sym e_width (minSigned w)
        iteM bvIte sym does_underflow (bvLit sym w (minSigned w)) $ do
          -- Check if e overflows target signed representation.
          does_overflow <- bvSgt sym e =<< bvLit sym e_width (maxSigned w)
          iteM bvIte sym does_overflow (bvLit sym w (maxSigned w)) $ do
            -- Just do truncation.
            bvTrunc sym w e
      NatEQ -> return e
      NatGT _ -> do
        -- Add dynamic check due to limitation in GHC typechecker.
        Just LeqProof <- return (testLeq (incNat e_width) w)
        bvSext sym w e

  -- | Convert an unsigned bitvector to the nearest unsigned bitvector with
  -- the given width (clamp on overflow).
  uintSetWidth :: (1 <= m, 1 <= n) => sym -> SymBV sym m -> NatRepr n -> IO (SymBV sym n)
  uintSetWidth sym e w = do
    let e_width = bvWidth e
    case w `compareNat` e_width of
      NatLT _ -> do
        -- Add dynamic check due to limitation in GHC typechecker.
        Just LeqProof <- return (testLeq (incNat w) e_width)
          -- Check if e overflows target unsigned representation.
        does_overflow <- bvUgt sym e =<< bvLit sym e_width (maxUnsigned w)
        iteM bvIte sym does_overflow (bvLit sym w (maxUnsigned w)) $ do
          -- Just do truncation.
          bvTrunc sym w e
      NatEQ -> return e
      NatGT _ -> do
        -- Add dynamic check due to limitation in GHC typechecker.
        Just LeqProof <- return (testLeq (incNat e_width) w)
        bvZext sym w e

  -- | Convert an signed bitvector to the nearest unsigned bitvector with
  -- the given width (clamp on overflow).
  intToUInt :: (1 <= m, 1 <= n) => sym -> SymBV sym m -> NatRepr n -> IO (SymBV sym n)
  intToUInt sym e w = do
    p <- bvIsNeg sym e
    iteM bvIte sym p (bvLit sym w 0) (uintSetWidth sym e w)

  -- | Convert an unsigned bitvector to the nearest signed bitvector with
  -- the given width (clamp on overflow).
  uintToInt :: (1 <= m, 1 <= n) => sym -> SymBV sym m -> NatRepr n -> IO (SymBV sym n)
  uintToInt sym e w = do
    let n = bvWidth e
    case w `compareNat` n of
      NatLT _ -> do
        -- Get maximum signed w-bit number.
        max_val <- bvLit sym n ((2^(widthVal w-1))-1)
        -- Check if expression is less than maximum.
        p <- bvUle sym e max_val
        Just LeqProof <- return (testLeq (incNat w) n)
        -- Select appropriate number then truncate.
        bvTrunc sym w =<< bvIte sym p e max_val
      NatEQ -> do
        max_val <- maxSignedBV sym w
        p <- bvUle sym e max_val
        bvIte sym p e max_val
      NatGT _ -> do
        -- Add dynamic check to ensure GHC typechecks.
        Just LeqProof <- return (testLeq (incNat n) w)
        bvZext sym w e

  ----------------------------------------------------------------------
  -- Real operations

  -- | Return real number 0.
  realZero :: sym -> SymReal sym

  -- | Create a constant real literal.
  realLit :: sym -> Rational -> IO (SymReal sym)

  -- | Make a real literal from a scientific value. May be overridden
  -- if we want to avoid the overhead of converting scientific value
  -- to rational.
  sciLit :: sym -> Scientific -> IO (SymReal sym)
  sciLit sym s = realLit sym (toRational s)

  -- | Check equality of two real numbers.
  realEq :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)
  realEq = isEq

  -- | Check non-equality of two real numbers.
  realNe :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)
  realNe sym x y = notPred sym =<< realEq sym x y

  -- | Check @<=@ on two real numbers.
  realLe :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)

  -- | Check @<@ on two real numbers.
  realLt :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)
  realLt sym x y = notPred sym =<< realLe sym y x

  -- | Check @>=@ on two real numbers.
  realGe :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)
  realGe sym x y = realLe sym y x

  -- | Check @>@ on two real numbers.
  realGt :: sym -> SymReal sym -> SymReal sym -> IO (Pred sym)
  realGt sym x y = realLt sym y x

  -- | If-then-else on real numbers.
  realIte :: sym -> Pred sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | Negate a real number.
  realNeg :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Add two real numbers.
  realAdd :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | Evaluate a weighted sum of real values.
  realSum :: sym -> WeightedSum (SymExpr sym) BaseRealType -> IO (SymReal sym)

  -- | Multiply two real numbers.
  realMul :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | Subtract one real from another.
  realSub :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)
  realSub sym x y = realAdd sym x =<< realNeg sym y

  -- | @realSq sym x@ returns @x * x@.
  realSq :: sym -> SymReal sym -> IO (SymReal sym)
  realSq sym x = realMul sym x x

  -- | @realDiv sym x y@ returns term equivalent to @x/y@.
  --
  -- The result is undefined when @y@ is zero.
  realDiv :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | @realMod x y@ returns the value of @x - y * floor(x ./ y)@ when
  -- @y@ is not zero and @x@ when @y@ is zero.
  realMod :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)
  realMod sym x y = do
    isZero <- realEq sym y (realZero sym)
    iteM realIte sym isZero (return x) $ do
      realSub sym x =<< realMul sym y
                    =<< integerToReal sym
                    =<< realFloor sym
                    =<< realDiv sym x y

  -- | Predicate that holds if the real number is an exact integer.
  isInteger :: sym -> SymReal sym -> IO (Pred sym)

  -- | Return true if the real is non-negative.
  realIsNonNeg :: sym -> SymReal sym -> IO (Pred sym)
  realIsNonNeg sym x = realLe sym (realZero sym) x

  -- | @realSqrt sym x@ returns sqrt(x).  Result is undefined
  -- if @x@ is negative.
  realSqrt :: sym -> SymReal sym -> IO (SymReal sym)

  -- | @realAtan2 sym y x@ returns the arctangent of @y/x@ with a range
  -- of @-pi@ to @pi@; this corresponds to the angle between the positive
  -- x-axis and the line from the origin @(x,y)@.
  --
  -- When @x@ is @0@ this returns @pi/2 * sgn y@.
  realAtan2 :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | Return value denoting pi.
  realPi :: sym -> IO (SymReal sym)

  realLog :: sym -> SymReal sym -> IO (SymReal sym)

  realExp :: sym -> SymReal sym -> IO (SymReal sym)

  realSin :: sym -> SymReal sym -> IO (SymReal sym)
  realCos :: sym -> SymReal sym -> IO (SymReal sym)

  realTan :: sym -> SymReal sym -> IO (SymReal sym)
  realTan sym x = do
    sin_x <- realSin sym x
    cos_x <- realCos sym x
    realDiv sym sin_x cos_x

  realSinh :: sym -> SymReal sym -> IO (SymReal sym)
  realCosh :: sym -> SymReal sym -> IO (SymReal sym)
  realTanh :: sym -> SymReal sym -> IO (SymReal sym)
  realTanh sym x = do
    sinh_x <- realSinh sym x
    cosh_x <- realCosh sym x
    realDiv sym sinh_x cosh_x

  -- | Return absolute value of the real number.
  realAbs :: sym -> SymReal sym -> IO (SymReal sym)
  realAbs sym x = do
    c <- realGe sym x (realZero sym)
    realIte sym c x =<< realNeg sym x

  -- | @realHypot x y@ returns sqrt(x^2 + y^2).
  realHypot :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)
  realHypot sym x y = do
    case (asRational x, asRational y) of
      (Just 0, _) -> realAbs sym y
      (_, Just 0) -> realAbs sym x
      _ -> do
        x2 <- realSq sym x
        y2 <- realSq sym y
        realSqrt sym =<< realAdd sym x2 y2

  ----------------------------------------------------------------------
  -- Cplx operations

  -- | Create a complex from cartesian coordinates.
  mkComplex :: sym -> Complex (SymReal sym) -> IO (SymCplx sym)

  -- | @getRealPart x@ returns the real part of @x@.
  getRealPart :: sym -> SymCplx sym -> IO (SymReal sym)

  -- | @getImagPart x@ returns the imaginary part of @x@.
  getImagPart :: sym -> SymCplx sym -> IO (SymReal sym)

  -- | Convert a complex number into the real and imaginary part.
  cplxGetParts :: sym -> SymCplx sym -> IO (Complex (SymReal sym))

  -- | Create a constant complex literal.
  mkComplexLit :: sym -> Complex Rational -> IO (SymCplx sym)
  mkComplexLit sym d = mkComplex sym =<< traverse (realLit sym) d

  -- | Create a complex from a real value.
  cplxFromReal :: sym -> SymReal sym -> IO (SymCplx sym)
  cplxFromReal sym r = mkComplex sym (r :+ realZero sym)

  -- | If-then-else on complex values.
  cplxIte :: sym -> Pred sym -> SymCplx sym -> SymCplx sym -> IO (SymCplx sym)
  cplxIte sym c x y = do
    case asConstantPred c of
      Just True -> return x
      Just False -> return y
      _ -> do
        xr :+ xi <- cplxGetParts sym x
        yr :+ yi <- cplxGetParts sym y
        zr <- realIte sym c xr yr
        zi <- realIte sym c xi yi
        mkComplex sym (zr :+ zi)

  -- | Negate a complex number.
  cplxNeg :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxNeg sym x = mkComplex sym =<< traverse (realNeg sym) =<< cplxGetParts sym x

  -- | Add two complex numbers together.
  cplxAdd :: sym -> SymCplx sym -> SymCplx sym -> IO (SymCplx sym)
  cplxAdd sym x y = do
    xr :+ xi <- cplxGetParts sym x
    yr :+ yi <- cplxGetParts sym y
    zr <- realAdd sym xr yr
    zi <- realAdd sym xi yi
    mkComplex sym (zr :+ zi)

  -- | Subtract one complex number from another.
  cplxSub :: sym -> SymCplx sym -> SymCplx sym -> IO (SymCplx sym)
  cplxSub sym x y = do
    xr :+ xi <- cplxGetParts sym x
    yr :+ yi <- cplxGetParts sym y
    zr <- realSub sym xr yr
    zi <- realSub sym xi yi
    mkComplex sym (zr :+ zi)

  -- | Multiply two complex numbers together.
  cplxMul :: sym -> SymCplx sym -> SymCplx sym -> IO (SymCplx sym)
  cplxMul sym x y = do
    xr :+ xi <- cplxGetParts sym x
    yr :+ yi <- cplxGetParts sym y
    rz0 <- realMul sym xr yr
    rz <- realSub sym rz0 =<< realMul sym xi yi
    iz0 <- realMul sym xi yr
    iz <- realAdd sym iz0 =<< realMul sym xr yi
    mkComplex sym (rz :+ iz)

  -- | Compute the magnitude of a complex number.
  cplxMag :: sym -> SymCplx sym -> IO (SymReal sym)
  cplxMag sym x = do
    (xr :+ xi) <- cplxGetParts sym x
    realHypot sym xr xi

  -- | Return the principal square root of a complex number.
  cplxSqrt :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxSqrt sym x = do
    (r_part :+ i_part) <- cplxGetParts sym x
    case (asRational r_part :+ asRational i_part)of
      (Just r :+ Just i) | Just z <- tryComplexSqrt tryRationalSqrt (r :+ i) ->
        mkComplexLit sym z

      (_ :+ Just 0) -> do
        c <- realGe sym r_part (realZero sym)
        u <- iteM realIte sym c
          (realSqrt sym r_part)
          (realLit sym 0)
        v <- iteM realIte sym c
          (realLit sym 0)
          (realSqrt sym =<< realNeg sym r_part)
        mkComplex sym (u :+ v)

      _ -> do
        m <- realHypot sym r_part i_part
        m_plus_r <- realAdd sym m r_part
        m_sub_r  <- realSub sym m r_part
        two <- realLit sym 2
        u <- realSqrt sym =<< realDiv sym m_plus_r two
        v <- realSqrt sym =<< realDiv sym m_sub_r  two
        neg_v <- realNeg sym v
        i_part_nonneg <- realIsNonNeg sym i_part
        v' <- realIte sym i_part_nonneg v neg_v
        mkComplex sym (u :+ v')

  -- | Compute sine of a complex number.
  cplxSin :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxSin sym arg = do
    c@(x :+ y) <- cplxGetParts sym arg
    case asRational <$> c of
      (Just 0 :+ Just 0) -> cplxFromReal sym (realZero sym)
      (_ :+ Just 0) -> cplxFromReal sym =<< realSin sym x
      (Just 0 :+ _) -> do
        -- sin(0 + bi) = sin(0) cosh(b) + i*cos(0)sinh(b) = i*sinh(b)
        sinh_y <- realSinh sym y
        mkComplex sym (realZero sym :+ sinh_y)
      _ -> do
        sin_x <- realSin sym x
        cos_x <- realCos sym x
        sinh_y <- realSinh sym y
        cosh_y <- realCosh sym y
        r_part <- realMul sym sin_x cosh_y
        i_part <- realMul sym cos_x sinh_y
        mkComplex sym (r_part :+ i_part)

  -- | Compute cosine of a complex number.
  cplxCos :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxCos sym arg = do
    c@(x :+ y) <- cplxGetParts sym arg
    case asRational <$> c of
      (Just 0 :+ Just 0) -> cplxFromReal sym =<< realLit sym 1
      (_ :+ Just 0) -> cplxFromReal sym =<< realCos sym x
      (Just 0 :+ _) -> do
        -- cos(0 + bi) = cos(0) cosh(b) - i*sin(0)sinh(b) = cosh(b)
        cosh_y    <- realCosh sym y
        cplxFromReal sym cosh_y
      _ -> do
        neg_sin_x <- realNeg sym =<< realSin sym x
        cos_x     <- realCos sym x
        sinh_y    <- realSinh sym y
        cosh_y    <- realCosh sym y
        r_part <- realMul sym cos_x cosh_y
        i_part <- realMul sym neg_sin_x sinh_y
        mkComplex sym (r_part :+ i_part)

  -- | Compute tangent of a complex number.
  cplxTan :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxTan sym arg = do
    c@(x :+ y) <- cplxGetParts sym arg
    case asRational <$> c of
      (Just 0 :+ Just 0) -> cplxFromReal sym (realZero sym)
      (_ :+ Just 0) -> do
        cplxFromReal sym =<< realTan sym x
      (Just 0 :+ _) -> do
        i_part <- realTanh sym y
        mkComplex sym (realZero sym :+ i_part)
      _ -> do
        sin_x <- realSin sym x
        cos_x <- realCos sym x
        sinh_y <- realSinh sym y
        cosh_y <- realCosh sym y
        u <- realMul sym cos_x cosh_y
        v <- realMul sym sin_x sinh_y
        u2 <- realMul sym u u
        v2 <- realMul sym v v
        m <- realAdd sym u2 v2
        sin_x_cos_x   <- realMul sym sin_x cos_x
        sinh_y_cosh_y <- realMul sym sinh_y cosh_y
        r_part <- realDiv sym sin_x_cos_x m
        i_part <- realDiv sym sinh_y_cosh_y m
        mkComplex sym (r_part :+ i_part)

  -- | @hypotCplx x y@ returns @sqrt(abs(x)^2 + abs(y)^2)@.
  cplxHypot :: sym -> SymCplx sym -> SymCplx sym -> IO (SymCplx sym)
  cplxHypot sym x y = do
    (xr :+ xi) <- cplxGetParts sym x
    (yr :+ yi) <- cplxGetParts sym y
    xr2 <- realSq sym xr
    xi2 <- realSq sym xi
    yr2 <- realSq sym yr
    yi2 <- realSq sym yi

    r2 <- foldM (realAdd sym) xr2 [xi2, yr2, yi2]
    cplxFromReal sym =<< realSqrt sym r2

  -- | @roundCplx x@ rounds complex number to nearest integer.
  -- Numbers with a fractional part of 0.5 are rounded away from 0.
  -- Imaginary and real parts are rounded independently.
  cplxRound :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxRound sym x = do
    c <- cplxGetParts sym x
    mkComplex sym =<< traverse (integerToReal sym <=< realRound sym) c

  -- | @cplxFloor x@ rounds to nearest integer less than or equal to x.
  -- Imaginary and real parts are rounded independently.
  cplxFloor :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxFloor sym x =
    mkComplex sym =<< traverse (integerToReal sym <=< realFloor sym)
                  =<< cplxGetParts sym x
  -- | @cplxCeil x@ rounds to nearest integer greater than or equal to x.
  -- Imaginary and real parts are rounded independently.
  cplxCeil :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxCeil sym x =
    mkComplex sym =<< traverse (integerToReal sym <=< realCeil sym)
                  =<< cplxGetParts sym x

  -- | @conjReal x@ returns the complex conjugate of the input.
  cplxConj :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxConj sym x  = do
    r :+ i <- cplxGetParts sym x
    ic <- realNeg sym i
    mkComplex sym (r :+ ic)

  -- | Returns exponential of a complex number.
  cplxExp :: sym -> SymCplx sym -> IO (SymCplx sym)
  cplxExp sym x = do
    (rx :+ i_part) <- cplxGetParts sym x
    expx <- realExp sym rx
    cosx <- realCos sym i_part
    sinx <- realSin sym i_part
    rz <- realMul sym expx cosx
    iz <- realMul sym expx sinx
    mkComplex sym (rz :+ iz)

  -- | Check equality of two complex numbers.
  cplxEq :: sym -> SymCplx sym -> SymCplx sym -> IO (Pred sym)
  cplxEq sym x y = do
    xr :+ xi <- cplxGetParts sym x
    yr :+ yi <- cplxGetParts sym y
    pr <- realEq sym xr yr
    pj <- realEq sym xi yi
    andPred sym pr pj

  -- | Check non-equality of two complex numbers.
  cplxNe :: sym -> SymCplx sym -> SymCplx sym -> IO (Pred sym)
  cplxNe sym x y = do
    xr :+ xi <- cplxGetParts sym x
    yr :+ yi <- cplxGetParts sym y
    pr <- realNe sym xr yr
    pj <- realNe sym xi yi
    orPred sym pr pj


-----------------------------------------------------------------------
-- WordMap operations

data WordMap sym w tp =
     SimpleWordMap !(SymExpr sym
                       (BaseArrayType (EmptyCtx ::> BaseBVType w) BaseBoolType))
                   !(SymExpr sym
                       (BaseArrayType (EmptyCtx ::> BaseBVType w) tp))

emptyWordMap :: (IsExprBuilder sym, 1 <= w)
             => sym
             -> NatRepr w
             -> BaseTypeRepr a
             -> IO (WordMap sym w a)
emptyWordMap sym w tp = do
  let idxRepr = Ctx.singleton (BaseBVRepr w)
  SimpleWordMap <$> constantArray sym idxRepr (falsePred sym)
                <*> baseDefaultValue sym (BaseArrayRepr idxRepr tp)

muxWordMap :: IsExprBuilder sym
           => sym
           -> NatRepr w
           -> BaseTypeRepr a
           -> (Pred sym
               -> WordMap sym w a
               -> WordMap sym w a
               -> IO (WordMap sym w a))
muxWordMap sym _w _tp p (SimpleWordMap bs1 xs1) (SimpleWordMap bs2 xs2) = do
  SimpleWordMap <$> arrayIte sym p bs1 bs2
                <*> arrayIte sym p xs1 xs2


insertWordMap :: IsExprBuilder sym
              => sym
              -> NatRepr w
              -> BaseTypeRepr a
              -> SymBV sym w
              -> SymExpr sym a
              -> WordMap sym w a
              -> IO (WordMap sym w a)
insertWordMap sym _w _ idx v (SimpleWordMap bs xs) = do
  let i = Ctx.singleton idx
  SimpleWordMap <$> arrayUpdate sym bs i (truePred sym)
                <*> arrayUpdate sym xs i v


lookupWordMap :: IsExprBuilder sym
              => sym
              -> NatRepr w
              -> BaseTypeRepr a
              -> SymBV sym w
              -> WordMap sym w a
              -> IO (PartExpr (Pred sym) (SymExpr sym a))
lookupWordMap sym _w _tp idx (SimpleWordMap bs xs) = do
  let i = Ctx.singleton idx
  p <- arrayLookup sym bs i
  case asConstantPred p of
    Just False -> return Unassigned
    _ -> PE p <$> arrayLookup sym xs i

-- | Create a literal from an indexlit.
indexLit :: IsExprBuilder sym => sym -> IndexLit idx -> IO (SymExpr sym idx)
indexLit sym (NatIndexLit i)  = natLit sym i
indexLit sym (BVIndexLit w v) = bvLit sym w v

iteM :: IsExprBuilder sym
        => (sym -> Pred sym -> v -> v -> IO v)
        -> sym -> Pred sym -> IO v -> IO v -> IO v
iteM ite sym p mx my = do
  case asConstantPred p of
    Just True -> mx
    Just False -> my
    Nothing -> join $ ite sym p <$> mx <*> my

-- | Divide one number by another.
--
-- Adds assertion on divide by zero.
cplxDiv :: (IsExprBuilder sym, IsBoolSolver sym)
        => sym
        -> SymCplx sym
        -> SymCplx sym
        -> IO (SymCplx sym)
cplxDiv sym x y = do
  addAssertionM sym (isNonZero sym y) (GenericSimError "Divide by zero")
  xr :+ xi <- cplxGetParts sym x
  yc@(yr :+ yi) <- cplxGetParts sym y
  case asRational <$> yc of
    (_ :+ Just 0) -> do
      zc <- (:+) <$> realDiv sym xr yr <*> realDiv sym xi yr
      mkComplex sym zc
    (Just 0 :+ _) -> do
      zc <- (:+) <$> realDiv sym xi yi <*> realDiv sym xr yi
      mkComplex sym zc
    _ -> do
      yr_abs <- realMul sym yr yr
      yi_abs <- realMul sym yi yi
      y_abs <- realAdd sym yr_abs yi_abs

      zr_1 <- realMul sym xr yr
      zr_2 <- realMul sym xi yi
      zr <- realAdd sym zr_1 zr_2

      zi_1 <- realMul sym xi yr
      zi_2 <- realMul sym xr yi
      zi <- realSub sym zi_1 zi_2

      zc <- (:+) <$> realDiv sym zr y_abs <*> realDiv sym zi y_abs
      mkComplex sym zc

-- | Helper function that returns logarithm of input.
--
-- This operation adds an assertion that the input is non-zero.
cplxLog' :: (IsExprBuilder sym, IsBoolSolver sym)
         => sym -> SymCplx sym -> IO (Complex (SymReal sym))
cplxLog' sym x = do
  let err = GenericSimError "Input to log must be non-zero."
  addAssertionM sym (isNonZero sym x) err
  xr :+ xi <- cplxGetParts sym x
  -- Get the magnitude of the value.
  xm <- realHypot sym xr xi
  -- Get angle of complex number.
  xa <- realAtan2 sym xi xr
  -- Get log of magnitude
  zr <- realLog sym xm
  return $! zr :+ xa

-- | Returns logarithm of input.
--
-- This operation adds an assertion that the input is non-zero.
cplxLog :: (IsExprBuilder sym, IsBoolSolver sym)
        => sym -> SymCplx sym -> IO (SymCplx sym)
cplxLog sym x = mkComplex sym =<< cplxLog' sym x

-- | Returns logarithm of input at a given base.
--
-- This operation adds an assertion that the input is non-zero.
cplxLogBase :: (IsExprBuilder sym, IsBoolSolver sym)
            => Rational
            -> sym
            -> SymCplx sym
            -> IO (SymCplx sym)
cplxLogBase base sym x = do
  b <- realLog sym =<< realLit sym base
  z <- traverse (\r -> realDiv sym r b) =<< cplxLog' sym x
  mkComplex sym z

-- | A function that can be applied to symbolic arguments.
--
-- This type is used by some methods in classes 'IsExprBuilder' and
-- 'IsSymInterface'.
type family SymFn sym :: Ctx BaseType -> BaseType -> *

class IsSymFn fn where
  -- | Get the argument types of a function.
  fnArgTypes :: fn args ret -> Ctx.Assignment BaseTypeRepr args

  -- | Get the return type of a function.
  fnReturnType :: fn args ret -> BaseTypeRepr ret

-- | This extends the interface for building expressions with operations
-- for creating new constants and functions.
class ( IsBoolSolver sym
      , IsExprBuilder sym
      , IsSymFn (SymFn sym)
      , OrdF (SymExpr sym)
      ) => IsSymInterface sym where

  ----------------------------------------------------------------------
  -- Caching operations.

  -- | Stop caching applications.
  stopCaching :: sym -> IO ()

  -- | Restart caching applications.
  -- (clears cache if it is currently caching).
  restartCaching :: sym -> IO ()

  ----------------------------------------------------------------------
  -- Fresh variables

  -- | Create a fresh uninterpreted constant.
  freshConstant :: sym -> SolverSymbol -> BaseTypeRepr tp -> IO (SymExpr sym tp)

  -- | Create a fresh latch.
  freshLatch    :: sym -> SolverSymbol -> BaseTypeRepr tp -> IO (SymExpr sym tp)

  ----------------------------------------------------------------------
  -- Functions needs to support quantifiers.

  -- | Creates a bound variable.
  --
  -- This will be treated as a free constant when appearing inside asserted
  -- expressions.  It can be added to predicates as well.
  freshBoundVar :: sym -> SolverSymbol -> BaseTypeRepr tp -> IO (BoundVar sym tp)

  -- | Return an expression that references the bound variable.
  varExpr :: sym -> BoundVar sym tp -> SymExpr sym tp

  -- | @forallPred sym v e@ returns an expression that repesents @forall v . e@.
  -- Throws a user error if bound var has already been used in a quantifier.
  forallPred :: sym
             -> BoundVar sym tp
             -> Pred sym
             -> IO (Pred sym)

  -- | @existsPred sym v e@ returns an expression that repesents @exists v . e@.
  -- Throws a user error if bound var has already been used in a quantifier.
  existsPred :: sym
             -> BoundVar sym tp
             -> Pred sym
             -> IO (Pred sym)

  ----------------------------------------------------------------------
  -- SymFn operations.

  -- | Return a function defined by an expresion over bound variables.
  -- This allows the user to provide a predicate for determining whether
  -- to evaluate the function.
  definedFn :: sym
            -- ^ Symbolic interface
            -> SolverSymbol
            -- ^ The name to give a function (need not be unique)
            -> Ctx.Assignment (BoundVar sym) args
            -- ^ Bound variables to use as arguments for function.
            -> SymExpr sym ret
            -- ^ Operation defining result of defined function.
            -> (Ctx.Assignment (SymExpr sym) args -> Bool)
               -- ^ Predicate for checking if we should evaluate function.
            -> IO (SymFn sym args ret)

  -- | Return a function defined by Haskell computation over symbolic expressions
  inlineDefineFun :: Ctx.CurryAssignmentClass args
                  => sym
                     -- ^ Symbolic interface
                  -> SolverSymbol
                  -- ^ The name to give a function (need not be unique)
                  -> Ctx.Assignment BaseTypeRepr args
                  -- ^ Arguments for function1

                  -> Ctx.CurryAssignment args (SymExpr sym) (IO (SymExpr sym ret))
                  -- ^ Operation defining result of defined function.
                  -> IO (SymFn sym args ret)
  inlineDefineFun sym nm tps f = do
    -- Create bound variables for function
    vars <- traverseFC (freshBoundVar sym emptySymbol) tps
    -- Call operation on expressions created from variables
    r <- Ctx.uncurryAssignment f (fmapFC (varExpr sym) vars)
    -- Define function
    definedFn sym nm vars r (\_ -> False)

  -- | Create a potentially partial new uninterpreted function
  freshTotalUninterpFn :: forall args ret
                        .  sym
                          -- ^ Symbolic interface
                       -> SolverSymbol
                          -- ^ The name to give a function (need not be unique)
                       -> Ctx.Assignment BaseTypeRepr args
                          -- ^ Types of arguments expected by function
                       -> BaseTypeRepr ret
                           -- ^ Return type of function
                       -> IO (SymFn sym args ret)

  -- | Apply a set of arguments to an symbolic function.
  --
  -- This will automatically add assertions to the current context stating that
  -- the preconditions hold.
  applySymFn :: sym
                -- ^ Symbolic interface
             -> SymFn sym args ret
                -- ^ Function to call
             -> Ctx.Assignment (SymExpr sym) args
                -- ^ Arguments to function
             -> IO (SymExpr sym ret)

------------------------------------------------------------------------
-- IsSymInterface utilities

-- | This returns true if the value corresponds to a concrete value.
baseIsConcrete :: forall sym bt
                . IsExprBuilder sym
               => sym
               -> SymExpr sym bt
               -> IO Bool
baseIsConcrete sym x =
  case exprType x of
    BaseBoolRepr    -> return $ isJust $ asConstantPred x
    BaseNatRepr     -> return $ isJust $ asNat x
    BaseIntegerRepr -> return $ isJust $ asInteger x
    BaseBVRepr _    -> return $ isJust $ asUnsignedBV x
    BaseRealRepr    -> return $ isJust $ asRational x
    BaseComplexRepr -> return $ isJust $ asComplex x
    BaseStructRepr (flds ::Ctx.Assignment BaseTypeRepr ctx) ->
        Ctx.forIndex (Ctx.size flds) f (return True)
      where f :: IO Bool -> Ctx.Index ctx tp -> IO Bool
            f b i = (&&) <$> b <*> (baseIsConcrete sym =<< structField sym x i)
    BaseArrayRepr _ _bt' -> do
      case asConstantArray x of
        Just x' -> baseIsConcrete sym x'
        Nothing -> return $ False

baseDefaultValue :: forall sym bt
                  . IsExprBuilder sym
                 => sym
                 -> BaseTypeRepr bt
                 -> IO (SymExpr sym bt)
baseDefaultValue sym bt =
  case bt of
    BaseBoolRepr    -> return $! falsePred sym
    BaseNatRepr     -> natLit sym 0
    BaseIntegerRepr -> intLit sym 0
    BaseBVRepr w    -> bvLit sym w 0
    BaseRealRepr    -> return $! realZero sym
    BaseComplexRepr -> mkComplexLit sym (0 :+ 0)
    BaseStructRepr flds -> do
      let f :: BaseTypeRepr tp -> IO (SymExpr sym tp)
          f v = baseDefaultValue sym v
      mkStruct sym =<< traverseFC f flds
    BaseArrayRepr idx bt' -> do
      elt <- baseDefaultValue sym bt'
      constantArray sym idx elt

addAssertionM :: IsBoolSolver sym
              => sym
              -> IO (Pred sym)
              -> SimErrorReason
              -> IO ()
addAssertionM sym pf msg = do
  p <- pf
  addAssertion sym p msg

-- | Return predicate equivalent to a Boolean.
backendPred :: IsBoolExprBuilder sym => sym -> Bool -> Pred sym
backendPred sym True  = truePred  sym
backendPred sym False = falsePred sym

-- | Create a value from a rational.
mkRational :: IsExprBuilder sym => sym -> Rational -> IO (SymCplx sym)
mkRational sym v = mkComplexLit sym (v :+ 0)

-- | Create a value from an integer.
mkReal  :: (IsExprBuilder sym, Real a) => sym -> a -> IO (SymCplx sym)
mkReal sym v = mkRational sym (toRational v)

-- | Return 1 if the predicate is true; 0 otherwise.
predToReal :: IsExprBuilder sym => sym -> Pred sym -> IO (SymReal sym)
predToReal sym p = do
  r1 <- realLit sym 1
  realIte sym p r1 (realZero sym)

-- | Extract the value of a rational expression; fail if the
--   value is not a constant.
realExprAsRational :: (Monad m, IsExpr e) => e BaseRealType -> m Rational
realExprAsRational x = do
  case asRational x of
    Just r -> return r
    Nothing -> fail "Value is not a constant expression."

-- | Extract the value of a complex expression, which is assumed
--   to be a constant real number.  Fail if the number has nonzero
--   imaginary component, or if it is not a constant.
cplxExprAsRational :: (Monad m, IsExpr e) => e BaseComplexType -> m Rational
cplxExprAsRational x = do
  case asComplex x of
    Just (r :+ i) -> do
      when (i /= 0) $
        fail "Complex value has an imaginary part."
      return r
    Nothing -> do
      fail "Complex value is not a constant expression."

-- | Return a complex value as a constant integer if it exists.
cplxExprAsInteger :: (Monad m, IsExpr e) => e BaseComplexType -> m Integer
cplxExprAsInteger x = rationalAsInteger =<< cplxExprAsRational x

-- | Return value as a constant integer if it exists.
rationalAsInteger :: Monad m => Rational -> m Integer
rationalAsInteger r = do
  when (denominator r /= 1) $ do
    fail "Value is not an integer."
  return (numerator r)

assertIsInteger :: IsSymInterface sym
                => sym
                -> SymReal sym
                -> SimErrorReason
                -> IO ()
assertIsInteger sym v msg = do
  addAssertionM sym (isInteger sym v) msg

-- | Return value as a constant integer if it exists.
realExprAsInteger :: (IsExpr e, Monad m) => e BaseRealType -> m Integer
realExprAsInteger x =
  rationalAsInteger =<< realExprAsRational x

-- | Return value as a constant integer if it exists.
realExprAsNat :: (IsExpr e, Monad m) => e BaseRealType -> m Natural
realExprAsNat x =
  fromInteger <$> (rationalAsInteger =<< realExprAsRational x)

-- | Return value as a constant integer if it exists.
cplxExprAsNat :: (IsExpr e, Monad m) => e BaseComplexType -> m Natural
cplxExprAsNat x = fromInteger <$> cplxExprAsInteger x

andAllOf :: IsBoolExprBuilder sym
         => sym
         -> Fold s (Pred sym)
         -> s
         -> IO (Pred sym)
andAllOf sym f s = foldlMOf f (andPred sym) (truePred sym) s

-- | Return predicate that holds if value is non-zero.
isNonZero :: IsExprBuilder sym => sym -> SymCplx sym -> IO (Pred sym)
isNonZero sym v = cplxNe sym v =<< mkRational sym 0

-- | Return predicate that holds if imaginary part of number is zero.
isReal :: IsExprBuilder sym => sym -> SymCplx sym -> IO (Pred sym)
isReal sym v = do
  i <- getImagPart sym v
  realEq sym i (realZero sym)

------------------------------------------------------------------------
-- muxIntegerRange

{-# INLINABLE muxIntegerRange #-}
-- | This function is used for selecting a value from among potential values in a
-- range.
--
-- 'muxIntegerRange p ite f l h' returns an expression denoting the value obtained
-- from the value 'f i' where 'i' is the smallest value in the range '[l..h]' such that
-- 'p i' is true.  If 'p i' is true for no such value then, this returns the value 'f h'.
muxIntegerRange :: Monad m
                => (Integer -> m (e BaseBoolType))
                   -- ^ Returns predicate that holds if we have found the value we are looking
                   -- for.  It is assumed that the predicate must hold for a unique integer in
                   -- the range.
                -> (e BaseBoolType -> a -> a -> m a)
                   -- ^ Ite function
                -> (Integer -> m a)
                   -- ^ Function for concrete values.
                -> Integer -- ^ Lower bound (inclusive)
                -> Integer -- ^ Upper bound (inclusive)
                -> m a
muxIntegerRange predFn iteFn f l h
  | l < h = do
    c <- predFn l
    match_branch <- f l
    other_branch <- muxIntegerRange predFn iteFn f (succ l) h
    iteFn c match_branch other_branch
  | otherwise = f h

-- | This provides an interface for converting between Haskell values and a
-- solver representation.
data SymEncoder sym v tp
   = SymEncoder { symEncoderType :: !(BaseTypeRepr tp)
                , symFromExpr :: !(sym -> SymExpr sym tp -> IO v)
                , symToExpr   :: !(sym -> v -> IO (SymExpr sym tp))
                }
