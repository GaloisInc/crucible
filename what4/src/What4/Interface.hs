{-|
Module           : What4.Interface
Copyright        : (c) Galois, Inc 2014-2018
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

  [@instance 'IsExprBuilder' sym@]
  Functions for building expressions of various types.

  [@instance 'IsSymExprBuilder' sym@]
  Functions for building expressions with bound variables and quantifiers.

  [@instance 'IsExpr' ('SymExpr' sym)@]
  Recognizers for various kinds of literal expressions.

  [@instance 'OrdF' ('SymExpr' sym)@]

  [@instance 'TestEquality' ('SymExpr' sym)@]

  [@instance 'HashableF' ('SymExpr' sym)@]

The canonical implementation of these interface classes is found in "What4.Expr.Builder".
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module What4.Interface
  ( -- * Interface classes
    -- ** Type Families
    SymExpr
  , BoundVar
  , SymFn
  , SymAnnotation

    -- ** Expression recognizers
  , IsExpr(..)
  , IsSymFn(..)

    -- ** IsExprBuilder
  , IsExprBuilder(..)
  , IsSymExprBuilder(..)
  , SolverEvent(..)

    -- ** Bitvector operations
  , bvJoinVector
  , bvSplitVector
  , bvSwap
  , bvBitreverse

    -- ** Floating-point rounding modes
  , RoundingMode(..)

    -- ** Run-time statistics
  , Statistics(..)
  , zeroStatistics

    -- * Type Aliases
  , Pred
  , SymNat
  , SymInteger
  , SymReal
  , SymFloat
  , SymString
  , SymCplx
  , SymStruct
  , SymBV
  , SymArray

    -- * Array utility types
  , IndexLit(..)
  , indexLit
  , ArrayResultWrapper(..)

    -- * Concrete values
  , asConcrete
  , concreteToSym
  , baseIsConcrete
  , baseDefaultValue
  , realExprAsInteger
  , rationalAsInteger
  , cplxExprAsRational
  , cplxExprAsInteger

    -- * SymEncoder
  , SymEncoder(..)

    -- * Utilitity combinators
    -- ** Boolean operations
  , backendPred
  , andAllOf
  , orOneOf
  , itePredM
  , iteM
  , predToReal

    -- ** Complex number operations
  , cplxDiv
  , cplxLog
  , cplxLogBase
  , mkRational
  , mkReal
  , isNonZero
  , isReal

    -- ** Indexing
  , muxRange

    -- * Reexports
  , module Data.Parameterized.NatRepr
  , module What4.BaseTypes
  , What4.Symbol.SolverSymbol
  , What4.Symbol.emptySymbol
  , What4.Symbol.userSymbol
  , What4.Symbol.safeSymbol
  , NatValueRange(..)
  , ValueRange(..)
  , StringLiteral(..)
  , stringLiteralInfo
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Bits
import           Data.Coerce (coerce)
import           Data.Foldable
import           Data.Hashable
import           Data.Kind ( Type )
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.Utils.Endian (Endian(..))
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Vector as Vector
import           Data.Ratio
import           Data.Scientific (Scientific)
import           GHC.Generics (Generic)
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen (Doc)

import           What4.BaseTypes
import           What4.Config
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.IndexLit
import           What4.ProgramLoc
import           What4.Concrete
import           What4.SatResult
import           What4.Symbol
import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import           What4.Utils.Complex
import           What4.Utils.StringLiteral

------------------------------------------------------------------------
-- SymExpr names

type Pred sym = SymExpr sym BaseBoolType

-- | Symbolic natural numbers.
type SymNat sym = SymExpr sym BaseNatType

-- | Symbolic integers.
type SymInteger sym = SymExpr sym BaseIntegerType

-- | Symbolic real numbers.
type SymReal sym = SymExpr sym BaseRealType

-- | Symbolic floating point numbers.
type SymFloat sym fpp = SymExpr sym (BaseFloatType fpp)

-- | Symbolic complex numbers.
type SymCplx sym = SymExpr sym BaseComplexType

-- | Symbolic structures.
type SymStruct sym flds = SymExpr sym (BaseStructType flds)

-- | Symbolic arrays.
type SymArray sym idx b = SymExpr sym (BaseArrayType idx b)

-- | Symbolic bitvectors.
type SymBV sym n = SymExpr sym (BaseBVType n)

-- | Symbolic strings.
type SymString sym si = SymExpr sym (BaseStringType si)

------------------------------------------------------------------------
-- Type families for the interface.

-- | The class for expressions.
type family SymExpr (sym :: Type) :: BaseType -> Type

-- | The class of term annotations
type family SymAnnotation (sym :: Type) :: BaseType -> Type

------------------------------------------------------------------------
-- | Type of bound variable associated with symbolic state.
--
-- This type is used by some methods in class 'IsSymExprBuilder'.
type family BoundVar (sym :: Type) :: BaseType -> Type


------------------------------------------------------------------------
-- IsBoolSolver

-- | Perform an ite on a predicate lazily.
itePredM :: (IsExpr (SymExpr sym), IsExprBuilder sym, MonadIO m)
         => sym
         -> Pred sym
         -> m (Pred sym)
         -> m (Pred sym)
         -> m (Pred sym)
itePredM sym c mx my =
  case asConstantPred c of
    Just True -> mx
    Just False -> my
    Nothing -> do
      x <- mx
      y <- my
      liftIO $ itePred sym c x y

------------------------------------------------------------------------
-- IsExpr

-- | This class provides operations for recognizing when symbolic expressions
--   represent concrete values, extracting the type from an expression,
--   and for providing pretty-printed representations of an expression.
class IsExpr e where
  -- | Evaluate if predicate is constant.
  asConstantPred :: e BaseBoolType -> Maybe Bool
  asConstantPred _ = Nothing

  -- | Return nat if this is a constant natural number.
  asNat :: e BaseNatType -> Maybe Natural
  asNat _ = Nothing

  -- | Return any bounding information we have about the term
  natBounds :: e BaseNatType -> NatValueRange

  -- | Return integer if this is a constant integer.
  asInteger :: e BaseIntegerType -> Maybe Integer
  asInteger _ = Nothing

  -- | Return any bounding information we have about the term
  integerBounds :: e BaseIntegerType -> ValueRange Integer

  -- | Return rational if this is a constant value.
  asRational :: e BaseRealType -> Maybe Rational
  asRational _ = Nothing

  -- | Return any bounding information we have about the term
  rationalBounds :: e BaseRealType -> ValueRange Rational

  -- | Return complex if this is a constant value.
  asComplex :: e BaseComplexType -> Maybe (Complex Rational)
  asComplex _ = Nothing

  -- | Return the unsigned value if this is a constant bitvector.
  asUnsignedBV :: e (BaseBVType w) -> Maybe Integer
  asUnsignedBV _ = Nothing

  -- | Return the signed value if this is a constant bitvector.
  asSignedBV   :: (1 <= w) => e (BaseBVType w) -> Maybe Integer
  asSignedBV _ = Nothing

  -- | If we have bounds information about the term, return unsigned upper and lower bounds
  unsignedBVBounds :: (1 <= w) => e (BaseBVType w) -> Maybe (Integer, Integer)

  -- | If we have bounds information about the term, return signed upper and lower bounds
  signedBVBounds :: (1 <= w) => e (BaseBVType w) -> Maybe (Integer, Integer)

  asAffineVar :: e tp -> Maybe (ConcreteVal tp, e tp, ConcreteVal tp)

  -- | Return the string value if this is a constant string
  asString :: e (BaseStringType si) -> Maybe (StringLiteral si)
  asString _ = Nothing

  stringInfo :: e (BaseStringType si) -> StringInfoRepr si
  stringInfo e =
    case exprType e of
      BaseStringRepr si -> si

  -- | Return the unique element value if this is a constant array,
  --   such as one made with 'constantArray'.
  asConstantArray :: e (BaseArrayType idx bt) -> Maybe (e bt)
  asConstantArray _ = Nothing

  -- | Return the struct fields if this is a concrete struct.
  asStruct :: e (BaseStructType flds) -> Maybe (Ctx.Assignment e flds)
  asStruct _ = Nothing

  -- | Get type of expression.
  exprType :: e tp -> BaseTypeRepr tp

  -- | Get the width of a bitvector
  bvWidth      :: e (BaseBVType w) -> NatRepr w
  bvWidth e =
    case exprType e of
      BaseBVRepr w -> w

  -- | Print a sym expression for debugging or display purposes.
  printSymExpr :: e tp -> Doc


newtype ArrayResultWrapper f idx tp =
  ArrayResultWrapper { unwrapArrayResult :: f (BaseArrayType idx tp) }

instance TestEquality f => TestEquality (ArrayResultWrapper f idx) where
  testEquality (ArrayResultWrapper x) (ArrayResultWrapper y) = do
    Refl <- testEquality x y
    return Refl

instance HashableF e => HashableF (ArrayResultWrapper e idx) where
  hashWithSaltF s (ArrayResultWrapper v) = hashWithSaltF s v


-- | This datatype describes events that involve interacting with
--   solvers.  A @SolverEvent@ will be provided to the action
--   installed via @setSolverLogListener@ whenever an interesting
--   event occurs.
data SolverEvent
  = SolverStartSATQuery
    { satQuerySolverName :: !String
    , satQueryReason     :: !String
    }
  | SolverEndSATQuery
    { satQueryResult     :: !(SatResult () ())
    , satQueryError      :: !(Maybe String)
    }
 deriving (Show, Generic)

------------------------------------------------------------------------
-- IsExprBuilder

-- | This class allows the simulator to build symbolic expressions.
--
-- Methods of this class refer to type families @'SymExpr' sym@
-- and @'SymFn' sym@.
--
-- Note: Some methods in this class represent operations that are
-- partial functions on their domain (e.g., division by 0).
-- Such functions will have documentation strings indicating that they
-- are undefined under some conditions.
--
-- The behavior of these functions is generally to throw an error
-- if it is concretely obvious that the function results in an undefined
-- value; but otherwise they will silently produce an unspecified value
-- of the expected type.
class (IsExpr (SymExpr sym), HashableF (SymExpr sym)) => IsExprBuilder sym where

  -- | Retrieve the configuration object corresponding to this solver interface.
  getConfiguration :: sym -> Config


  -- | Install an action that will be invoked before and after calls to
  --   backend solvers.  This action is primarily intended to be used for
  --   logging\/profiling\/debugging purposes.  Passing 'Nothing' to this
  --   function disables logging.
  setSolverLogListener :: sym -> Maybe (SolverEvent -> IO ()) -> IO ()

  -- | Get the currently-installed solver log listener, if one has been installed.
  getSolverLogListener :: sym -> IO (Maybe (SolverEvent -> IO ()))

  -- | Provide the given even to the currently installed
  --   solver log listener, if any.
  logSolverEvent :: sym -> SolverEvent -> IO ()

  -- | Get statistics on execution from the initialization of the
  -- symbolic interface to this point.  May return zeros if gathering
  -- statistics isn't supported.
  getStatistics :: sym -> IO Statistics
  getStatistics _ = return zeroStatistics

  ----------------------------------------------------------------------
  -- Program location operations

  -- | Get current location of program for term creation purposes.
  getCurrentProgramLoc :: sym -> IO ProgramLoc

  -- | Set current location of program for term creation purposes.
  setCurrentProgramLoc :: sym -> ProgramLoc -> IO ()

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
      BaseFloatRepr{}  -> floatEq sym x y
      BaseComplexRepr  -> cplxEq sym x y
      BaseStringRepr{} -> stringEq sym x y
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
      BaseFloatRepr{}  -> floatIte  sym c x y
      BaseStringRepr{} -> stringIte sym c x y
      BaseComplexRepr  -> cplxIte   sym c x y
      BaseStructRepr{} -> structIte sym c x y
      BaseArrayRepr{}  -> arrayIte  sym c x y


  -- | Add an annotation to the given symbolic expression.  This annotation
  --   does not affect the semantics of the term, but can later be
  --   accessed when the term is traversed.
  annotateTerm :: sym -> SymAnnotation sym tp -> SymExpr sym tp -> IO (SymExpr sym tp)

  ----------------------------------------------------------------------
  -- Boolean operations.

  -- | Constant true predicate
  truePred  :: sym -> Pred sym

  -- | Constant false predicate
  falsePred :: sym -> Pred sym

  -- | Boolean negation
  notPred :: sym -> Pred sym -> IO (Pred sym)

  -- | Boolean conjunction
  andPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  -- | Boolean disjunction
  orPred  :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  -- | Boolean implication
  impliesPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)
  impliesPred sym x y = do
    nx <- notPred sym x
    orPred sym y nx

  -- | Exclusive-or operation
  xorPred :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  -- | Equality of boolean values
  eqPred  :: sym -> Pred sym -> Pred sym -> IO (Pred sym)

  -- | If-then-else on a predicate.
  itePred :: sym -> Pred sym -> Pred sym -> Pred sym -> IO (Pred sym)

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

  -- | @'natDiv' sym x y@ performs division on naturals.
  --
  -- The result is undefined if @y@ equals @0@.
  --
  -- 'natDiv' and 'natMod' satisfy the property that given
  --
  -- @
  --   d <- natDiv sym x y
  --   m <- natMod sym x y
  -- @
  --
  --  and @y > 0@, we have that @y * d + m = x@ and @m < y@.
  natDiv :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | @'natMod' sym x y@ returns @x@ mod @y@.
  --
  -- See 'natDiv' for a description of the properties the return
  -- value is expected to satisfy.
  natMod :: sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | If-then-else applied to natural numbers.
  natIte :: sym -> Pred sym -> SymNat sym -> SymNat sym -> IO (SymNat sym)

  -- | Equality predicate for natural numbers.
  natEq :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)

  -- | @'natLe' sym x y@ returns @true@ if @x <= y@.
  natLe :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)

  -- | @'natLt' sym x y@ returns @true@ if @x < y@.
  natLt :: sym -> SymNat sym -> SymNat sym -> IO (Pred sym)
  natLt sym x y = notPred sym =<< natLe sym y x

  ----------------------------------------------------------------------
  -- Integer operations

  -- | Create an integer literal.
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

  -- | If-then-else applied to integers.
  intIte :: sym -> Pred sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | Integer equality.
  intEq  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)

  -- | Integer less-than-or-equal.
  intLe  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)

  -- | Integer less-than.
  intLt  :: sym -> SymInteger sym -> SymInteger sym -> IO (Pred sym)
  intLt sym x y = notPred sym =<< intLe sym y x

  -- | Compute the absolute value of an integer.
  intAbs :: sym -> SymInteger sym -> IO (SymInteger sym)

  -- | @intDiv x y@ computes the integer division of @x@ by @y@.  This division is
  --   interpreted the same way as the SMT-Lib integer theory, which states that
  --   @div@ and @mod@ are the unique Eucledian division operations satisfying the
  --   following for all @y /= 0@:
  --
  --   * @x * (div x y) + (mod x y) == x@
  --   * @ 0 <= mod x y < abs y@
  --
  --   The value of @intDiv x y@ is undefined when @y = 0@.
  --
  --   Integer division requires nonlinear support whenever the divisor is
  --   not a constant.
  --
  --   Note: @div x y@ is @floor (x/y)@ when @y@ is positive
  --   (regardless of sign of @x@) and @ceiling (x/y)@ when @y@ is
  --   negative.  This is neither of the more common "round toward
  --   zero" nor "round toward -inf" definitions.
  --
  --   Some useful theorems that are true of this division/modulus pair:
  --    * @mod x y == mod x (- y) == mod x (abs y)@
  --    * @div x (-y) == -(div x y)@
  intDiv :: sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | @intMod x y@ computes the integer modulus of @x@ by @y@.  See 'intDiv' for
  --   more details.
  --
  --   The value of @intMod x y@ is undefined when @y = 0@.
  --
  --   Integer modulus requires nonlinear support whenever the divisor is
  --   not a constant.
  intMod :: sym -> SymInteger sym -> SymInteger sym -> IO (SymInteger sym)

  -- | @intDivisible x k@ is true whenever @x@ is an integer divisible
  --   by the known natural number @k@.  In other words `divisible x k`
  --   holds if there exists an integer `z` such that `x = k*z`.
  intDivisible :: sym -> SymInteger sym -> Natural -> IO (Pred sym)

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
  bvSelect :: forall idx n w. (1 <= n, idx + n <= w)
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
  --
  --   The result of @bvUdiv x y@ is undefined when @y@ is zero,
  --   but is otherwise equal to @floor( x / y )@.
  bvUdiv :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Unsigned bitvector remainder.
  --
  --   The result of @bvUrem x y@ is undefined when @y@ is zero,
  --   but is otherwise equal to @x - (bvUdiv x y) * y@.
  bvUrem :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Signed bitvector division.  The result is truncated to zero.
  --
  --   The result of @bvSdiv x y@ is undefined when @y@ is zero,
  --   but is equal to @floor(x/y)@ when @x@ and @y@ have the same sign,
  --   and equal to @ceiling(x/y)@ when @x@ and @y@ have opposite signs.
  --
  --   NOTE! However, that there is a corner case when dividing @MIN_INT@ by
  --   @-1@, in which case an overflow condition occurs, and the result is instead
  --   @MIN_INT@.
  bvSdiv :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Signed bitvector remainder.
  --
  --   The result of @bvSrem x y@ is undefined when @y@ is zero, but is
  --   otherwise equal to @x - (bvSdiv x y) * y@.
  bvSrem :: (1 <= w)
         => sym
         -> SymBV sym w
         -> SymBV sym w
         -> IO (SymBV sym w)

  -- | Returns true if the corresponding bit in the bitvector is set.
  testBitBV :: (1 <= w)
            => sym
            -> Natural -- ^ Index of bit (0 is the least significant bit)
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

  -- | Left shift.  The shift amount is treated as an unsigned value.
  bvShl :: (1 <= w) => sym ->
                       SymBV sym w {- ^ Shift this -} ->
                       SymBV sym w {- ^ Amount to shift by -} ->
                       IO (SymBV sym w)

  -- | Logical right shift.  The shift amount is treated as an unsigned value.
  bvLshr :: (1 <= w) => sym ->
                        SymBV sym w {- ^ Shift this -} ->
                        SymBV sym w {- ^ Amount to shift by -} ->
                        IO (SymBV sym w)

  -- | Arithmetic right shift.  The shift amount is treated as a
  -- signed value, and a negative shift value indicates a left shift.
  bvAshr :: (1 <= w) => sym ->
                        SymBV sym w {- ^ Shift this -} ->
                        SymBV sym w {- ^ Amount to shift by -} ->
                        IO (SymBV sym w)

  -- | Rotate left.  The rotate amount is treated as an unsigned value.
  bvRol :: (1 <= w) =>
    sym ->
    SymBV sym w {- ^ bitvector to rotate -} ->
    SymBV sym w {- ^ amount to rotate by -} ->
    IO (SymBV sym w)

  -- | Rotate right.  The rotate amount is treated as an unsigned value.
  bvRor :: (1 <= w) =>
    sym ->
    SymBV sym w {- ^ bitvector to rotate -} ->
    SymBV sym w {- ^ amount to rotate by -} ->
    IO (SymBV sym w)

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
  bvTrunc sym w x
    | LeqProof <- leqTrans
        (addIsLeq w (knownNat @1))
        (leqProof (incNat w) (bvWidth x))
    = bvSelect sym (knownNat @0) w x

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
        -> SymBV sym w -- ^ Bitvector to update
        -> Natural     -- ^ 0-based index to set
        -> Pred sym    -- ^ Predicate to set.
        -> IO (SymBV sym w)
  bvSet sym v i p = assert (i < natValue (bvWidth v)) $
    -- NB, this representation based on AND/XOR structure is designed so that a
    -- sequence of bvSet operations will collapse nicely into a xor-linear combination
    -- of the original term and bvFill terms. It has the nice property that we
    -- do not introduce any additional subterm sharing.
    do let w    = bvWidth v
       let mask = bit (fromIntegral i)
       pbits <- bvFill sym w p
       vbits <- bvAndBits sym v =<< bvLit sym w (complement mask)
       bvXorBits sym vbits =<< bvAndBits sym pbits =<< bvLit sym w mask

  -- | @bvFill sym w p@ returns a bitvector @w@-bits long where every bit
  --   is given by the boolean value of @p@.
  bvFill :: forall w. (1 <= w) =>
    sym       {-^ symbolic interface -} ->
    NatRepr w {-^ output bitvector width -} ->
    Pred sym  {-^ predicate to fill the bitvector with -} ->
    IO (SymBV sym w)

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

  -- | Return the number of 1 bits in the input.
  bvPopcount :: (1 <= w) => sym -> SymBV sym w -> IO (SymBV sym w)

  -- | Return the number of consecutive 0 bits in the input, starting from
  --   the most significant bit position.  If the input is zero, all bits are counted
  --   as leading.
  bvCountLeadingZeros :: (1 <= w) => sym -> SymBV sym w -> IO (SymBV sym w)

  -- | Return the number of consecutive 0 bits in the input, starting from
  --   the least significant bit position.  If the input is zero, all bits are counted
  --   as leading.
  bvCountTrailingZeros :: (1 <= w) => sym -> SymBV sym w -> IO (SymBV sym w)

  -- | Unsigned add with overflow bit.
  addUnsignedOF :: (1 <= w)
                => sym
                -> SymBV sym w
                -> SymBV sym w
                -> IO (Pred sym, SymBV sym w)
  addUnsignedOF sym x y = do
    -- Compute result
    r   <- bvAdd sym x y
    -- Return that this overflows if r is less than either x or y
    ovx  <- bvUlt sym r x
    ovy  <- bvUlt sym r y
    ov   <- orPred sym ovx ovy
    return (ov, r)

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

  -- | Unsigned subtract with overflow bit. Overflow is true if x < y.
  subUnsignedOF ::
    (1 <= w) =>
    sym ->
    SymBV sym w ->
    SymBV sym w ->
    IO (Pred sym, SymBV sym w)
  subUnsignedOF sym x y = do
    xy <- bvSub sym x y
    ov <- bvUlt sym x y
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


  -- | Compute the carryless multiply of the two input bitvectors.
  --   This operation is essentially the same as a standard multiply, except that
  --   the partial addends are simply XOR'd together instead of using a standard
  --   adder.  This operation is useful for computing on GF(2^n) polynomials.
  carrylessMultiply ::
    (1 <= w) =>
    sym ->
    SymBV sym w ->
    SymBV sym w ->
    IO (SymBV sym (w+w))
  carrylessMultiply sym x0 y0
    | Just _  <- asUnsignedBV x0
    , Nothing <- asUnsignedBV y0
    = go y0 x0
    | otherwise
    = go x0 y0
   where
   go :: (1 <= w) => SymBV sym w -> SymBV sym w -> IO (SymBV sym (w+w))
   go x y =
    do let w = bvWidth x
       let w2 = addNat w w
       Just LeqProof <- return (testLeq (knownNat @1) w2)
       Just LeqProof <- return (testLeq (addNat w (knownNat @1)) w2)
       z  <- bvLit sym w2 0
       x' <- bvZext sym w2 x
       xs <- sequence [ do p <- testBitBV sym i y
                           iteM bvIte sym
                             p
                             (bvShl sym x' =<< bvLit sym w2 (toInteger i))
                             (return z)
                      | i <- [ 0 .. natValue w - 1 ]
                      ]
       foldM (bvXorBits sym) z xs

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
       n   <- bvLit sym dbl_w (intValue w)
       hi  <- bvTrunc sym w =<< bvLshr sym s n
       return (hi, lo)

  -- | Compute the unsigned multiply of two values with overflow bit.
  mulUnsignedOF ::
    (1 <= w) =>
    sym ->
    SymBV sym w ->
    SymBV sym w ->
    IO (Pred sym, SymBV sym w)
  mulUnsignedOF sym x y =
    do let w = bvWidth x
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

       -- overflow if the result is greater than the max representable value in w bits
       ov  <- bvUgt sym s =<< bvLit sym dbl_w (maxUnsigned w)

       return (ov, lo)

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

  -- | Compute the signed multiply of two values with overflow bit.
  mulSignedOF ::
    (1 <= w) =>
    sym ->
    SymBV sym w ->
    SymBV sym w ->
    IO (Pred sym, SymBV sym w)
  mulSignedOF sym x y =
    do let w = bvWidth x
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

       -- overflow if greater or less than max representable values
       ov1 <- bvSlt sym s =<< bvLit sym dbl_w (minSigned w)
       ov2 <- bvSgt sym s =<< bvLit sym dbl_w (maxSigned w)
       ov  <- orPred sym ov1 ov2
       return (ov, lo)

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
  -- for equality when provided to backend solvers.
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
  -- This is implemented, but designed to be overridden for efficiency.
  arrayFromMap :: sym
               -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
                  -- ^ Types for indices
               -> AUM.ArrayUpdateMap (SymExpr sym) (idx ::> itp) tp
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
                       -> AUM.ArrayUpdateMap (SymExpr sym) (idx ::> itp) tp
                       -- ^ Value for known indices.
                       -> SymArray sym (idx ::> itp) tp
                       -- ^ Value for existing array.
                       -> IO (SymArray sym (idx ::> itp) tp)
  arrayUpdateAtIdxLits sym m a0 = do
    let updateAt a (i,v) = do
          idx <-  traverseFC (indexLit sym) i
          arrayUpdate sym a idx v
    foldlM updateAt a0 (AUM.toList m)

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

  -- | Convert the unsigned value of a bitvector to a natural.
  bvToNat :: (1 <= w) => sym -> SymBV sym w -> IO (SymNat sym)

  -- | Return the unsigned value of the given bitvector as an integer.
  bvToInteger :: (1 <= w) => sym -> SymBV sym w -> IO (SymInteger sym)

  -- | Return the signed value of the given bitvector as an integer.
  sbvToInteger :: (1 <= w) => sym -> SymBV sym w -> IO (SymInteger sym)

  -- | Return @1@ if the predicate is true; @0@ otherwise.
  predToBV :: (1 <= w) => sym -> Pred sym -> NatRepr w -> IO (SymBV sym w)

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
  --
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  realRound :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Round down to the nearest integer that is at most this value.
  realFloor :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Round up to the nearest integer that is at least this value.
  realCeil :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Convert an integer to a bitvector.  The result is the unique bitvector
  --   whose value (signed or unsigned) is congruent to the input integer, modulo @2^w@.
  --
  --   This operation has the following properties:
  --   *  @bvToInteger (integerToBv x w) == mod x (2^w)@
  --   *  @bvToInteger (integerToBV x w) == x@     when @0 <= x < 2^w@.
  --   *  @sbvToInteger (integerToBV x w) == mod (x + 2^(w-1)) (2^w) - 2^(w-1)@
  --   *  @sbvToInteger (integerToBV x w) == x@    when @-2^(w-1) <= x < 2^(w-1)@
  --   *  @integerToBV (bvToInteger y) w == y@     when @y@ is a @SymBV sym w@
  --   *  @integerToBV (sbvToInteger y) w == y@    when @y@ is a @SymBV sym w@
  integerToBV :: (1 <= w) => sym -> SymInteger sym -> NatRepr w -> IO (SymBV sym w)

  ----------------------------------------------------------------------
  -- Lossy (non-injective) combinators

  -- | Convert an integer to a natural number.
  --
  -- For negative integers, the result is undefined.
  integerToNat :: sym -> SymInteger sym -> IO (SymNat sym)

  -- | Convert a real number to an integer.
  --
  -- The result is undefined if the given real number does not represent an integer.
  realToInteger :: sym -> SymReal sym -> IO (SymInteger sym)

  -- | Convert a real number to a natural number.
  --
  -- The result is undefined if the given real number does not represent a natural number.
  realToNat :: sym -> SymReal sym -> IO (SymNat sym)
  realToNat sym r = realToInteger sym r >>= integerToNat sym

  -- | Convert a real number to an unsigned bitvector.
  --
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  -- When the real is negative the result is zero.
  realToBV :: (1 <= w) => sym -> SymReal sym -> NatRepr w -> IO (SymBV sym w)
  realToBV sym r w = do
    i <- realRound sym r
    clampedIntToBV sym i w

  -- | Convert a real number to a signed bitvector.
  --
  -- Numbers are rounded to the nearest representable number, with rounding away from
  -- zero when two integers are equi-distant (e.g., 1.5 rounds to 2).
  realToSBV  :: (1 <= w) => sym -> SymReal sym -> NatRepr w -> IO (SymBV sym w)
  realToSBV sym r w  = do
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
          integerToBV sym i w

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

  ----------------------------------------------------------------------
  -- Bitvector operations.

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
  -- String operations

  -- | Create an empty string literal
  stringEmpty :: sym -> StringInfoRepr si -> IO (SymString sym si)

  -- | Create a concrete string literal
  stringLit :: sym -> StringLiteral si -> IO (SymString sym si)

  -- | Check the equality of two strings
  stringEq :: sym -> SymString sym si -> SymString sym si -> IO (Pred sym)

  -- | If-then-else on strings
  stringIte :: sym -> Pred sym -> SymString sym si -> SymString sym si -> IO (SymString sym si)

  -- | Concatenate two strings
  stringConcat :: sym -> SymString sym si -> SymString sym si -> IO (SymString sym si)

  -- | Test if the first string contains the second string as a substring
  stringContains :: sym -> SymString sym si -> SymString sym si -> IO (Pred sym)

  -- | Test if the first string is a prefix of the second string
  stringIsPrefixOf :: sym -> SymString sym si -> SymString sym si -> IO (Pred sym)

  -- | Test if the first string is a suffix of the second string
  stringIsSuffixOf :: sym -> SymString sym si -> SymString sym si -> IO (Pred sym)

  -- | Return the first position at which the second string can be found as a substring
  --   in the first string, starting from the given index.
  --   If no such position exists, return a negative value.
  stringIndexOf :: sym -> SymString sym si -> SymString sym si -> SymNat sym -> IO (SymInteger sym)

  -- | Compute the length of a string
  stringLength :: sym -> SymString sym si -> IO (SymNat sym)

  -- | @stringSubstring s off len@ extracts the substring of @s@ starting at index @off@ and
  --   having length @len@.  The result of this operation is undefined if @off@ and @len@
  --   do not specify a valid substring of @s@; in particular, we must have @off+len <= length(s)@.
  stringSubstring :: sym -> SymString sym si -> SymNat sym -> SymNat sym -> IO (SymString sym si)

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

  -- | @realMod x y@ returns the value of @x - y * floor(x / y)@ when
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
  --
  -- When @x@ and @y@ are both zero, this function is undefined.
  realAtan2 :: sym -> SymReal sym -> SymReal sym -> IO (SymReal sym)

  -- | Return value denoting pi.
  realPi :: sym -> IO (SymReal sym)

  -- | Natural logarithm.  @realLog x@ is undefined
  --   for @x <= 0@.
  realLog :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Natural exponentiation
  realExp :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Sine trig function
  realSin :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Cosine trig function
  realCos :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Tangent trig function.  @realTan x@ is undefined
  --   when @cos x = 0@,  i.e., when @x = pi/2 + k*pi@ for
  --   some integer @k@.
  realTan :: sym -> SymReal sym -> IO (SymReal sym)
  realTan sym x = do
    sin_x <- realSin sym x
    cos_x <- realCos sym x
    realDiv sym sin_x cos_x

  -- | Hyperbolic sine
  realSinh :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Hyperbolic cosine
  realCosh :: sym -> SymReal sym -> IO (SymReal sym)

  -- | Hyperbolic tangent
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
  -- IEEE-754 floating-point operations
  -- | Return floating point number @+0@.
  floatPZero :: sym -> FloatPrecisionRepr fpp -> IO (SymFloat sym fpp)

  -- | Return floating point number @-0@.
  floatNZero :: sym -> FloatPrecisionRepr fpp -> IO (SymFloat sym fpp)

  -- |  Return floating point NaN.
  floatNaN :: sym -> FloatPrecisionRepr fpp -> IO (SymFloat sym fpp)

  -- | Return floating point @+infinity@.
  floatPInf :: sym -> FloatPrecisionRepr fpp -> IO (SymFloat sym fpp)

  -- | Return floating point @-infinity@.
  floatNInf :: sym -> FloatPrecisionRepr fpp -> IO (SymFloat sym fpp)

  -- | Create a floating point literal from a rational literal.
  floatLit
    :: sym -> FloatPrecisionRepr fpp -> Rational -> IO (SymFloat sym fpp)

  -- | Negate a floating point number.
  floatNeg
    :: sym
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Return the absolute value of a floating point number.
  floatAbs
    :: sym
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Compute the square root of a floating point number.
  floatSqrt
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Add two floating point numbers.
  floatAdd
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Subtract two floating point numbers.
  floatSub
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Multiply two floating point numbers.
  floatMul
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Divide two floating point numbers.
  floatDiv
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Compute the reminder: @x - y * n@, where @n@ in Z is nearest to @x / y@.
  floatRem
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Return the min of two floating point numbers.
  floatMin
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Return the max of two floating point numbers.
  floatMax
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Compute the fused multiplication and addition: @(x * y) + z@.
  floatFMA
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Check logical equality of two floating point numbers.
  --
  --   NOTE! This does NOT accurately represent the equality test on floating point
  --   values typically found in programming languages.  See 'floatFpEq' instead.
  floatEq
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check logical non-equality of two floating point numbers.
  --
  --   NOTE! This does NOT accurately represent the non-equality test on floating point
  --   values typically found in programming languages.  See 'floatFpEq' instead.
  floatNe
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 equality of two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not equal to itself!  Moreover, positive and negative 0 will
  --   compare equal, despite having different bit patterns.
  --
  --   This test is most appropriate for interpreting the equality tests of
  --   typical languages using floating point.  Moreover, not-equal tests
  --   are usually the negation of this test, rather than the `floatFpNe`
  --   test below.
  floatFpEq
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 non-equality of two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not distinct from any other value!  Moreover, positive and
  --   negative 0 will not compare distinct, despite having different
  --   bit patterns.
  --
  --   This test usually does NOT correspond to the not-equal tests found
  --   in programming languages.  Instead, one generally takes the logical
  --   negation of the `floatFpEq` test.
  floatFpNe
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 @<=@ on two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not less-than-or-equal-to any other value!  Moreover, positive
  --   and negative 0 are considered equal, despite having different bit patterns.
  floatLe
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 @<@ on two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not less-than any other value! Moreover, positive
  --   and negative 0 are considered equal, despite having different bit patterns.
  floatLt
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 @>=@ on two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not greater-than-or-equal-to any other value!  Moreover, positive
  --   and negative 0 are considered equal, despite having different bit patterns.
  floatGe
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Check IEEE-754 @>@ on two floating point numbers.
  --
  --   NOTE! This test returns false if either value is @NaN@; in particular
  --   @NaN@ is not greater-than any other value! Moreover, positive
  --   and negative 0 are considered equal, despite having different bit patterns.
  floatGt
    :: sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (Pred sym)

  -- | Test if a floating-point value is NaN.
  floatIsNaN :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floating-point value is (positive or negative) infinity.
  floatIsInf :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floaint-point value is (positive or negative) zero.
  floatIsZero :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floaint-point value is positive.  NOTE!
  --   NaN is considered neither positive nor negative.
  floatIsPos :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floaint-point value is negative.  NOTE!
  --   NaN is considered neither positive nor negative.
  floatIsNeg :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floaint-point value is subnormal.
  floatIsSubnorm :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | Test if a floaint-point value is normal.
  floatIsNorm :: sym -> SymFloat sym fpp -> IO (Pred sym)

  -- | If-then-else on floating point numbers.
  floatIte
    :: sym
    -> Pred sym
    -> SymFloat sym fpp
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)

  -- | Change the precision of a floating point number.
  floatCast
    :: sym
    -> FloatPrecisionRepr fpp
    -> RoundingMode
    -> SymFloat sym fpp'
    -> IO (SymFloat sym fpp)
  -- | Round a floating point number to an integral value.
  floatRound
    :: sym
    -> RoundingMode
    -> SymFloat sym fpp
    -> IO (SymFloat sym fpp)
  -- | Convert from binary representation in IEEE 754-2008 format to
  --   floating point.
  floatFromBinary
    :: (2 <= eb, 2 <= sb)
    => sym
    -> FloatPrecisionRepr (FloatingPointPrecision eb sb)
    -> SymBV sym (eb + sb)
    -> IO (SymFloat sym (FloatingPointPrecision eb sb))
  -- | Convert from floating point from to the binary representation in
  --   IEEE 754-2008 format.
  --
  --   NOTE! @NaN@ has multiple representations, i.e. all bit patterns where
  --   the exponent is @0b1..1@ and the significant is not @0b0..0@.
  --   This functions returns the representation of positive "quiet" @NaN@,
  --   i.e. the bit pattern where the sign is @0b0@, the exponent is @0b1..1@,
  --   and the significant is @0b10..0@.
  floatToBinary
    :: (2 <= eb, 2 <= sb)
    => sym
    -> SymFloat sym (FloatingPointPrecision eb sb)
    -> IO (SymBV sym (eb + sb))
  -- | Convert a unsigned bitvector to a floating point number.
  bvToFloat
    :: (1 <= w)
    => sym
    -> FloatPrecisionRepr fpp
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymFloat sym fpp)
  -- | Convert a signed bitvector to a floating point number.
  sbvToFloat
    :: (1 <= w)
    => sym
    -> FloatPrecisionRepr fpp
    -> RoundingMode
    -> SymBV sym w
    -> IO (SymFloat sym fpp)
  -- | Convert a real number to a floating point number.
  realToFloat
    :: sym
    -> FloatPrecisionRepr fpp
    -> RoundingMode
    -> SymReal sym
    -> IO (SymFloat sym fpp)
  -- | Convert a floating point number to a unsigned bitvector.
  floatToBV
    :: (1 <= w)
    => sym
    -> NatRepr w
    -> RoundingMode
    -> SymFloat sym fpp
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a signed bitvector.
  floatToSBV
    :: (1 <= w)
    => sym
    -> NatRepr w
    -> RoundingMode
    -> SymFloat sym fpp
    -> IO (SymBV sym w)
  -- | Convert a floating point number to a real number.
  floatToReal :: sym -> SymFloat sym fpp -> IO (SymReal sym)

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

  -- | Compute tangent of a complex number.  @cplxTan x@ is undefined
  --   when @cplxCos x@ is @0@, which occurs only along the real line
  --   in the same conditions where @realCos x@ is @0@.
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

-- | This newtype is necessary for @bvJoinVector@ and @bvSplitVector@.
-- These both use functions from Data.Parameterized.Vector that
-- that expect a wrapper of kind (Type -> Type), and we can't partially
-- apply the type synonym (e.g. SymBv sym), whereas we can partially
-- apply this newtype.
newtype SymBV' sym w = MkSymBV' (SymBV sym w)

-- | Join a @Vector@ of smaller bitvectors.
bvJoinVector :: forall sym n w. (1 <= w, IsExprBuilder sym)
             => sym
             -> NatRepr w
             -> Vector.Vector n (SymBV sym w)
             -> IO (SymBV sym (n * w))
bvJoinVector sym w =
  coerce $ Vector.joinWithM @IO @(SymBV' sym) @n bvConcat' w
  where bvConcat' :: forall l. (1 <= l)
                  => NatRepr l
                  -> SymBV' sym w
                  -> SymBV' sym l
                  -> IO (SymBV' sym (w + l))
        bvConcat' _ (MkSymBV' x) (MkSymBV' y) = MkSymBV' <$> bvConcat sym x y

-- | Split a bitvector to a @Vector@ of smaller bitvectors.
bvSplitVector :: forall sym n w. (IsExprBuilder sym, 1 <= w, 1 <= n)
              => sym
              -> NatRepr n
              -> NatRepr w
              -> SymBV sym (n * w)
              -> IO (Vector.Vector n (SymBV sym w))
bvSplitVector sym n w x =
  coerce $ Vector.splitWithA @IO LittleEndian bvSelect' n w (MkSymBV' @sym x)
  where
    bvSelect' :: forall i. (i + w <= n * w)
              => NatRepr (n * w)
              -> NatRepr i
              -> SymBV' sym (n * w)
              -> IO (SymBV' sym w)
    bvSelect' _ i (MkSymBV' y) =
      fmap MkSymBV' $ bvSelect @_ @i @w sym i w y

-- | Implement LLVM's "bswap" intrinsic
--
-- See <https://llvm.org/docs/LangRef.html#llvm-bswap-intrinsics
--       the LLVM @bswap@ documentation.>
--
-- This is the implementation in SawCore:
--
-- > llvmBSwap :: (n :: Nat) -> bitvector (mulNat n 8) -> bitvector (mulNat n 8);
-- > llvmBSwap n x = join n 8 Bool (reverse n (bitvector 8) (split n 8 Bool x));
bvSwap :: forall sym n. (1 <= n, IsExprBuilder sym)
       => sym               -- ^ Symbolic interface
       -> NatRepr n
       -> SymBV sym (n*8)   -- ^ Bitvector to swap around
       -> IO (SymBV sym (n*8))
bvSwap sym n v = do
  bvJoinVector sym (knownNat @8) . Vector.reverse
    =<< bvSplitVector sym n (knownNat @8) v

-- | Swap the order of the bits in a bitvector.
bvBitreverse :: forall sym w.
  (1 <= w, IsExprBuilder sym) =>
  sym ->
  SymBV sym w ->
  IO (SymBV sym w)
bvBitreverse sym v = do
  bvJoinVector sym (knownNat @1) . Vector.reverse
    =<< bvSplitVector sym (bvWidth v) (knownNat @1) v

-- | Rounding modes for IEEE-754 floating point operations.
data RoundingMode
  = RNE -- ^ Round to nearest even.
  | RNA -- ^ Round to nearest away.
  | RTP -- ^ Round toward plus Infinity.
  | RTN -- ^ Round toward minus Infinity.
  | RTZ -- ^ Round toward zero.
  deriving (Eq, Generic, Ord, Show, Enum)

instance Hashable RoundingMode


-- | Create a literal from an 'IndexLit'.
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


-- | A function that can be applied to symbolic arguments.
--
-- This type is used by some methods in classes 'IsExprBuilder' and
-- 'IsSymExprBuilder'.
type family SymFn sym :: Ctx BaseType -> BaseType -> Type

-- | A class for extracting type representatives from symbolic functions
class IsSymFn fn where
  -- | Get the argument types of a function.
  fnArgTypes :: fn args ret -> Ctx.Assignment BaseTypeRepr args

  -- | Get the return type of a function.
  fnReturnType :: fn args ret -> BaseTypeRepr ret

-- | This extends the interface for building expressions with operations
--   for creating new symbolic constants and functions.
class ( IsExprBuilder sym
      , IsSymFn (SymFn sym)
      , OrdF (SymExpr sym)
      ) => IsSymExprBuilder sym where

  ----------------------------------------------------------------------
  -- Fresh variables

  -- | Create a fresh top-level uninterpreted constant.
  freshConstant :: sym -> SolverSymbol -> BaseTypeRepr tp -> IO (SymExpr sym tp)

  -- | Create a fresh latch variable.
  freshLatch    :: sym -> SolverSymbol -> BaseTypeRepr tp -> IO (SymExpr sym tp)

  -- | Create a fresh bitvector value with optional upper and lower bounds (which bound the
  --   unsigned value of the bitvector).
  freshBoundedBV :: (1 <= w) => sym -> SolverSymbol -> NatRepr w -> Maybe Natural -> Maybe Natural -> IO (SymBV sym w)

  -- | Create a fresh bitvector value with optional upper and lower bounds (which bound the
  --   signed value of the bitvector)
  freshBoundedSBV :: (1 <= w) => sym -> SolverSymbol -> NatRepr w -> Maybe Integer -> Maybe Integer -> IO (SymBV sym w)

  -- | Create a fresh natural number constant with optional upper and lower bounds.
  --   If provided, the bounds are inclusive.
  freshBoundedNat :: sym -> SolverSymbol -> Maybe Natural -> Maybe Natural -> IO (SymNat sym)

  -- | Create a fresh integer constant with optional upper and lower bounds.
  --   If provided, the bounds are inclusive.
  freshBoundedInt :: sym -> SolverSymbol -> Maybe Integer -> Maybe Integer -> IO (SymInteger sym)

  -- | Create a fresh real constant with optional upper and lower bounds.
  --   If provided, the bounds are inclusive.
  freshBoundedReal :: sym -> SolverSymbol -> Maybe Rational -> Maybe Rational -> IO (SymReal sym)


  ----------------------------------------------------------------------
  -- Functions needs to support quantifiers.

  -- | Creates a bound variable.
  --
  -- This will be treated as a free constant when appearing inside asserted
  -- expressions.  These are intended to be bound using quantifiers or
  -- symbolic functions.
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

  -- | Return a function defined by an expression over bound
  -- variables. The predicate argument allows the user to specify when
  -- an application of the function should be unfolded and evaluated,
  -- e.g. to perform constant folding.
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
            --
            --   When applied to actual arguments, this predicate indicates
            --   if the definition of the function should be unfolded and reduced.
            --   A typical use would be to unfold and evaluate the body of the function
            --   if all the input arguments are concrete.
            -> IO (SymFn sym args ret)

  -- | Return a function defined by Haskell computation over symbolic expressions.
  inlineDefineFun :: Ctx.CurryAssignmentClass args
                  => sym
                     -- ^ Symbolic interface
                  -> SolverSymbol
                  -- ^ The name to give a function (need not be unique)
                  -> Ctx.Assignment BaseTypeRepr args
                  -- ^ Type signature for the arguments
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

  -- | Create a new uninterpreted function.
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

  -- | Apply a set of arguments to a symbolic function.
  applySymFn :: sym
                -- ^ Symbolic interface
             -> SymFn sym args ret
                -- ^ Function to call
             -> Ctx.Assignment (SymExpr sym) args
                -- ^ Arguments to function
             -> IO (SymExpr sym ret)

-- | This returns true if the value corresponds to a concrete value.
baseIsConcrete :: forall e bt
                . IsExpr e
               => e bt
               -> Bool
baseIsConcrete x =
  case exprType x of
    BaseBoolRepr    -> isJust $ asConstantPred x
    BaseNatRepr     -> isJust $ asNat x
    BaseIntegerRepr -> isJust $ asInteger x
    BaseBVRepr _    -> isJust $ asUnsignedBV x
    BaseRealRepr    -> isJust $ asRational x
    BaseFloatRepr _ -> False
    BaseStringRepr{} -> isJust $ asString x
    BaseComplexRepr -> isJust $ asComplex x
    BaseStructRepr _ -> case asStruct x of
        Just flds -> allFC baseIsConcrete flds
        Nothing -> False
    BaseArrayRepr _ _bt' -> do
      case asConstantArray x of
        Just x' -> baseIsConcrete x'
        Nothing -> False

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
    BaseFloatRepr fpp -> floatPZero sym fpp
    BaseComplexRepr -> mkComplexLit sym (0 :+ 0)
    BaseStringRepr si -> stringEmpty sym si
    BaseStructRepr flds -> do
      let f :: BaseTypeRepr tp -> IO (SymExpr sym tp)
          f v = baseDefaultValue sym v
      mkStruct sym =<< traverseFC f flds
    BaseArrayRepr idx bt' -> do
      elt <- baseDefaultValue sym bt'
      constantArray sym idx elt

-- | Return predicate equivalent to a Boolean.
backendPred :: IsExprBuilder sym => sym -> Bool -> Pred sym
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
realExprAsRational :: (MonadFail m, IsExpr e) => e BaseRealType -> m Rational
realExprAsRational x = do
  case asRational x of
    Just r -> return r
    Nothing -> fail "Value is not a constant expression."

-- | Extract the value of a complex expression, which is assumed
--   to be a constant real number.  Fail if the number has nonzero
--   imaginary component, or if it is not a constant.
cplxExprAsRational :: (MonadFail m, IsExpr e) => e BaseComplexType -> m Rational
cplxExprAsRational x = do
  case asComplex x of
    Just (r :+ i) -> do
      when (i /= 0) $
        fail "Complex value has an imaginary part."
      return r
    Nothing -> do
      fail "Complex value is not a constant expression."

-- | Return a complex value as a constant integer if it exists.
cplxExprAsInteger :: (MonadFail m, IsExpr e) => e BaseComplexType -> m Integer
cplxExprAsInteger x = rationalAsInteger =<< cplxExprAsRational x

-- | Return value as a constant integer if it exists.
rationalAsInteger :: MonadFail m => Rational -> m Integer
rationalAsInteger r = do
  when (denominator r /= 1) $ do
    fail "Value is not an integer."
  return (numerator r)

-- | Return value as a constant integer if it exists.
realExprAsInteger :: (IsExpr e, MonadFail m) => e BaseRealType -> m Integer
realExprAsInteger x =
  rationalAsInteger =<< realExprAsRational x

-- | Compute the conjunction of a sequence of predicates.
andAllOf :: IsExprBuilder sym
         => sym
         -> Fold s (Pred sym)
         -> s
         -> IO (Pred sym)
andAllOf sym f s = foldlMOf f (andPred sym) (truePred sym) s

-- | Compute the disjunction of a sequence of predicates.
orOneOf :: IsExprBuilder sym
         => sym
         -> Fold s (Pred sym)
         -> s
         -> IO (Pred sym)
orOneOf sym f s = foldlMOf f (orPred sym) (falsePred sym) s

-- | Return predicate that holds if value is non-zero.
isNonZero :: IsExprBuilder sym => sym -> SymCplx sym -> IO (Pred sym)
isNonZero sym v = cplxNe sym v =<< mkRational sym 0

-- | Return predicate that holds if imaginary part of number is zero.
isReal :: IsExprBuilder sym => sym -> SymCplx sym -> IO (Pred sym)
isReal sym v = do
  i <- getImagPart sym v
  realEq sym i (realZero sym)

-- | Divide one number by another.
--
--   @cplxDiv x y@ is undefined when @y@ is @0@.
cplxDiv :: IsExprBuilder sym
        => sym
        -> SymCplx sym
        -> SymCplx sym
        -> IO (SymCplx sym)
cplxDiv sym x y = do
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

-- | Helper function that returns the principal logarithm of input.
cplxLog' :: IsExprBuilder sym
         => sym -> SymCplx sym -> IO (Complex (SymReal sym))
cplxLog' sym x = do
  xr :+ xi <- cplxGetParts sym x
  -- Get the magnitude of the value.
  xm <- realHypot sym xr xi
  -- Get angle of complex number.
  xa <- realAtan2 sym xi xr
  -- Get log of magnitude
  zr <- realLog sym xm
  return $! zr :+ xa

-- | Returns the principal logarithm of the input value.
--
--   @cplxLog x@ is undefined when @x@ is @0@, and has a
--   cut discontinuity along the negative real line.
cplxLog :: IsExprBuilder sym
        => sym -> SymCplx sym -> IO (SymCplx sym)
cplxLog sym x = mkComplex sym =<< cplxLog' sym x

-- | Returns logarithm of input at a given base.
--
--   @cplxLogBase b x@ is undefined when @x@ is @0@.
cplxLogBase :: IsExprBuilder sym
            => Rational {- ^ Base for the logarithm -}
            -> sym
            -> SymCplx sym
            -> IO (SymCplx sym)
cplxLogBase base sym x = do
  b <- realLog sym =<< realLit sym base
  z <- traverse (\r -> realDiv sym r b) =<< cplxLog' sym x
  mkComplex sym z

--------------------------------------------------------------------------
-- Relationship to concrete values

-- | Return a concrete representation of a value, if it
--   is concrete.
asConcrete :: IsExpr e => e tp -> Maybe (ConcreteVal tp)
asConcrete x =
  case exprType x of
    BaseBoolRepr    -> ConcreteBool <$> asConstantPred x
    BaseNatRepr    -> ConcreteNat <$> asNat x
    BaseIntegerRepr -> ConcreteInteger <$> asInteger x
    BaseRealRepr    -> ConcreteReal <$> asRational x
    BaseStringRepr _si -> ConcreteString <$> asString x
    BaseComplexRepr -> ConcreteComplex <$> asComplex x
    BaseBVRepr w    -> ConcreteBV w <$> asUnsignedBV x
    BaseFloatRepr _ -> Nothing
    BaseStructRepr _ -> Nothing -- FIXME?
    BaseArrayRepr _ _ -> Nothing -- FIXME?


-- | Create a literal symbolic value from a concrete value.
concreteToSym :: IsExprBuilder sym => sym -> ConcreteVal tp -> IO (SymExpr sym tp)
concreteToSym sym = \case
   ConcreteBool True    -> return (truePred sym)
   ConcreteBool False   -> return (falsePred sym)
   ConcreteNat x        -> natLit sym x
   ConcreteInteger x    -> intLit sym x
   ConcreteReal x       -> realLit sym x
   ConcreteString x     -> stringLit sym x
   ConcreteComplex x    -> mkComplexLit sym x
   ConcreteBV w x       -> bvLit sym w x
   ConcreteStruct xs    -> mkStruct sym =<< traverseFC (concreteToSym sym) xs
   ConcreteArray idxTy def xs0 -> go (Map.toAscList xs0) =<< constantArray sym idxTy =<< concreteToSym sym def
     where
     go [] arr = return arr
     go ((i,x):xs) arr =
        do arr' <- go xs arr
           i' <- traverseFC (concreteToSym sym) i
           x' <- concreteToSym sym x
           arrayUpdate sym arr' i' x'

------------------------------------------------------------------------
-- muxNatRange

{-# INLINABLE muxRange #-}
{- | This function is used for selecting a value from among potential
values in a range.

@muxRange p ite f l h@ returns an expression denoting the value obtained
from the value @f i@ where @i@ is the smallest value in the range @[l..h]@
such that @p i@ is true.  If @p i@ is true for no such value, then
this returns the value @f h@. -}
muxRange :: (IsExpr e, Monad m) =>
   (Natural -> m (e BaseBoolType)) 
      {- ^ Returns predicate that holds if we have found the value we are looking
           for.  It is assumed that the predicate must hold for a unique integer in
           the range.
      -} ->
   (e BaseBoolType -> a -> a -> m a) {- ^ Ite function -} ->
   (Natural -> m a) {- ^ Function for concrete values -} ->
   Natural {- ^ Lower bound (inclusive) -} ->
   Natural {- ^ Upper bound (inclusive) -} ->
   m a
muxRange predFn iteFn f l h
  | l < h = do
    c <- predFn l
    case asConstantPred c of
      Just True  -> f l
      Just False -> muxRange predFn iteFn f (succ l) h
      Nothing ->
        do match_branch <- f l
           other_branch <- muxRange predFn iteFn f (succ l) h
           iteFn c match_branch other_branch
  | otherwise = f h

-- | This provides an interface for converting between Haskell values and a
-- solver representation.
data SymEncoder sym v tp
   = SymEncoder { symEncoderType :: !(BaseTypeRepr tp)
                , symFromExpr :: !(sym -> SymExpr sym tp -> IO v)
                , symToExpr   :: !(sym -> v -> IO (SymExpr sym tp))
                }

----------------------------------------------------------------------
-- Statistics

-- | Statistics gathered on a running expression builder.  See
-- 'getStatistics'.
data Statistics
  = Statistics { statAllocs :: !Integer
                 -- ^ The number of times an expression node has been
                 -- allocated.
               , statNonLinearOps :: !Integer
                 -- ^ The number of non-linear operations, such as
                 -- multiplications, that have occurred.
               }
  deriving ( Show )

zeroStatistics :: Statistics
zeroStatistics = Statistics { statAllocs = 0
                            , statNonLinearOps = 0 }
