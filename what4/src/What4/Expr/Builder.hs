{-|
Module      : What4.Expr.Builder
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

This module defines the canonical implementation of the solver interface
from "What4.Interface". Type @'ExprBuilder' t st@ is
an instance of the classes 'IsExprBuilder' and 'IsSymExprBuilder'.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module What4.Expr.Builder
  ( -- * ExprBuilder
    ExprBuilder
  , newExprBuilder
  , getSymbolVarBimap
  , sbMakeExpr
  , sbNonceExpr
  , curProgramLoc
  , sbUnaryThreshold
  , sbCacheStartSize
  , sbBVDomainRangeLimit
  , sbStateManager
  , exprCounter
  , startCaching
  , stopCaching

    -- * Specialized representations
  , bvUnary
  , natSum
  , intSum
  , realSum

    -- ** configuration options
  , unaryThresholdOption
  , bvdomainRangeLimitOption
  , cacheStartSizeOption
  , cacheTerms

    -- * Expr
  , Expr(..)
  , asApp
  , iteSize
  , exprLoc
  , ppExpr
  , ppExprTop
  , asConjunction
  , exprMaybeId
    -- ** AppExpr
  , AppExpr
  , appExprId
  , appExprLoc
  , appExprApp
    -- ** NonceAppExpr
  , NonceAppExpr
  , nonceExprId
  , nonceExprLoc
  , nonceExprApp
    -- ** Type abbreviations
  , BoolExpr
  , NatExpr
  , IntegerExpr
  , RealExpr
  , BVExpr
  , CplxExpr
  , StringExpr

    -- * App
  , App(..)
  , traverseApp
  , appType
    -- * NonceApp
  , NonceApp(..)
  , nonceAppType

    -- * Bound Variable information
  , ExprBoundVar
  , bvarId
  , bvarLoc
  , bvarName
  , bvarType
  , bvarKind
  , bvarAbstractValue
  , VarKind(..)
  , boundVars
  , ppBoundVar
  , evalBoundVars

    -- * Symbolic Function
  , ExprSymFn(..)
  , SymFnInfo(..)
  , symFnArgTypes
  , symFnReturnType

    -- * SymbolVarBimap
  , SymbolVarBimap
  , SymbolBinding(..)
  , emptySymbolVarBimap
  , lookupBindingOfSymbol
  , lookupSymbolOfBinding

    -- * IdxCache
  , IdxCache
  , newIdxCache
  , lookupIdx
  , lookupIdxValue
  , insertIdxValue
  , deleteIdxValue
  , clearIdxCache
  , idxCacheEval
  , idxCacheEval'

    -- * Flags
  , type FloatInterpretation
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  , Flags

    -- * Re-exports
  , SymExpr
  , What4.Interface.bvWidth
  , What4.Interface.exprType
  , What4.Interface.IndexLit(..)
  , What4.Interface.ArrayResultWrapper(..)
  , What4.Expr.WeightedSum.SemiRingRepr(..)
  ) where

import qualified Control.Exception as Ex
import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import qualified Data.Binary.IEEE754 as IEEE754
import qualified Data.Bits as Bits
import           Data.Foldable
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Cuckoo as H
import           Data.Hashable
import           Data.IORef
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import           Data.STRef
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word (Word64)
import           GHC.Generics (Generic)
import qualified Numeric as N
import           Numeric.Natural
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.BaseTypes
import           What4.Concrete
import qualified What4.Config as CFG
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.ProgramLoc
import           What4.Symbol
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (SemiRing, SemiRingRepr(..), WeightedSum, semiRingBase)
import qualified What4.Expr.WeightedSum as WSum
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import qualified What4.Utils.Hashable as Hash

------------------------------------------------------------------------
-- Utilities

toDouble :: Rational -> Double
toDouble = fromRational

cachedEval :: (HashableF k, TestEquality k)
           => PH.HashTable RealWorld k a
           -> k tp
           -> IO (a tp)
           -> IO (a tp)
cachedEval tbl k action = do
  mr <- stToIO $ PH.lookup tbl k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- action
      seq r $ do
      stToIO $ PH.insert tbl k r
      return r

------------------------------------------------------------------------
-- ExprBoundVar

-- | The Kind of a bound variable.
data VarKind
  = QuantifierVarKind
    -- ^ A variable appearing in a quantifier.
  | LatchVarKind
    -- ^ A variable appearing as a latch input.
  | UninterpVarKind
    -- ^ A variable appearing in a uninterpreted constant

-- | Information about bound variables.
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Type @'ExprBoundVar' t@ instantiates the type family
-- @'BoundVar' ('ExprBuilder' t st)@.
--
-- Selector functions are provided to destruct 'ExprBoundVar'
-- values, but the constructor is kept hidden. The preferred way to
-- construct a 'ExprBoundVar' is to use 'freshBoundVar'.
data ExprBoundVar t (tp :: BaseType) =
  BVar { bvarId  :: {-# UNPACK #-} !(Nonce t tp)
       , bvarLoc :: !ProgramLoc
       , bvarName :: !SolverSymbol
       , bvarType :: !(BaseTypeRepr tp)
       , bvarKind :: !VarKind
       , bvarAbstractValue :: !(Maybe (AbstractValue tp))
       }

instance Eq (ExprBoundVar t tp) where
  x == y = bvarId x == bvarId y

instance TestEquality (ExprBoundVar t) where
  testEquality x y = testEquality (bvarId x) (bvarId y)

instance Ord (ExprBoundVar t tp) where
  compare x y = compare (bvarId x) (bvarId y)

instance OrdF (ExprBoundVar t) where
  compareF x y = compareF (bvarId x) (bvarId y)

instance Hashable (ExprBoundVar t tp) where
  hashWithSalt s x = hashWithSalt s (bvarId x)

instance HashableF (ExprBoundVar t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- NonceApp

-- | Type @NonceApp t e tp@ encodes the top-level application of an
-- 'Expr'. It includes expression forms that bind variables (contrast
-- with 'App').
--
-- Parameter @t@ is a phantom type brand used to track nonces.
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'NonceApp' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data NonceApp t (e :: BaseType -> Type) (tp :: BaseType) where
  Forall :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType
  Exists :: !(ExprBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType

  -- Create an array from a function
  ArrayFromFn :: !(ExprSymFn t (idx ::> itp) ret)
              -> NonceApp t e (BaseArrayType (idx ::> itp) ret)

  -- Create an array by mapping over one or more existing arrays.
  MapOverArrays :: !(ExprSymFn t (ctx::>d) r)
                -> !(Ctx.Assignment BaseTypeRepr (idx ::> itp))
                -> !(Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) (ctx::>d))
                -> NonceApp t e (BaseArrayType (idx ::> itp) r)

  -- This returns true if all the indices satisfying the given predicate equal true.
  ArrayTrueOnEntries
    :: !(ExprSymFn t (idx ::> itp) BaseBoolType)
    -> !(e (BaseArrayType (idx ::> itp) BaseBoolType))
    -> NonceApp t e BaseBoolType

  -- Apply a function to some arguments
  FnApp :: !(ExprSymFn t args ret)
        -> !(Ctx.Assignment e args)
        -> NonceApp t e ret

------------------------------------------------------------------------
-- App

-- | Type @'App' e tp@ encodes the top-level application of an 'Expr'
-- expression. It includes first-order expression forms that do not
-- bind variables (contrast with 'NonceApp').
--
-- Parameter @e@ is used everywhere a recursive sub-expression would
-- go. Uses of the 'App' type will tie the knot through this
-- parameter. Parameter @tp@ indicates the type of the expression.
data App (e :: BaseType -> Type) (tp :: BaseType) where

  ------------------------------------------------------------------------
  -- Boolean operations

  TrueBool  :: App e BaseBoolType
  FalseBool :: App e BaseBoolType
  NotBool :: !(e BaseBoolType) -> App e BaseBoolType
  AndBool :: !(e BaseBoolType) -> !(e BaseBoolType) -> App e BaseBoolType
  XorBool :: !(e BaseBoolType) -> !(e BaseBoolType) -> App e BaseBoolType
  IteBool :: !(e BaseBoolType)
          -> !(e BaseBoolType)
          -> !(e BaseBoolType)
          -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Semiring operations

  -- This represents a weighted sum of other expressions plus an offset.
  SemiRingSum
     :: SemiRing e tp
     => !(SemiRingRepr tp)
     -> {-# UNPACK #-} !(WeightedSum e tp)
     -> App e tp

  -- Multiplication of two semiring values
  --
  -- The ExprBuilder should maintain the invariant that neither value is
  -- a constant, and hence this denotes a non-linear expression.
  -- Multiplications by scalars should use the 'SemiRingSum' constructor.
  SemiRingMul
     :: SemiRing e tp
     => !(SemiRingRepr tp)
     -> !(e tp)
     -> !(e tp)
     -> App e tp

  -- If/then/else on semiring values.
  SemiRingIte
     :: SemiRing e tp
     => !(SemiRingRepr tp)
     -> !(e BaseBoolType)
     -> !(e tp)
     -> !(e tp)
     -> App e tp

  SemiRingEq
     :: SemiRing e tp
     => !(SemiRingRepr tp)
     -> !(e tp)
     -> !(e tp)
     -> App e BaseBoolType

  SemiRingLe
     :: SemiRing e tp
     => !(SemiRingRepr tp)
     -> !(e tp)
     -> !(e tp)
     -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Basic arithmetic operations

  RealIsInteger :: !(e BaseRealType) -> App e BaseBoolType

  -- This does natural number division rounded to zero.
  NatDiv :: !(e BaseNatType)  -> !(e BaseNatType) -> App e BaseNatType
  NatMod :: !(e BaseNatType)  -> !(e BaseNatType) -> App e BaseNatType

  IntDiv :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntMod :: !(e BaseIntegerType)  -> !(e BaseIntegerType) -> App e BaseIntegerType
  IntAbs :: !(e BaseIntegerType)  -> App e BaseIntegerType
  IntDivisible :: !(e BaseIntegerType) -> Natural -> App e BaseBoolType

  RealDiv :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType

  -- Returns @sqrt(x)@, result is not defined if @x@ is negative.
  RealSqrt :: !(e BaseRealType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Operations that introduce irrational numbers.

  Pi :: App e BaseRealType

  RealSin   :: !(e BaseRealType) -> App e BaseRealType
  RealCos   :: !(e BaseRealType) -> App e BaseRealType
  RealATan2 :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType
  RealSinh  :: !(e BaseRealType) -> App e BaseRealType
  RealCosh  :: !(e BaseRealType) -> App e BaseRealType

  RealExp :: !(e BaseRealType) -> App e BaseRealType
  RealLog :: !(e BaseRealType) -> App e BaseRealType

  --------------------------------
  -- Bitvector operations

  -- Perform if-then-else on two bitvectors.
  BVIte :: (1 <= w)
        => !(NatRepr w)        -- Width of result.
        -> Integer             -- Number of if-then-else branches.
        -> !(e BaseBoolType)   -- Predicate
        -> !(e (BaseBVType w)) -- True value
        -> !(e (BaseBVType w)) -- False value
        -> App e (BaseBVType w)

  -- Return value of bit at given index.
  BVTestBit :: (1 <= w)
            => !Natural -- Index of bit to test
                        -- (least-significant bit has index 0)
            -> !(e (BaseBVType w))
            -> App e BaseBoolType
  BVEq :: (1 <= w)
       => !(e (BaseBVType w))
       -> !(e (BaseBVType w))
       -> App e BaseBoolType
  BVSlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType
  BVUlt :: (1 <= w)
        => !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e BaseBoolType

  -- A unary representation of terms where an integer @i@ is mapped to a
  -- predicate that is true if the unsigned encoding of the value is greater
  -- than or equal to @i@.
  --
  -- The map contains a binding (i -> p_i) when the predicate
  --
  -- As an example, we can encode the value @1@ with the assignment:
  --   { 0 => true ; 2 => false }
  BVUnaryTerm :: (1 <= n)
              => !(UnaryBV (e BaseBoolType) n)
              -> App e (BaseBVType n)

  BVConcat :: (1 <= u, 1 <= v, 1 <= (u+v))
           => !(NatRepr (u+v))
           -> !(e (BaseBVType u))
           -> !(e (BaseBVType v))
           -> App e (BaseBVType (u+v))

  BVSelect :: (1 <= n, idx + n <= w)
              -- First bit to select from (least-significant bit has index 0)
           => !(NatRepr idx)
              -- Number of bits to select, counting up toward more significant bits
           -> !(NatRepr n)
              -- Bitvector to select from.
           -> !(e (BaseBVType w))
           -> App e (BaseBVType n)

  BVNeg :: (1 <= w) => !(NatRepr w) -> !(e (BaseBVType w)) -> App e (BaseBVType w)

  BVAdd  :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

{-
  -- | This represents a real number as a weighted sum of other expressions plus
  -- an offset.
  BVSum :: (1 <= w)
        => !(NatRepr w)
        -> {-# UNPACK #-} !(WeightedSum Integer (e (BaseBVType w)))
        -> App e (BaseBVType w)
-}

  BVMul  :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVUdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVUrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSdiv :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)
  BVSrem :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVShl :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))
        -> !(e (BaseBVType w))
        -> App e (BaseBVType w)

  BVLshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVAshr :: (1 <= w)
         => !(NatRepr w)
         -> !(e (BaseBVType w))
         -> !(e (BaseBVType w))
         -> App e (BaseBVType w)

  BVZext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVSext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> App e (BaseBVType r)

  BVPopcount ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountTrailingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVCountLeadingZeros ::
    (1 <= w) =>
    !(NatRepr w) ->
    !(e (BaseBVType w)) ->
    App e (BaseBVType w)

  BVBitNot :: (1 <= w)
           => !(NatRepr w)
           -> !(e (BaseBVType w))
           -> App e (BaseBVType w)

  BVBitAnd :: (1 <= w)
           => !(NatRepr w)
           -> !(e (BaseBVType w))
           -> !(e (BaseBVType w))
           -> App e (BaseBVType w)
  BVBitOr :: (1 <= w)
          => !(NatRepr w)
          -> !(e (BaseBVType w))
          -> !(e (BaseBVType w))
          -> App e (BaseBVType w)
  BVBitXor :: (1 <= w)
           => !(NatRepr w)
           -> !(e (BaseBVType w))
           -> !(e (BaseBVType w))
           -> App e (BaseBVType w)

  --------------------------------
  -- Float operations

  FloatPZero :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNZero :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNaN :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatPInf :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNInf :: !(FloatPrecisionRepr fpp) -> App e (BaseFloatType fpp)
  FloatNeg
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAbs
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSqrt
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatAdd
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatSub
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMul
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatDiv
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatRem
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMin
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatMax
    :: !(FloatPrecisionRepr fpp)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFMA
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatEq
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatFpEq
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatFpNe
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLe
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatLt
    :: !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e BaseBoolType
  FloatIsNaN :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsInf :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsZero :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsPos :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNeg :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsSubnorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIsNorm :: !(e (BaseFloatType fpp)) -> App e BaseBoolType
  FloatIte
    :: !(FloatPrecisionRepr fpp)
    -> !(e BaseBoolType)
    -> !(e (BaseFloatType fpp))
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatCast
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp'))
    -> App e (BaseFloatType fpp)
  FloatRound
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseFloatType fpp)
  FloatFromBinary
    :: (2 <= eb, 2 <= sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseBVType (eb + sb)))
    -> App e (BaseFloatType (FloatingPointPrecision eb sb))
  FloatToBinary
    :: (2 <= eb, 2 <= sb, 1 <= eb + sb)
    => !(FloatPrecisionRepr (FloatingPointPrecision eb sb))
    -> !(e (BaseFloatType (FloatingPointPrecision eb sb)))
    -> App e (BaseBVType (eb + sb))
  BVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  SBVToFloat
    :: (1 <= w)
    => !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e (BaseBVType w))
    -> App e (BaseFloatType fpp)
  RealToFloat
    :: !(FloatPrecisionRepr fpp)
    -> !RoundingMode
    -> !(e BaseRealType)
    -> App e (BaseFloatType fpp)
  FloatToBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToSBV
    :: (1 <= w)
    => !(NatRepr w)
    -> !RoundingMode
    -> !(e (BaseFloatType fpp))
    -> App e (BaseBVType w)
  FloatToReal :: !(e (BaseFloatType fpp)) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Array operations

  ArrayEq :: !(e (BaseArrayType idx b))
          -> !(e (BaseArrayType idx b))
          -> App e BaseBoolType

  -- Partial map from concrete indices to array values over another array.
  ArrayMap :: !(Ctx.Assignment BaseTypeRepr (i ::> itp))
           -> !(BaseTypeRepr tp)
                -- /\ The type of the array.
           -> !(Hash.Map IndexLit (i ::> itp) e tp)
              -- /\ Maps indices that are updated to the associated value.
           -> !(e (BaseArrayType (i::> itp) tp))
              -- /\ The underlying array that has been updated.
           -> App e (BaseArrayType (i ::> itp) tp)

  -- Constant array
  ConstantArray :: !(Ctx.Assignment BaseTypeRepr (i ::> tp))
                -> !(BaseTypeRepr b)
                -> !(e b)
                -> App e (BaseArrayType (i::>tp) b)

  MuxArray :: !(Ctx.Assignment BaseTypeRepr (i::>tp))
           -> !(BaseTypeRepr b)
           -> !(e BaseBoolType)
           -> !(e (BaseArrayType (i::>tp) b))
           -> !(e (BaseArrayType (i::>tp) b))
           -> App e (BaseArrayType (i::>tp) b)

  UpdateArray :: !(BaseTypeRepr b)
              -> !(Ctx.Assignment BaseTypeRepr (i::>tp))
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> !(e b)
              -> App e (BaseArrayType (i::>tp) b)

  SelectArray :: !(BaseTypeRepr b)
              -> !(e (BaseArrayType (i::>tp) b))
              -> !(Ctx.Assignment e (i::>tp))
              -> App e b

  ------------------------------------------------------------------------
  -- Conversions.

  NatToInteger  :: !(e BaseNatType)  -> App e BaseIntegerType
  -- Converts non-negative integer to nat.
  -- Not defined on negative values.
  IntegerToNat :: !(e BaseIntegerType) -> App e BaseNatType

  IntegerToReal :: !(e BaseIntegerType) -> App e BaseRealType

  -- Convert a real value to an integer
  --
  -- Not defined on non-integral reals.
  RealToInteger :: !(e BaseRealType) -> App e BaseIntegerType

  BVToNat       :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseNatType
  BVToInteger   :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType
  SBVToInteger  :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType
  PredToBV      :: !(e BaseBoolType) -> App e (BaseBVType 1)

  -- Converts integer to a bitvector.  The number is interpreted modulo 2^n.
  IntegerToBV  :: (1 <= w) => !(e BaseIntegerType) -> NatRepr w -> App e (BaseBVType w)

  RoundReal :: !(e BaseRealType) -> App e BaseIntegerType
  FloorReal :: !(e BaseRealType) -> App e BaseIntegerType
  CeilReal  :: !(e BaseRealType) -> App e BaseIntegerType

  ------------------------------------------------------------------------
  -- Complex operations

  Cplx  :: {-# UNPACK #-} !(Complex (e BaseRealType)) -> App e BaseComplexType
  RealPart :: !(e BaseComplexType) -> App e BaseRealType
  ImagPart :: !(e BaseComplexType) -> App e BaseRealType

  ------------------------------------------------------------------------
  -- Structs

  -- A struct with its fields.
  StructCtor :: !(Ctx.Assignment BaseTypeRepr flds)
             -> !(Ctx.Assignment e flds)
             -> App e (BaseStructType flds)

  StructField :: !(e (BaseStructType flds))
              -> !(Ctx.Index flds tp)
              -> !(BaseTypeRepr tp)
              -> App e tp

  StructIte :: !(Ctx.Assignment BaseTypeRepr flds)
            -> !(e BaseBoolType)
            -> !(e (BaseStructType flds))
            -> !(e (BaseStructType flds))
            -> App e (BaseStructType flds)

-- | This type represents 'Expr' values that were built from a
-- 'NonceApp'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'NonceAppExpr' values,
-- but the constructor is kept hidden. The preferred way to construct
-- an 'Expr' from a 'NonceApp' is to use 'sbNonceExpr'.
data NonceAppExpr t (tp :: BaseType)
   = NonceAppExprCtor { nonceExprId  :: {-# UNPACK #-} !(Nonce t tp)
                     , nonceExprLoc :: !ProgramLoc
                     , nonceExprApp :: !(NonceApp t (Expr t) tp)
                     , nonceExprAbsValue :: !(AbstractValue tp)
                     }

-- | This type represents 'Expr' values that were built from an 'App'.
--
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Selector functions are provided to destruct 'AppExpr' values, but
-- the constructor is kept hidden. The preferred way to construct an
-- 'Expr' from an 'App' is to use 'sbMakeExpr'.
data AppExpr t (tp :: BaseType)
   = AppExprCtor { appExprId  :: {-# UNPACK #-} !(Nonce t tp)
                , appExprLoc :: !ProgramLoc
                , appExprApp :: !(App (Expr t) tp)
                , appExprAbsValue :: !(AbstractValue tp)
                }

------------------------------------------------------------------------
-- Expr

-- | The main ExprBuilder expression datastructure. We call the type
-- 'Expr' because each 'Expr' is an element of a DAG that represents
-- sub-term sharing. Expressions of type @Expr t tp@ contain nonces of
-- type @'Nonce' t tp@, which are used to identify shared sub-terms.
--
-- Type parameter @t@ is a phantom type brand used to relate nonces to
-- a specific nonce generator (similar to the @s@ parameter of the
-- @ST@ monad). The type index @tp@ of kind 'BaseType' indicates the
-- type of the values denoted by the given expression.
--
-- Type @'Expr' t@ instantiates the type family @'SymExpr'
-- ('ExprBuilder' t st)@.
data Expr t (tp :: BaseType) where
  SemiRingLiteral :: !(SemiRingRepr tp) -> !(WSum.Coefficient tp) -> !ProgramLoc -> Expr t tp
  BVExpr  :: (1 <= w) => !(NatRepr w) -> !Integer -> !ProgramLoc -> Expr t (BaseBVType w)
  StringExpr :: !Text -> !ProgramLoc -> Expr t BaseStringType
  -- Application
  AppExpr :: {-# UNPACK #-} !(AppExpr t tp) -> Expr t tp
  -- An atomic predicate
  NonceAppExpr :: {-# UNPACK #-} !(NonceAppExpr t tp) -> Expr t tp
  -- A bound variable
  BoundVarExpr :: !(ExprBoundVar t tp) -> Expr t tp

-- | Destructor for the 'AppExpr' constructor.
{-# INLINE asApp #-}
asApp :: Expr t tp -> Maybe (App (Expr t) tp)
asApp (AppExpr a) = Just (appExprApp a)
asApp _ = Nothing

-- | Destructor for the 'NonceAppExpr' constructor.
{-# INLINE asNonceApp #-}
asNonceApp :: Expr t tp -> Maybe (NonceApp t (Expr t) tp)
asNonceApp (NonceAppExpr a) = Just (nonceExprApp a)
asNonceApp _ = Nothing

exprLoc :: Expr t tp -> ProgramLoc
exprLoc (SemiRingLiteral _ _ l) = l
exprLoc (BVExpr _ _ l) = l
exprLoc (StringExpr _ l) = l
exprLoc (NonceAppExpr a)  = nonceExprLoc a
exprLoc (AppExpr a)   = appExprLoc a
exprLoc (BoundVarExpr v) = bvarLoc v

mkExpr :: Nonce t tp
      -> ProgramLoc
      -> App (Expr t) tp
      -> AbstractValue tp
      -> Expr t tp
mkExpr n l a v = AppExpr $ AppExprCtor { appExprId  = n
                                    , appExprLoc = l
                                    , appExprApp = a
                                    , appExprAbsValue = v
                                    }

type BoolExpr t = Expr t BaseBoolType
type NatExpr  t = Expr t BaseNatType
type BVExpr t n = Expr t (BaseBVType n)
type IntegerExpr t = Expr t BaseIntegerType
type RealExpr t = Expr t BaseRealType
type CplxExpr t = Expr t BaseComplexType
type StringExpr t = Expr t BaseStringType

iteSize :: Expr t tp -> Integer
iteSize e =
  case asApp e of
    Just (BVIte _ 0  _ _ _) -> error "iteSize given bad BVIte"
    Just (BVIte _ sz _ _ _) -> sz
    _ -> 0

{-# INLINE boolExprAsBool #-}
boolExprAsBool :: BoolExpr t -> Maybe Bool
boolExprAsBool e
  | Just TrueBool  <- asApp e = Just True
  | Just FalseBool <- asApp e = Just False
  | otherwise = Nothing

instance IsExpr (Expr t) where
  asConstantPred = boolExprAsBool

  asNat (SemiRingLiteral SemiRingNat n _) = Just n
  asNat _ = Nothing

  natBounds x = exprAbsValue x

  asInteger (SemiRingLiteral SemiRingInt n _) = Just n
  asInteger _ = Nothing

  integerBounds x = exprAbsValue x

  asRational (SemiRingLiteral SemiRingReal r _) = Just r
  asRational _ = Nothing

  rationalBounds x = ravRange $ exprAbsValue x

  asComplex e
    | Just (Cplx c) <- asApp e = traverse asRational c
    | otherwise = Nothing

  exprType (SemiRingLiteral sr _ _) = semiRingBase sr
  exprType (BVExpr w _ _) = BaseBVRepr w
  exprType (StringExpr _ _) = BaseStringRepr
  exprType (NonceAppExpr e)  = nonceAppType (nonceExprApp e)
  exprType (AppExpr e) = appType (appExprApp e)
  exprType (BoundVarExpr i) = bvarType i

  asUnsignedBV (BVExpr _ i _) = Just i
  asUnsignedBV _ = Nothing

  asSignedBV x = toSigned (bvWidth x) <$> asUnsignedBV x

  unsignedBVBounds x = BVD.ubounds (bvWidth x) $ exprAbsValue x
  signedBVBounds x = BVD.sbounds (bvWidth x) $ exprAbsValue x

  asString (StringExpr x _) = Just x
  asString _ = Nothing

  asConstantArray (asApp -> Just (ConstantArray _ _ def)) = Just def
  asConstantArray _ = Nothing

  asStruct (asApp -> Just (StructCtor _ flds)) = Just flds
  asStruct _ = Nothing

  printSymExpr = pretty


asSemiRingLit :: Expr t tp -> Maybe (WSum.Coefficient tp)
asSemiRingLit (SemiRingLiteral _sr x _loc) = Just x
asSemiRingLit _ = Nothing


------------------------------------------------------------------------
-- ExprSymFn

-- | This describes information about an undefined or defined function.
-- Parameter @t@ is a phantom type brand used to track nonces.
data SymFnInfo t (args :: Ctx BaseType) (ret :: BaseType)
   = UninterpFnInfo !(Ctx.Assignment BaseTypeRepr args)
                    !(BaseTypeRepr ret)
     -- ^ Information about the argument type and return type of an uninterpreted function.

   | DefinedFnInfo !(Ctx.Assignment (ExprBoundVar t) args)
                   !(Expr t ret)
                   !(Ctx.Assignment (Expr t) args -> Bool)
     -- ^ Information about a defined function.
     -- Includes bound variables, expression associated to a defined function, and
     -- an assignment for determining when to instantiate values.

   | MatlabSolverFnInfo !(MatlabSolverFn (Expr t) args ret)
                        !(Ctx.Assignment (ExprBoundVar t) args)
                        !(Expr t ret)
     -- ^ This is a function that corresponds to a matlab solver function.
     --   It includes the definition as a ExprBuilder expr to
     --   enable export to other solvers.

-- | This represents a symbolic function in the simulator.
-- Parameter @t@ is a phantom type brand used to track nonces.
--
-- Type @'ExprSymFn' t@ instantiates the type family @'SymFn'
-- ('ExprBuilder' t st)@.
data ExprSymFn t (args :: Ctx BaseType) (ret :: BaseType)
   = ExprSymFn { symFnId :: !(Nonce t (args ::> ret))
                 -- /\ A unique identifier for the function
                 , symFnName :: !SolverSymbol
                 -- /\ Name of the function
                 , symFnInfo :: !(SymFnInfo t args ret)
                 -- /\ Information about function
                 , symFnLoc  :: !ProgramLoc
                 -- /\ Location where function was defined.
                 }

instance Show (ExprSymFn t args ret) where
  show f | symFnName f == emptySymbol = "f" ++ show (indexValue (symFnId f))
         | otherwise                  = show (symFnName f)


symFnArgTypes :: ExprSymFn t args ret -> Ctx.Assignment BaseTypeRepr args
symFnArgTypes f =
  case symFnInfo f of
    UninterpFnInfo tps _ -> tps
    DefinedFnInfo vars _ _ -> fmapFC bvarType vars
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverArgTypes fn_id

symFnReturnType :: ExprSymFn t args ret -> BaseTypeRepr ret
symFnReturnType f =
  case symFnInfo f of
    UninterpFnInfo _ tp -> tp
    DefinedFnInfo _ r _ -> exprType r
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverReturnType fn_id

-- | Return solver function associated with ExprSymFn if any.
asMatlabSolverFn :: ExprSymFn t args ret -> Maybe (MatlabSolverFn (Expr t) args ret)
asMatlabSolverFn f
  | MatlabSolverFnInfo g _ _ <- symFnInfo f = Just g
  | otherwise = Nothing



instance Hashable (ExprSymFn t args tp) where
  hashWithSalt s f = s `hashWithSalt` symFnId f

testExprSymFnEq :: ExprSymFn t a1 r1
                  -> ExprSymFn t a2 r2
                  -> Maybe ((a1::>r1) :~: (a2::>r2))
testExprSymFnEq f g = testEquality (symFnId f) (symFnId g)


instance IsSymFn (ExprSymFn t) where
  fnArgTypes = symFnArgTypes
  fnReturnType = symFnReturnType

------------------------------------------------------------------------
-- asConjunction

-- | View a boolean 'Expr' as a conjunction.
asConjunction :: BoolExpr t -> [BoolExpr t]
asConjunction e = asConjunction' [e] Set.empty []

asConjunction' :: [BoolExpr t]
               -> Set (BoolExpr t) -- ^ Set of elements already visited.
               -> [BoolExpr t] -- ^ List of elements.
               -> [BoolExpr t]
asConjunction' [] _ result = result
asConjunction' (h:r) visited result
  | Just TrueBool  <- asApp h = asConjunction' r visited result
  | Just FalseBool <- asApp h = [h]
  | Set.member h visited =
    asConjunction' r visited result
  | Just (AndBool x y) <- asApp h =
    asConjunction' (x:y:r) (Set.insert h visited) result
  | otherwise =
    asConjunction' r (Set.insert h visited) (h:result)

------------------------------------------------------------------------
-- Types

nonceAppType :: NonceApp t e tp -> BaseTypeRepr tp
nonceAppType a =
  case a of
    Forall{} -> knownRepr
    Exists{} -> knownRepr
    ArrayFromFn   fn       -> BaseArrayRepr (symFnArgTypes fn) (symFnReturnType fn)
    MapOverArrays fn idx _ -> BaseArrayRepr idx (symFnReturnType fn)
    ArrayTrueOnEntries _ _ -> knownRepr
    FnApp f _ ->  symFnReturnType f

appType :: App e tp -> BaseTypeRepr tp
appType a =
  case a of
    TrueBool  -> knownRepr
    FalseBool -> knownRepr
    NotBool{} -> knownRepr
    AndBool{} -> knownRepr
    XorBool{} -> knownRepr
    IteBool{} -> knownRepr

    RealIsInteger{} -> knownRepr
    BVTestBit{} -> knownRepr
    BVEq{}    -> knownRepr
    BVSlt{}   -> knownRepr
    BVUlt{}   -> knownRepr
    ArrayEq{} -> knownRepr

    NatDiv{} -> knownRepr
    NatMod{} -> knownRepr

    IntDiv{} -> knownRepr
    IntMod{} -> knownRepr
    IntAbs{} -> knownRepr
    IntDivisible{} -> knownRepr

    SemiRingEq{} -> knownRepr
    SemiRingLe{} -> knownRepr
    SemiRingSum sr _ -> semiRingBase sr
    SemiRingMul sr _ _ -> semiRingBase sr
    SemiRingIte sr _ _ _ -> semiRingBase sr

    RealDiv{} -> knownRepr
    RealSqrt{} -> knownRepr

    RoundReal{} -> knownRepr
    FloorReal{} -> knownRepr
    CeilReal{}  -> knownRepr

    Pi -> knownRepr
    RealSin{}   -> knownRepr
    RealCos{}   -> knownRepr
    RealATan2{} -> knownRepr
    RealSinh{}  -> knownRepr
    RealCosh{}  -> knownRepr

    RealExp{} -> knownRepr
    RealLog{} -> knownRepr

    BVUnaryTerm u  -> BaseBVRepr (UnaryBV.width u)
    BVConcat w _ _ -> BaseBVRepr w
    BVSelect _ n _ -> BaseBVRepr n
    BVNeg w _    -> BaseBVRepr w
    BVAdd w _ _  -> BaseBVRepr w
--    BVSum w _ _  -> BaseBVRepr w
    BVMul w _ _  -> BaseBVRepr w
    BVUdiv w _ _ -> BaseBVRepr w
    BVUrem w _ _ -> BaseBVRepr w
    BVSdiv w _ _ -> BaseBVRepr w
    BVSrem w _ _ -> BaseBVRepr w
    BVIte w _ _ _ _ -> BaseBVRepr w
    BVShl  w _ _  -> BaseBVRepr w
    BVLshr w _ _ -> BaseBVRepr w
    BVAshr w _ _ -> BaseBVRepr w
    BVPopcount w _ -> BaseBVRepr w
    BVCountLeadingZeros w _ -> BaseBVRepr w
    BVCountTrailingZeros w _ -> BaseBVRepr w
    BVZext  w _ -> BaseBVRepr w
    BVSext  w _ -> BaseBVRepr w
    BVBitNot w _ -> BaseBVRepr w
    BVBitAnd w _ _ -> BaseBVRepr w
    BVBitOr  w _ _ -> BaseBVRepr w
    BVBitXor w _ _ -> BaseBVRepr w

    FloatPZero fpp -> BaseFloatRepr fpp
    FloatNZero fpp -> BaseFloatRepr fpp
    FloatNaN fpp -> BaseFloatRepr fpp
    FloatPInf fpp -> BaseFloatRepr fpp
    FloatNInf fpp -> BaseFloatRepr fpp
    FloatNeg fpp _ -> BaseFloatRepr fpp
    FloatAbs fpp _ -> BaseFloatRepr fpp
    FloatSqrt fpp _ _ -> BaseFloatRepr fpp
    FloatAdd fpp _ _ _ -> BaseFloatRepr fpp
    FloatSub fpp _ _ _ -> BaseFloatRepr fpp
    FloatMul fpp _ _ _ -> BaseFloatRepr fpp
    FloatDiv fpp _ _ _ -> BaseFloatRepr fpp
    FloatRem fpp _ _ -> BaseFloatRepr fpp
    FloatMin fpp _ _ -> BaseFloatRepr fpp
    FloatMax fpp _ _ -> BaseFloatRepr fpp
    FloatFMA fpp _ _ _ _ -> BaseFloatRepr fpp
    FloatEq{} -> knownRepr
    FloatFpEq{} -> knownRepr
    FloatFpNe{} -> knownRepr
    FloatLe{} -> knownRepr
    FloatLt{} -> knownRepr
    FloatIsNaN{} -> knownRepr
    FloatIsInf{} -> knownRepr
    FloatIsZero{} -> knownRepr
    FloatIsPos{} -> knownRepr
    FloatIsNeg{} -> knownRepr
    FloatIsSubnorm{} -> knownRepr
    FloatIsNorm{} -> knownRepr
    FloatIte fpp _ _ _ -> BaseFloatRepr fpp
    FloatCast fpp _ _ -> BaseFloatRepr fpp
    FloatRound fpp _ _ -> BaseFloatRepr fpp
    FloatFromBinary fpp _ -> BaseFloatRepr fpp
    FloatToBinary fpp _ -> floatPrecisionToBVType fpp
    BVToFloat fpp _ _ -> BaseFloatRepr fpp
    SBVToFloat fpp _ _ -> BaseFloatRepr fpp
    RealToFloat fpp _ _ -> BaseFloatRepr fpp
    FloatToBV w _ _ -> BaseBVRepr w
    FloatToSBV w _ _ -> BaseBVRepr w
    FloatToReal{} -> knownRepr

    ArrayMap      idx b _ _ -> BaseArrayRepr idx b
    ConstantArray idx b _   -> BaseArrayRepr idx b
    MuxArray idx b _ _ _    -> BaseArrayRepr idx b
    SelectArray b _ _       -> b
    UpdateArray b itp _ _ _     -> BaseArrayRepr itp b

    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    BVToNat{} -> knownRepr
    BVToInteger{} -> knownRepr
    SBVToInteger{} -> knownRepr
    PredToBV _ -> knownRepr

    IntegerToNat{} -> knownRepr
    IntegerToBV _ w -> BaseBVRepr w

    RealToInteger{} -> knownRepr

    Cplx{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    StructCtor flds _     -> BaseStructRepr flds
    StructField _ _ tp    -> tp
    StructIte  flds _ _ _ -> BaseStructRepr flds

------------------------------------------------------------------------
-- ExprAllocator

-- | ExprAllocator provides an interface for creating expressions from
-- an applications.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprAllocator t
   = ExprAllocator { appExpr  :: forall tp
                            .  ProgramLoc
                            -> App (Expr t) tp
                            -> AbstractValue tp
                            -> IO (Expr t tp)
                  , nonceExpr :: forall tp
                             .  ProgramLoc
                             -> NonceApp t (Expr t) tp
                             -> AbstractValue tp
                             -> IO (Expr t tp)
                  }

------------------------------------------------------------------------
-- SymbolVarBimap

-- | A bijective map between vars and their canonical name for printing
-- purposes.
-- Parameter @t@ is a phantom type brand used to track nonces.
newtype SymbolVarBimap t = SymbolVarBimap (Bimap SolverSymbol (SymbolBinding t))

-- | This describes what a given SolverSymbol is associated with.
-- Parameter @t@ is a phantom type brand used to track nonces.
data SymbolBinding t
   = forall tp . VarSymbolBinding !(ExprBoundVar t tp)
     -- ^ Solver
   | forall args ret . FnSymbolBinding  !(ExprSymFn t args ret)

instance Eq (SymbolBinding t) where
  VarSymbolBinding x == VarSymbolBinding y = isJust (testEquality x y)
  FnSymbolBinding  x == FnSymbolBinding  y = isJust (testEquality (symFnId x) (symFnId y))
  _ == _ = False

instance Ord (SymbolBinding t) where
  compare (VarSymbolBinding x) (VarSymbolBinding y) =
    toOrdering (compareF x y)
  compare VarSymbolBinding{} _ = LT
  compare _ VarSymbolBinding{} = GT
  compare (FnSymbolBinding  x) (FnSymbolBinding  y) =
    toOrdering (compareF (symFnId x) (symFnId y))

-- | Empty symbol var bimap
emptySymbolVarBimap :: SymbolVarBimap t
emptySymbolVarBimap = SymbolVarBimap Bimap.empty

lookupBindingOfSymbol :: SolverSymbol -> SymbolVarBimap t -> Maybe (SymbolBinding t)
lookupBindingOfSymbol s (SymbolVarBimap m) = Bimap.lookup s m

lookupSymbolOfBinding :: SymbolBinding t -> SymbolVarBimap t -> Maybe SolverSymbol
lookupSymbolOfBinding b (SymbolVarBimap m) = Bimap.lookupR b m

------------------------------------------------------------------------
-- MatlabSolverFn

-- Parameter @t@ is a phantom type brand used to track nonces.
data MatlabFnWrapper t c where
   MatlabFnWrapper :: !(MatlabSolverFn (Expr t) a r) -> MatlabFnWrapper t (a::> r)

instance TestEquality (MatlabFnWrapper t) where
  testEquality (MatlabFnWrapper f) (MatlabFnWrapper g) = do
    Refl <- testSolverFnEq f g
    return Refl


instance HashableF (MatlabFnWrapper t) where
  hashWithSaltF s (MatlabFnWrapper f) = hashWithSalt s f

data ExprSymFnWrapper t c
   = forall a r . (c ~ (a ::> r)) => ExprSymFnWrapper (ExprSymFn t a r)

data SomeSymFn sym = forall args ret . SomeSymFn (SymFn sym args ret)

------------------------------------------------------------------------
-- ExprBuilder

data FloatInterpretation where
  FloatIEEE :: FloatInterpretation
  FloatUninterpreted :: FloatInterpretation
  FloatReal :: FloatInterpretation
type FloatIEEE = 'FloatIEEE
type FloatUninterpreted = 'FloatUninterpreted
type FloatReal = 'FloatReal

data Flags (fi :: FloatInterpretation)

-- | Cache for storing dag terms.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprBuilder t (st :: Type -> Type) (fs :: Type)
   = SB { sbTrue  :: !(BoolExpr t)
        , sbFalse :: !(BoolExpr t)
          -- | Constant zero.
        , sbZero  :: !(RealExpr t)
          -- | Configuration object for this symbolic backend
        , sbConfiguration :: !CFG.Config
          -- | Flag used to tell the backend whether to evaluate
          -- ground rational values as double precision floats when
          -- a function cannot be evaluated as a rational.
        , sbFloatReduce :: !Bool
          -- | The maximum number of distinct values a term may have and use the
          -- unary representation.
        , sbUnaryThreshold :: !(CFG.OptionSetting BaseIntegerType)
          -- | The maximum number of distinct ranges in a BVDomain expression.
        , sbBVDomainRangeLimit :: !(CFG.OptionSetting BaseIntegerType)
          -- | The starting size when building a new cache
        , sbCacheStartSize :: !(CFG.OptionSetting BaseIntegerType)
          -- | Counter to generate new unique identifiers for elements and functions.
        , exprCounter :: !(NonceGenerator IO t)
          -- | Reference to current allocator for expressions.
        , curAllocator :: !(IORef (ExprAllocator t))
          -- | Number of times an 'Expr' for a non-linear operation has been
          -- created.
        , sbNonLinearOps :: !(IORef Integer)
          -- | The current program location
        , sbProgramLoc :: !(IORef ProgramLoc)
          -- | Additional state maintained by the state manager
        , sbStateManager :: !(IORef (st t))

        , sbVarBindings :: !(IORef (SymbolVarBimap t))
        , sbUninterpFnCache :: !(IORef (Map (SolverSymbol, Some (Ctx.Assignment BaseTypeRepr)) (SomeSymFn (ExprBuilder t st fs))))
          -- | Cache for Matlab functions
        , sbMatlabFnCache
          :: !(PH.HashTable RealWorld (MatlabFnWrapper t) (ExprSymFnWrapper t))
        , sbSolverLogger
          :: !(IORef (Maybe (SolverEvent -> IO ())))
        }

type instance SymFn (ExprBuilder t st fs) = ExprSymFn t
type instance SymExpr (ExprBuilder t st fs) = Expr t
type instance BoundVar (ExprBuilder t st fs) = ExprBoundVar t

sbBVDomainParams :: ExprBuilder t st fs -> IO (BVD.BVDomainParams)
sbBVDomainParams sym =
  do rl <- CFG.getOpt (sbBVDomainRangeLimit sym)
     return BVD.DP { BVD.rangeLimit = fromInteger rl }


------------------------------------------------------------------------
-- abstractEval

-- | Return abstract domain associated with a nonce app
quantAbsEval :: ExprBuilder t st fs
             -> (forall u . Expr t u -> AbstractValue u)
             -> NonceApp t (Expr t) tp
             -> AbstractValue tp
quantAbsEval _ f q =
  case q of
    Forall _ v -> f v
    Exists _ v -> f v
    ArrayFromFn _       -> unconstrainedAbsValue (nonceAppType q)
    MapOverArrays g _ _ -> unconstrainedAbsValue tp
      where tp = symFnReturnType g
    ArrayTrueOnEntries _ a -> f a
    FnApp g _           -> unconstrainedAbsValue (symFnReturnType g)

abstractEval :: BVD.BVDomainParams
             -> (forall u . Expr t u -> AbstractValue u)
             -> App (Expr t) tp
             -> AbstractValue tp
abstractEval bvParams f a0 = do
  case a0 of

    ------------------------------------------------------------------------
    -- Boolean operations
    TrueBool -> Just True
    FalseBool -> Just False
    NotBool x -> not <$> f x
    AndBool x y -> absAnd (f x) (f y)
    XorBool x y -> Bits.xor <$> f x <*> f y
    IteBool c x y | Just True  <- f c -> f x
                  | Just False <- f c -> f y
                  | Just True  <- f x -> absOr  (f c) (f y)
                  | Just False <- f x -> absAnd (not <$> f c) (f y)
                  | Just True  <- f y -> absOr  (not <$> f c) (f x)
                  | Just False <- f y -> absAnd (f c) (f x)
                  | otherwise -> Nothing

    SemiRingEq{} -> Nothing
    SemiRingLe{} -> Nothing
    RealIsInteger{} -> Nothing
    BVTestBit{} -> Nothing
    BVEq{} -> Nothing
    BVSlt{} -> Nothing
    BVUlt{} -> Nothing
    ArrayEq{} -> Nothing

    ------------------------------------------------------------------------
    -- Arithmetic operations

    NatDiv x y -> natRangeDiv (f x) (f y)
    NatMod x y -> natRangeMod (f x) (f y)

    IntAbs x -> intAbsRange (f x)
    IntDiv x y -> intDivRange (f x) (f y)
    IntMod x y -> intModRange (f x) (f y)
    IntDivisible x 0 -> rangeCheckEq (SingleRange 0) (f x)
    IntDivisible x n -> rangeCheckEq (SingleRange 0) (intModRange (f x) (SingleRange (toInteger n)))

    SemiRingMul SemiRingInt x y -> mulRange (f x) (f y)
    SemiRingSum SemiRingInt s -> WSum.eval addRange smul SingleRange s
      where smul sm e = rangeScalarMul sm (f e)
    SemiRingIte SemiRingInt _ x y -> joinRange (f x) (f y)

    SemiRingMul SemiRingNat x y -> natRangeMul (f x) (f y)
    SemiRingSum SemiRingNat s -> WSum.eval natRangeAdd smul natSingleRange s
      where smul sm e = natRangeScalarMul sm (f e)
    SemiRingIte SemiRingNat _ x y -> natRangeJoin (f x) (f y)

    SemiRingMul SemiRingReal x y -> ravMul (f x) (f y)
    SemiRingSum SemiRingReal s -> WSum.eval ravAdd smul ravSingle s
      where smul sm e = ravScalarMul sm (f e)
    SemiRingIte SemiRingReal _ x y -> ravJoin (f x) (f y)

    RealDiv _ _ -> ravUnbounded
    RealSqrt _  -> ravUnbounded
    Pi -> ravConcreteRange 3.14 3.15
    RealSin _ -> ravConcreteRange (-1) 1
    RealCos _ -> ravConcreteRange (-1) 1
    RealATan2 _ _ -> ravUnbounded
    RealSinh _ -> ravUnbounded
    RealCosh _ -> ravUnbounded
    RealExp _ -> ravUnbounded
    RealLog _ -> ravUnbounded

    BVUnaryTerm u -> UnaryBV.domain bvParams f u
    BVConcat _ x y -> BVD.concat bvParams (bvWidth x) (f x) (bvWidth y) (f y)
    BVSelect i n x -> BVD.select bvParams i n (f x)
    BVNeg w x   -> BVD.negate bvParams w (f x)
    BVAdd w x y -> BVD.add bvParams w (f x) (f y)
    {-
    BVSum w s ->   WSum.eval add smul single s
      where add = BVD.add bvParams w
            smul c x = BVD.mul bvParams w (BVD.singleton w c) (f x)
            single = BVD.singleton w
-}
    BVMul w x y -> BVD.mul bvParams w (f x) (f y)
    BVUdiv w x y -> BVD.udiv w (f x) (f y)
    BVUrem w x y -> BVD.urem w (f x) (f y)
    BVSdiv w x y -> BVD.sdiv w (f x) (f y)
    BVSrem w x y -> BVD.srem w (f x) (f y)
    BVIte w _ _ x y -> BVD.union bvParams w (f x) (f y)

    BVShl  w x y -> BVD.shl w (f x) (f y)
    BVLshr w x y -> BVD.lshr w (f x) (f y)
    BVAshr w x y -> BVD.ashr w (f x) (f y)
    BVZext w x   -> BVD.zext (f x) w
    BVSext w x   -> BVD.sext bvParams (bvWidth x) (f x) w

    BVPopcount w _ -> BVD.range w 0 (intValue w)
    BVCountLeadingZeros w _ -> BVD.range w 0 (intValue w)
    BVCountTrailingZeros w _ -> BVD.range w 0 (intValue w)

    BVBitNot w x   -> BVD.not w (f x)
    BVBitAnd w x y -> BVD.and w (f x) (f y)
    BVBitOr  w x y -> BVD.or  w (f x) (f y)
    BVBitXor w x y -> BVD.xor w (f x) (f y)

    FloatPZero{} -> ()
    FloatNZero{} -> ()
    FloatNaN{} -> ()
    FloatPInf{} -> ()
    FloatNInf{} -> ()
    FloatNeg{} -> ()
    FloatAbs{} -> ()
    FloatSqrt{} -> ()
    FloatAdd{} -> ()
    FloatSub{} -> ()
    FloatMul{} -> ()
    FloatDiv{} -> ()
    FloatRem{} -> ()
    FloatMin{} -> ()
    FloatMax{} -> ()
    FloatFMA{} -> ()
    FloatEq{} -> Nothing
    FloatFpEq{} -> Nothing
    FloatFpNe{} -> Nothing
    FloatLe{} -> Nothing
    FloatLt{} -> Nothing
    FloatIsNaN{} -> Nothing
    FloatIsInf{} -> Nothing
    FloatIsZero{} -> Nothing
    FloatIsPos{} -> Nothing
    FloatIsNeg{} -> Nothing
    FloatIsSubnorm{} -> Nothing
    FloatIsNorm{} -> Nothing
    FloatIte{} -> ()
    FloatCast{} -> ()
    FloatRound{} -> ()
    FloatFromBinary{} -> ()
    FloatToBinary fpp _ -> case floatPrecisionToBVType fpp of
      BaseBVRepr w -> BVD.range w (minUnsigned w) (maxUnsigned w)
    BVToFloat{} -> ()
    SBVToFloat{} -> ()
    RealToFloat{} -> ()
    FloatToBV w _ _ -> BVD.range w (minUnsigned w) (maxUnsigned w)
    FloatToSBV w _ _ -> BVD.range w (minSigned w) (maxSigned w)
    FloatToReal{} -> ravUnbounded

    ArrayMap _ bRepr m d ->
      withAbstractable bRepr $
        Map.foldl' (\av e -> avJoin bRepr (f e) av) (f d) (Hash.hashedMap m)
    ConstantArray _idxRepr _bRepr v -> f v
    MuxArray _idxRepr bRepr _ x y ->
       withAbstractable bRepr $ avJoin bRepr (f x) (f y)
    SelectArray _bRepr a _i -> f a  -- FIXME?
    UpdateArray bRepr _ a _i v -> withAbstractable bRepr $ avJoin bRepr (f a) (f v)

    NatToInteger x -> natRangeToRange (f x)
    IntegerToReal x -> RAV (mapRange toRational (f x)) (Just True)
    BVToNat x -> natRange (fromInteger lx) (Inclusive (fromInteger ux))
      where Just (lx, ux) = BVD.ubounds (bvWidth x) (f x)
    BVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where Just (lx, ux) = BVD.ubounds (bvWidth x) (f x)
    SBVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where Just (lx, ux) = BVD.sbounds (bvWidth x) (f x)
    PredToBV p ->
      case f p of
        Nothing    -> BVD.range (knownNat @1) 0 1
        Just True  -> BVD.singleton (knownNat @1) 1
        Just False -> BVD.singleton (knownNat @1) 0
    RoundReal x -> mapRange roundAway (ravRange (f x))
    FloorReal x -> mapRange floor (ravRange (f x))
    CeilReal x  -> mapRange ceiling (ravRange (f x))
    IntegerToNat x ->
       case f x of
         SingleRange c              -> NatSingleRange (fromInteger (max 0 c))
         MultiRange Unbounded u     -> natRange 0 (fromInteger . max 0 <$> u)
         MultiRange (Inclusive l) u -> natRange (fromInteger (max 0 l)) (fromInteger . max 0 <$> u)
    IntegerToBV x w -> BVD.range w l u
      where rng = f x
            l = case rangeLowBound rng of
                  Unbounded -> minUnsigned w
                  Inclusive v -> max (minUnsigned w) v
            u = case rangeHiBound rng of
                  Unbounded -> maxUnsigned w
                  Inclusive v -> min (maxUnsigned w) v
    RealToInteger x -> valueRange (ceiling <$> lx) (floor <$> ux)
      where lx = rangeLowBound rng
            ux = rangeHiBound rng
            rng = ravRange (f x)

    Cplx c -> f <$> c
    RealPart x -> realPart (f x)
    ImagPart x -> imagPart (f x)

    StructCtor _ flds -> fmapFC (\v -> AbstractValueWrapper (f v)) flds
    StructField s idx _ -> unwrapAV (f s Ctx.! idx)
    StructIte flds _p x y ->
      let tp = BaseStructRepr flds
       in withAbstractable tp $ avJoin tp (f x) (f y)

-- | Get abstract value associated with element.
exprAbsValue :: Expr t tp -> AbstractValue tp
exprAbsValue (SemiRingLiteral sr x _) =
  case sr of
    SemiRingNat  -> natSingleRange x
    SemiRingInt  -> singleRange x
    SemiRingReal -> ravSingle x
exprAbsValue (StringExpr{})   = ()
exprAbsValue (BVExpr w c _)   = BVD.singleton w c
exprAbsValue (NonceAppExpr e) = nonceExprAbsValue e
exprAbsValue (AppExpr e)      = appExprAbsValue e
exprAbsValue (BoundVarExpr v) =
  fromMaybe (unconstrainedAbsValue (bvarType v)) (bvarAbstractValue v)

-- | Return an unconstrained abstract value.
unconstrainedAbsValue :: BaseTypeRepr tp -> AbstractValue tp
unconstrainedAbsValue tp = withAbstractable tp (avTop tp)

------------------------------------------------------------------------

-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

------------------------------------------------------------------------
-- App operations

-- | Pretty print a code to identify the type of constant.
ppVarTypeCode :: BaseTypeRepr tp -> String
ppVarTypeCode tp =
  case tp of
    BaseNatRepr     -> "n"
    BaseBoolRepr    -> "b"
    BaseBVRepr _    -> "bv"
    BaseIntegerRepr -> "i"
    BaseRealRepr    -> "r"
    BaseFloatRepr _ -> "f"
    BaseStringRepr  -> "s"
    BaseComplexRepr -> "c"
    BaseArrayRepr _ _ -> "a"
    BaseStructRepr _ -> "struct"

-- | Either a argument or text or text
type PrettyArg (e :: BaseType -> Type) = Either (Some e) Text

exprPrettyArg :: e tp -> PrettyArg e
exprPrettyArg e = Left $! Some e

exprPrettyIndices :: Ctx.Assignment e ctx -> [PrettyArg e]
exprPrettyIndices = toListFC exprPrettyArg

stringPrettyArg :: String -> PrettyArg e
stringPrettyArg x = Right $! Text.pack x

showPrettyArg :: Show a => a -> PrettyArg e
showPrettyArg x = stringPrettyArg $! show x

type PrettyApp e = (Text, [PrettyArg e])

prettyApp :: Text -> [PrettyArg e] -> PrettyApp e
prettyApp nm args = (nm, args)

ppNonceApp :: forall m t e tp
           . Applicative m
           => (forall ctx r . ExprSymFn t ctx r -> m (PrettyArg e))
           -> NonceApp t e tp
           -> m (PrettyApp e)
ppNonceApp ppFn a0 = do
  case a0 of
    Forall v x -> pure $ prettyApp "forall" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    Exists v x -> pure $ prettyApp "exists" [ stringPrettyArg (ppBoundVar v), exprPrettyArg x ]
    ArrayFromFn f -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayFromFn" [ f_nm ]
    MapOverArrays f _ args -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "mapArray" (f_nm : arg_nms)
            arg_nms = toListFC (\(ArrayResultWrapper a) -> exprPrettyArg a) args
    ArrayTrueOnEntries f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayTrueOnEntries" [ f_nm, a_nm ]
            a_nm = exprPrettyArg a
    FnApp f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "apply" (f_nm : toListFC exprPrettyArg a)

instance ShowF e => Pretty (App e u) where
  pretty a = text (Text.unpack nm) <+> sep (ppArg <$> args)
    where (nm, args) = ppApp' a
          ppArg :: PrettyArg e -> Doc
          ppArg (Left (Some e)) = text (showF e)
          ppArg (Right txt) = text (Text.unpack txt)

instance ShowF e => Show (App e u) where
  show = show . pretty

ppApp' :: forall e u . App e u -> PrettyApp e
ppApp' a0 = do
  let ppSExpr :: Text -> [e x] -> PrettyApp e
      ppSExpr f l = prettyApp f (exprPrettyArg <$> l)

      ppITE :: Text -> e BaseBoolType -> e x -> e x -> PrettyApp e
      ppITE nm c x y = prettyApp nm [exprPrettyArg c, exprPrettyArg x, exprPrettyArg y]

  case a0 of
    TrueBool    -> prettyApp "true" []
    FalseBool   -> prettyApp "false" []
    NotBool x   -> ppSExpr "boolNot" [x]
    AndBool x y -> ppSExpr "boolAnd" [x, y]
    XorBool x y -> ppSExpr "boolXor" [x, y]
    IteBool x y z -> ppITE "boolIte" x y z

    RealIsInteger x -> ppSExpr "isInteger" [x]
    BVTestBit i x   -> prettyApp "testBit"  [exprPrettyArg x, showPrettyArg i]
    BVEq  x y   -> ppSExpr "bvEq" [x, y]
    BVUlt x y -> ppSExpr "bvUlt" [x, y]
    BVSlt x y -> ppSExpr "bvSlt" [x, y]
    ArrayEq x y -> ppSExpr "arrayEq" [x, y]

    NatDiv x y -> ppSExpr "natDiv" [x, y]
    NatMod x y -> ppSExpr "natMod" [x, y]

    IntAbs x   -> prettyApp "intAbs" [exprPrettyArg x]
    IntDiv x y -> prettyApp "intDiv" [exprPrettyArg x, exprPrettyArg y]
    IntMod x y -> prettyApp "intMod" [exprPrettyArg x, exprPrettyArg y]
    IntDivisible x k -> prettyApp "intDivisible" [exprPrettyArg x, showPrettyArg k]

    SemiRingEq sr x y ->
      case sr of
        SemiRingReal -> ppSExpr "realEq" [x, y]
        SemiRingInt  -> ppSExpr "intEq" [x, y]
        SemiRingNat  -> ppSExpr "natEq" [x, y]

    SemiRingLe sr x y ->
      case sr of
        SemiRingReal -> ppSExpr "realLe" [x, y]
        SemiRingInt  -> ppSExpr "intLe" [x, y]
        SemiRingNat  -> ppSExpr "natLe" [x, y]

    SemiRingSum sr s ->
      case sr of
        SemiRingReal -> prettyApp "realSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppRat c) ]
                ppEntry 1 e = [ exprPrettyArg e ]
                ppEntry sm e = [ stringPrettyArg (ppRat sm ++ "*"), exprPrettyArg e ]
                ppRat r | d == 1 = show n
                        | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
                     where n = numerator r
                           d = denominator r

        SemiRingInt -> prettyApp "intSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ stringPrettyArg (show sm ++ "*"), exprPrettyArg e ]

        SemiRingNat  -> prettyApp "natSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ stringPrettyArg (show sm ++ "*"), exprPrettyArg e ]

    SemiRingMul sr x y ->
      case sr of
        SemiRingReal -> ppSExpr "realMul" [x, y]
        SemiRingInt  -> ppSExpr "intMul" [x, y]
        SemiRingNat  -> ppSExpr "natMul" [x, y]

    SemiRingIte sr x y z ->
      case sr of
        SemiRingReal -> ppITE "realIte" x y z
        SemiRingInt  -> ppITE "intIte" x y z
        SemiRingNat  -> ppITE "natIte" x y z

    RealDiv x y -> ppSExpr "divReal" [x, y]
    RealSqrt x  -> ppSExpr "sqrt" [x]

    Pi -> prettyApp "pi" []
    RealSin x     -> ppSExpr "sin" [x]
    RealCos x     -> ppSExpr "cos" [x]
    RealATan2 x y -> ppSExpr "atan2" [x, y]
    RealSinh x    -> ppSExpr "sinh" [x]
    RealCosh x    -> ppSExpr "cosh" [x]

    RealExp x -> ppSExpr "exp" [x]
    RealLog x -> ppSExpr "log" [x]

    --------------------------------
    -- Bitvector operations

    BVUnaryTerm u -> prettyApp "bvUnary" (concatMap go $ UnaryBV.unsignedEntries u)
      where go :: (Integer, e BaseBoolType) -> [PrettyArg e]
            go (k,v) = [ exprPrettyArg v, showPrettyArg k ]
    BVConcat _ x y -> prettyApp "bvConcat" [exprPrettyArg x, exprPrettyArg y]
    BVSelect idx n x -> prettyApp "bvSelect" [showPrettyArg idx, showPrettyArg n, exprPrettyArg x]
    BVNeg  _ x   -> ppSExpr "bvNeg" [x]
    BVAdd  _ x y -> ppSExpr "bvAdd" [x, y]
    BVMul  _ x y -> ppSExpr "bvMul" [x, y]
    BVUdiv _ x y -> ppSExpr "bvUdiv" [x, y]
    BVUrem _ x y -> ppSExpr "bvUrem" [x, y]
    BVSdiv _ x y -> ppSExpr "bvSdiv" [x, y]
    BVSrem _ x y -> ppSExpr "bvSrem" [x, y]

    BVIte _ _ c x y -> ppITE "bvIte" c x y

    BVShl  _ x y -> ppSExpr "bvShl" [x, y]
    BVLshr _ x y -> ppSExpr "bvLshr" [x, y]
    BVAshr _ x y -> ppSExpr "bvAshr" [x, y]

    BVZext w x -> prettyApp "bvZext"   [showPrettyArg w, exprPrettyArg x]
    BVSext w x -> prettyApp "bvSext"   [showPrettyArg w, exprPrettyArg x]

    BVPopcount w x -> prettyApp "bvPopcount" [showPrettyArg w, exprPrettyArg x]
    BVCountLeadingZeros w x -> prettyApp "bvCountLeadingZeros" [showPrettyArg w, exprPrettyArg x]
    BVCountTrailingZeros w x -> prettyApp "bvCountTrailingZeros" [showPrettyArg w, exprPrettyArg x]

    BVBitNot _ x   -> ppSExpr "bvNot" [x]
    BVBitAnd _ x y -> ppSExpr "bvAnd" [x, y]
    BVBitOr  _ x y -> ppSExpr "bvOr"  [x, y]
    BVBitXor _ x y -> ppSExpr "bvXor" [x, y]

    --------------------------------
    -- Float operations
    FloatPZero _ -> prettyApp "floatPZero" []
    FloatNZero _ -> prettyApp "floatNZero" []
    FloatNaN _ -> prettyApp "floatNaN" []
    FloatPInf _ -> prettyApp "floatPInf" []
    FloatNInf _ -> prettyApp "floatNInf" []
    FloatNeg _ x -> ppSExpr "floatNeg" [x]
    FloatAbs _ x -> ppSExpr "floatAbs" [x]
    FloatSqrt _ r x -> ppSExpr (Text.pack $ "floatSqrt " <> show r) [x]
    FloatAdd _ r x y -> ppSExpr (Text.pack $ "floatAdd " <> show r) [x, y]
    FloatSub _ r x y -> ppSExpr (Text.pack $ "floatSub " <> show r) [x, y]
    FloatMul _ r x y -> ppSExpr (Text.pack $ "floatMul " <> show r) [x, y]
    FloatDiv _ r x y -> ppSExpr (Text.pack $ "floatDiv " <> show r) [x, y]
    FloatRem _ x y -> ppSExpr "floatRem" [x, y]
    FloatMin _ x y -> ppSExpr "floatMin" [x, y]
    FloatMax _ x y -> ppSExpr "floatMax" [x, y]
    FloatFMA _ r x y z -> ppSExpr (Text.pack $ "floatFMA " <> show r) [x, y, z]
    FloatEq x y -> ppSExpr "floatEq" [x, y]
    FloatFpEq x y -> ppSExpr "floatFpEq" [x, y]
    FloatFpNe x y -> ppSExpr "floatFpNe" [x, y]
    FloatLe x y -> ppSExpr "floatLe" [x, y]
    FloatLt x y -> ppSExpr "floatLt" [x, y]
    FloatIsNaN x -> ppSExpr "floatIsNaN" [x]
    FloatIsInf x -> ppSExpr "floatIsInf" [x]
    FloatIsZero x -> ppSExpr "floatIsZero" [x]
    FloatIsPos x -> ppSExpr "floatIsPos" [x]
    FloatIsNeg x -> ppSExpr "floatIsNeg" [x]
    FloatIsSubnorm x -> ppSExpr "floatIsSubnorm" [x]
    FloatIsNorm x -> ppSExpr "floatIsNorm" [x]
    FloatIte _ c x y -> ppITE "floatIte" c x y
    FloatCast _ r x -> ppSExpr (Text.pack $ "floatCast " <> show r) [x]
    FloatRound _ r x -> ppSExpr (Text.pack $ "floatRound " <> show r) [x]
    FloatFromBinary _ x -> ppSExpr "floatFromBinary" [x]
    FloatToBinary _ x -> ppSExpr "floatToBinary" [x]
    BVToFloat _ r x -> ppSExpr (Text.pack $ "bvToFloat " <> show r) [x]
    SBVToFloat _ r x -> ppSExpr (Text.pack $ "sbvToFloat " <> show r) [x]
    RealToFloat _ r x -> ppSExpr (Text.pack $ "realToFloat " <> show r) [x]
    FloatToBV _ r x -> ppSExpr (Text.pack $ "floatToBV " <> show r) [x]
    FloatToSBV _ r x -> ppSExpr (Text.pack $ "floatToSBV " <> show r) [x]
    FloatToReal x -> ppSExpr "floatToReal " [x]

    -------------------------------------
    -- Arrays

    ArrayMap _ _ m d ->
        prettyApp "arrayMap" (Map.foldrWithKey ppEntry [exprPrettyArg d] (Hash.hashedMap m))
      where ppEntry k e l = showPrettyArg k : exprPrettyArg e : l
    ConstantArray _ _ v ->
      prettyApp "constArray" [exprPrettyArg v]
    MuxArray _ _ p x y ->
      prettyApp "muxArray" [exprPrettyArg p, exprPrettyArg x, exprPrettyArg y]
    SelectArray _ a i ->
      prettyApp "select" (exprPrettyArg a : exprPrettyIndices i)
    UpdateArray _ _ a i v ->
      prettyApp "update" ([exprPrettyArg a] ++ exprPrettyIndices i ++ [exprPrettyArg v])

    ------------------------------------------------------------------------
    -- Conversions.

    NatToInteger x  -> ppSExpr "natToInteger" [x]
    IntegerToReal x -> ppSExpr "integerToReal" [x]
    BVToNat x       -> ppSExpr "bvToNat" [x]
    BVToInteger  x  -> ppSExpr "bvToInteger" [x]
    SBVToInteger x  -> ppSExpr "sbvToInteger" [x]
    PredToBV x      -> prettyApp "predToBV" [exprPrettyArg x]

    RoundReal x -> ppSExpr "round" [x]
    FloorReal x -> ppSExpr "floor" [x]
    CeilReal  x -> ppSExpr "ceil"  [x]

    IntegerToNat x   -> ppSExpr "integerToNat" [x]
    IntegerToBV x w -> prettyApp "integerToBV" [exprPrettyArg x, showPrettyArg w]

    RealToInteger x   -> ppSExpr "realToInteger" [x]

    ------------------------------------------------------------------------
    -- Complex operations

    Cplx (r :+ i) -> ppSExpr "complex" [r, i]
    RealPart x -> ppSExpr "realPart" [x]
    ImagPart x -> ppSExpr "imagPart" [x]

    ------------------------------------------------------------------------
    -- SymStruct

    StructCtor _ flds -> prettyApp "struct" (toListFC exprPrettyArg flds)
    StructField s idx _ ->
      prettyApp "field" [exprPrettyArg s, showPrettyArg idx]
    StructIte _ c x y -> ppITE "ite" c x y



instance Eq (NonceApp t (Expr t) tp) where
  x == y = isJust (testEquality x y)

instance TestEquality (NonceApp t (Expr t)) where
  testEquality =
    $(structuralTypeEquality [t|NonceApp|]
           [ (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (DataArg 1 `TypeApp` AnyType, [|testEquality|])
           , ( ConType [t|ExprBoundVar|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|ExprSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
              , [|testExprSymFnEq|]
              )
           , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           ]
          )

instance HashableF (NonceApp t (Expr t)) where
  hashWithSaltF = $(structuralHash [t|NonceApp|])

instance FunctorFC (NonceApp t)  where
  fmapFC = fmapFCDefault

instance FoldableFC (NonceApp t) where
  foldMapFC = foldMapFCDefault

traverseArrayResultWrapper
  :: Functor m
  => (forall tp . e tp -> m (f tp))
     -> ArrayResultWrapper e (idx ::> itp) c
     -> m (ArrayResultWrapper f (idx ::> itp) c)
traverseArrayResultWrapper f (ArrayResultWrapper a) =
  ArrayResultWrapper <$> f a

traverseArrayResultWrapperAssignment
  :: Applicative m
  => (forall tp . e tp -> m (f tp))
     -> Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) c
     -> m (Ctx.Assignment (ArrayResultWrapper f (idx ::> itp)) c)
traverseArrayResultWrapperAssignment f = traverseFC (\e -> traverseArrayResultWrapper f e)

instance TraversableFC (NonceApp t) where
  traverseFC =
    $(structuralTraversal [t|NonceApp|]
      [ ( ConType [t|Ctx.Assignment|]
          `TypeApp` (ConType [t|ArrayResultWrapper|] `TypeApp` AnyType `TypeApp` AnyType)
          `TypeApp` AnyType
        , [|traverseArrayResultWrapperAssignment|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` ConType [t|BaseTypeRepr|] `TypeApp` AnyType
        , [|\_ -> pure|]
        )
      , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
        , [|traverseFC|]
        )
      ]
     )

------------------------------------------------------------------------
-- App operations

-- | Used to implement foldMapFc from traversal.
data Dummy (tp :: k)

instance Eq (Dummy tp) where
  _ == _ = True
instance EqF Dummy where
  eqF _ _ = True
instance TestEquality Dummy where
  testEquality !_x !_y = error "you made a magic Dummy value!"

instance Ord (Dummy tp) where
  compare _ _ = EQ
instance OrdF Dummy where
  compareF !_x !_y = error "you made a magic Dummy value!"

instance HashableF Dummy where
  hashWithSaltF _ _ = 0

instance FoldableFC App where
  foldMapFC f0 t = getConst (traverseApp (g f0) t)
    where g :: (f tp -> a) -> f tp -> Const a (Dummy tp)
          g f v = Const (f v)

traverseApp :: (Applicative m, OrdF f, Eq (f (BaseBoolType)), HashableF f)
            => (forall tp. e tp -> m (f tp))
            -> App e utp -> m ((App f) utp)
traverseApp =
  $(structuralTraversal [t|App|]
    [ ( ConType [t|UnaryBV|] `TypeApp` AnyType `TypeApp` AnyType
      , [|UnaryBV.instantiate|]
      )
    , ( ConType [t|Ctx.Assignment BaseTypeRepr|] `TypeApp` AnyType
      , [|(\_ -> pure) |]
      )
    , ( ConType [t|WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseVars |]
      )
    ,  ( ConType [t|Hash.Map |] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
       , [| Hash.traverseHashedMap |]
       )
    , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
      , [|traverseFC|]
      )
    ]
   )

-- | Return 'true' if an app represents a non-linear operation.
-- Controls whether the non-linear counter ticks upward in the
-- 'Statistics'.
isNonLinearApp :: App e tp -> Bool
isNonLinearApp app = case app of
  -- FIXME: These are just guesses; someone who knows what's actually
  -- slow in the solvers should correct them.
  SemiRingMul {} -> True
  NatDiv {} -> True
  NatMod {} -> True
  IntDiv {} -> True
  IntMod {} -> True
  IntDivisible {} -> True
  RealDiv {} -> True
  RealSqrt {} -> True
  RealSin {} -> True
  RealCos {} -> True
  RealATan2 {} -> True
  RealSinh {} -> True
  RealCosh {} -> True
  RealExp {} -> True
  RealLog {} -> True
  BVMul {} -> True
  BVUdiv {} -> True
  BVUrem {} -> True
  BVSdiv {} -> True
  BVSrem {} -> True
  FloatSqrt {} -> True
  FloatMul {} -> True
  FloatDiv {} -> True
  FloatRem {} -> True
  _ -> False

------------------------------------------------------------------------
-- Expr operations

{-# INLINE compareExpr #-}
compareExpr :: Expr t x -> Expr t y -> OrderingF x y
compareExpr (SemiRingLiteral srx x _) (SemiRingLiteral sry y _) =
  case compareF srx sry of
    LTF -> LTF
    EQF -> fromOrdering (WSum.semiringCompare srx x y)
    GTF -> GTF
compareExpr SemiRingLiteral{} _ = LTF
compareExpr _ SemiRingLiteral{} = GTF

compareExpr (BVExpr wx x _) (BVExpr wy y _) =
  case compareF wx wy of
    LTF -> LTF
    EQF -> fromOrdering (compare x y)
    GTF -> GTF
compareExpr BVExpr{} _ = LTF
compareExpr _ BVExpr{} = GTF

compareExpr (StringExpr x _) (StringExpr y _) = fromOrdering (compare x y)
compareExpr StringExpr{} _ = LTF
compareExpr _ StringExpr{} = GTF

compareExpr (NonceAppExpr x) (NonceAppExpr y) = compareF x y
compareExpr NonceAppExpr{} _ = LTF
compareExpr _ NonceAppExpr{} = GTF

compareExpr (AppExpr x) (AppExpr y) = compareF (appExprId x) (appExprId y)
compareExpr AppExpr{} _ = LTF
compareExpr _ AppExpr{} = GTF

compareExpr (BoundVarExpr x) (BoundVarExpr y) = compareF x y

instance TestEquality (NonceAppExpr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (NonceAppExpr t)  where
  compareF x y = compareF (nonceExprId x) (nonceExprId y)

instance Eq (NonceAppExpr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (NonceAppExpr t tp) where
  compare x y = toOrdering (compareF x y)

instance TestEquality (Expr t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (Expr t)  where
  compareF = compareExpr

instance Eq (Expr t tp) where
  x == y = isJust (testEquality x y)

instance Ord (Expr t tp) where
  compare x y = toOrdering (compareF x y)

instance Hashable (Expr t tp) where
  hashWithSalt s (SemiRingLiteral sr x _) =
    case sr of
      SemiRingNat  -> hashWithSalt (hashWithSalt s (0::Int)) x
      SemiRingInt  -> hashWithSalt (hashWithSalt s (1::Int)) x
      SemiRingReal -> hashWithSalt (hashWithSalt s (2::Int)) x
  hashWithSalt s (BVExpr w x _) =
    s `hashWithSalt` (3::Int)
      `hashWithSalt` w
      `hashWithSalt` x
  hashWithSalt s (StringExpr x _) = hashWithSalt (hashWithSalt s (4::Int)) x
  hashWithSalt s (AppExpr x)      = hashWithSalt (hashWithSalt s (5::Int)) (appExprId x)
  hashWithSalt s (NonceAppExpr x) = hashWithSalt (hashWithSalt s (6::Int)) (nonceExprId x)
  hashWithSalt s (BoundVarExpr x) = hashWithSalt (hashWithSalt s (7::Int)) x

instance PH.HashableF (Expr t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- PPIndex

data PPIndex
   = ExprPPIndex {-# UNPACK #-} !Word64
   | RatPPIndex !Rational
  deriving (Eq, Ord, Generic)

instance Hashable PPIndex

------------------------------------------------------------------------
-- countOccurrences

countOccurrences :: Expr t tp -> Map.Map PPIndex Int
countOccurrences e0 = runST $ do
  visited <- H.new
  countOccurrences' visited e0
  Map.fromList <$> H.toList visited

type OccurrenceTable s = H.HashTable s PPIndex Int


incOccurrence :: OccurrenceTable s -> PPIndex -> ST s () -> ST s ()
incOccurrence visited idx sub = do
  mv <- H.lookup visited idx
  case mv of
    Just i -> H.insert visited idx $! i+1
    Nothing -> sub >> H.insert visited idx 1

-- FIXME... why does this ignore Nat and Int literals?
countOccurrences' :: forall t tp s . OccurrenceTable s -> Expr t tp -> ST s ()
countOccurrences' visited (SemiRingLiteral SemiRingReal r _) = do
  incOccurrence visited (RatPPIndex r) $
    return ()
countOccurrences' visited (AppExpr e) = do
  let idx = ExprPPIndex (indexValue (appExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (appExprApp e)
countOccurrences' visited (NonceAppExpr e) = do
  let idx = ExprPPIndex (indexValue (nonceExprId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (nonceExprApp e)
countOccurrences' _ _ = return ()

------------------------------------------------------------------------
-- boundVars

type BoundVarMap s t = H.HashTable s PPIndex (Set (Some (ExprBoundVar t)))

cache :: (Eq k, Hashable k) => H.HashTable s k r -> k -> ST s r -> ST s r
cache h k m = do
  mr <- H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      H.insert h k r
      return r


boundVars :: Expr t tp -> ST s (BoundVarMap s t)
boundVars e0 = do
  visited <- H.new
  _ <- boundVars' visited e0
  return visited

boundVars' :: BoundVarMap s t
           -> Expr t tp
           -> ST s (Set (Some (ExprBoundVar t)))
boundVars' visited (AppExpr e) = do
  let idx = indexValue (appExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (appExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (NonceAppExpr e) = do
  let idx = indexValue (nonceExprId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (nonceExprApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (BoundVarExpr v)
  | QuantifierVarKind <- bvarKind v = do
      let idx = indexValue (bvarId v)
      cache visited (ExprPPIndex idx) $
        return (Set.singleton (Some v))
boundVars' _ _ = return Set.empty

------------------------------------------------------------------------
-- Pretty printing

ppVar :: String -> SolverSymbol -> Nonce t tp -> BaseTypeRepr tp -> String
ppVar pr sym i tp = pr ++ show sym ++ "@" ++ show (indexValue i) ++ ":" ++ ppVarTypeCode tp

instance Show (Expr t tp) where
  show = show . ppExpr

instance Pretty (Expr t tp) where
  pretty = ppExpr

ppBoundVar :: ExprBoundVar t tp -> String
ppBoundVar v =
  case bvarKind v of
    QuantifierVarKind -> ppVar "?" (bvarName v) (bvarId v) (bvarType v)
    LatchVarKind   -> ppVar "l" (bvarName v) (bvarId v) (bvarType v)
    UninterpVarKind -> ppVar "c" (bvarName v) (bvarId v) (bvarType v)

instance Show (ExprBoundVar t tp) where
  show = ppBoundVar

instance ShowF (ExprBoundVar t)

-- | @AppPPExpr@ represents a an application, and it may be let bound.
data AppPPExpr
   = APE { apeIndex :: !PPIndex
         , apeLoc :: !ProgramLoc
         , apeName :: !Text
         , apeExprs :: ![PPExpr]
         , apeLength :: !Int
           -- ^ Length of AppPPExpr not including parenthesis.
         }

data PPExpr
   = FixedPPExpr !String ![String] !Int
     -- ^ A fixed doc with length.
   | AppPPExpr !AppPPExpr
     -- ^ A doc that can be let bound.

-- | Pretty print a AppPPExpr
apeDoc :: AppPPExpr -> (Doc, [Doc])
apeDoc a = (text (Text.unpack (apeName a)), ppExprDoc True <$> apeExprs a)

textPPExpr :: Text -> PPExpr
textPPExpr t = FixedPPExpr (Text.unpack t) [] (Text.length t)

stringPPExpr :: String -> PPExpr
stringPPExpr t = FixedPPExpr t [] (length t)

-- | Get length of Expr including parens.
ppExprLength :: PPExpr -> Int
ppExprLength (FixedPPExpr _ [] n) = n
ppExprLength (FixedPPExpr _ _ n) = n + 2
ppExprLength (AppPPExpr a) = apeLength a + 2

parenIf :: Bool -> Doc -> [Doc] -> Doc
parenIf _ h [] = h
parenIf False h l = hsep (h:l)
parenIf True h l = parens (hsep (h:l))

-- | Pretty print PPExpr
ppExprDoc :: Bool -> PPExpr -> Doc
ppExprDoc b (FixedPPExpr d a _) = parenIf b (text d) (fmap text a)
ppExprDoc b (AppPPExpr a) = uncurry (parenIf b) (apeDoc a)

data PPExprOpts = PPExprOpts { ppExpr_maxWidth :: Int
                           , ppExpr_useDecimal :: Bool
                           }

defaultPPExprOpts :: PPExprOpts
defaultPPExprOpts =
  PPExprOpts { ppExpr_maxWidth = 68
            , ppExpr_useDecimal = True
            }

-- | Pretty print an 'Expr' using let bindings to create the term.
ppExpr :: Expr t tp -> Doc
ppExpr e
     | Prelude.null bindings = ppExprDoc False r
     | otherwise =
         text "let" <+> align (vcat bindings) PP.<$>
         text " in" <+> align (ppExprDoc False r)
  where (bindings,r) = runST (ppExpr' e defaultPPExprOpts)

instance ShowF (Expr t)

-- | Pretty print the top part of an element.
ppExprTop :: Expr t tp -> Doc
ppExprTop e = ppExprDoc False r
  where (_,r) = runST (ppExpr' e defaultPPExprOpts)

-- | Contains the elements before, the index, doc, and width and
-- the elements after.
type SplitPPExprList = Maybe ([PPExpr], AppPPExpr, [PPExpr])

findExprToRemove :: [PPExpr] -> SplitPPExprList
findExprToRemove exprs0 = go [] exprs0 Nothing
  where go :: [PPExpr] -> [PPExpr] -> SplitPPExprList -> SplitPPExprList
        go _ [] mr = mr
        go prev (e@FixedPPExpr{} : exprs) mr = do
          go (e:prev) exprs mr
        go prev (AppPPExpr a:exprs) mr@(Just (_,a',_))
          | apeLength a < apeLength a' = go (AppPPExpr a:prev) exprs mr
        go prev (AppPPExpr a:exprs) _ = do
          go (AppPPExpr a:prev) exprs (Just (reverse prev, a, exprs))


ppExpr' :: forall t tp s . Expr t tp -> PPExprOpts -> ST s ([Doc], PPExpr)
ppExpr' e0 o = do
  let max_width = ppExpr_maxWidth o
  let use_decimal = ppExpr_useDecimal o
  -- Get map that counts number of elements.
  let m = countOccurrences e0
  -- Return number of times a term is referred to in dag.
  let isShared :: PPIndex -> Bool
      isShared w = fromMaybe 0 (Map.lookup w m) > 1

  -- Get bounds variables.
  bvars <- boundVars e0

  bindingsRef <- newSTRef Seq.empty

  visited <- H.new :: ST s (H.HashTable s PPIndex PPExpr)
  visited_fns <- H.new :: ST s (H.HashTable s Word64 Text)

  let -- Add a binding to the list of bindings
      addBinding :: AppPPExpr -> ST s PPExpr
      addBinding a = do
        let idx = apeIndex a
        cnt <- Seq.length <$> readSTRef bindingsRef

        vars <- fromMaybe Set.empty <$> H.lookup bvars idx
        let args :: [String]
            args = viewSome ppBoundVar <$> Set.toList vars

        let nm = case idx of
                   ExprPPIndex e -> "v" ++ show e
                   RatPPIndex _ -> "r" ++ show cnt
        let lhs = parenIf False (text nm) (text <$> args)
        let doc = text "--" <+> pretty (plSourceLoc (apeLoc a)) <$$>
                  lhs <+> text "=" <+> uncurry (parenIf False) (apeDoc a)
        modifySTRef' bindingsRef (Seq.|> doc)
        let len = length nm + sum ((\arg_s -> length arg_s + 1) <$> args)
        let nm_expr = FixedPPExpr nm args len
        H.insert visited idx $! nm_expr
        return nm_expr

  let fixLength :: Int
                -> [PPExpr]
                -> ST s ([PPExpr], Int)
      fixLength cur_width exprs
        | cur_width > max_width
        , Just (prev_e, a, next_e) <- findExprToRemove exprs = do
          r <- addBinding a
          let exprs' = prev_e ++ [r] ++ next_e
          fixLength (cur_width - apeLength a + ppExprLength r) exprs'
      fixLength cur_width exprs = do
        return $! (exprs, cur_width)

  -- Pretty print an argument.
  let renderArg :: PrettyArg (Expr t) -> ST s PPExpr
      renderArg (Left (Some e)) = getBindings e
      renderArg (Right txt) = return (textPPExpr txt)

      renderApp :: PPIndex
                -> ProgramLoc
                -> Text
                -> [PrettyArg (Expr t)]
                -> ST s AppPPExpr
      renderApp idx loc nm args = Ex.assert (not (Prelude.null args)) $ do
        exprs0 <- traverse renderArg args
        -- Get width not including parenthesis of outer app.
        let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
        (exprs, cur_width) <- fixLength total_width exprs0
        return APE { apeIndex = idx
                   , apeLoc = loc
                   , apeName = nm
                   , apeExprs = exprs
                   , apeLength = cur_width
                   }

      cacheResult :: PPIndex
                  -> ProgramLoc
                  -> PrettyApp (Expr t)
                  -> ST s PPExpr
      cacheResult _ _ (nm,[]) = do
        return (textPPExpr nm)
      cacheResult idx loc (nm,args) = do
        mr <- H.lookup visited idx
        case mr of
          Just d -> return d
          Nothing -> do
            a <- renderApp idx loc nm args
            if isShared idx then
              addBinding a
             else
              return (AppPPExpr a)

      bindFn :: ExprSymFn t idx ret -> ST s (PrettyArg (Expr t))
      bindFn f = do
        let idx = indexValue (symFnId f)
        mr <- H.lookup visited_fns idx
        case mr of
          Just d -> return (Right d)
          Nothing -> do
            case symFnInfo f of
              UninterpFnInfo{} -> do
                let def_doc = text (show f) <+> text "=" <+> text "??"
                modifySTRef' bindingsRef (Seq.|> def_doc)
              DefinedFnInfo vars rhs _ -> do
                let pp_vars = toListFC (text . ppBoundVar) vars
                let def_doc = text (show f) <+> hsep pp_vars <+> text "=" <+> ppExpr rhs
                modifySTRef' bindingsRef (Seq.|> def_doc)
              MatlabSolverFnInfo fn_id _ _ -> do
                let def_doc = text (show f) <+> text "=" <+> ppMatlabSolverFn fn_id
                modifySTRef' bindingsRef (Seq.|> def_doc)

            let d = Text.pack (show f)
            H.insert visited_fns idx $! d
            return $! Right d

      -- Collect definitions for all applications that occur multiple times
      -- in term.
      getBindings :: Expr t u -> ST s PPExpr
      getBindings (SemiRingLiteral sr x l) =
        case sr of
          SemiRingNat -> do
            return $ stringPPExpr (show x)
          SemiRingInt -> do
            return $ stringPPExpr (show x)
          SemiRingReal -> cacheResult (RatPPIndex x) l app
             where n = numerator x
                   d = denominator x
                   app | d == 1      = prettyApp (fromString (show n)) []
                       | use_decimal = prettyApp (fromString (show (fromRational x :: Double))) []
                       | otherwise   = prettyApp "divReal"  [ showPrettyArg n, showPrettyArg d ]
      getBindings (BVExpr w n _) = do
        return $ stringPPExpr $ "0x" ++ (N.showHex n []) ++ ":[" ++ show w ++ "]"
      getBindings (StringExpr x _) = do
        return $ stringPPExpr $ (show x)
      getBindings (NonceAppExpr e) = do
        cacheResult (ExprPPIndex (indexValue (nonceExprId e))) (nonceExprLoc e)
          =<< ppNonceApp bindFn (nonceExprApp e)
      getBindings (AppExpr e) = do
        cacheResult (ExprPPIndex (indexValue (appExprId e)))
                    (appExprLoc e)
                    (ppApp' (appExprApp e))
      getBindings (BoundVarExpr i) = do
        return $ stringPPExpr $ ppBoundVar i

  r <- getBindings e0
  bindings <- toList <$> readSTRef bindingsRef
  return (toList bindings, r)

------------------------------------------------------------------------
-- Uncached storage

-- | Create a new storage that does not do hash consing.
newStorage :: NonceGenerator IO t -> IO (ExprAllocator t)
newStorage g = do
  return $! ExprAllocator { appExpr = uncachedExprFn g
                         , nonceExpr = uncachedNonceExpr g
                         }

uncachedExprFn :: NonceGenerator IO t
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
uncachedExprFn g pc a v = do
  n <- freshNonce g
  return $! mkExpr n pc a v

uncachedNonceExpr :: NonceGenerator IO t
                 -> ProgramLoc
                 -> NonceApp t (Expr t) tp
                 -> AbstractValue tp
                 -> IO (Expr t tp)
uncachedNonceExpr g pc p v = do
  n <- freshNonce g
  return $! NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                          , nonceExprLoc = pc
                                          , nonceExprApp = p
                                          , nonceExprAbsValue = v
                                          }

------------------------------------------------------------------------
-- Cached storage

cachedNonceExpr :: NonceGenerator IO t
               -> PH.HashTable RealWorld (NonceApp t (Expr t)) (Expr t)
               -> ProgramLoc
               -> NonceApp t (Expr t) tp
               -> AbstractValue tp
               -> IO (Expr t tp)
cachedNonceExpr g h pc p v = do
  me <- stToIO $ PH.lookup h p
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = NonceAppExpr $ NonceAppExprCtor { nonceExprId = n
                                            , nonceExprLoc = pc
                                            , nonceExprApp = p
                                            , nonceExprAbsValue = v
                                            }
      seq e $ stToIO $ PH.insert h p e
      return $! e


cachedAppExpr :: forall t tp
               . NonceGenerator IO t
              -> PH.HashTable RealWorld (App (Expr t)) (Expr t)
              -> ProgramLoc
              -> App (Expr t) tp
              -> AbstractValue tp
              -> IO (Expr t tp)
cachedAppExpr g h pc a v = do
  me <- stToIO $ PH.lookup h a
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = mkExpr n pc a v
      seq e $ stToIO $ PH.insert h a e
      return e

-- | Create a storage that does hash consing.
newCachedStorage :: forall t
                  . NonceGenerator IO t
                 -> Int
                 -> IO (ExprAllocator t)
newCachedStorage g sz = stToIO $ do
  appCache  <- PH.newSized sz
  predCache <- PH.newSized sz
  return $ ExprAllocator { appExpr = cachedAppExpr g appCache
                        , nonceExpr = cachedNonceExpr g predCache
                        }

instance PolyEq (Expr t x) (Expr t y) where
  polyEqF x y = do
    Refl <- testEquality x y
    return Refl

{-# NOINLINE appEqF #-}
-- | Check if two applications are equal.
appEqF :: App (Expr t) x -> App (Expr t) y -> Maybe (x :~: y)
appEqF = $(structuralTypeEquality [t|App|]
           [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|FloatPrecisionRepr|]) AnyType, [|testEquality|])
           , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
           , (ConType [t|Hash.Vector|] `TypeApp` AnyType
             , [|\x y -> if x == y then Just Refl else Nothing|])
           , (ConType [t|Hash.Map |] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
             , [|\x y -> if x == y then Just Refl else Nothing|])
           , (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (ConType [t|UnaryBV|]        `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|Ctx.Index|]      `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           ]
          )

{-# NOINLINE hashApp #-}
-- | Hash an an application.
hashApp :: Int -> App (Expr t) s -> Int
hashApp = $(structuralHash [t|App|])

instance Eq (App (Expr t) tp) where
  x == y = isJust (testEquality x y)

instance TestEquality (App (Expr t)) where
  testEquality = appEqF

instance HashableF (App (Expr t)) where
  hashWithSaltF = hashApp

------------------------------------------------------------------------
-- IdxCache

-- | An IdxCache is used to map expressions with type @Expr t tp@ to
-- values with a corresponding type @f tp@. It is a mutable map using
-- an 'IO' hash table. Parameter @t@ is a phantom type brand used to
-- track nonces.
newtype IdxCache t (f :: BaseType -> Type)
      = IdxCache { cMap :: PH.HashTable RealWorld (Nonce t) f }

-- | Create a new IdxCache
newIdxCache :: IO (IdxCache t f)
newIdxCache = stToIO $ IdxCache <$> PH.new

{-# INLINE lookupIdxValue #-}
-- | Return the value associated to the expr in the index.
lookupIdxValue :: MonadIO m => IdxCache t f -> Expr t tp -> m (Maybe (f tp))
lookupIdxValue _ SemiRingLiteral{} = return Nothing
lookupIdxValue _ BVExpr{} = return Nothing
lookupIdxValue _ StringExpr{} = return Nothing
lookupIdxValue c (NonceAppExpr e) = liftIO $ lookupIdx c (nonceExprId e)
lookupIdxValue c (AppExpr e)  = liftIO $ lookupIdx c (appExprId e)
lookupIdxValue c (BoundVarExpr i) = liftIO $ lookupIdx c (bvarId i)

lookupIdx :: IdxCache t f -> Nonce t tp -> IO (Maybe (f tp))
lookupIdx c n = stToIO $ PH.lookup (cMap c) n

{-# INLINE insertIdxValue #-}
-- | Bind the value to the given expr in the index.
insertIdxValue :: MonadIO m => IdxCache t f -> Nonce t tp -> f tp -> m ()
insertIdxValue c e v = seq v $ liftIO $ stToIO $ PH.insert (cMap c) e v

{-# INLINE deleteIdxValue #-}
-- | Bind the value to the given expr in the index.
deleteIdxValue :: MonadIO m => IdxCache t f -> Nonce t (tp :: BaseType) -> m ()
deleteIdxValue c e = liftIO $ stToIO $ do
  PH.delete (cMap c) e

clearIdxCache :: IdxCache t f -> IO ()
clearIdxCache c = stToIO $ PH.clear (cMap c)

exprMaybeId :: Expr t tp -> Maybe (Nonce t tp)
exprMaybeId SemiRingLiteral{} = Nothing
exprMaybeId BVExpr{}  = Nothing
exprMaybeId StringExpr{} = Nothing
exprMaybeId (NonceAppExpr e) = Just $! nonceExprId e
exprMaybeId (AppExpr  e) = Just $! appExprId e
exprMaybeId (BoundVarExpr e) = Just $! bvarId e

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
idxCacheEval :: IdxCache t f
             -> Expr t tp
             -> IO (f tp)
             -> IO (f tp)
idxCacheEval c e m = do
  case exprMaybeId e of
    Nothing -> m
    Just n -> idxCacheEval' c n m

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
idxCacheEval' :: IdxCache t f
             -> Nonce t tp
             -> IO (f tp)
             -> IO (f tp)
idxCacheEval' c n m = do
  mr <- liftIO $ lookupIdx c n
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      insertIdxValue c n r
      return r

------------------------------------------------------------------------
-- ExprBuilder operations

curProgramLoc :: ExprBuilder t st fs -> IO ProgramLoc
curProgramLoc sym = readIORef (sbProgramLoc sym)

-- | Create an element from a nonce app.
sbNonceExpr :: ExprBuilder t st fs
           -> NonceApp t (Expr t) tp
           -> IO (Expr t tp)
sbNonceExpr sym a = do
  s <- readIORef (curAllocator sym)
  pc <- curProgramLoc sym
  nonceExpr s pc a (quantAbsEval sym exprAbsValue a)

semiRingLit :: ExprBuilder t st fs
            -> SemiRingRepr tp
            -> WSum.Coefficient tp
            -> IO (Expr t tp)
semiRingLit sb sr x = do
  l <- curProgramLoc sb
  return $! SemiRingLiteral sr x l

sbMakeExpr :: ExprBuilder t st fs -> App (Expr t) tp -> IO (Expr t tp)
sbMakeExpr sym a = do
  s <- readIORef (curAllocator sym)
  params <- sbBVDomainParams sym
  pc <- curProgramLoc sym
  let v = abstractEval params exprAbsValue a
  when (isNonLinearApp a) $
    modifyIORef' (sbNonLinearOps sym) (+1)
  case appType a of
    -- Check if abstract interpretation concludes this is a constant.
    BaseBoolRepr | Just b <- v -> return $ backendPred sym b
    BaseNatRepr  | Just c <- asSingleNatRange v -> natLit sym c

    BaseIntegerRepr | Just c <- asSingleRange v -> intLit sym c
    BaseRealRepr | Just c <- asSingleRange (ravRange v) -> realLit sym c
    BaseBVRepr w | Just LeqProof <- isPosNat w
                 , Just x <- BVD.asSingleton v ->
      bvLit sym w x
    _ -> do
      appExpr s pc a v

-- | Update the binding to point to the current variable.
updateVarBinding :: ExprBuilder t st fs
                 -> SolverSymbol
                 -> SymbolBinding t
                 -> IO ()
updateVarBinding sym nm v
  | nm == emptySymbol = return ()
  | otherwise =
    modifyIORef' (sbVarBindings sym) $ (ins nm $! v)
  where ins n x (SymbolVarBimap m) = SymbolVarBimap (Bimap.insert n x m)

-- | Creates a new bound var.
sbMakeBoundVar :: ExprBuilder t st fs
               -> SolverSymbol
               -> BaseTypeRepr tp
               -> VarKind
               -> Maybe (AbstractValue tp)
               -> IO (ExprBoundVar t tp)
sbMakeBoundVar sym nm tp k absVal = do
  n  <- sbFreshIndex sym
  pc <- curProgramLoc sym
  return $! BVar { bvarId   = n
                 , bvarLoc  = pc
                 , bvarName = nm
                 , bvarType = tp
                 , bvarKind = k
                 , bvarAbstractValue = absVal
                 }

-- | Create fresh index
sbFreshIndex :: ExprBuilder t st fs -> IO (Nonce t (tp::BaseType))
sbFreshIndex sb = freshNonce (exprCounter sb)

sbFreshSymFnNonce :: ExprBuilder t st fs -> IO (Nonce t (ctx:: Ctx BaseType))
sbFreshSymFnNonce sb = freshNonce (exprCounter sb)

------------------------------------------------------------------------
-- Configuration option for controlling the maximum number of value a unary
-- threshold may have.

-- | Maximum number of values in unary bitvector encoding.
--
--   This option is named \"backend.unary_threshold\"
unaryThresholdOption :: CFG.ConfigOption BaseIntegerType
unaryThresholdOption = CFG.configOption BaseIntegerRepr "backend.unary_threshold"

-- | The configuration option for setting the maximum number of
-- values a unary threshold may have.
unaryThresholdDesc :: CFG.ConfigDesc
unaryThresholdDesc = CFG.mkOpt unaryThresholdOption sty help (Just (ConcreteInteger 0))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Maximum number of values in unary bitvector encoding.")

------------------------------------------------------------------------
-- Configuration option for controlling how many disjoint ranges
-- should be allowed in bitvector domains.

-- | Maximum number of ranges in bitvector abstract domains.
--
--   This option is named \"backend.bvdomain_range_limit\"
bvdomainRangeLimitOption :: CFG.ConfigOption BaseIntegerType
bvdomainRangeLimitOption = CFG.configOption BaseIntegerRepr "backend.bvdomain_range_limit"

bvdomainRangeLimitDesc :: CFG.ConfigDesc
bvdomainRangeLimitDesc = CFG.mkOpt bvdomainRangeLimitOption sty help (Just (ConcreteInteger 2))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Maximum number of ranges in bitvector domains.")

------------------------------------------------------------------------
-- Cache start size

-- | Starting size for element cache when caching is enabled.
--
--   This option is named \"backend.cache_start_size\"
cacheStartSizeOption :: CFG.ConfigOption BaseIntegerType
cacheStartSizeOption = CFG.configOption BaseIntegerRepr "backend.cache_start_size"

-- | The configuration option for setting the size of the initial hash set
-- used by simple builder
cacheStartSizeDesc :: CFG.ConfigDesc
cacheStartSizeDesc = CFG.mkOpt cacheStartSizeOption sty help (Just (ConcreteInteger 100000))
  where sty = CFG.integerWithMinOptSty (CFG.Inclusive 0)
        help = Just (text "Starting size for element cache")

------------------------------------------------------------------------
-- Cache terms

-- | Indicates if we should cache terms.  When enabled, hash-consing
--   is used to find and deduplicate common subexpressions.
--
--   This option is named \"use_cache\"
cacheTerms :: CFG.ConfigOption BaseBoolType
cacheTerms = CFG.configOption BaseBoolRepr "use_cache"

cacheOptStyle ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  CFG.OptionSetting BaseIntegerType ->
  CFG.OptionStyle BaseBoolType
cacheOptStyle gen storageRef szSetting =
  CFG.boolOptSty & CFG.set_opt_onset
        (\mb b -> f (fmap fromConcreteBool mb) (fromConcreteBool b) >> return CFG.optOK)
 where
 f :: Maybe Bool -> Bool -> IO ()
 f mb b | mb /= Just b = if b then start else stop
        | otherwise = return ()

 stop  = do s <- newStorage gen
            writeIORef storageRef s

 start = do sz <- CFG.getOpt szSetting
            s <- newCachedStorage gen (fromInteger sz)
            writeIORef storageRef s

cacheOptDesc ::
  NonceGenerator IO t ->
  IORef (ExprAllocator t) ->
  CFG.OptionSetting BaseIntegerType ->
  CFG.ConfigDesc
cacheOptDesc gen storageRef szSetting =
  CFG.mkOpt
    cacheTerms
    (cacheOptStyle gen storageRef szSetting)
    (Just (text "Use hash-consing during term construction"))
    (Just (ConcreteBool False))


newExprBuilder :: --IsExprBuilderState st
                 -- => st t
                 st t
                    -- ^ Current state for simple builder.
                 -> NonceGenerator IO t
                    -- ^ Nonce generator for names
                 ->  IO (ExprBuilder t st fs)
newExprBuilder st gen = do
  st_ref <- newIORef st
  es <- newStorage gen

  t <- appExpr es initializationLoc TrueBool  (Just True)
  f <- appExpr es initializationLoc FalseBool (Just False)
  let z = SemiRingLiteral SemiRingReal 0 initializationLoc

  loc_ref       <- newIORef initializationLoc
  storage_ref   <- newIORef es
  bindings_ref  <- newIORef emptySymbolVarBimap
  uninterp_fn_cache_ref <- newIORef Map.empty
  matlabFnCache <- stToIO $ PH.new
  loggerRef     <- newIORef Nothing

  -- Set up configuration options
  cfg <- CFG.initialConfig 0
           [ unaryThresholdDesc
           , bvdomainRangeLimitDesc
           , cacheStartSizeDesc
           ]
  unarySetting       <- CFG.getOptionSetting unaryThresholdOption cfg
  domainRangeSetting <- CFG.getOptionSetting bvdomainRangeLimitOption cfg
  cacheStartSetting  <- CFG.getOptionSetting cacheStartSizeOption cfg
  CFG.extendConfig [cacheOptDesc gen storage_ref cacheStartSetting] cfg
  nonLinearOps <- newIORef 0

  return $! SB { sbTrue  = t
               , sbFalse = f
               , sbZero = z
               , sbConfiguration = cfg
               , sbFloatReduce = True
               , sbUnaryThreshold = unarySetting
               , sbBVDomainRangeLimit = domainRangeSetting
               , sbCacheStartSize = cacheStartSetting
               , sbProgramLoc = loc_ref
               , exprCounter = gen
               , curAllocator = storage_ref
               , sbNonLinearOps = nonLinearOps
               , sbStateManager = st_ref
               , sbVarBindings = bindings_ref
               , sbUninterpFnCache = uninterp_fn_cache_ref
               , sbMatlabFnCache = matlabFnCache
               , sbSolverLogger = loggerRef
               }

-- | Get current variable bindings.
getSymbolVarBimap :: ExprBuilder t st fs -> IO (SymbolVarBimap t)
getSymbolVarBimap sym = readIORef (sbVarBindings sym)

-- | Stop caching applications in backend.
stopCaching :: ExprBuilder t st fs -> IO ()
stopCaching sb = do
  s <- newStorage (exprCounter sb)
  writeIORef (curAllocator sb) s

-- | Restart caching applications in backend (clears cache if it is currently caching).
startCaching :: ExprBuilder t st fs -> IO ()
startCaching sb = do
  sz <- CFG.getOpt (sbCacheStartSize sb)
  s <- newCachedStorage (exprCounter sb) (fromInteger sz)
  writeIORef (curAllocator sb) s


bvBinOp1 :: (1 <= w)
         => (Integer -> Integer -> Integer)
         -> (NatRepr w -> BVExpr t w -> BVExpr t w -> App (Expr t) (BaseBVType w))
         -> ExprBuilder t st fs
         -> BVExpr t w
         -> BVExpr t w
         -> IO (BVExpr t w)
bvBinOp1 f c sb x y = do
  let w = bvWidth x
  case (asUnsignedBV x, asUnsignedBV y) of
    (Just i, Just j) -> bvLit sb w $ f i j
    _ -> sbMakeExpr sb $ c w x y

-- | A version of 'bvBinOp1' that avoids dividing by zero in the case where the
-- divisor is zero
bvBinDivOp1 :: (1 <= w)
            => (Integer -> Integer -> Integer)
            -> (NatRepr w -> BVExpr t w -> BVExpr t w -> App (Expr t) (BaseBVType w))
            -> ExprBuilder t st fs
            -> BVExpr t w
            -> BVExpr t w
            -> IO (BVExpr t w)
bvBinDivOp1 f c sb x y = do
  let w = bvWidth x
  case (asUnsignedBV x, asUnsignedBV y) of
    (Just i, Just j) | j /= 0 -> bvLit sb w $ f i j
    _ -> sbMakeExpr sb $ c w x y

bvSignedBinDivOp :: (1 <= w)
                 => (Integer -> Integer -> Integer)
                 -> (NatRepr w -> BVExpr t w
                               -> BVExpr t w
                               -> App (Expr t) (BaseBVType w))
                 -> ExprBuilder t st fs
                 -> BVExpr t w
                 -> BVExpr t w
                 -> IO (BVExpr t w)
bvSignedBinDivOp f c sym x y = do
  let w = bvWidth x
  case (asSignedBV x, asSignedBV y) of
    (Just i, Just j) | j /= 0 -> bvLit sym w $ f i j
    _ -> sbMakeExpr sym $ c w x y


asConcreteIndices :: IsExpr e
                  => Ctx.Assignment e ctx
                  -> Maybe (Ctx.Assignment IndexLit ctx)
asConcreteIndices = traverseFC f
  where f :: IsExpr e => e tp -> Maybe (IndexLit tp)
        f x =
          case exprType x of
            BaseNatRepr  -> NatIndexLit . fromIntegral <$> asNat x
            BaseBVRepr w -> BVIndexLit w <$> asUnsignedBV x
            _ -> Nothing

symbolicIndices :: forall sym ctx
                 . IsExprBuilder sym
                => sym
                -> Ctx.Assignment IndexLit ctx
                -> IO (Ctx.Assignment (SymExpr sym) ctx)
symbolicIndices sym = traverseFC f
  where f :: IndexLit tp -> IO (SymExpr sym tp)
        f (NatIndexLit n)  = natLit sym n
        f (BVIndexLit w i) = bvLit sym w i

-- | This evaluate a symbolic function against a set of arguments.
betaReduce :: ExprBuilder t st fs
           -> ExprSymFn t args ret
           -> Ctx.Assignment (Expr t) args
           -> IO (Expr t ret)
betaReduce sym f args =
  case symFnInfo f of
    UninterpFnInfo{} ->
      sbNonceExpr sym $! FnApp f args
    DefinedFnInfo bound_vars e _ -> do
      evalBoundVars sym e bound_vars args
    MatlabSolverFnInfo fn_id _ _ -> do
      evalMatlabSolverFn fn_id sym args

reduceApp :: (IsExprBuilder sym, sym ~ ExprBuilder t st fs)
          => sym
          -> App (SymExpr sym) tp
          -> IO (SymExpr sym tp)
reduceApp sym a0 = do
  case a0 of
    TrueBool  -> return $ truePred sym
    FalseBool -> return $ falsePred sym
    NotBool x     -> notPred sym x
    AndBool x y   -> andPred sym x y
    XorBool x y   -> xorPred sym x y
    IteBool c x y -> itePred sym c x y

    SemiRingSum SemiRingNat s -> natSum sym s
    SemiRingMul SemiRingNat x y -> natMul sym x y
    SemiRingIte SemiRingNat c x y -> natIte sym c x y

    SemiRingSum SemiRingInt s -> intSum sym s
    SemiRingMul SemiRingInt x y -> intMul sym x y
    SemiRingIte SemiRingInt c x y -> intIte sym c x y

    SemiRingEq SemiRingReal x y -> realEq sym x y
    SemiRingEq SemiRingInt x y -> intEq sym x y
    SemiRingEq SemiRingNat x y -> natEq sym x y

    SemiRingLe SemiRingReal x y -> realLe sym x y
    SemiRingLe SemiRingInt x y -> intLe sym x y
    SemiRingLe SemiRingNat x y -> natLe sym x y

    RealIsInteger x -> isInteger sym x
    SemiRingSum SemiRingReal s -> realSum sym s
    SemiRingMul SemiRingReal x y -> realMul sym x y
    SemiRingIte SemiRingReal c x y -> realIte sym c x y

    NatDiv x y -> natDiv sym x y
    NatMod x y -> natMod sym x y

    IntDiv x y -> intDiv sym x y
    IntMod x y -> intMod sym x y
    IntAbs x -> intAbs sym x
    IntDivisible x k -> intDivisible sym x k

    RealDiv x y -> realDiv sym x y
    RealSqrt x  -> realSqrt sym x

    Pi -> realPi sym
    RealSin x -> realSin sym x
    RealCos x -> realCos sym x
    RealATan2 y x -> realAtan2 sym y x
    RealSinh x -> realSinh sym x
    RealCosh x -> realCosh sym x
    RealExp x -> realExp sym x
    RealLog x -> realLog sym x

    BVIte _ _ c x y -> bvIte sym c x y
    BVTestBit i e -> testBitBV sym i e
    BVEq x y -> bvEq sym x y
    BVSlt x y -> bvSlt sym x y
    BVUlt x y -> bvUlt sym x y
    BVUnaryTerm x -> bvUnary sym x
    BVConcat _ x y -> bvConcat sym x y
    BVSelect idx n x -> bvSelect sym idx n x
    BVNeg  _ x   -> bvNeg sym x
    BVAdd  _ x y -> bvAdd sym x y
--    BVSum  w x   -> bvSum sym w x
    BVMul  _ x y -> bvMul sym x y
    BVUdiv _ x y -> bvUdiv sym x y
    BVUrem _ x y -> bvUrem sym x y
    BVSdiv _ x y -> bvSdiv sym x y
    BVSrem _ x y -> bvSrem sym x y
    BVShl _ x y  -> bvShl  sym x y
    BVLshr _ x y -> bvLshr sym x y
    BVAshr _ x y -> bvAshr sym x y
    BVZext  w x  -> bvZext sym w x
    BVSext  w x  -> bvSext sym w x
    BVPopcount _ x -> bvPopcount sym x
    BVCountLeadingZeros _ x -> bvCountLeadingZeros sym x
    BVCountTrailingZeros _ x -> bvCountTrailingZeros sym x

    BVBitNot _ x -> bvNotBits sym x
    BVBitAnd _ x y -> bvAndBits sym x y
    BVBitOr  _ x y -> bvOrBits  sym x y
    BVBitXor _ x y -> bvXorBits sym x y

    FloatPZero fpp -> floatPZero sym fpp
    FloatNZero fpp -> floatNZero sym fpp
    FloatNaN   fpp -> floatNaN sym fpp
    FloatPInf  fpp -> floatPInf sym fpp
    FloatNInf  fpp -> floatNInf sym fpp
    FloatNeg _ x -> floatNeg sym x
    FloatAbs _ x -> floatAbs sym x
    FloatSqrt _ r x -> floatSqrt sym r x
    FloatAdd _ r x y -> floatAdd sym r x y
    FloatSub _ r x y -> floatSub sym r x y
    FloatMul _ r x y -> floatMul sym r x y
    FloatDiv _ r x y -> floatDiv sym r x y
    FloatRem _ x y -> floatRem sym x y
    FloatMin _ x y -> floatMin sym x y
    FloatMax _ x y -> floatMax sym x y
    FloatFMA _ r x y z -> floatFMA sym r x y z
    FloatEq   x y -> floatEq sym x y
    FloatFpEq x y -> floatFpEq sym x y
    FloatFpNe x y -> floatFpNe sym x y
    FloatLe   x y -> floatLe sym x y
    FloatLt   x y -> floatLt sym x y
    FloatIsNaN     x -> floatIsNaN sym x
    FloatIsInf     x -> floatIsInf sym x
    FloatIsZero    x -> floatIsZero sym x
    FloatIsPos     x -> floatIsPos sym x
    FloatIsNeg     x -> floatIsNeg sym x
    FloatIsSubnorm x -> floatIsSubnorm sym x
    FloatIsNorm    x -> floatIsNorm sym x
    FloatIte _ c x y -> floatIte sym c x y
    FloatCast fpp r x -> floatCast sym fpp r x
    FloatRound  _ r x -> floatRound sym r x
    FloatFromBinary fpp x -> floatFromBinary sym fpp x
    FloatToBinary   _   x -> floatToBinary sym x
    BVToFloat   fpp r x -> bvToFloat sym fpp r x
    SBVToFloat  fpp r x -> sbvToFloat sym fpp r x
    RealToFloat fpp r x -> realToFloat sym fpp r x
    FloatToBV   w   r x -> floatToBV sym w r x
    FloatToSBV  w   r x -> floatToSBV sym w r x
    FloatToReal x -> floatToReal sym x

    ArrayEq x y -> arrayEq sym x y
    ArrayMap _ _ m def_map ->
      arrayUpdateAtIdxLits sym m def_map
    ConstantArray idx_tp _ e -> constantArray sym idx_tp e
    MuxArray _ _ c x y    -> arrayIte sym c x y
    SelectArray _ a i     -> arrayLookup sym a i
    UpdateArray _ _ a i v -> arrayUpdate sym a i v

    NatToInteger x -> natToInteger sym x
    IntegerToNat x -> integerToNat sym x
    IntegerToReal x -> integerToReal sym x
    RealToInteger x -> realToInteger sym x

    BVToNat x       -> bvToNat sym x
    BVToInteger x   -> bvToInteger sym x
    SBVToInteger x  -> sbvToInteger sym x
    PredToBV x      -> predToBV sym x (knownNat @1)
    IntegerToBV x w -> integerToBV sym x w

    RoundReal x -> realRound sym x
    FloorReal x -> realFloor sym x
    CeilReal  x -> realCeil sym x

    Cplx c     -> mkComplex sym c
    RealPart x -> getRealPart sym x
    ImagPart x -> getImagPart sym x

    StructCtor _ args -> mkStruct sym args
    StructField s i _ -> structField sym s i
    StructIte _ c x y -> structIte sym c x y


-- | This runs one action, and if it returns a value different from the input,
-- then it runs the second.  Otherwise it returns the result value passed in.
--
-- It is used when an action may modify a value, and we only want to run a
-- second action if the value changed.
runIfChanged :: Eq e
             => e
             -> (e -> IO e) -- ^ First action to run
             -> r           -- ^ Result if no change.
             -> (e -> IO r) -- ^ Second action to run
             -> IO r
runIfChanged x f unChanged onChange = do
  y <- f x
  if x == y then
    return unChanged
   else
    onChange y

-- | This adds a binding from the variable to itself in the hashtable
-- to ensure it can't be rebound.
recordBoundVar :: PH.HashTable RealWorld (Expr t) (Expr t)
                  -> ExprBoundVar t tp
                  -> IO ()
recordBoundVar tbl v = do
  let e = BoundVarExpr v
  mr <- stToIO $ PH.lookup tbl e
  case mr of
    Just r -> do
      when (r /= e) $ do
        fail $ "Simulator internal error; do not support rebinding variables."
    Nothing -> do
      -- Bind variable to itself to ensure we catch when it is used again.
      stToIO $ PH.insert tbl e e


-- | The CachedSymFn is used during evaluation to store the results of reducing
-- the definitions of symbolic functions.
--
-- For each function it stores a pair containing a 'Bool' that is true if the
-- function changed as a result of evaluating it, and the reduced function
-- after evaluation.
--
-- The second arguments contains the arguments with the return type appended.
data CachedSymFn t c
  = forall a r
    . (c ~ (a ::> r))
    => CachedSymFn Bool (ExprSymFn t a r)

-- | Data structure used for caching evaluation.
data EvalHashTables t
   = EvalHashTables { exprTable :: !(PH.HashTable RealWorld (Expr t) (Expr t))
                    , fnTable  :: !(PH.HashTable RealWorld (Nonce t) (CachedSymFn t))
                    }

-- | Evaluate a simple function.
--
-- This returns whether the function changed as a Boolean and the function itself.
evalSimpleFn :: EvalHashTables t
             -> ExprBuilder t st fs
             -> ExprSymFn t idx ret
             -> IO (Bool,ExprSymFn t idx ret)
evalSimpleFn tbl sym f =
  case symFnInfo f of
    UninterpFnInfo{} -> return (False, f)
    DefinedFnInfo vars e evalFn -> do
      let n = symFnId f
      let nm = symFnName f
      CachedSymFn changed f' <-
        cachedEval (fnTable tbl) n $ do
          traverseFC_ (recordBoundVar (exprTable tbl)) vars
          e' <- evalBoundVars' tbl sym e
          if e == e' then
            return $! CachedSymFn False f
           else
            CachedSymFn True <$> definedFn sym nm vars e' evalFn
      return (changed, f')
    MatlabSolverFnInfo{} -> return (False, f)

evalBoundVars' :: forall t st fs ret
               .  EvalHashTables t
               -> ExprBuilder t st fs
               -> Expr t ret
               -> IO (Expr t ret)
evalBoundVars' tbls sym e0 =
  case e0 of
    SemiRingLiteral{} -> return e0
    BVExpr{}  -> return e0
    StringExpr{} -> return e0
    AppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      let a = appExprApp ae
      a' <- traverseApp (evalBoundVars' tbls sym) a
      if a == a' then
        return e0
       else
        reduceApp sym a'
    NonceAppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      case nonceExprApp ae of
        Forall v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (forallPred sym v)
        Exists v e -> do
          recordBoundVar (exprTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (existsPred sym v)
        ArrayFromFn f -> do
          (changed, f') <- evalSimpleFn tbls sym f
          if not changed then
            return e0
           else
            arrayFromFn sym f'
        MapOverArrays f _ args -> do
          (changed, f') <- evalSimpleFn tbls sym f
          let evalWrapper :: ArrayResultWrapper (Expr t) (idx ::> itp) utp
                          -> IO (ArrayResultWrapper (Expr t) (idx ::> itp) utp)
              evalWrapper (ArrayResultWrapper a) =
                ArrayResultWrapper <$> evalBoundVars' tbls sym a
          args' <- traverseFC evalWrapper args
          if not changed && args == args' then
            return e0
           else
            arrayMap sym f' args'
        ArrayTrueOnEntries f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- evalBoundVars' tbls sym a
          if not changed && a == a' then
            return e0
           else
            arrayTrueOnEntries sym f' a'
        FnApp f a -> do
          (changed, f') <- evalSimpleFn tbls sym f
          a' <- traverseFC (evalBoundVars' tbls sym) a
          if not changed && a == a' then
            return e0
           else
            applySymFn sym f' a'

    BoundVarExpr{} -> cachedEval (exprTable tbls) e0 $ return e0

initHashTable :: (HashableF key, TestEquality key)
              => Ctx.Assignment key args
              -> Ctx.Assignment val args
              -> ST s (PH.HashTable s key val)
initHashTable keys vals = do
  let sz = Ctx.size keys
  tbl <- PH.newSized (Ctx.sizeInt sz)
  Ctx.forIndexM sz $ \i -> do
    PH.insert tbl (keys Ctx.! i) (vals Ctx.! i)
  return tbl

-- | This evaluates the term with the given bound variables rebound to
-- the given arguments.
--
-- The algorithm works by traversing the subterms in the term in a bottom-up
-- fashion while using a hash-table to memoize results for shared subterms.  The
-- hash-table is pre-populated so that the bound variables map to the element,
-- so we do not need any extra map lookup when checking to see if a variable is
-- bound.
--
-- NOTE: This function assumes that variables in the substitution are not
-- themselves bound in the term (e.g. in a function definition or quantifier).
-- If this is not respected, then 'evalBoundVars' will call 'fail' with an
-- error message.
evalBoundVars :: ExprBuilder t st fs
              -> Expr t ret
              -> Ctx.Assignment (ExprBoundVar t) args
              -> Ctx.Assignment (Expr t) args
              -> IO (Expr t ret)
evalBoundVars sym e vars exprs = do
  expr_tbl <- stToIO $ initHashTable (fmapFC BoundVarExpr vars) exprs
  fn_tbl  <- stToIO $ PH.new
  let tbls = EvalHashTables { exprTable = expr_tbl
                            , fnTable  = fn_tbl
                            }
  evalBoundVars' tbls sym e

-- | Return true if corresponding expressions in contexts are equivalent.
allEq :: forall sym ctx
      .  IsExprBuilder sym
      => sym
      -> Ctx.Assignment (SymExpr sym) ctx
      -> Ctx.Assignment (SymExpr sym) ctx
      -> IO (Pred sym)
allEq sym x y = Ctx.forIndex (Ctx.size x) joinEq (pure (truePred sym))
  where joinEq :: IO (Pred sym) -> Ctx.Index ctx tp -> IO (Pred sym)
        joinEq mp i = do
          q <- isEq sym (x Ctx.! i) (y Ctx.! i)
          case asConstantPred q of
            Just True -> mp
            Just False -> return (falsePred sym)
            Nothing -> andPred sym q =<< mp

-- | This attempts to lookup an entry in a symbolic array.
--
-- It patterns maps on the array constructor.
sbConcreteLookup :: forall t st fs d tp range
                 . ExprBuilder t st fs
                   -- ^ Simple builder for creating terms.
                 -> Expr t (BaseArrayType (d::>tp) range)
                    -- ^ Array to lookup value in.
                 -> Maybe (Ctx.Assignment IndexLit (d::>tp))
                    -- ^ A concrete index that corresponds to the index or nothing
                    -- if the index is symbolic.
                 -> Ctx.Assignment (Expr t) (d::>tp)
                    -- ^ The index to lookup.
                 -> IO (Expr t range)
sbConcreteLookup sym arr0 mcidx idx
    -- Try looking up a write to a concrete address.
  | Just (ArrayMap _ _ entry_map def) <- asApp arr0 = do
    case mcidx of
      Just cidx -> do
        case Hash.mapLookup cidx entry_map of
          Just v -> return v
          Nothing -> sbConcreteLookup sym def mcidx idx
      Nothing -> Map.foldrWithKey f (sbConcreteLookup sym def mcidx idx) (Hash.hashedMap entry_map)
        where f updated_cidx c m = do
                updated_idx <- traverseFC (indexLit sym) updated_cidx
                p <- allEq sym updated_idx idx
                iteM baseTypeIte sym p (pure c) m

    -- Reduce array updates
  | Just (UpdateArray _ _ arr idx' v) <- asApp arr0 = do
    p <- allEq sym idx idx'
    iteM baseTypeIte sym p (pure v) (sbConcreteLookup sym arr mcidx idx)

    -- Evaluate function arrays on ground values.
  | Just (ArrayFromFn f) <- asNonceApp arr0 = do
      betaReduce sym f idx

    -- Lookups on constant arrays just return value
  | Just (ConstantArray _ _ v) <- asApp arr0 = do
      return v
    -- Lookups on mux arrays just distribute over mux.
  | Just (MuxArray _ _ p x y) <- asApp arr0 = do
      xv <- sbConcreteLookup sym x mcidx idx
      yv <- sbConcreteLookup sym y mcidx idx
      baseTypeIte sym p xv yv
  | Just (MapOverArrays f _ args) <- asNonceApp arr0 = do
      let eval :: ArrayResultWrapper (Expr t) (d::>tp) utp
               -> IO (Expr t utp)
          eval a = sbConcreteLookup sym (unwrapArrayResult a) mcidx idx
      betaReduce sym f =<< traverseFC eval args
    -- Create select index.
  | otherwise = do
    case exprType arr0 of
      BaseArrayRepr _ range ->
        sbMakeExpr sym (SelectArray range arr0 idx)

----------------------------------------------------------------------
-- Expression builder instances

-- | Evaluate a weighted sum of natural number values
natSum :: ExprBuilder t st fs -> WeightedSum (Expr t) BaseNatType -> IO (NatExpr t)
natSum sym s = semiRingSum sym SemiRingNat s

-- | Evaluate a weighted sum of integer values
intSum :: ExprBuilder t st fs -> WeightedSum (Expr t) BaseIntegerType -> IO (IntegerExpr t)
intSum sym s = semiRingSum sym SemiRingInt s

-- | Evaluate a weighted sum of real values.
realSum :: ExprBuilder t st fs -> WeightedSum (Expr t) BaseRealType -> IO (RealExpr t)
realSum sym s = semiRingSum sym SemiRingReal s


bvUnary :: (1 <= w) => ExprBuilder t st fs -> UnaryBV (BoolExpr t) w -> IO (BVExpr t w)
bvUnary sym u
    | Just v <-  UnaryBV.asConstant u =
      bvLit sym (UnaryBV.width u) v
    | otherwise =
      sbMakeExpr sym (BVUnaryTerm u)

asUnaryBV :: (?unaryThreshold :: Int)
          => ExprBuilder t st fs
          -> BVExpr t n
          -> Maybe (UnaryBV (BoolExpr t) n)
asUnaryBV sym e
  | Just (BVUnaryTerm u) <- asApp e = Just u
  | ?unaryThreshold == 0 = Nothing
  | BVExpr w v _ <- e = Just $ UnaryBV.constant sym w v
  | otherwise = Nothing

-- | This create a unary bitvector representing if the size is not too large.
sbTryUnaryTerm :: (1 <= w, ?unaryThreshold :: Int)
               => ExprBuilder t st fs
               -> UnaryBV (BoolExpr t) w
               -> App (Expr t) (BaseBVType w)
               -> IO (BVExpr t w)
sbTryUnaryTerm sym u a
  | UnaryBV.size u < ?unaryThreshold =
    bvUnary sym u
  | otherwise =
    sbMakeExpr sym a

-- | This privides a view of a real expr as a weighted sum of values.
data SumView t tp
   = ConstantSum !(WSum.Coefficient tp)
   | LinearSum !(WeightedSum (Expr t) tp)
   | GeneralSum

viewSum :: Expr t tp -> SumView t tp
viewSum x
  | SemiRingLiteral _sr r _ <- x = ConstantSum r
  | Just (SemiRingSum _sr s) <- asApp x = LinearSum s
  | otherwise = GeneralSum

asWeightedSum :: WSum.SemiRingCoefficient tp
              => HashableF (Expr t)
              => Expr t tp
              -> WeightedSum (Expr t) tp
asWeightedSum x
  | SemiRingLiteral _sr r _ <- x = WSum.constant r
  | Just (SemiRingSum _sr s) <- asApp x = s
  | otherwise = WSum.var x

semiRingSum :: WSum.SemiRingCoefficient tp
            => ExprBuilder t st fs
            -> SemiRingRepr tp
            -> WeightedSum (Expr t) tp
            -> IO (Expr t tp)
semiRingSum sym sr s
    | Just c <- WSum.asConstant s =
      semiRingLit sym sr c
    | Just r <- WSum.asVar s =
      return r
    | otherwise =
      sum' sym sr s

sum' :: WSum.SemiRingCoefficient tp
     => ExprBuilder t st fs
     -> SemiRingRepr tp
     -> WeightedSum (Expr t) tp
     -> IO (Expr t tp)
sum' sym sr s = sbMakeExpr sym $ SemiRingSum sr $ s
{-# INLINE sum' #-}

scalarMul :: WSum.SemiRingCoefficient tp
          => ExprBuilder t st fs
          -> SemiRingRepr tp
          -> WSum.Coefficient tp
          -> Expr t tp
          -> IO (Expr t tp)
scalarMul sym sr c x
  | c == 0 =
    semiRingLit sym sr 0
  | c == 1 =
    return x
  | Just r <- asSemiRingLit x =
    semiRingLit sym sr (c*r)
  | Just (SemiRingSum _sr s) <- asApp x =
    sum' sym sr (WSum.scale c s)
  | otherwise = do
    sum' sym sr (WSum.scaledVar c x)

semiRingIte :: WSum.SemiRingCoefficient tp
            => ExprBuilder t st fs
            -> SemiRingRepr tp
            -> Expr t BaseBoolType
            -> Expr t tp
            -> Expr t tp
            -> IO (Expr t tp)
semiRingIte sym sr c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotBool cn) <- asApp c = semiRingIte sym sr cn y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

    -- Try to extract common sum information.
  | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
  , not (WSum.isZero z) = do
    xr <- semiRingSum sym sr x'
    yr <- semiRingSum sym sr y'
    r <- sbMakeExpr sym (SemiRingIte sr c xr yr)
    semiRingSum sym sr $! z `WSum.addVar` r

    -- final fallback, create the ite term
  | otherwise = do
    sbMakeExpr sym (SemiRingIte sr c x y)

semiRingLe
   :: WSum.SemiRingCoefficient tp
   => ExprBuilder t st fs
   -> SemiRingRepr tp
   -> (Expr t tp -> Expr t tp -> IO (Expr t BaseBoolType)) {- ^ recursive call for simplifications -}
   -> Expr t tp
   -> Expr t tp
   -> IO (Expr t BaseBoolType)
semiRingLe sym sr rec x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)

      -- Strength reductions on a non-linear constraint to piecewise linear.
    | SemiRingLiteral _ 0 _ <- x, Just (SemiRingMul _ u v) <- asApp y = do
      leNonneg le x sym u v
      -- Another strength reduction
    | Just (SemiRingMul _ u v) <- asApp x, SemiRingLiteral _ 0 _ <- y = do
      leNonpos le y sym u v

      -- Push some comparisons under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (SemiRingIte _ c a b) <- asApp y
    = join (itePred sym c <$> rec x a <*> rec x b)

      -- Push some comparisons under if/then/else
    | Just (SemiRingIte _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    = join (itePred sym c <$> rec a y <*> rec b y)

      -- Simplify ite expressions when one of the values is ground.
      -- This appears to occur fairly often due to range checks.
    | isJust (asSemiRingLit x)
    , Just (SemiRingIte _sr yc y1 y2) <- asApp y
    , isJust (asSemiRingLit y1) || isJust (asSemiRingLit y2) = do
      c1 <- le sym x y1
      c2 <- le sym x y2
      itePred sym yc c1 c2

      -- Simplify ite expressions when one of the values is ground.
      -- This appears to occur fairly often due to range checks.
    | isJust (asSemiRingLit y)
    , Just (SemiRingIte _sr xc x1 x2) <- asApp x
    , isJust (asSemiRingLit x1) || isJust (asSemiRingLit x2) = do
      c1 <- le sym x1 y
      c2 <- le sym x2 y
      itePred sym xc c1 c2

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
    , not (WSum.isZero z) = do
      xr <- semiRingSum sym sr x'
      yr <- semiRingSum sym sr y'
      le sym xr yr

      -- Default case
    | otherwise = sbMakeExpr sym $ SemiRingLe sr x y

 where le = case sr of
              SemiRingReal -> realLe
              SemiRingInt  -> intLe
              SemiRingNat  -> natLe


semiRingEq :: WSum.SemiRingCoefficient tp
           => ExprBuilder t st fs
           -> SemiRingRepr tp
           -> (Expr t tp -> Expr t tp -> IO (Expr t BaseBoolType)) {- ^ recursive call for simplifications -}
           -> Expr t tp
           -> Expr t tp
           -> IO (Expr t BaseBoolType)
semiRingEq sym sr rec x y
  -- Check for syntactic equality.
  | x == y = return (truePred sym)

    -- Push some equalities under if/then/else
  | SemiRingLiteral _ _ _ <- x
  , Just (SemiRingIte _ c a b) <- asApp y
  = join (itePred sym c <$> rec x a <*> rec x b)

    -- Push some equalities under if/then/else
  | Just (SemiRingIte _ c a b) <- asApp x
  , SemiRingLiteral _ _ _ <- y
  = join (itePred sym c <$> rec a y <*> rec b y)

  | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
  , not (WSum.isZero z) =
    case (WSum.asConstant x', WSum.asConstant y') of
      (Just a, Just b) -> return $! backendPred sym (a == b)
      _ -> do xr <- semiRingSum sym sr x'
              yr <- semiRingSum sym sr y'
              sbMakeExpr sym $ SemiRingEq sr (min xr yr) (max xr yr)

  | otherwise =
    sbMakeExpr sym $ SemiRingEq sr (min x y) (max x y)


semiRingAdd :: WSum.SemiRingCoefficient tp
            => ExprBuilder t st fs
            -> SemiRingRepr tp
            -> Expr t tp
            -> Expr t tp
            -> IO (Expr t tp)
semiRingAdd sym sr x y =
    case (viewSum x, viewSum y) of
      (ConstantSum 0, _) -> return y
      (_, ConstantSum 0) -> return x

      (ConstantSum xc, ConstantSum yc) ->
        semiRingLit sym sr (xc + yc)

      (ConstantSum xc, LinearSum ys) ->
        sum' sym sr (ys `WSum.addConstant` xc)
      (LinearSum xs, ConstantSum yc) ->
        sum' sym sr (xs `WSum.addConstant` yc)

      (ConstantSum xc, GeneralSum) -> do
        sum' sym sr (WSum.var y `WSum.addConstant` xc)
      (GeneralSum, ConstantSum yc) -> do
        sum' sym sr (WSum.var x `WSum.addConstant` yc)

      (LinearSum xs, LinearSum ys) -> semiRingSum sym sr (xs `WSum.add` ys)
      (LinearSum xs, GeneralSum)   -> semiRingSum sym sr (xs `WSum.addVar` y)
      (GeneralSum, LinearSum ys)   -> semiRingSum sym sr (ys `WSum.addVar` x)
      (GeneralSum, GeneralSum)     -> semiRingSum sym sr (x  `WSum.addVars` y)

semiRingMul :: WSum.SemiRingCoefficient tp
            => ExprBuilder t st fs
            -> SemiRingRepr tp
            -> Expr t tp
            -> Expr t tp
            -> IO (Expr t tp)
semiRingMul sym sr x y
    | Just xd <- asSemiRingLit x =
      scalarMul sym sr xd y
    | Just yd <- asSemiRingLit y =
      scalarMul sym sr yd x
      -- (cx*xx) * y = cx*(xx*y)
    | Just (SemiRingMul _ (SemiRingLiteral _ cx _) xx) <- asApp x = do
      scalarMul sym sr cx =<< semiRingMul sym sr xx y
      -- x*(cy*yy) = cy*(x*yy)
    | Just (SemiRingMul _ (SemiRingLiteral _ cy _) yy) <- asApp y = do
      scalarMul sym sr cy =<< semiRingMul sym sr x yy
    | otherwise =
      sbMakeExpr sym $ SemiRingMul sr (min x y) (max x y)


-- Add following rule to do a strength reduction on non-linear
-- constraint non-negative constraint
--
-- (0 <= u * v)
-- -> not (u * v < 0)
-- -> not (u > 0 & v < 0 | u < 0 & v > 0)
-- -> not (u > 0 & v < 0) & not (u < 0 & v > 0)
-- -> (u <= 0 | v >= 0) & (u >= 0 | v <= 0)
-- -> (u <= 0 | 0 <= v) & (0 <= u | v <= 0)
leNonneg :: IsExprBuilder sym
         => (sym -> a -> a -> IO (Pred sym)) -- ^ Less than or equal
         -> a -- ^ zero
         -> sym
         -> a
         -> a
         -> IO (Pred sym)
leNonneg le zero sym u v = do
  ule <- le sym u zero
  vle <- le sym v zero
  vge <- le sym zero v
  uge <- le sym zero u
  a <- orPred sym ule vge
  b <- orPred sym uge vle
  andPred sym a b

-- Add following rule to do a strength reduction on non-linear
-- constraint non-negative constraint
--
-- (u * v <= 0)
-- -> not (u * v > 0)
-- -> not (u > 0 & v > 0 | u < 0 & v < 0)
-- -> not (u > 0 & v > 0) & not (u < 0 & v < 0)
-- -> (u <= 0 | v <= 0) & (u >= 0 | v >= 0)
leNonpos :: IsExprBuilder sym
         => (sym -> a -> a -> IO (Pred sym)) -- ^ Less than or equal
         -> a -- ^ zero
         -> sym
         -> a
         -> a
         -> IO (Pred sym)
leNonpos le zero sym u v = do
  ule <- le sym u zero
  vle <- le sym v zero
  vge <- le sym zero v
  uge <- le sym zero u
  a <- orPred sym ule vle
  b <- orPred sym uge vge
  andPred sym a b



arrayResultIdxType :: BaseTypeRepr (BaseArrayType (idx ::> itp) d)
                   -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
arrayResultIdxType (BaseArrayRepr idx _) = idx

-- | This decomposes A ExprBuilder array expression into a set of indices that
-- have been updated, and an underlying index.
data ArrayMapView i f tp
   = ArrayMapView { _arrayMapViewIndices :: !(Hash.Map IndexLit i f tp)
                  , _arrayMapViewExpr    :: !(f (BaseArrayType i tp))
                  }

-- | Construct an 'ArrayMapView' for an element.
viewArrayMap :: Expr t (BaseArrayType i tp)
             -> ArrayMapView i (Expr t) tp
viewArrayMap  x
  | Just (ArrayMap _ _ m c) <- asApp x = ArrayMapView m c
  | otherwise = ArrayMapView Hash.mapEmpty x

-- | Construct an 'ArrayMapView' for an element.
underlyingArrayMapExpr :: ArrayResultWrapper (Expr t) i tp
                      -> ArrayResultWrapper (Expr t) i tp
underlyingArrayMapExpr x
  | Just (ArrayMap _ _ _ c) <- asApp (unwrapArrayResult x) = ArrayResultWrapper c
  | otherwise = x

-- | Return set of addresss in assignment that are written to by at least one expr
concreteArrayEntries :: forall t i ctx
                     .  Ctx.Assignment (ArrayResultWrapper (Expr t) i) ctx
                     -> Set (Ctx.Assignment IndexLit i)
concreteArrayEntries = foldlFC' f Set.empty
  where f :: Set (Ctx.Assignment IndexLit i)
          -> ArrayResultWrapper (Expr t) i tp
          -> Set (Ctx.Assignment IndexLit i)
        f s e
          | Just (ArrayMap _ _ m _) <- asApp (unwrapArrayResult  e) =
            Set.union s (Map.keysSet (Hash.hashedMap m))
          | otherwise = s

data NatLit tp = (tp ~ BaseNatType) => NatLit Natural

asNatBounds :: Ctx.Assignment (Expr t) idx -> Maybe (Ctx.Assignment NatLit idx)
asNatBounds = traverseFC f
  where f :: Expr t tp -> Maybe (NatLit tp)
        f (SemiRingLiteral SemiRingNat n _) = Just (NatLit n)
        f _ = Nothing

foldBoundLeM :: (r -> Natural -> IO r) -> r -> Natural -> IO r
foldBoundLeM _ r 0 = pure r
foldBoundLeM f r n = do
  r' <- foldBoundLeM f r (n-1)
  f r' n

foldIndicesInRangeBounds :: forall sym idx r
                         .  IsExprBuilder sym
                         => sym
                         -> (r -> Ctx.Assignment (SymExpr sym) idx -> IO r)
                         -> r
                         -> Ctx.Assignment NatLit idx
                         -> IO r
foldIndicesInRangeBounds sym f0 a0 bnds0 = do
  case bnds0 of
    Ctx.Empty -> f0 a0 Ctx.empty
    bnds Ctx.:> NatLit b -> foldIndicesInRangeBounds sym (g f0) a0 bnds
      where g :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> r
              -> Ctx.Assignment (SymExpr sym) idx0
              -> IO r
            g f a i = foldBoundLeM (h f i) a b

            h :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> Ctx.Assignment (SymExpr sym) idx0
              -> r
              -> Natural
              -> IO r
            h f i a j = do
              je <- natLit sym j
              f a (i Ctx.:> je)
#if !MIN_VERSION_base(4,10,0)
    -- This should never happen, but silences a warning.
    _ -> error "internal: invalid index to foldIndicesInRangeBounds"
#endif

{-
-- | Compute the weighted sum of two bitvectors.
bvSum :: (1 <= w)
      => sym
      -> NatRepr w
      -> WeightedSum Integer (SymBV sym w)
      -> IO (SymBV sym w)
bvSum = undefined
-}


instance IsExprBuilder (ExprBuilder t st fs) where
  getConfiguration = sbConfiguration

  setSolverLogListener sb = writeIORef (sbSolverLogger sb)
  getSolverLogListener sb = readIORef (sbSolverLogger sb)

  logSolverEvent sb ev =
    readIORef (sbSolverLogger sb) >>= \case
      Nothing -> return ()
      Just f  -> f ev

  getStatistics sb = do
    allocs <- countNoncesGenerated (exprCounter sb)
    nonLinearOps <- readIORef (sbNonLinearOps sb)
    return $ Statistics { statAllocs = allocs
                        , statNonLinearOps = nonLinearOps }

  ----------------------------------------------------------------------
  -- Program location operations

  getCurrentProgramLoc = curProgramLoc
  setCurrentProgramLoc sym l = writeIORef (sbProgramLoc sym) l

  ----------------------------------------------------------------------
  -- Bool operations.

  truePred  = sbTrue
  falsePred = sbFalse

  notPred sym x
    | Just TrueBool  <- asApp x = return $! falsePred sym
    | Just FalseBool <- asApp x = return $! truePred sym
    | Just (NotBool xn) <- asApp x = return xn
    | otherwise = sbMakeExpr sym (NotBool x)

  andPred sym x y
    | Just True  <- asConstantPred x = return y
    | Just False <- asConstantPred x = return x
    | Just True  <- asConstantPred y = return x
    | Just False <- asConstantPred y = return y
    | x == y = return x

    | Just (NotBool xn) <- asApp x, xn == y =
      return (falsePred sym)
    | Just (NotBool yn) <- asApp y, yn == x =
      return (falsePred sym)
    | Just (AndBool x1 x2) <- asApp x, (x1 == y || x2 == y) = return x
    | Just (AndBool y1 y2) <- asApp y, (y1 == x || y2 == x) = return y

    | otherwise = sbMakeExpr sym (AndBool (min x y) (max x y))

  xorPred sym x y
    | Just True  <- asConstantPred x = notPred sym y
    | Just False <- asConstantPred x = return y
    | Just True  <- asConstantPred y = notPred sym x
    | Just False <- asConstantPred y = return x
    | x == y = return $ falsePred sym

    | Just (NotBool xn) <- asApp x
    , Just (NotBool yn) <- asApp y = do
      sbMakeExpr sym (XorBool xn yn)

    | Just (NotBool xn) <- asApp x = do
      notPred sym =<< sbMakeExpr sym (XorBool xn y)

    | Just (NotBool yn) <- asApp y = do
      notPred sym =<< sbMakeExpr sym (XorBool x yn)

    | otherwise = do
      sbMakeExpr sym (XorBool x y)

  itePred sb c x y
      -- ite c c y = c || y
    | c == x = orPred sb c y
      -- ite c x c = c && x
    | c == y = andPred sb c x
      -- ite c x x = x
    | x == y = return x
      -- ite 1 x y = x
    | Just True  <- asConstantPred c = return x
      -- ite 0 x y = y
    | Just False <- asConstantPred c = return y
      -- ite !c x y = c y x
    | Just (NotBool cn) <- asApp c   = itePred sb cn y x
      -- ite c 1 y = c || y
    | Just True  <- asConstantPred x = orPred sb c y
      -- ite c 0 y = !c && y
    | Just False <- asConstantPred x = do
      andPred sb y =<< sbMakeExpr sb (NotBool c)
      -- ite c x 1 = !c || x
      --             !(c && !x)
    | Just True  <- asConstantPred y = do
      notPred sb =<< andPred sb c =<< notPred sb x
      -- ite c x 0 = c && x
    | Just False <- asConstantPred y = do
      andPred sb c x
      -- ite c (!x) (!y) = !(ite c x y)
    | Just (NotBool xn) <- asApp x
    , Just (NotBool yn) <- asApp y = do
      notPred sb =<< itePred sb c xn yn
      -- Default case
    | otherwise = sbMakeExpr sb $ IteBool c x y

  ----------------------------------------------------------------------
  -- Nat operations.

  natLit sym n = semiRingLit sym SemiRingNat n

  natAdd sym x y = semiRingAdd sym SemiRingNat x y

  natSub sym x y = do
    xr <- natToInteger sym x
    yr <- natToInteger sym y
    integerToNat sym =<< intSub sym xr yr

  natMul sym x y = semiRingMul sym SemiRingNat x y

  natDiv sym x y
    | Just m <- asNat x, Just n <- asNat y, n /= 0 = do
      natLit sym (m `div` n)
      -- 0 / y
    | Just 0 <- asNat x = do
      return x
      -- x / 1
    | Just 1 <- asNat y = do
      return x
    | otherwise = do
      sbMakeExpr sym (NatDiv x y)

  natMod sym x y
    | Just m <- asNat x, Just n <- asNat y, n /= 0 = do
      natLit sym (m `mod` n)
    | Just 0 <- asNat x = do
      natLit sym 0
    | Just 1 <- asNat y = do
      natLit sym 0
    | otherwise = do
      sbMakeExpr sym (NatMod x y)

  natIte sym c x y = semiRingIte sym SemiRingNat c x y

  natEq sym x y
    | Just b <- natCheckEq (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingEq sym SemiRingNat (natEq sym) x y

  natLe sym x y
    | Just b <- natCheckLe (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingLe sym SemiRingNat (natLe sym) x y

  ----------------------------------------------------------------------
  -- Integer operations.

  intLit sym n = semiRingLit sym SemiRingInt n

  intNeg sym x = scalarMul sym SemiRingInt (-1) x

  intAdd sym x y = semiRingAdd sym SemiRingInt x y

  intMul sym x y = semiRingMul sym SemiRingInt x y

  intIte sym c x y = semiRingIte sym SemiRingInt c x y

  intEq sym x y
      -- Use range check
    | Just b <- rangeCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to bitvector equality, when possible
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Sign extend to largest bitvector and compare.
       in case compareNat wx wy of
            NatLT _ -> do
              Just LeqProof <- return (testLeq (incNat wx) wy)
              x' <- bvSext sym wy xbv
              bvEq sym x' ybv
            NatEQ ->
              bvEq sym xbv ybv
            NatGT _ -> do
              Just LeqProof <- return (testLeq (incNat wy) wx)
              y' <- bvSext sym wx ybv
              bvEq sym xbv y'

      -- Reduce to bitvector equality, when possible
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = let wx = bvWidth xbv
          wy = bvWidth ybv
          -- Zero extend to largest bitvector and compare.
       in case compareNat wx wy of
            NatLT _ -> do
              Just LeqProof <- return (testLeq (incNat wx) wy)
              x' <- bvZext sym wy xbv
              bvEq sym x' ybv
            NatEQ ->
              bvEq sym xbv ybv
            NatGT _ -> do
              Just LeqProof <- return (testLeq (incNat wy) wx)
              y' <- bvZext sym wx ybv
              bvEq sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , SemiRingLiteral _ yi _ <- y
    = let w = bvWidth xbv in
      if yi < minSigned w || yi > maxSigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | SemiRingLiteral _ xi _ <- x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minSigned w || xi > maxSigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | Just (BVToInteger xbv) <- asApp x
    , SemiRingLiteral _ yi _ <- y
    = let w = bvWidth xbv in
      if yi < minUnsigned w || yi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | SemiRingLiteral _ xi _ <- x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minUnsigned w || xi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | otherwise = semiRingEq sym SemiRingInt (intEq sym) x y

  intLe sym x y
      -- Use abstract domains
    | Just b <- rangeCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Check with two bitvectors.
    | Just (SBVToInteger xbv) <- asApp x
    , Just (SBVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Sign extend to largest bitvector and compare.
         case compareNat wx wy of
           NatLT _ -> do
             Just LeqProof <- return (testLeq (incNat wx) wy)
             x' <- bvSext sym wy xbv
             bvSle sym x' ybv
           NatEQ -> bvSle sym xbv ybv
           NatGT _ -> do
             Just LeqProof <- return (testLeq (incNat wy) wx)
             y' <- bvSext sym wx ybv
             bvSle sym xbv y'

      -- Check with two bitvectors.
    | Just (BVToInteger xbv) <- asApp x
    , Just (BVToInteger ybv) <- asApp y
    = do let wx = bvWidth xbv
         let wy = bvWidth ybv
         -- Zero extend to largest bitvector and compare.
         case compareNat wx wy of
           NatLT _ -> do
             Just LeqProof <- return (testLeq (incNat wx) wy)
             x' <- bvZext sym wy xbv
             bvUle sym x' ybv
           NatEQ -> bvUle sym xbv ybv
           NatGT _ -> do
             Just LeqProof <- return (testLeq (incNat wy) wx)
             y' <- bvZext sym wx ybv
             bvUle sym xbv y'

    | Just (SBVToInteger xbv) <- asApp x
    , SemiRingLiteral _ yi _ <- y
    = let w = bvWidth xbv in
      if | yi < minSigned w -> return (falsePred sym)
         | yi > maxSigned w -> return (truePred sym)
         | otherwise -> join (bvSle sym <$> pure xbv <*> bvLit sym w yi)

    | SemiRingLiteral _ xi _ <- x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minSigned w -> return (truePred sym)
         | xi > maxSigned w -> return (falsePred sym)
         | otherwise -> join (bvSle sym <$> bvLit sym w xi <*> pure ybv)

    | Just (BVToInteger xbv) <- asApp x
    , SemiRingLiteral _ yi _ <- y
    = let w = bvWidth xbv in
      if | yi < minUnsigned w -> return (falsePred sym)
         | yi > maxUnsigned w -> return (truePred sym)
         | otherwise -> join (bvUle sym <$> pure xbv <*> bvLit sym w yi)

    | SemiRingLiteral _ xi _ <- x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minUnsigned w -> return (truePred sym)
         | xi > maxUnsigned w -> return (falsePred sym)
         | otherwise -> join (bvUle sym <$> bvLit sym w xi <*> pure ybv)

{-  FIXME? how important are these reductions?

      -- Compare to BV lower bound.
    | Just (SBVToInteger xbv) <- x = do
      let w = bvWidth xbv
      l <- curProgramLoc sym
      b_max <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      b_min <- realGe sym y (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      orPred sym b_max =<< andPred sym b_min =<< (bvSle sym xbv =<< realToSBV sym w y)

      -- Compare to SBV upper bound.
    | SBVToReal ybv <- y = do
      let w = bvWidth ybv
      l <- curProgramLoc sym
      b_min <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (minSigned w)) l)
      b_max <- realLe sym x (SemiRingLiteral SemiRingReal (toRational (maxSigned w)) l)
      orPred sym b_min
        =<< andPred sym b_max
        =<< (\xbv -> bvSle sym xbv ybv) =<< realToSBV sym w x
-}

    | otherwise
    = semiRingLe sym SemiRingInt (intLe sym) x y

  intAbs sym x
    | Just i <- asInteger x = intLit sym (abs i)
    | Just True <- rangeCheckLe (SingleRange 0) (exprAbsValue x) = return x
    | Just True <- rangeCheckLe (exprAbsValue x) (SingleRange 0) = intNeg sym x
    | otherwise = sbMakeExpr sym (IntAbs x)

  intDiv sym x y
      -- Div by 1.
    | Just 1 <- asInteger y = return x
      -- Div 0 by anything is zero.
    | Just 0 <- asInteger x = intLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
      if yi >= 0 then
        intLit sym (xi `div` yi)
      else
        intLit sym (negate (xi `div` negate yi))
      -- Return int div
    | otherwise =
        sbMakeExpr sym (IntDiv x y)

  intMod sym x y
      -- Mod by 1.
    | Just 1 <- asInteger y = intLit sym 0
      -- Mod 0 by anything is zero.
    | Just 0 <- asInteger x = intLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asInteger y, yi /= 0 =
        intLit sym (xi `mod` abs yi)
    | Just (SemiRingSum _sr xsum) <- asApp x, Just yi <- asInteger y, yi /= 0 =
        case WSum.reduceIntSumMod xsum (abs yi) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    intLit sym xi
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntMod x' y)
      -- Return int mod.
    | otherwise =
        sbMakeExpr sym (IntMod x y)

  intDivisible sym x k
    | k == 0 = intEq sym x =<< intLit sym 0
    | k == 1 = return (truePred sym)
    | Just xi <- asInteger x = return $ backendPred sym (xi `mod` (toInteger k) == 0)
    | Just (SemiRingSum _sr xsum) <- asApp x =
        case WSum.reduceIntSumMod xsum (toInteger k) of
          xsum' | Just xi <- WSum.asConstant xsum' ->
                    return $ backendPred sym (xi == 0)
                | otherwise ->
                    do x' <- intSum sym xsum'
                       sbMakeExpr sym (IntDivisible x' k)
    | otherwise =
        sbMakeExpr sym (IntDivisible x k)

  ---------------------------------------------------------------------
  -- Bitvector operations

  bvLit sym w i = do
    l <- curProgramLoc sym
    return $ BVExpr w (toUnsigned w i) l

  bvConcat sym x y =
    case (asUnsignedBV x, asUnsignedBV y) of
      -- both values are constants, just compute the concatenation
      (Just xv, Just yv) -> do
          l <- curProgramLoc sym
          let shft :: Int
              shft = fromIntegral (natValue (bvWidth y))
          let w' = addNat (bvWidth x) (bvWidth y)
          -- Work around to satisfy GHC typechecker.
          case isPosNat w' of
            Nothing -> fail $ "bvConcat given bad width."
            Just LeqProof -> do
              return $ BVExpr w' ((xv `Bits.shiftL` shft) Bits..|. yv) l
      -- reassociate to combine constants where possible
      (Just _xv, _)
        | Just (BVConcat _w a b) <- asApp y
        , Just _av <- asUnsignedBV a
        , Just Refl <- testEquality (addNat (bvWidth x) (addNat (bvWidth a) (bvWidth b)))
                        (addNat (addNat (bvWidth x) (bvWidth a)) (bvWidth b))
        , Just LeqProof <- isPosNat (addNat (bvWidth x) (bvWidth a)) -> do
            xa <- bvConcat sym x a
            bvConcat sym xa b
      -- concat two adjacent sub-selects just makes a single select
      _ | Just (BVSelect idx1 n1 a) <- asApp x
        , Just (BVSelect idx2 n2 b) <- asApp y
        , Just Refl <- testEquality a b
        , Just Refl <- testEquality idx1 (addNat idx2 n2)
        , Just LeqProof <- isPosNat (addNat n1 n2)
        , Just LeqProof <- testLeq (addNat idx2 (addNat n1 n2)) (bvWidth a) ->
            bvSelect sym idx2 (addNat n1 n2) a
      -- always reassociate to the right
      _ | Just (BVConcat _w a b) <- asApp x
        , Just _bv <- asUnsignedBV b
        , Just Refl <- testEquality (addNat (bvWidth a) (addNat (bvWidth b) (bvWidth y)))
                        (addNat (addNat (bvWidth a) (bvWidth b)) (bvWidth y))
        , Just LeqProof <- isPosNat (addNat (bvWidth b) (bvWidth y)) -> do
            by <- bvConcat sym b y
            bvConcat sym a by
      -- no special case applies, emit a basic concat expression
      _ -> do
        let wx = bvWidth x
        let wy = bvWidth y
        Just LeqProof <- return (isPosNat (addNat wx wy))
        sbMakeExpr sym $ BVConcat (addNat wx wy) x y

  -- bvSelect has a bunch of special cases that examine the form of the
  -- bitvector being selected from.  This can significantly reduce the size
  -- of expressions that result from the very verbose packing and unpacking
  -- operations that arise from byte-oriented memory models.
  bvSelect sb idx n x
    | Just xv <- asUnsignedBV x = do
      l <- curProgramLoc sb
      let mask = maxUnsigned n
      let shft = fromIntegral (natValue idx)
      return $ BVExpr n ((xv `Bits.shiftR` shft) Bits..&. mask) l

      -- nested selects can be collapsed
    | Just (BVSelect idx' _n' b) <- asApp x
    , let idx2 = addNat idx idx'
    , Just LeqProof <- testLeq (addNat idx2 n) (bvWidth b) =
      bvSelect sb idx2 n b

      -- select the entire bitvector is the identity function
    | Just _ <- testEquality idx (knownNat :: NatRepr 0)
    , Just Refl <- testEquality n (bvWidth x) =
      return x

    | Just (BVShl w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq diffRepr idx = do
      Just LeqProof <- return $ testLeq (addNat (subNat idx diffRepr) n) w
      bvSelect sb (subNat idx diffRepr) n a
    | Just (BVShl _w _a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat idx n) diffRepr =
      bvLit sb n 0

    | Just (BVAshr w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a

    | Just (BVLshr w a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq (addNat (addNat idx diffRepr) n) w =
      bvSelect sb (addNat idx diffRepr) n a
    | Just (BVLshr w _a b) <- asApp x
    , Just diff <- asUnsignedBV b
    , Just (Some diffRepr) <- someNat diff
    , Just LeqProof <- testLeq w (addNat idx diffRepr) =
      bvLit sb n 0

      -- select from a sign extension
    | Just (BVSext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      -- Add dynamic check
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      zeros <- minUnsignedBV sb ext
      ones  <- maxUnsignedBV sb ext
      c     <- bvIsNeg sb b
      hi    <- bvIte sb c ones zeros
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select from a zero extension
    | Just (BVZext w b) <- asApp x = do
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (bvWidth b) w
      let ext = subNat w (bvWidth b)
      Just LeqProof <- return $ isPosNat w
      Just LeqProof <- return $ isPosNat ext
      hi    <- bvLit sb ext 0
      x'    <- bvConcat sb hi b
      -- Add dynamic check
      Just LeqProof <- return $ testLeq (addNat idx n) (addNat ext (bvWidth b))
      bvSelect sb idx n x'

      -- select is entirely within the less-significant bits of a concat
   | Just (BVConcat _w _a b) <- asApp x
   , Just LeqProof <- testLeq (addNat idx n) (bvWidth b) = do
     bvSelect sb idx n b

      -- select is entirely within the more-significant bits of a concat
   | Just (BVConcat _w a b) <- asApp x
   , Just LeqProof <- testLeq (bvWidth b) idx
   , Just LeqProof <- isPosNat idx
   , let diff = subNat idx (bvWidth b)
   , Just LeqProof <- testLeq (addNat diff n) (bvWidth a) = do
     bvSelect sb (subNat idx (bvWidth b)) n a

   -- when the selected region overlaps a concat boundary we have:
   --  select idx n (concat a b) =
   --      concat (select 0 n1 a) (select idx n2 b)
   --   where n1 + n2 = n and idx + n2 = width b
   --
   -- NB: this case must appear after the two above that check for selects
   --     entirely within the first or second arguments of a concat, otherwise
   --     some of the arithmetic checks below may fail
   | Just (BVConcat _w a b) <- asApp x = do
     Just LeqProof <- return $ testLeq idx (bvWidth b)
     let n2 = subNat (bvWidth b) idx
     Just LeqProof <- return $ testLeq n2 n
     let n1 = subNat n n2
     let z  = knownNat :: NatRepr 0

     Just LeqProof <- return $ isPosNat n1
     Just LeqProof <- return $ testLeq (addNat z n1) (bvWidth a)
     a' <- bvSelect sb z   n1 a

     Just LeqProof <- return $ isPosNat n2
     Just LeqProof <- return $ testLeq (addNat idx n2) (bvWidth b)
     b' <- bvSelect sb idx n2 b

     Just Refl <- return $ testEquality (addNat n1 n2) n
     bvConcat sb a' b'

    | Just (BVBitAnd _w a b) <- asApp x = do
      a' <- bvSelect sb idx n a
      b' <- bvSelect sb idx n b
      bvAndBits sb a' b'

    | Just (BVBitOr _w a b) <- asApp x = do
      a' <- bvSelect sb idx n a
      b' <- bvSelect sb idx n b
      bvOrBits sb a' b'

    | Just (BVBitXor _w a b) <- asApp x = do
      a' <- bvSelect sb idx n a
      b' <- bvSelect sb idx n b
      bvXorBits sb a' b'

    | Just (BVBitNot _w a) <- asApp x = do
      a' <- bvSelect sb idx n a
      bvNotBits sb a'

    | Just (BVUnaryTerm u) <- asApp x
    , Just Refl <- testEquality idx (knownNat @0) =
      bvUnary sb =<< UnaryBV.trunc sb u n

      -- if none of the above apply, produce a basic select term
    | otherwise = sbMakeExpr sb $ BVSelect idx n x

  testBitBV sym i y
    | i < 0 || i >= natValue (bvWidth y) =
      fail $ "Illegal bit index."

      -- Constant evaluation
    | Just yc <- asUnsignedBV y
    , i <= fromIntegral (maxBound :: Int) =
      return $! backendPred sym (yc `Bits.testBit` fromIntegral i)

    | Just (BVZext _w y') <- asApp y =
      if i >= natValue (bvWidth y') then
        return $ falsePred sym
      else
        testBitBV sym i y'

    | Just (BVSext _w y') <- asApp y =
      if i >= natValue (bvWidth y') then
        testBitBV sym (natValue (bvWidth y') - 1) y'
      else
        testBitBV sym i y'

    | Just (BVIte _ _ c a b) <- asApp y =
      do a' <- testBitBV sym i a
         b' <- testBitBV sym i b
         itePred sym c a' b'

      -- i must equal 0 because width is 1
    | Just (PredToBV py) <- asApp y =
      return py

    | Just b <- BVD.testBit (bvWidth y) (exprAbsValue y) i = do
      return $! backendPred sym b

    | otherwise = do
      sbMakeExpr sym $ BVTestBit i y

  bvIte sym c x y
    | Just TrueBool  <- asApp c = return x
    | Just FalseBool <- asApp c = return y
    | x == y = return x
    | Just (NotBool cn) <- asApp c = bvIte sym cn y x

    | Just (PredToBV px) <- asApp x
    , Just (PredToBV py) <- asApp y =
      do z <- itePred sym c px py
         predToBV sym z (knownNat @1)

    | Just (BVZext w  x') <- asApp x
    , Just (BVZext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvZext sym w z

    | Just (BVSext w  x') <- asApp x
    , Just (BVSext w' y') <- asApp y
    , Just Refl <- testEquality (bvWidth x') (bvWidth y')
    , Just Refl <- testEquality w w' =
      do z <- bvIte sym c x' y'
         bvSext sym w z

    | Just (FloatToBinary fpp1 x') <- asApp x
    , Just (FloatToBinary fpp2 y') <- asApp y
    , Just Refl <- testEquality fpp1 fpp2 =
      floatToBinary sym =<< floatIte sym c x' y'

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y ->
             do uz <- UnaryBV.mux sym c ux uy
                let sz = 1 + iteSize x + iteSize y
                sbTryUnaryTerm sym uz (BVIte (bvWidth x) sz c x y)
           | otherwise ->
             do let sz = 1 + iteSize x + iteSize y
                sbMakeExpr sym $ BVIte (bvWidth x) sz c x y

  bvEq sym x y
    | Just xc <- asUnsignedBV x
    , Just yc <- asUnsignedBV y = do
      return $! backendPred sym (xc == yc)

    | Just (PredToBV px) <- asApp x
    , Just (PredToBV py) <- asApp y =
      eqPred sym px py

    | Just b <- BVD.eq (exprAbsValue x) (exprAbsValue y) = do
      return $! backendPred sym b

    | x == y = return $! truePred sym

    | Just i <- asUnsignedBV x
    , Just (BVAdd w (asUnsignedBV -> Just j) y_r) <- asApp y = do
      c <- bvLit sym w (i - j)
      bvEq sym c y_r

    | Just (BVAdd w (asUnsignedBV -> Just i) x_r) <- asApp x
    , Just j <- asUnsignedBV y = do
      c <- bvLit sym w (j - i)
      bvEq sym c x_r

    | Just (BVAdd w (asUnsignedBV -> Just i) x_r) <- asApp x
    , Just (BVAdd _ (asUnsignedBV -> Just j) y_r) <- asApp y = do

      z_c <- bvLit sym w (i - j)
      z_r <- bvAdd sym z_c x_r
      bvEq sym z_r y_r

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.eq sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BVEq (min x y) (max x y)

  bvSlt sym x y
    | Just xc <- asSignedBV x
    , Just yc <- asSignedBV y =
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.slt (bvWidth x) (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y = return (falsePred sym)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.slt sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BVSlt x y

  bvUlt sym x y
    | Just xc <- asUnsignedBV x
    , Just yc <- asUnsignedBV y = do
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.ult (bvWidth x) (exprAbsValue x) (exprAbsValue y) =
      return $! backendPred sym b
    | x == y =
      return $! falsePred sym

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.ult sym ux uy

           | otherwise
           -> sbMakeExpr sym $ BVUlt x y

  bvShl sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftL i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeExpr sym $ BVShl (bvWidth x) x y

  bvLshr sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftR i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeExpr sym $ BVLshr (bvWidth x) x y

  bvAshr sym x y
   | Just i <- asSignedBV x, Just n <- asSignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftR i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeExpr sym $ BVAshr (bvWidth x) x y

  bvZext sym w x
    | Just i <- asUnsignedBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w i

      -- Concatenate unsign extension.
    | Just (BVZext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym $ BVZext w y

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.uext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym $ BVZext w x

  bvSext sym w x
    | Just i <- asSignedBV x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvLit sym w i

      -- Concatenate sign extension.
    | Just (BVSext _ y) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym (BVSext w y)

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.sext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeExpr sym (BVSext w x)

  bvNotBits sym x
    | Just i <- asUnsignedBV x = do
      bvLit sym (bvWidth x) $ i `Bits.xor` (maxUnsigned (bvWidth x))
    | Just (BVBitNot _ y) <- asApp x = return y
    | otherwise = sbMakeExpr sym $ BVBitNot (bvWidth x) x

  bvAndBits sym x y
    | Just 0 <- asUnsignedBV x = return x
    | Just 0 <- asUnsignedBV y = return y
    | Just (maxUnsigned (bvWidth x)) == asUnsignedBV x = return y
    | Just (maxUnsigned (bvWidth x)) == asUnsignedBV y = return x
    | otherwise = bvBinOp1 (Bits..&.) BVBitAnd sym x y
  bvOrBits sym x y
    | Just 0 <- asUnsignedBV x = return y
    | Just 0 <- asUnsignedBV y = return x
    | Just (maxUnsigned (bvWidth x)) == asUnsignedBV x = return x
    | Just (maxUnsigned (bvWidth x)) == asUnsignedBV y = return y
    | otherwise = bvBinOp1 (Bits..|.) BVBitOr sym x y

  -- Special case for the self-XOR trick, which compilers sometimes will use
  -- to zero the state of a register
  bvXorBits sym x y | x == y = bvLit sym (bvWidth x) 0
  bvXorBits sym x y = bvBinOp1 Bits.xor BVBitXor sym x y

  bvNeg sym x
    | Just i <- asSignedBV x = bvLit sym (bvWidth x) (-i)
    | Just (BVNeg _ y) <- asApp x = return y

    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           if | Just ux <- asUnaryBV sym x
              -> do uz <- UnaryBV.neg sym ux
                    sbTryUnaryTerm sym uz (BVNeg (bvWidth x) x)
              | otherwise
              -> sbMakeExpr sym $ BVNeg (bvWidth x) x

  bvAdd sym x y
    | Just 0 <- asUnsignedBV x = return y
    | Just 0 <- asUnsignedBV y = return x

      -- Constants
    | Just i <- asUnsignedBV x
    , Just j <- asUnsignedBV y =

      bvLit sym (bvWidth x) $ i + j

    | Just i <- asUnsignedBV x
    , Just (BVAdd w (asUnsignedBV -> Just j) y_r) <- asApp y = do
      c <- bvLit sym w (i + j)
      bvAdd sym c y_r

    | Just (BVAdd w (asUnsignedBV -> Just i) x_r) <- asApp x
    , Just j <- asUnsignedBV y = do
      c <- bvLit sym w (i + j)
      bvAdd sym c x_r

    | Just (BVAdd w (asUnsignedBV -> Just i) x_r) <- asApp x
    , Just (BVAdd _ (asUnsignedBV -> Just j) y_r) <- asApp y = do

      z_c <- bvLit sym w (i + j)
      z_r <- bvAdd sym x_r y_r
      bvAdd sym z_c z_r

    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           if | Just ux <- asUnaryBV sym x
              , Just uy <- asUnaryBV sym y
              -> do uz <- UnaryBV.add sym ux uy
                    sbTryUnaryTerm sym uz (BVAdd (bvWidth x) (min x y) (max x y))
              | otherwise
              -> sbMakeExpr sym $ BVAdd (bvWidth x) (min x y) (max x y)

  bvMul sym x y
    | Just 0 <- asUnsignedBV x = return x
    | Just 1 <- asUnsignedBV x = return y
    | Just 0 <- asUnsignedBV y = return y
    | Just 1 <- asUnsignedBV y = return x
    | Just i <- asUnsignedBV x, Just j <- asUnsignedBV y =
      bvLit sym (bvWidth x) $ i * j
    | x <= y =
      sbMakeExpr sym $ BVMul (bvWidth x) x y
    | otherwise =
      sbMakeExpr sym $ BVMul (bvWidth x) y x

  bvIsNonzero sym x
    | Just (BVIte _ _ p t f) <- asApp x = do
          t' <- bvIsNonzero sym t
          f' <- bvIsNonzero sym f
          itePred sym p t' f'
    | Just (BVConcat _ a b) <- asApp x =
       do pa <- bvIsNonzero sym a
          pb <- bvIsNonzero sym b
          orPred sym pa pb
    | Just (BVZext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVSext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (PredToBV p) <- asApp x =
          return p
    | Just (BVUnaryTerm ubv) <- asApp x =
          UnaryBV.sym_evaluate
            (\i -> return $! backendPred sym (i/=0))
            (itePred sym)
            ubv
    | otherwise = do
          let w = bvWidth x
          zro <- bvLit sym w 0
          notPred sym =<< bvEq sym x zro

  bvUdiv = bvBinDivOp1 quot BVUdiv
  bvUrem = bvBinDivOp1 rem BVUrem
  bvSdiv = bvSignedBinDivOp quot BVSdiv
  bvSrem = bvSignedBinDivOp rem BVSrem

  bvPopcount sym x
    | Just i <- asUnsignedBV x = bvLit sym w (toInteger (Bits.popCount i))
    | otherwise = sbMakeExpr sym $ BVPopcount w x
   where w = bvWidth x

  bvCountTrailingZeros sym x
    | Just i <- asUnsignedBV x = bvLit sym w (ctz w i)
    | otherwise = sbMakeExpr sym $ BVCountTrailingZeros w x
   where w = bvWidth x

  bvCountLeadingZeros sym x
    | Just i <- asUnsignedBV x = bvLit sym w (clz w i)
    | otherwise = sbMakeExpr sym $ BVCountLeadingZeros w x
   where w = bvWidth x

  mkStruct sym args = do
    sbMakeExpr sym $ StructCtor (fmapFC exprType args) args

  structField sym s i
    | Just (StructCtor _ args) <- asApp s = return $! args Ctx.! i
    | otherwise = do
      case exprType s of
        BaseStructRepr flds ->
          sbMakeExpr sym $ StructField s i (flds Ctx.! i)

  structIte sym p x y
    | Just TrueBool     <- asApp p = return x
    | Just FalseBool    <- asApp p = return y
    | Just (NotBool pn) <- asApp p = structIte sym pn y x
    | x == y    = return x
    | otherwise =
      case exprType x of
        BaseStructRepr flds -> sbMakeExpr sym $ StructIte flds p x y

  --------------------------------------------------------------------
  -- String operations

  stringLit sym txt =
    do l <- curProgramLoc sym
       return $! StringExpr txt l

  stringEq sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = if x' == y' then return (truePred sym) else return (falsePred sym)
  stringEq _ _ _
    = fail "Expected concrete strings in stringEq"

  stringIte _sym c x y
    | Just c' <- asConstantPred c
    = if c' then return x else return y
  stringIte _sym _c x y
    | Just x' <- asString x
    , Just y' <- asString y
    , x' == y'
    = return x
  stringIte _sym _c _x _y
    = fail "Cannot merge distinct concrete strings"

  stringConcat sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = stringLit sym (x' <> y')
  stringConcat _ _ _
    = fail "Expected concrete strings in stringConcat"

  stringLength sym x
    | Just x' <- asString x
    = do natLit sym (fromIntegral (Text.length x'))
  stringLength _ _
    = fail "Expected concrete strings in stringLength"

  --------------------------------------------------------------------
  -- Symbolic array operations

  constantArray sym idxRepr v =
    sbMakeExpr sym $ ConstantArray idxRepr (exprType v) v

  arrayFromFn sym fn = do
    sbNonceExpr sym $ ArrayFromFn fn

  arrayMap sym f arrays
      -- Cancel out integerToReal (realToInteger a)
    | Just IntegerToRealFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just RealToIntegerFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)
      -- Cancel out realToInteger (integerToReal a)
    | Just RealToIntegerFn  <- asMatlabSolverFn f
    , Just (MapOverArrays g _ args) <- asNonceApp (unwrapArrayResult (arrays^._1))
    , Just IntegerToRealFn <- asMatlabSolverFn g =
      return $! unwrapArrayResult (args^._1)

    -- When the array is an update of concrete entries, map over the entries.
    | s <- concreteArrayEntries arrays
    , not (Set.null s) = do
        -- Distribute over base values.
        --
        -- The underlyingArrayMapElf function strings a top-level arrayMap value.
        --
        -- It is ok because we don't care what the value of base is at any index
        -- in s.
        base <- arrayMap sym f (fmapFC underlyingArrayMapExpr arrays)

        -- This lookups a given index in an array used as an argument.
        let evalArgs :: Ctx.Assignment IndexLit (idx ::> itp)
                        -- ^ A representatio of the concrete index (if defined).
                        -> Ctx.Assignment (Expr t)  (idx ::> itp)
                           -- ^ The index to use.
                        -> ArrayResultWrapper (Expr t) (idx ::> itp) d
                           -- ^ The array to get the value at.
                        -> IO (Expr t d)
            evalArgs const_idx sym_idx a = do
              sbConcreteLookup sym (unwrapArrayResult a) (Just const_idx) sym_idx
        let evalIndex :: ExprSymFn t ctx ret
                      -> Ctx.Assignment (ArrayResultWrapper (Expr t) (i::>itp)) ctx
                      -> Ctx.Assignment IndexLit (i::>itp)
                      -> IO (Expr t ret)
            evalIndex g arrays0 const_idx = do
              sym_idx <- traverseFC (indexLit sym) const_idx
              applySymFn sym g =<< traverseFC (evalArgs const_idx sym_idx) arrays0
        m <- fmap Hash.mkMap $ sequence $ Map.fromSet (evalIndex f arrays) s
        arrayUpdateAtIdxLits sym m base
      -- When entries are constants, then just evaluate constant.
    | Just cns <-  traverseFC (\a -> asConstantArray (unwrapArrayResult a)) arrays = do
      r <- betaReduce sym f cns
      case exprType (unwrapArrayResult (Ctx.last arrays)) of
        BaseArrayRepr idxRepr _ -> do
          constantArray sym idxRepr r

    | otherwise = do
      let idx = arrayResultIdxType (exprType (unwrapArrayResult (Ctx.last arrays)))
      sbNonceExpr sym $ MapOverArrays f idx arrays

  arrayUpdate sym arr i v
      -- Update at concrete index.
    | Just ci <- asConcreteIndices i =
      case asApp arr of
        Just (ArrayMap idx tp m def) -> do
          let new_map =
                case asApp def of
                  Just (ConstantArray _ _ cns) | v == cns -> Hash.mapDelete ci m
                  _ -> Hash.mapInsert ci v m
          sbMakeExpr sym $ ArrayMap idx tp new_map def
        _ -> do
          let idx = fmapFC exprType  i
          let bRepr = exprType v
          let new_map = Map.singleton ci v
          sbMakeExpr sym $ ArrayMap idx bRepr (Hash.mkMap new_map) arr
    | otherwise = do
      let bRepr = exprType v
      sbMakeExpr sym (UpdateArray bRepr (fmapFC exprType i)  arr i v)

  arrayLookup sym arr idx =
    sbConcreteLookup sym arr (asConcreteIndices idx) idx

  -- | Create an array from a map of concrete indices to values.
  arrayUpdateAtIdxLits sym m def_map = do
    BaseArrayRepr idx_tps baseRepr <- return $ exprType def_map
    let new_map
          | Just (ConstantArray _ _ default_value) <- asApp def_map =
            Hash.mapFilter (/= default_value) m
          | otherwise = m
    if Hash.mapNull new_map then
      return def_map
     else
      sbMakeExpr sym $ ArrayMap idx_tps baseRepr new_map def_map

  arrayIte sym p x y
     | Just b <- asConstantPred p = return $! if b then x else y
     | x == y = return x
       -- Extract all concrete updates out.
     | ArrayMapView mx x' <- viewArrayMap x
     , ArrayMapView my y' <- viewArrayMap y
     , not (Hash.mapNull mx) || not (Hash.mapNull my) = do
       case exprType x of
         BaseArrayRepr idxRepr bRepr -> do
           let both_fn _ u v = baseTypeIte sym p u v
               left_fn idx u = do
                 v <- sbConcreteLookup sym y' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
               right_fn idx v = do
                 u <- sbConcreteLookup sym x' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
           mz <- Hash.mergeMapWithM both_fn left_fn right_fn mx my
           z' <- arrayIte sym p x' y'

           sbMakeExpr sym $ ArrayMap idxRepr bRepr mz z'

     | otherwise =
       case exprType x of
         BaseArrayRepr idxRepr bRepr ->
            sbMakeExpr sym (MuxArray idxRepr bRepr p x y)

  arrayEq sym x y
    | x == y =
      return $! truePred sym
    | otherwise =
      sbMakeExpr sym $! ArrayEq x y


  arrayTrueOnEntries sym f a
    | Just True <- exprAbsValue a =
      return $ truePred sym
    | Just (IndicesInRange _ bnds) <- asMatlabSolverFn f
    , Just v <- asNatBounds bnds = do
      let h :: Expr t (BaseArrayType (i::>it) BaseBoolType)
            -> BoolExpr t
            -> Ctx.Assignment (Expr t) (i::>it)
            -> IO (BoolExpr t)
          h a0 p i = andPred sym p =<< arrayLookup sym a0 i
      foldIndicesInRangeBounds sym (h a) (truePred sym) v

    | otherwise =
      sbNonceExpr sym $! ArrayTrueOnEntries f a

  ----------------------------------------------------------------------
  -- Lossless (injective) conversions

  natToInteger sym x
    | SemiRingLiteral SemiRingNat n l <- x = return $! SemiRingLiteral SemiRingInt (toInteger n) l
    | Just (IntegerToNat y) <- asApp x = return y
    | otherwise = sbMakeExpr sym (NatToInteger x)

  integerToNat sb x
    | SemiRingLiteral SemiRingInt i l <- x
    , 0 <= i
    = return $! SemiRingLiteral SemiRingNat (fromIntegral i) l
    | Just (NatToInteger y) <- asApp x = return y
    | otherwise =
      sbMakeExpr sb (IntegerToNat x)

  integerToReal sym x
    | SemiRingLiteral SemiRingInt i l <- x = return $! SemiRingLiteral SemiRingReal (toRational i) l
    | Just (RealToInteger y) <- asApp x = return y
    | otherwise  = sbMakeExpr sym (IntegerToReal x)

  realToInteger sym x
      -- Ground case
    | SemiRingLiteral SemiRingReal r l <- x = return $! SemiRingLiteral SemiRingInt (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | otherwise =
      sbMakeExpr sym (RealToInteger x)

  bvToNat sym x
    | Just i <- asUnsignedBV x =
      natLit sym (fromInteger i)
    | otherwise = sbMakeExpr sym (BVToNat x)

  bvToInteger sym x
    | Just i <- asUnsignedBV x =
      intLit sym i
      -- bvToInteger (integerToBv x w) == mod x (2^w)
    | Just (IntegerToBV xi w) <- asApp x =
      intMod sym xi =<< intLit sym (2^natValue w)
    | otherwise =
      sbMakeExpr sym (BVToInteger x)

  sbvToInteger sym x
    | Just i <- asSignedBV x =
      intLit sym i
      -- sbvToInteger (integerToBv x w) == mod (x + 2^(w-1)) (2^w) - 2^(w-1)
    | Just (IntegerToBV xi w) <- asApp x =
      do halfmod <- intLit sym (2 ^ (natValue w - 1))
         modulus <- intLit sym (2 ^ natValue w)
         x'      <- intAdd sym xi halfmod
         z       <- intMod sym x' modulus
         intSub sym z halfmod
    | otherwise =
      sbMakeExpr sym (SBVToInteger x)

  predToBV sym p w
    | Just b <- asConstantPred p =
        if b then bvLit sym w 1 else bvLit sym w 0
    | otherwise =
       case compareNat w (knownNat @1) of
         NatEQ   -> sbMakeExpr sym (PredToBV p)
         NatGT _ -> bvZext sym w =<< sbMakeExpr sym (PredToBV p)
         NatLT _ -> fail "impossible case in predToBV"

  integerToBV sym xr w
    | SemiRingLiteral SemiRingInt i _ <- xr =
      bvLit sym w i

    | Just (BVToInteger r) <- asApp xr =
      case compareNat (bvWidth r) w of
        NatLT _ -> bvZext sym w r
        NatEQ   -> return r
        NatGT _ -> bvTrunc sym w r

    | Just (SBVToInteger r) <- asApp xr =
      case compareNat (bvWidth r) w of
        NatLT _ -> bvSext sym w r
        NatEQ   -> return r
        NatGT _ -> bvTrunc sym w r

    | otherwise =
      sbMakeExpr sym (IntegerToBV xr w)

  realRound sym x
      -- Ground case
    | SemiRingLiteral SemiRingReal r l <- x = return $ SemiRingLiteral SemiRingInt (roundAway r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (RoundReal x)

  realFloor sym x
      -- Ground case
    | SemiRingLiteral SemiRingReal r l <- x = return $ SemiRingLiteral SemiRingInt (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (FloorReal x)

  realCeil sym x
      -- Ground case
    | SemiRingLiteral SemiRingReal r l <- x = return $ SemiRingLiteral SemiRingInt (ceiling r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (CeilReal x)

  ----------------------------------------------------------------------
  -- Real operations

  realLit sb r = do
    l <- curProgramLoc sb
    return (SemiRingLiteral SemiRingReal r l)

  realZero = sbZero

  realEq sym x y
      -- Use range check
    | Just b <- ravCheckEq (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer equality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intEq sym xi yi

    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SemiRingReal yr _ <- y
    = if denominator yr == 1
         then intEq sym xi =<< intLit sym (numerator yr)
         else return (falsePred sym)

    | SemiRingLiteral SemiRingReal xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = if denominator xr == 1
         then intEq sym yi =<< intLit sym (numerator xr)
         else return (falsePred sym)

    | otherwise
    = semiRingEq sym SemiRingReal (realEq sym) x y

  realLe sym x y
      -- Use range check
    | Just b <- ravCheckLe (exprAbsValue x) (exprAbsValue y)
    = return $ backendPred sym b

      -- Reduce to integer inequality, when possible
    | Just (IntegerToReal xi) <- asApp x
    , Just (IntegerToReal yi) <- asApp y
    = intLe sym xi yi

      -- if the upper range is a constant, do an integer comparison
      -- with @floor(y)@
    | Just (IntegerToReal xi) <- asApp x
    , SemiRingLiteral SemiRingReal yr _ <- y
    = join (intLe sym <$> pure xi <*> intLit sym (floor yr))

      -- if the lower range is a constant, do an integer comparison
      -- with @ceiling(x)@
    | SemiRingLiteral SemiRingReal xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = join (intLe sym <$> intLit sym (ceiling xr) <*> pure yi)

    | otherwise
    = semiRingLe sym SemiRingReal (realLe sym) x y

  realIte sym c x y = semiRingIte sym SemiRingReal c x y

  realNeg sym x = scalarMul sym SemiRingReal (-1) x

  realAdd sym x y = semiRingAdd sym SemiRingReal x y

  realMul sym x y = semiRingMul sym SemiRingReal x y

  realDiv sym x y
    | Just 0 <- asRational x =
      return x
    | Just xd <- asRational x, Just yd <- asRational y, yd /= 0 = do
      realLit sym (xd / yd)
      -- Handle division by a constant.
    | Just yd <- asRational y, yd /= 0 = do
      scalarMul sym SemiRingReal (1 / yd) x
    | otherwise =
      sbMakeExpr sym $ RealDiv x y

  isInteger sb x
    | Just r <- asRational x = return $ backendPred sb (denominator r == 1)
    | Just b <- ravIsInteger (exprAbsValue x) = return $ backendPred sb b
    | otherwise = sbMakeExpr sb $ RealIsInteger x

  realSqrt sym x = do
    let sqrt_dbl :: Double -> Double
        sqrt_dbl = sqrt
    case x of
      SemiRingLiteral SemiRingReal r _
        | r <= 0 -> realLit sym 0
        | Just w <- tryRationalSqrt r -> realLit sym w
        | sbFloatReduce sym -> realLit sym (toRational (sqrt_dbl (fromRational r)))
      _ -> sbMakeExpr sym (RealSqrt x)

  realPi sym = do
    if sbFloatReduce sym then
      realLit sym (toRational (pi :: Double))
     else
      sbMakeExpr sym Pi

  realSin sym x =
    case asRational x of
      Just 0 -> realLit sym 0
      Just c | sbFloatReduce sym -> realLit sym (toRational (sin (toDouble c)))
      _ -> sbMakeExpr sym (RealSin x)

  realCos sym x =
    case asRational x of
      Just 0 -> realLit sym 1
      Just c | sbFloatReduce sym -> realLit sym (toRational (cos (toDouble c)))
      _ -> sbMakeExpr sym (RealCos x)

  realAtan2 sb y x = do
    case (asRational y, asRational x) of
      (Just 0, _) -> realLit sb 0
      (Just yc, Just xc) | sbFloatReduce sb -> do
        realLit sb (toRational (atan2 (toDouble yc) (toDouble xc)))
      _ -> sbMakeExpr sb (RealATan2 y x)

  realSinh sb x =
    case asRational x of
      Just 0 -> realLit sb 0
      Just c | sbFloatReduce sb -> realLit sb (toRational (sinh (toDouble c)))
      _ -> sbMakeExpr sb (RealSinh x)

  realCosh sb x =
    case asRational x of
      Just 0 -> realLit sb 1
      Just c | sbFloatReduce sb -> realLit sb (toRational (cosh (toDouble c)))
      _ -> sbMakeExpr sb (RealCosh x)

  realExp sym x
    | Just 0 <- asRational x = realLit sym 1
    | Just c <- asRational x, sbFloatReduce sym = realLit sym (toRational (exp (toDouble c)))
    | otherwise = sbMakeExpr sym (RealExp x)

  realLog sym x =
    case asRational x of
      Just c | sbFloatReduce sym -> realLit sym (toRational (log (toDouble c)))
      _ -> sbMakeExpr sym (RealLog x)

  ----------------------------------------------------------------------
  -- IEEE-754 floating-point operations
  floatPZero = floatIEEEArithCt FloatPZero
  floatNZero = floatIEEEArithCt FloatNZero
  floatNaN = floatIEEEArithCt FloatNaN
  floatPInf = floatIEEEArithCt FloatPInf
  floatNInf = floatIEEEArithCt FloatNInf
  floatLit sym fpp x = realToFloat sym fpp RNE =<< realLit sym x
  floatNeg = floatIEEEArithUnOp FloatNeg
  floatAbs = floatIEEEArithUnOp FloatAbs
  floatSqrt = floatIEEEArithUnOpR FloatSqrt
  floatAdd = floatIEEEArithBinOpR FloatAdd
  floatSub = floatIEEEArithBinOpR FloatSub
  floatMul = floatIEEEArithBinOpR FloatMul
  floatDiv = floatIEEEArithBinOpR FloatDiv
  floatRem = floatIEEEArithBinOp FloatRem
  floatMin = floatIEEEArithBinOp FloatMin
  floatMax = floatIEEEArithBinOp FloatMax
  floatFMA sym r x y z =
    let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ FloatFMA fpp r x y z
  floatEq sym x y
    | x == y = return $! truePred sym
    | otherwise = (floatIEEELogicBinOp FloatEq) sym x y
  floatNe sym x y = notPred sym =<< floatEq sym x y
  floatFpEq = floatIEEELogicBinOp FloatFpEq
  floatFpNe = floatIEEELogicBinOp FloatFpNe
  floatLe = floatIEEELogicBinOp FloatLe
  floatLt = floatIEEELogicBinOp FloatLt
  floatGe sym x y = floatLe sym y x
  floatGt sym x y = floatLt sym y x
  floatIte sym c x y
    | Just TrueBool  <- asApp c = return x
    | Just FalseBool <- asApp c = return y
    | x == y = return x
    | Just (NotBool c') <- asApp c = floatIte sym c' y x
    | otherwise =
      let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ FloatIte fpp c x y
  floatIsNaN = floatIEEELogicUnOp FloatIsNaN
  floatIsInf = floatIEEELogicUnOp FloatIsInf
  floatIsZero = floatIEEELogicUnOp FloatIsZero
  floatIsPos = floatIEEELogicUnOp FloatIsPos
  floatIsNeg = floatIEEELogicUnOp FloatIsNeg
  floatIsSubnorm = floatIEEELogicUnOp FloatIsSubnorm
  floatIsNorm = floatIEEELogicUnOp FloatIsNorm
  floatCast sym fpp r x
    | FloatingPointPrecisionRepr eb sb <- fpp
    , Just (FloatCast (FloatingPointPrecisionRepr eb' sb') _ fval) <- asApp x
    , natValue eb <= natValue eb'
    , natValue sb <= natValue sb'
    , Just Refl <- testEquality (BaseFloatRepr fpp) (exprType fval)
    = return fval
    | otherwise = sbMakeExpr sym $ FloatCast fpp r x
  floatRound = floatIEEEArithUnOpR FloatRound
  floatFromBinary sym fpp x
    | Just (FloatToBinary fpp' fval) <- asApp x
    , Just Refl <- testEquality fpp fpp'
    = return fval
    | otherwise = sbMakeExpr sym $ FloatFromBinary fpp x
  floatToBinary sym x = case exprType x of
    BaseFloatRepr fpp | LeqProof <- lemmaFloatPrecisionIsPos fpp ->
      sbMakeExpr sym $ FloatToBinary fpp x
  bvToFloat sym fpp r = sbMakeExpr sym . BVToFloat fpp r
  sbvToFloat sym fpp r = sbMakeExpr sym . SBVToFloat fpp r
  realToFloat sym fpp r = sbMakeExpr sym . RealToFloat fpp r
  floatToBV sym w r = sbMakeExpr sym . FloatToBV w r
  floatToSBV sym w r = sbMakeExpr sym . FloatToSBV w r
  floatToReal sym = sbMakeExpr sym . FloatToReal

  ----------------------------------------------------------------------
  -- Cplx operations

  mkComplex sym c = sbMakeExpr sym (Cplx c)

  getRealPart _ e
    | Just (Cplx (r :+ _)) <- asApp e = return r
  getRealPart sym x =
    sbMakeExpr sym (RealPart x)

  getImagPart _ e
    | Just (Cplx (_ :+ i)) <- asApp e = return i
  getImagPart sym x =
    sbMakeExpr sym (ImagPart x)

  cplxGetParts _ e
    | Just (Cplx c) <- asApp e = return c
  cplxGetParts sym x =
    (:+) <$> sbMakeExpr sym (RealPart x)
         <*> sbMakeExpr sym (ImagPart x)

floatIEEEArithBinOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOp ctor sym x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x y
floatIEEEArithBinOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithBinOpR ctor sym r x y =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x y
floatIEEEArithUnOp
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOp ctor sym x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp x
floatIEEEArithUnOpR
  :: (e ~ Expr t)
  => (  FloatPrecisionRepr fpp
     -> RoundingMode
     -> e (BaseFloatType fpp)
     -> App e (BaseFloatType fpp)
     )
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e (BaseFloatType fpp)
  -> IO (e (BaseFloatType fpp))
floatIEEEArithUnOpR ctor sym r x =
  let BaseFloatRepr fpp = exprType x in sbMakeExpr sym $ ctor fpp r x
floatIEEEArithCt
  :: (e ~ Expr t)
  => (FloatPrecisionRepr fpp -> App e (BaseFloatType fpp))
  -> ExprBuilder t st fs
  -> FloatPrecisionRepr fpp
  -> IO (e (BaseFloatType fpp))
floatIEEEArithCt ctor sym fpp = sbMakeExpr sym $ ctor fpp
floatIEEELogicBinOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicBinOp ctor sym x y = sbMakeExpr sym $ ctor x y
floatIEEELogicUnOp
  :: (e ~ Expr t)
  => (e (BaseFloatType fpp) -> App e BaseBoolType)
  -> ExprBuilder t st fs
  -> e (BaseFloatType fpp)
  -> IO (e BaseBoolType)
floatIEEELogicUnOp ctor sym x = sbMakeExpr sym $ ctor x


----------------------------------------------------------------------
-- Float interpretations

type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatReal)) fi =
  BaseRealType

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatReal)) where
  iFloatPZero sym _ = return $ realZero sym
  iFloatNZero sym _ = return $ realZero sym
  iFloatNaN = fail "NaN cannot be represented as a real value."
  iFloatPInf = fail "+Infinity cannot be represented as a real value."
  iFloatNInf = fail "-Infinity cannot be represented as a real value."
  iFloatLit sym _ = realLit sym
  iFloatLitSingle sym = realLit sym . toRational
  iFloatLitDouble sym = realLit sym . toRational
  iFloatNeg = realNeg
  iFloatAbs = realAbs
  iFloatSqrt sym _ = realSqrt sym
  iFloatAdd sym _ = realAdd sym
  iFloatSub sym _ = realSub sym
  iFloatMul sym _ = realMul sym
  iFloatDiv sym _ = realDiv sym
  iFloatRem = realMod
  iFloatMin sym x y = do
    c <- realLe sym x y
    realIte sym c x y
  iFloatMax sym x y = do
    c <- realGe sym x y
    realIte sym c x y
  iFloatFMA sym _ x y z = do
    tmp <- (realMul sym x y)
    realAdd sym tmp z
  iFloatEq = realEq
  iFloatNe = realNe
  iFloatFpEq = realEq
  iFloatFpNe = realNe
  iFloatLe = realLe
  iFloatLt = realLt
  iFloatGe = realGe
  iFloatGt = realGt
  iFloatIte = realIte
  iFloatIsNaN sym _ = return $ falsePred sym
  iFloatIsInf sym _ = return $ falsePred sym
  iFloatIsZero sym = realEq sym $ realZero sym
  iFloatIsPos sym = realLt sym $ realZero sym
  iFloatIsNeg sym = realGt sym $ realZero sym
  iFloatIsSubnorm sym _ = return $ falsePred sym
  iFloatIsNorm sym = realNe sym $ realZero sym
  iFloatCast _ _ _ = return
  iFloatRound sym r x =
    integerToReal sym =<< case r of
      RNA -> realRound sym x
      RTP -> realCeil sym x
      RTN -> realFloor sym x
      RTZ -> do
        is_pos <- realLt sym (realZero sym) x
        iteM intIte sym is_pos (realFloor sym x) (realCeil sym x)
      RNE -> fail "Unsupported rond to nearest even for real values."
  iFloatFromBinary sym _ x
    | Just (FnApp fn args) <- asNonceApp x
    , "uninterpreted_real_to_float_binary" == solverSymbolAsText (symFnName fn)
    , UninterpFnInfo param_types (BaseBVRepr _) <- symFnInfo fn
    , (Ctx.Empty Ctx.:> BaseRealRepr) <- param_types
    , (Ctx.Empty Ctx.:> rval) <- args
    = return rval
    | otherwise = mkFreshUninterpFnApp sym
                                       "uninterpreted_real_from_float_binary"
                                       (Ctx.Empty Ctx.:> x)
                                       knownRepr
  iFloatToBinary sym fi x =
    mkFreshUninterpFnApp sym
                         "uninterpreted_real_to_float_binary"
                         (Ctx.Empty Ctx.:> x)
                         (floatInfoToBVTypeRepr fi)
  iBVToFloat sym _ _ = uintToReal sym
  iSBVToFloat sym _ _ = sbvToReal sym
  iRealToFloat _ _ _ = return
  iFloatToBV sym w _ x = realToBV sym x w
  iFloatToSBV sym w _ x = realToSBV sym x w
  iFloatToReal _ = return
  iFloatBaseTypeRepr _ _ = knownRepr

type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatUninterpreted)) fi =
  BaseBVType (FloatInfoToBitWidth fi)

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatUninterpreted)) where
  iFloatPZero sym =
    floatUninterpArithCt "uninterpreted_float_pzero" sym . iFloatBaseTypeRepr sym
  iFloatNZero sym =
    floatUninterpArithCt "uninterpreted_float_nzero" sym . iFloatBaseTypeRepr sym
  iFloatNaN sym =
    floatUninterpArithCt "uninterpreted_float_nan" sym . iFloatBaseTypeRepr sym
  iFloatPInf sym =
    floatUninterpArithCt "uninterpreted_float_pinf" sym . iFloatBaseTypeRepr sym
  iFloatNInf sym =
    floatUninterpArithCt "uninterpreted_float_ninf" sym . iFloatBaseTypeRepr sym
  iFloatLit sym fi x = iRealToFloat sym fi RNE =<< realLit sym x
  iFloatLitSingle sym x =
    iFloatFromBinary sym SingleFloatRepr
      =<< (bvLit sym knownNat $ toInteger $ IEEE754.floatToWord x)
  iFloatLitDouble sym x =
    iFloatFromBinary sym DoubleFloatRepr
      =<< (bvLit sym knownNat $ toInteger $ IEEE754.doubleToWord x)
  iFloatNeg = floatUninterpArithUnOp "uninterpreted_float_neg"
  iFloatAbs = floatUninterpArithUnOp "uninterpreted_float_abs"
  iFloatSqrt = floatUninterpArithUnOpR "uninterpreted_float_sqrt"
  iFloatAdd = floatUninterpArithBinOpR "uninterpreted_float_add"
  iFloatSub = floatUninterpArithBinOpR "uninterpreted_float_sub"
  iFloatMul = floatUninterpArithBinOpR "uninterpreted_float_mul"
  iFloatDiv = floatUninterpArithBinOpR "uninterpreted_float_div"
  iFloatRem = floatUninterpArithBinOp "uninterpreted_float_rem"
  iFloatMin = floatUninterpArithBinOp "uninterpreted_float_min"
  iFloatMax = floatUninterpArithBinOp "uninterpreted_float_max"
  iFloatFMA sym r x y z = do
    let ret_type = exprType x
    r_arg <- roundingModeToSymNat sym r
    mkUninterpFnApp sym
                    "uninterpreted_float_fma"
                    (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y Ctx.:> z)
                    ret_type
  iFloatEq = isEq
  iFloatNe sym x y = notPred sym =<< isEq sym x y
  iFloatFpEq = floatUninterpLogicBinOp "uninterpreted_float_fp_eq"
  iFloatFpNe = floatUninterpLogicBinOp "uninterpreted_float_fp_ne"
  iFloatLe = floatUninterpLogicBinOp "uninterpreted_float_le"
  iFloatLt = floatUninterpLogicBinOp "uninterpreted_float_lt"
  iFloatGe sym x y = floatUninterpLogicBinOp "uninterpreted_float_le" sym y x
  iFloatGt sym x y = floatUninterpLogicBinOp "uninterpreted_float_lt" sym y x
  iFloatIte = baseTypeIte
  iFloatIsNaN = floatUninterpLogicUnOp "uninterpreted_float_is_nan"
  iFloatIsInf = floatUninterpLogicUnOp "uninterpreted_float_is_inf"
  iFloatIsZero = floatUninterpLogicUnOp "uninterpreted_float_is_zero"
  iFloatIsPos = floatUninterpLogicUnOp "uninterpreted_float_is_pos"
  iFloatIsNeg = floatUninterpLogicUnOp "uninterpreted_float_is_neg"
  iFloatIsSubnorm = floatUninterpLogicUnOp "uninterpreted_float_is_subnorm"
  iFloatIsNorm = floatUninterpLogicUnOp "uninterpreted_float_is_norm"
  iFloatCast sym =
    floatUninterpCastOp "uninterpreted_float_cast" sym . iFloatBaseTypeRepr sym
  iFloatRound = floatUninterpArithUnOpR "uninterpreted_float_round"
  iFloatFromBinary _ _ = return
  iFloatToBinary _ _ = return
  iBVToFloat sym =
    floatUninterpCastOp "uninterpreted_bv_to_float" sym . iFloatBaseTypeRepr sym
  iSBVToFloat sym =
    floatUninterpCastOp "uninterpreted_sbv_to_float" sym . iFloatBaseTypeRepr sym
  iRealToFloat sym =
    floatUninterpCastOp "uninterpreted_real_to_float" sym . iFloatBaseTypeRepr sym
  iFloatToBV sym =
    floatUninterpCastOp "uninterpreted_float_to_bv" sym . BaseBVRepr
  iFloatToSBV sym =
    floatUninterpCastOp "uninterpreted_float_to_sbv" sym . BaseBVRepr
  iFloatToReal sym x =
    mkUninterpFnApp sym
                    "uninterpreted_float_to_real"
                    (Ctx.empty Ctx.:> x)
                    knownRepr
  iFloatBaseTypeRepr _ = floatInfoToBVTypeRepr

floatUninterpArithBinOp
  :: (e ~ Expr t) => String -> ExprBuilder t st fs -> e bt -> e bt -> IO (e bt)
floatUninterpArithBinOp fn sym x y =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) ret_type

floatUninterpArithBinOpR
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e bt
  -> e bt
  -> IO (e bt)
floatUninterpArithBinOpR fn sym r x y = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x Ctx.:> y) ret_type

floatUninterpArithUnOp
  :: (e ~ Expr t) => String -> ExprBuilder t st fs -> e bt -> IO (e bt)
floatUninterpArithUnOp fn sym x =
  let ret_type = exprType x
  in  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) ret_type
floatUninterpArithUnOpR
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> RoundingMode
  -> e bt
  -> IO (e bt)
floatUninterpArithUnOpR fn sym r x = do
  let ret_type = exprType x
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

floatUninterpArithCt
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> BaseTypeRepr bt
  -> IO (e bt)
floatUninterpArithCt fn sym ret_type =
  mkUninterpFnApp sym fn Ctx.empty ret_type

floatUninterpLogicBinOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> e bt
  -> e bt
  -> IO (e BaseBoolType)
floatUninterpLogicBinOp fn sym x y =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x Ctx.:> y) knownRepr

floatUninterpLogicUnOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> e bt
  -> IO (e BaseBoolType)
floatUninterpLogicUnOp fn sym x =
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> x) knownRepr

floatUninterpCastOp
  :: (e ~ Expr t)
  => String
  -> ExprBuilder t st fs
  -> BaseTypeRepr bt
  -> RoundingMode
  -> e bt'
  -> IO (e bt)
floatUninterpCastOp fn sym ret_type r x = do
  r_arg <- roundingModeToSymNat sym r
  mkUninterpFnApp sym fn (Ctx.empty Ctx.:> r_arg Ctx.:> x) ret_type

roundingModeToSymNat
  :: (sym ~ ExprBuilder t st fs) => sym -> RoundingMode -> IO (SymNat sym)
roundingModeToSymNat sym = natLit sym . fromIntegral . fromEnum


type instance SymInterpretedFloatType (ExprBuilder t st (Flags FloatIEEE)) fi =
  BaseFloatType (FloatInfoToPrecision fi)

instance IsInterpretedFloatExprBuilder (ExprBuilder t st (Flags FloatIEEE)) where
  iFloatPZero sym = floatPZero sym . floatInfoToPrecisionRepr
  iFloatNZero sym = floatNZero sym . floatInfoToPrecisionRepr
  iFloatNaN sym = floatNaN sym . floatInfoToPrecisionRepr
  iFloatPInf sym = floatPInf sym . floatInfoToPrecisionRepr
  iFloatNInf sym = floatNInf sym . floatInfoToPrecisionRepr
  iFloatLit sym = floatLit sym . floatInfoToPrecisionRepr
  iFloatLitSingle sym x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ toInteger $ IEEE754.floatToWord x)
  iFloatLitDouble sym x =
    floatFromBinary sym knownRepr
      =<< (bvLit sym knownNat $ toInteger $ IEEE754.doubleToWord x)
  iFloatNeg = floatNeg
  iFloatAbs = floatAbs
  iFloatSqrt = floatSqrt
  iFloatAdd = floatAdd
  iFloatSub = floatSub
  iFloatMul = floatMul
  iFloatDiv = floatDiv
  iFloatRem = floatRem
  iFloatMin = floatMin
  iFloatMax = floatMax
  iFloatFMA = floatFMA
  iFloatEq = floatEq
  iFloatNe = floatNe
  iFloatFpEq = floatFpEq
  iFloatFpNe = floatFpNe
  iFloatLe = floatLe
  iFloatLt = floatLt
  iFloatGe = floatGe
  iFloatGt = floatGt
  iFloatIte = floatIte
  iFloatIsNaN = floatIsNaN
  iFloatIsInf = floatIsInf
  iFloatIsZero = floatIsZero
  iFloatIsPos = floatIsPos
  iFloatIsNeg = floatIsNeg
  iFloatIsSubnorm = floatIsSubnorm
  iFloatIsNorm = floatIsNorm
  iFloatCast sym = floatCast sym . floatInfoToPrecisionRepr
  iFloatRound = floatRound
  iFloatFromBinary sym fi x = case fi of
    HalfFloatRepr         -> floatFromBinary sym knownRepr x
    SingleFloatRepr       -> floatFromBinary sym knownRepr x
    DoubleFloatRepr       -> floatFromBinary sym knownRepr x
    QuadFloatRepr         -> floatFromBinary sym knownRepr x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iFloatToBinary sym fi x = case fi of
    HalfFloatRepr         -> floatToBinary sym x
    SingleFloatRepr       -> floatToBinary sym x
    DoubleFloatRepr       -> floatToBinary sym x
    QuadFloatRepr         -> floatToBinary sym x
    X86_80FloatRepr       -> fail "x86_80 is not an IEEE-754 format."
    DoubleDoubleFloatRepr -> fail "double-double is not an IEEE-754 format."
  iBVToFloat sym = bvToFloat sym . floatInfoToPrecisionRepr
  iSBVToFloat sym = sbvToFloat sym . floatInfoToPrecisionRepr
  iRealToFloat sym = realToFloat sym . floatInfoToPrecisionRepr
  iFloatToBV = floatToBV
  iFloatToSBV = floatToSBV
  iFloatToReal = floatToReal
  iFloatBaseTypeRepr _ = BaseFloatRepr . floatInfoToPrecisionRepr


instance IsSymExprBuilder (ExprBuilder t st fs) where
  freshConstant sym nm tp = do
    v <- sbMakeBoundVar sym nm tp UninterpVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  freshBoundedBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedBV sym nm w mlo mhi =
    do v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   lo = maybe (minUnsigned w) toInteger mlo
   hi = maybe (maxUnsigned w) toInteger mhi

  freshBoundedSBV sym nm w Nothing Nothing = freshConstant sym nm (BaseBVRepr w)
  freshBoundedSBV sym nm w mlo mhi =
    do v <- sbMakeBoundVar sym nm (BaseBVRepr w) UninterpVarKind (Just $! (BVD.range w lo hi))
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   lo = fromMaybe (minSigned w) mlo
   hi = fromMaybe (maxSigned w) mhi

  freshBoundedInt sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseIntegerRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! MultiRange (Inclusive lo) Unbounded
   absVal Nothing (Just hi) = Just $! MultiRange Unbounded (Inclusive hi)
   absVal (Just lo) (Just hi) = Just $! MultiRange (Inclusive lo) (Inclusive hi)

  freshBoundedReal sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseRealRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! RAV (MultiRange (Inclusive lo) Unbounded) Nothing
   absVal Nothing (Just hi) = Just $! RAV (MultiRange Unbounded (Inclusive hi)) Nothing
   absVal (Just lo) (Just hi) = Just $! RAV (MultiRange (Inclusive lo) (Inclusive hi)) Nothing

  freshBoundedNat sym nm mlo mhi =
    do v <- sbMakeBoundVar sym nm BaseNatRepr UninterpVarKind (absVal mlo mhi)
       updateVarBinding sym nm (VarSymbolBinding v)
       return $! BoundVarExpr v
   where
   absVal Nothing Nothing = Nothing
   absVal (Just lo) Nothing = Just $! natRange lo Unbounded
   absVal Nothing (Just hi) = Just $! natRange 0 (Inclusive hi)
   absVal (Just lo) (Just hi) = Just $! natRange lo (Inclusive hi)

  freshLatch sym nm tp = do
    v <- sbMakeBoundVar sym nm tp LatchVarKind Nothing
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarExpr v

  freshBoundVar sym nm tp =
    sbMakeBoundVar sym nm tp QuantifierVarKind Nothing

  varExpr _ = BoundVarExpr

  forallPred sym bv e = sbNonceExpr sym $ Forall bv e

  existsPred sym bv e = sbNonceExpr sym $ Exists bv e

  ----------------------------------------------------------------------
  -- SymFn operations.

  -- | Create a function defined in terms of previous functions.
  definedFn sym fn_name bound_vars result evalFn0 = do
    l <- curProgramLoc sym
    n <- sbFreshSymFnNonce sym
    let evalFn
          | Just TrueBool  <- asApp result = (\_ -> True)
          | Just FalseBool <- asApp result = (\_ -> True)
          | otherwise = evalFn0
    let fn = ExprSymFn { symFnId   = n
                         , symFnName = fn_name
                         , symFnInfo = DefinedFnInfo bound_vars result evalFn
                         , symFnLoc  = l
                         }
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  freshTotalUninterpFn sym fn_name arg_types ret_type = do
    n <- sbFreshSymFnNonce sym
    l <- curProgramLoc sym
    let fn = ExprSymFn { symFnId = n
                         , symFnName = fn_name
                         , symFnInfo = UninterpFnInfo arg_types ret_type
                         , symFnLoc = l
                         }
    seq fn $ do
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  applySymFn sym fn args = do
   case symFnInfo fn of
     DefinedFnInfo bound_vars e shouldEval
       | shouldEval args -> do
           evalBoundVars sym e bound_vars args
     MatlabSolverFnInfo f _ _ -> do
       evalMatlabSolverFn f sym args
     _ -> sbNonceExpr sym $! FnApp fn args


instance IsInterpretedFloatExprBuilder (ExprBuilder t st fs) => IsInterpretedFloatSymExprBuilder (ExprBuilder t st fs)


--------------------------------------------------------------------------------
-- MatlabSymbolicArrayBuilder instance

instance MatlabSymbolicArrayBuilder (ExprBuilder t st fs) where
  mkMatlabSolverFn sym fn_id = do
    let key = MatlabFnWrapper fn_id
    mr <- stToIO $ PH.lookup (sbMatlabFnCache sym) key
    case mr of
      Just (ExprSymFnWrapper f) -> return f
      Nothing -> do
        let tps = matlabSolverArgTypes fn_id
        vars <- traverseFC (freshBoundVar sym emptySymbol) tps
        r <- evalMatlabSolverFn fn_id sym (fmapFC BoundVarExpr vars)
--        f <- definedFn sym emptySymbol vars r (\_ -> True)

        l <- curProgramLoc sym
        n <- sbFreshSymFnNonce sym
        let f = ExprSymFn { symFnId   = n
                            , symFnName = emptySymbol
                            , symFnInfo = MatlabSolverFnInfo fn_id vars r
                            , symFnLoc  = l
                            }
        updateVarBinding sym emptySymbol (FnSymbolBinding f)
        stToIO $ PH.insert (sbMatlabFnCache sym) key (ExprSymFnWrapper f)
        return f

unsafeUserSymbol :: String -> IO SolverSymbol
unsafeUserSymbol s =
  case userSymbol s of
    Left err -> fail (show err)
    Right symbol  -> return symbol

cachedUninterpFn
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> SolverSymbol
  -> Ctx.Assignment BaseTypeRepr args
  -> BaseTypeRepr ret
  -> (  sym
     -> SolverSymbol
     -> Ctx.Assignment BaseTypeRepr args
     -> BaseTypeRepr ret
     -> IO (SymFn sym args ret)
     )
  -> IO (SymFn sym args ret)
cachedUninterpFn sym fn_name arg_types ret_type handler = do
  fn_cache <- readIORef $ sbUninterpFnCache sym
  case Map.lookup fn_key fn_cache of
    Just (SomeSymFn fn)
      | Just Refl <- testEquality (fnArgTypes fn) arg_types
      , Just Refl <- testEquality (fnReturnType fn) ret_type
      -> return fn
      | otherwise
      -> fail "Duplicate uninterpreted function declaration."
    Nothing -> do
      fn <- handler sym fn_name arg_types ret_type
      modifyIORef' (sbUninterpFnCache sym) (Map.insert fn_key (SomeSymFn fn))
      return fn
  where fn_key =  (fn_name, Some (arg_types Ctx.:> ret_type))

mkUninterpFnApp
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> String
  -> Ctx.Assignment (SymExpr sym) args
  -> BaseTypeRepr ret
  -> IO (SymExpr sym ret)
mkUninterpFnApp sym str_fn_name args ret_type = do
  fn_name <- unsafeUserSymbol str_fn_name
  let arg_types = fmapFC exprType args
  fn <- cachedUninterpFn sym fn_name arg_types ret_type freshTotalUninterpFn
  applySymFn sym fn args

mkFreshUninterpFnApp
  :: (sym ~ ExprBuilder t st fs)
  => sym
  -> String
  -> Ctx.Assignment (SymExpr sym) args
  -> BaseTypeRepr ret
  -> IO (SymExpr sym ret)
mkFreshUninterpFnApp sym str_fn_name args ret_type = do
  fn_name <- unsafeUserSymbol str_fn_name
  let arg_types = fmapFC exprType args
  fn <- freshTotalUninterpFn sym fn_name arg_types ret_type
  applySymFn sym fn args
