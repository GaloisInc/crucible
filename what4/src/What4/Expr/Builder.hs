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
  , bvSum
  , scalarMul

    -- * configuration options
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
  , exprMaybeId
  , asConjunction
  , asDisjunction
  , Polarity(..)
  , BM.negatePolarity
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
  , type FloatMode
  , FloatModeRepr(..)
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  , Flags

    -- * BV Or Set
  , BVOrSet
  , bvOrToList
  , bvOrSingleton
  , bvOrInsert
  , bvOrUnion
  , bvOrAbs
  , traverseBVOrSet

    -- * Re-exports
  , SymExpr
  , What4.Interface.bvWidth
  , What4.Interface.exprType
  , What4.Interface.IndexLit(..)
  , What4.Interface.ArrayResultWrapper(..)
  ) where

import qualified Control.Exception as Ex
import           Control.Lens hiding (asIndex, (:>), Empty)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.Trans.Writer.Strict (writer, runWriter)
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
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid (Any(..))
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
import qualified What4.SemiRing as SR
import           What4.Symbol
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.Expr.BoolMap (BoolMap, Polarity(..), BoolMapView(..), Wrap(..))
import qualified What4.Expr.BoolMap as BM
import           What4.Expr.MATLAB
import           What4.Expr.WeightedSum (WeightedSum, SemiRingProduct)
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.StringSeq as SSeq
import           What4.Expr.UnaryBV (UnaryBV)
import qualified What4.Expr.UnaryBV as UnaryBV

import           What4.Utils.AbstractDomains
import           What4.Utils.Arithmetic
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex
import           What4.Utils.StringLiteral
import           What4.Utils.IncrHash
import qualified What4.Utils.AnnotatedMap as AM

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
  Annotation::
    !(BaseTypeRepr tp) ->
    !(Nonce t tp) ->
    !(e tp) ->
    NonceApp t e tp

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


-------------------------------------------------------------------------------
-- BVOrSet

data BVOrNote w = BVOrNote !IncrHash !(BVD.BVDomain w)

instance Semigroup (BVOrNote w) where
  BVOrNote xh xa <> BVOrNote yh ya = BVOrNote (xh <> yh) (BVD.or xa ya)

newtype BVOrSet e w = BVOrSet (AM.AnnotatedMap (Wrap e (BaseBVType w)) (BVOrNote w) ())

traverseBVOrSet :: (HashableF f, HasAbsValue f, OrdF f, Applicative m) =>
  (forall tp. e tp -> m (f tp)) ->
  (BVOrSet e w -> m (BVOrSet f w))
traverseBVOrSet f (BVOrSet m) =
  foldr bvOrInsert (BVOrSet AM.empty) <$> traverse (f . unWrap . fst) (AM.toList m)

bvOrInsert :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w -> BVOrSet e w
bvOrInsert e (BVOrSet m) = BVOrSet $ AM.insert (Wrap e) (BVOrNote (mkIncrHash (hashF e)) (getAbsValue e)) () m

bvOrSingleton :: (OrdF e, HashableF e, HasAbsValue e) => e (BaseBVType w) -> BVOrSet e w
bvOrSingleton e = bvOrInsert e (BVOrSet AM.empty)

bvOrContains :: OrdF e => e (BaseBVType w) -> BVOrSet e w -> Bool
bvOrContains x (BVOrSet m) = isJust $ AM.lookup (Wrap x) m

bvOrUnion :: OrdF e => BVOrSet e w -> BVOrSet e w -> BVOrSet e w
bvOrUnion (BVOrSet x) (BVOrSet y) = BVOrSet (AM.union x y)

bvOrToList :: BVOrSet e w -> [e (BaseBVType w)]
bvOrToList (BVOrSet m) = unWrap . fst <$> AM.toList m

bvOrAbs :: (OrdF e, 1 <= w) => NatRepr w -> BVOrSet e w -> BVD.BVDomain w
bvOrAbs w (BVOrSet m) =
  case AM.annotation m of
    Just (BVOrNote _ a) -> a
    Nothing -> BVD.singleton w 0

instance (OrdF e, TestEquality e) => Eq (BVOrSet e w) where
  BVOrSet x == BVOrSet y = AM.eqBy (\_ _ -> True) x y

instance OrdF e => Hashable (BVOrSet e w) where
  hashWithSalt s (BVOrSet m) =
    case AM.annotation m of
      Just (BVOrNote h _) -> hashWithSalt s h
      Nothing -> s

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
  -- Generic operations

  BaseIte ::
    !(BaseTypeRepr tp) ->
    !Integer {- Total number of predicates in this ite tree -} ->
    !(e BaseBoolType) ->
    !(e tp) ->
    !(e tp) ->
    App e tp

  BaseEq ::
    !(BaseTypeRepr tp) ->
    !(e tp) ->
    !(e tp) ->
    App e BaseBoolType

  ------------------------------------------------------------------------
  -- Boolean operations

  -- Invariant: The argument to a NotPred must not be another NotPred.
  NotPred :: !(e BaseBoolType) -> App e BaseBoolType

  -- Invariant: The BoolMap must contain at least two elements. No
  -- element may be a NotPred; negated elements must be represented
  -- with Negative element polarity.
  ConjPred :: !(BoolMap e) -> App e BaseBoolType

  ------------------------------------------------------------------------
  -- Semiring operations

  SemiRingSum ::
    {-# UNPACK #-} !(WeightedSum e sr) ->
    App e (SR.SemiRingBase sr)

  -- A product of semiring values
  --
  -- The ExprBuilder should maintain the invariant that none of the values is
  -- a constant, and hence this denotes a non-linear expression.
  -- Multiplications by scalars should use the 'SemiRingSum' constructor.
  SemiRingProd ::
     {-# UNPACK #-} !(SemiRingProduct e sr) ->
     App e (SR.SemiRingBase sr)

  SemiRingLe
     :: !(SR.OrderedSemiRingRepr sr)
     -> !(e (SR.SemiRingBase sr))
     -> !(e (SR.SemiRingBase sr))
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

  -- Return value of bit at given index.
  BVTestBit :: (1 <= w)
            => !Natural -- Index of bit to test
                        -- (least-significant bit has index 0)
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

  BVOrBits :: (1 <= w) => !(NatRepr w) -> !(BVOrSet e w) -> App e (BaseBVType w)

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

  BVFill :: (1 <= w)
         => !(NatRepr w)
         -> !(e BaseBoolType)
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

  BVRol :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w)) -- bitvector to rotate
        -> !(e (BaseBVType w)) -- rotate amount
        -> App e (BaseBVType w)

  BVRor :: (1 <= w)
        => !(NatRepr w)
        -> !(e (BaseBVType w))   -- bitvector to rotate
        -> !(e (BaseBVType w))   -- rotate amount
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

  -- Partial map from concrete indices to array values over another array.
  ArrayMap :: !(Ctx.Assignment BaseTypeRepr (i ::> itp))
           -> !(BaseTypeRepr tp)
                -- /\ The type of the array.
           -> !(AUM.ArrayUpdateMap e (i ::> itp) tp)
              -- /\ Maps indices that are updated to the associated value.
           -> !(e (BaseArrayType (i::> itp) tp))
              -- /\ The underlying array that has been updated.
           -> App e (BaseArrayType (i ::> itp) tp)

  -- Constant array
  ConstantArray :: !(Ctx.Assignment BaseTypeRepr (i ::> tp))
                -> !(BaseTypeRepr b)
                -> !(e b)
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
  -- Strings

  StringContains :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsPrefixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIsSuffixOf :: !(e (BaseStringType si))
                 -> !(e (BaseStringType si))
                 -> App e BaseBoolType

  StringIndexOf :: !(e (BaseStringType si))
                -> !(e (BaseStringType si))
                -> !(e BaseNatType)
                -> App e BaseIntegerType

  StringSubstring :: !(StringInfoRepr si)
                  -> !(e (BaseStringType si))
                  -> !(e BaseNatType)
                  -> !(e BaseNatType)
                  -> App e (BaseStringType si)

  StringAppend :: !(StringInfoRepr si)
               -> !(SSeq.StringSeq e si)
               -> App e (BaseStringType si)

  StringLength :: !(e (BaseStringType si))
               -> App e BaseNatType

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

-- | The main ExprBuilder expression datastructure.  The non-trivial @Expr@
-- values constructed by this module are uniquely identified by a
-- nonce value that is used to explicitly represent sub-term sharing.
-- When traversing the structure of an @Expr@ it is usually very important
-- to memoize computations based on the values of these identifiers to avoid
-- exponential blowups due to shared term structure.
--
-- Type parameter @t@ is a phantom type brand used to relate nonces to
-- a specific nonce generator (similar to the @s@ parameter of the
-- @ST@ monad). The type index @tp@ of kind 'BaseType' indicates the
-- type of the values denoted by the given expression.
--
-- Type @'Expr' t@ instantiates the type family @'SymExpr'
-- ('ExprBuilder' t st)@.
data Expr t (tp :: BaseType) where
  SemiRingLiteral :: !(SR.SemiRingRepr sr) -> !(SR.Coefficient sr) -> !ProgramLoc -> Expr t (SR.SemiRingBase sr)
  BoolExpr :: !Bool -> !ProgramLoc -> Expr t BaseBoolType
  StringExpr :: !(StringLiteral si) -> !ProgramLoc -> Expr t (BaseStringType si)
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
exprLoc (BoolExpr _ l) = l
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
type StringExpr t si = Expr t (BaseStringType si)



iteSize :: Expr t tp -> Integer
iteSize e =
  case asApp e of
    Just (BaseIte _ sz _ _ _) -> sz
    _ -> 0

instance IsExpr (Expr t) where
  asConstantPred (BoolExpr b _) = Just b
  asConstantPred _ = Nothing

  asNat (SemiRingLiteral SR.SemiRingNatRepr n _) = Just n
  asNat _ = Nothing

  natBounds x = exprAbsValue x

  asInteger (SemiRingLiteral SR.SemiRingIntegerRepr n _) = Just n
  asInteger _ = Nothing

  integerBounds x = exprAbsValue x

  asRational (SemiRingLiteral SR.SemiRingRealRepr r _) = Just r
  asRational _ = Nothing

  rationalBounds x = ravRange $ exprAbsValue x

  asComplex e
    | Just (Cplx c) <- asApp e = traverse asRational c
    | otherwise = Nothing

  exprType (SemiRingLiteral sr _ _) = SR.semiRingBase sr
  exprType (BoolExpr _ _) = BaseBoolRepr
  exprType (StringExpr s _) = BaseStringRepr (stringLiteralInfo s)
  exprType (NonceAppExpr e)  = nonceAppType (nonceExprApp e)
  exprType (AppExpr e) = appType (appExprApp e)
  exprType (BoundVarExpr i) = bvarType i

  asUnsignedBV (SemiRingLiteral (SR.SemiRingBVRepr _ _) i _) = Just i
  asUnsignedBV _ = Nothing

  asSignedBV x = toSigned (bvWidth x) <$> asUnsignedBV x

  unsignedBVBounds x = Just $ BVD.ubounds $ exprAbsValue x
  signedBVBounds x = Just $ BVD.sbounds (bvWidth x) $ exprAbsValue x

  asAffineVar e = case exprType e of
    BaseNatRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingNatRepr e ->
        Just (ConcreteNat a, x, ConcreteNat b)
    BaseIntegerRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingIntegerRepr e ->
        Just (ConcreteInteger a, x, ConcreteInteger b)
    BaseRealRepr
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum SR.SemiRingRealRepr e ->
        Just (ConcreteReal a, x, ConcreteReal b)
    BaseBVRepr w
      | Just (a, x, b) <- WSum.asAffineVar $
          asWeightedSum (SR.SemiRingBVRepr SR.BVArithRepr (bvWidth e)) e ->
        Just (ConcreteBV w a, x, ConcreteBV w b)
    _ -> Nothing

  asString (StringExpr x _) = Just x
  asString _ = Nothing

  asConstantArray (asApp -> Just (ConstantArray _ _ def)) = Just def
  asConstantArray _ = Nothing

  asStruct (asApp -> Just (StructCtor _ flds)) = Just flds
  asStruct _ = Nothing

  printSymExpr = pretty


asSemiRingLit :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SR.Coefficient sr)
asSemiRingLit sr (SemiRingLiteral sr' x _loc)
  | Just Refl <- testEquality sr sr'
  = Just x

  -- special case, ignore the BV ring flavor for this purpose
  | SR.SemiRingBVRepr _ w  <- sr
  , SR.SemiRingBVRepr _ w' <- sr'
  , Just Refl <- testEquality w w'
  = Just x

asSemiRingLit _ _ = Nothing

asSemiRingSum :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (WeightedSum (Expr t) sr)
asSemiRingSum sr (asSemiRingLit sr -> Just x) = Just (WSum.constant sr x)
asSemiRingSum sr (asApp -> Just (SemiRingSum x))
   | Just Refl <- testEquality sr (WSum.sumRepr x) = Just x
asSemiRingSum _ _ = Nothing

asSemiRingProd :: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> Maybe (SemiRingProduct (Expr t) sr)
asSemiRingProd sr (asApp -> Just (SemiRingProd x))
  | Just Refl <- testEquality sr (WSum.prodRepr x) = Just x
asSemiRingProd _ _ = Nothing

-- | This privides a view of a semiring expr as a weighted sum of values.
data SemiRingView t sr
   = SR_Constant !(SR.Coefficient sr)
   | SR_Sum  !(WeightedSum (Expr t) sr)
   | SR_Prod !(SemiRingProduct (Expr t) sr)
   | SR_General

viewSemiRing:: SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> SemiRingView t sr
viewSemiRing sr x
  | Just r <- asSemiRingLit sr x  = SR_Constant r
  | Just s <- asSemiRingSum sr x  = SR_Sum s
  | Just p <- asSemiRingProd sr x = SR_Prod p
  | otherwise = SR_General

asWeightedSum :: HashableF (Expr t) => SR.SemiRingRepr sr -> Expr t (SR.SemiRingBase sr) -> WeightedSum (Expr t) sr
asWeightedSum sr x
  | Just r <- asSemiRingLit sr x = WSum.constant sr r
  | Just s <- asSemiRingSum sr x = s
  | otherwise = WSum.var sr x

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

asConjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asConjunction (BoolExpr True _) = []
asConjunction (asApp -> Just (ConjPred xs)) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr False initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> tm:tms
asConjunction x = [(x,Positive)]


asDisjunction :: Expr t BaseBoolType -> [(Expr t BaseBoolType, Polarity)]
asDisjunction (BoolExpr False _) = []
asDisjunction (asApp -> Just (NotPred (asApp -> Just (ConjPred xs)))) =
 case BM.viewBoolMap xs of
   BoolMapUnit     -> []
   BoolMapDualUnit -> [(BoolExpr True initializationLoc, Positive)]
   BoolMapTerms (tm:|tms) -> map (over _2 BM.negatePolarity) (tm:tms)
asDisjunction x = [(x,Positive)]

asPosAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asPosAtom (asApp -> Just (NotPred x)) = (x, Negative)
asPosAtom x                           = (x, Positive)

asNegAtom :: Expr t BaseBoolType -> (Expr t BaseBoolType, Polarity)
asNegAtom (asApp -> Just (NotPred x)) = (x, Positive)
asNegAtom x                           = (x, Negative)

------------------------------------------------------------------------
-- Types

nonceAppType :: NonceApp t e tp -> BaseTypeRepr tp
nonceAppType a =
  case a of
    Annotation tpr _ _ -> tpr
    Forall{} -> knownRepr
    Exists{} -> knownRepr
    ArrayFromFn   fn       -> BaseArrayRepr (symFnArgTypes fn) (symFnReturnType fn)
    MapOverArrays fn idx _ -> BaseArrayRepr idx (symFnReturnType fn)
    ArrayTrueOnEntries _ _ -> knownRepr
    FnApp f _ ->  symFnReturnType f

appType :: App e tp -> BaseTypeRepr tp
appType a =
  case a of
    BaseIte tp _ _ _ _ -> tp
    BaseEq{} -> knownRepr

    NotPred{} -> knownRepr
    ConjPred{} -> knownRepr

    RealIsInteger{} -> knownRepr
    BVTestBit{} -> knownRepr
    BVSlt{}   -> knownRepr
    BVUlt{}   -> knownRepr

    NatDiv{} -> knownRepr
    NatMod{} -> knownRepr

    IntDiv{} -> knownRepr
    IntMod{} -> knownRepr
    IntAbs{} -> knownRepr
    IntDivisible{} -> knownRepr

    SemiRingLe{} -> knownRepr
    SemiRingProd pd -> SR.semiRingBase (WSum.prodRepr pd)
    SemiRingSum s -> SR.semiRingBase (WSum.sumRepr s)

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
    BVOrBits w _ -> BaseBVRepr w
    BVConcat w _ _ -> BaseBVRepr w
    BVSelect _ n _ -> BaseBVRepr n
    BVUdiv w _ _ -> BaseBVRepr w
    BVUrem w _ _ -> BaseBVRepr w
    BVSdiv w _ _ -> BaseBVRepr w
    BVSrem w _ _ -> BaseBVRepr w
    BVShl  w _ _  -> BaseBVRepr w
    BVLshr w _ _ -> BaseBVRepr w
    BVAshr w _ _ -> BaseBVRepr w
    BVRol w _ _ -> BaseBVRepr w
    BVRor w _ _ -> BaseBVRepr w
    BVPopcount w _ -> BaseBVRepr w
    BVCountLeadingZeros w _ -> BaseBVRepr w
    BVCountTrailingZeros w _ -> BaseBVRepr w
    BVZext  w _ -> BaseBVRepr w
    BVSext  w _ -> BaseBVRepr w
    BVFill w _ -> BaseBVRepr w

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
    SelectArray b _ _       -> b
    UpdateArray b itp _ _ _     -> BaseArrayRepr itp b

    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    BVToNat{} -> knownRepr
    BVToInteger{} -> knownRepr
    SBVToInteger{} -> knownRepr

    IntegerToNat{} -> knownRepr
    IntegerToBV _ w -> BaseBVRepr w

    RealToInteger{} -> knownRepr

    Cplx{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    StringContains{} -> knownRepr
    StringIsPrefixOf{} -> knownRepr
    StringIsSuffixOf{} -> knownRepr
    StringIndexOf{} -> knownRepr
    StringSubstring si _ _ _ -> BaseStringRepr si
    StringAppend si _ -> BaseStringRepr si
    StringLength{} -> knownRepr

    StructCtor flds _     -> BaseStructRepr flds
    StructField _ _ tp    -> tp

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

-- | Mode flag for how floating-point values should be interpreted.
data FloatMode where
  FloatIEEE :: FloatMode
  FloatUninterpreted :: FloatMode
  FloatReal :: FloatMode
type FloatIEEE = 'FloatIEEE
type FloatUninterpreted = 'FloatUninterpreted
type FloatReal = 'FloatReal

data Flags (fi :: FloatMode)


data FloatModeRepr :: FloatMode -> Type where
  FloatIEEERepr          :: FloatModeRepr FloatIEEE
  FloatUninterpretedRepr :: FloatModeRepr FloatUninterpreted
  FloatRealRepr          :: FloatModeRepr FloatReal

instance Show (FloatModeRepr fm) where
  showsPrec _ FloatIEEERepr          = showString "FloatIEEE"
  showsPrec _ FloatUninterpretedRepr = showString "FloatUninterpreted"
  showsPrec _ FloatRealRepr          = showString "FloatReal"

instance ShowF FloatModeRepr

instance KnownRepr FloatModeRepr FloatIEEE          where knownRepr = FloatIEEERepr
instance KnownRepr FloatModeRepr FloatUninterpreted where knownRepr = FloatUninterpretedRepr
instance KnownRepr FloatModeRepr FloatReal          where knownRepr = FloatRealRepr

instance TestEquality FloatModeRepr where
  testEquality FloatIEEERepr           FloatIEEERepr           = return Refl
  testEquality FloatUninterpretedRepr  FloatUninterpretedRepr  = return Refl
  testEquality FloatRealRepr           FloatRealRepr           = return Refl
  testEquality _ _ = Nothing


-- | Cache for storing dag terms.
-- Parameter @t@ is a phantom type brand used to track nonces.
data ExprBuilder t (st :: Type -> Type) (fs :: Type)
   = forall fm. (fs ~ (Flags fm)) =>
     SB { sbTrue  :: !(BoolExpr t)
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
          -- | Flag dictating how floating-point values/operations are translated
          -- when passed to the solver.
        , sbFloatMode :: !(FloatModeRepr fm)
        }

type instance SymFn (ExprBuilder t st fs) = ExprSymFn t
type instance SymExpr (ExprBuilder t st fs) = Expr t
type instance BoundVar (ExprBuilder t st fs) = ExprBoundVar t
type instance SymAnnotation (ExprBuilder t st fs) = Nonce t

------------------------------------------------------------------------
-- abstractEval

-- | Return abstract domain associated with a nonce app
quantAbsEval :: ExprBuilder t st fs
             -> (forall u . Expr t u -> AbstractValue u)
             -> NonceApp t (Expr t) tp
             -> AbstractValue tp
quantAbsEval _ f q =
  case q of
    Annotation _ _ v -> f v
    Forall _ v -> f v
    Exists _ v -> f v
    ArrayFromFn _       -> unconstrainedAbsValue (nonceAppType q)
    MapOverArrays g _ _ -> unconstrainedAbsValue tp
      where tp = symFnReturnType g
    ArrayTrueOnEntries _ a -> f a
    FnApp g _           -> unconstrainedAbsValue (symFnReturnType g)

abstractEval :: (forall u . Expr t u -> AbstractValue u)
             -> App (Expr t) tp
             -> AbstractValue tp
abstractEval f a0 = do
  case a0 of

    BaseIte tp _ _c x y -> withAbstractable tp $ avJoin tp (f x) (f y)
    BaseEq{} -> Nothing

    NotPred{} -> Nothing
    ConjPred{} -> Nothing

    SemiRingLe{} -> Nothing
    RealIsInteger{} -> Nothing
    BVTestBit{} -> Nothing
    BVSlt{} -> Nothing
    BVUlt{} -> Nothing

    ------------------------------------------------------------------------
    -- Arithmetic operations

    NatDiv x y -> natRangeDiv (f x) (f y)
    NatMod x y -> natRangeMod (f x) (f y)

    IntAbs x -> intAbsRange (f x)
    IntDiv x y -> intDivRange (f x) (f y)
    IntMod x y -> intModRange (f x) (f y)

    IntDivisible{} -> Nothing

    SemiRingSum s -> WSum.sumAbsValue s
    SemiRingProd pd -> WSum.prodAbsValue pd

    BVOrBits w m -> bvOrAbs w m

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

    BVUnaryTerm u -> UnaryBV.domain asConstantPred u
    BVConcat _ x y -> BVD.concat (bvWidth x) (f x) (bvWidth y) (f y)

    BVSelect i n x -> BVD.select i n (f x)
    BVUdiv _ x y -> BVD.udiv (f x) (f y)
    BVUrem _ x y -> BVD.urem (f x) (f y)
    BVSdiv w x y -> BVD.sdiv w (f x) (f y)
    BVSrem w x y -> BVD.srem w (f x) (f y)

    BVShl  _ x y -> BVD.shl (f x) (f y)
    BVLshr _ x y -> BVD.lshr (f x) (f y)
    BVAshr w x y -> BVD.ashr w (f x) (f y)
    BVRol  w _ _ -> BVD.any w -- TODO?
    BVRor  w _ _ -> BVD.any w -- TODO?
    BVZext w x   -> BVD.zext (f x) w
    BVSext w x   -> BVD.sext (bvWidth x) (f x) w
    BVFill w _   -> BVD.range w (-1) 0

    -- TODO: pretty sure we can do better for popcount, ctz and clz
    BVPopcount w _ -> BVD.range w 0 (intValue w)
    BVCountLeadingZeros w _ -> BVD.range w 0 (intValue w)
    BVCountTrailingZeros w _ -> BVD.range w 0 (intValue w)

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
    FloatCast{} -> ()
    FloatRound{} -> ()
    FloatFromBinary{} -> ()
    FloatToBinary fpp _ -> case floatPrecisionToBVType fpp of
      BaseBVRepr w -> BVD.any w
    BVToFloat{} -> ()
    SBVToFloat{} -> ()
    RealToFloat{} -> ()
    FloatToBV w _ _ -> BVD.any w
    FloatToSBV w _ _ -> BVD.any w
    FloatToReal{} -> ravUnbounded

    ArrayMap _ bRepr m d ->
      withAbstractable bRepr $
      case AUM.arrayUpdateAbs m of
        Nothing -> f d
        Just a -> avJoin bRepr (f d) a
    ConstantArray _idxRepr _bRepr v -> f v

    SelectArray _bRepr a _i -> f a  -- FIXME?
    UpdateArray bRepr _ a _i v -> withAbstractable bRepr $ avJoin bRepr (f a) (f v)

    NatToInteger x -> natRangeToRange (f x)
    IntegerToReal x -> RAV (mapRange toRational (f x)) (Just True)
    BVToNat x -> natRange (fromInteger lx) (Inclusive (fromInteger ux))
      where (lx, ux) = BVD.ubounds (f x)
    BVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.ubounds (f x)
    SBVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where (lx, ux) = BVD.sbounds (bvWidth x) (f x)
    RoundReal x -> mapRange roundAway (ravRange (f x))
    FloorReal x -> mapRange floor (ravRange (f x))
    CeilReal x  -> mapRange ceiling (ravRange (f x))
    IntegerToNat x -> intRangeToNatRange (f x)
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

    StringContains{} -> Nothing
    StringIsPrefixOf{} -> Nothing
    StringIsSuffixOf{} -> Nothing
    StringLength s -> stringAbsLength (f s)
    StringSubstring _ s t l -> stringAbsSubstring (f s) (f t) (f l)
    StringIndexOf s t k -> stringAbsIndexOf (f s) (f t) (f k)
    StringAppend _ xs -> SSeq.stringSeqAbs xs

    StructCtor _ flds -> fmapFC (\v -> AbstractValueWrapper (f v)) flds
    StructField s idx _ -> unwrapAV (f s Ctx.! idx)


-- | Get abstract value associated with element.
exprAbsValue :: Expr t tp -> AbstractValue tp
exprAbsValue (SemiRingLiteral sr x _) =
  case sr of
    SR.SemiRingNatRepr  -> natSingleRange x
    SR.SemiRingIntegerRepr  -> singleRange x
    SR.SemiRingRealRepr -> ravSingle x
    SR.SemiRingBVRepr _ w -> BVD.singleton w x

exprAbsValue (StringExpr l _) = stringAbsSingle l
exprAbsValue (BoolExpr b _)   = Just b
exprAbsValue (NonceAppExpr e) = nonceExprAbsValue e
exprAbsValue (AppExpr e)      = appExprAbsValue e
exprAbsValue (BoundVarExpr v) =
  fromMaybe (unconstrainedAbsValue (bvarType v)) (bvarAbstractValue v)

instance HasAbsValue (Expr t) where
  getAbsValue = exprAbsValue

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
    BaseStringRepr _ -> "s"
    BaseComplexRepr -> "c"
    BaseArrayRepr _ _ -> "a"
    BaseStructRepr _ -> "struct"

-- | Either a argument or text or text
data PrettyArg (e :: BaseType -> Type) where
  PrettyArg  :: e tp -> PrettyArg e
  PrettyText :: Text -> PrettyArg e
  PrettyFunc :: Text -> [PrettyArg e] -> PrettyArg e

exprPrettyArg :: e tp -> PrettyArg e
exprPrettyArg e = PrettyArg e

exprPrettyIndices :: Ctx.Assignment e ctx -> [PrettyArg e]
exprPrettyIndices = toListFC exprPrettyArg

stringPrettyArg :: String -> PrettyArg e
stringPrettyArg x = PrettyText $! Text.pack x

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
    Annotation _ n x -> pure $ prettyApp "annotation" [ showPrettyArg n, exprPrettyArg x ]
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
          ppArg (PrettyArg e) = text (showF e)
          ppArg (PrettyText txt) = text (Text.unpack txt)
          ppArg (PrettyFunc fnm fargs) = parens (text (Text.unpack fnm) <+> sep (ppArg <$> fargs))

instance ShowF e => Show (App e u) where
  show = show . pretty

ppApp' :: forall e u . App e u -> PrettyApp e
ppApp' a0 = do
  let ppSExpr :: Text -> [e x] -> PrettyApp e
      ppSExpr f l = prettyApp f (exprPrettyArg <$> l)

  case a0 of
    BaseIte _ _ c x y -> prettyApp "ite" [exprPrettyArg c, exprPrettyArg x, exprPrettyArg y]
    BaseEq _ x y -> ppSExpr "eq" [x, y]

    NotPred x -> ppSExpr "not" [x]

    ConjPred xs ->
      let pol (x,Positive) = exprPrettyArg x
          pol (x,Negative) = PrettyFunc "not" [ exprPrettyArg x ]
       in
       case BM.viewBoolMap xs of
         BoolMapUnit      -> prettyApp "true" []
         BoolMapDualUnit  -> prettyApp "false" []
         BoolMapTerms tms -> prettyApp "and" (map pol (toList tms))

    RealIsInteger x -> ppSExpr "isInteger" [x]
    BVTestBit i x   -> prettyApp "testBit"  [exprPrettyArg x, showPrettyArg i]
    BVUlt x y -> ppSExpr "bvUlt" [x, y]
    BVSlt x y -> ppSExpr "bvSlt" [x, y]

    NatDiv x y -> ppSExpr "natDiv" [x, y]
    NatMod x y -> ppSExpr "natMod" [x, y]

    IntAbs x   -> prettyApp "intAbs" [exprPrettyArg x]
    IntDiv x y -> prettyApp "intDiv" [exprPrettyArg x, exprPrettyArg y]
    IntMod x y -> prettyApp "intMod" [exprPrettyArg x, exprPrettyArg y]
    IntDivisible x k -> prettyApp "intDivisible" [exprPrettyArg x, showPrettyArg k]

    SemiRingLe sr x y ->
      case sr of
        SR.OrderedSemiRingRealRepr    -> ppSExpr "realLe" [x, y]
        SR.OrderedSemiRingIntegerRepr -> ppSExpr "intLe" [x, y]
        SR.OrderedSemiRingNatRepr     -> ppSExpr "natLe" [x, y]

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingRealRepr -> prettyApp "realSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppRat c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "realAdd" [stringPrettyArg (ppRat sm), exprPrettyArg e ] ]
                ppRat r | d == 1 = show n
                        | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
                     where n = numerator r
                           d = denominator r

        SR.SemiRingIntegerRepr -> prettyApp "intSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "intMul" [stringPrettyArg (show sm), exprPrettyArg e ] ]

        SR.SemiRingNatRepr -> prettyApp "natSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (show c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "natMul" [stringPrettyArg (show sm), exprPrettyArg e ] ]

        SR.SemiRingBVRepr SR.BVArithRepr w -> prettyApp "bvSum" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry 1 e  = [ exprPrettyArg e ]
                ppEntry sm e = [ PrettyFunc "bvMul" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV x       = "0x" ++ (N.showHex x []) ++ ":[" ++ show w ++ "]"

        SR.SemiRingBVRepr SR.BVBitsRepr w -> prettyApp "bvXor" (WSum.eval (++) ppEntry ppConstant s)
          where ppConstant 0 = []
                ppConstant c = [ stringPrettyArg (ppBV c) ]
                ppEntry sm e
                  | sm == maxUnsigned w = [ exprPrettyArg e ]
                  | otherwise = [ PrettyFunc "bvAnd" [ stringPrettyArg (ppBV sm), exprPrettyArg e ] ]
                ppBV x       = "0x" ++ (N.showHex x []) ++ ":[" ++ show w ++ "]"

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingRealRepr ->
          prettyApp "realProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingIntegerRepr ->
          prettyApp "intProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingNatRepr ->
          prettyApp "natProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVArithRepr _w ->
          prettyApp "bvProd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)
        SR.SemiRingBVRepr SR.BVBitsRepr _w ->
          prettyApp "bvAnd" $ fromMaybe [] (WSum.prodEval (++) ((:[]) . exprPrettyArg) pd)


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
    BVOrBits _ bs -> prettyApp "bvOr" $ map exprPrettyArg $ bvOrToList bs

    BVConcat _ x y -> prettyApp "bvConcat" [exprPrettyArg x, exprPrettyArg y]
    BVSelect idx n x -> prettyApp "bvSelect" [showPrettyArg idx, showPrettyArg n, exprPrettyArg x]
    BVUdiv _ x y -> ppSExpr "bvUdiv" [x, y]
    BVUrem _ x y -> ppSExpr "bvUrem" [x, y]
    BVSdiv _ x y -> ppSExpr "bvSdiv" [x, y]
    BVSrem _ x y -> ppSExpr "bvSrem" [x, y]

    BVShl  _ x y -> ppSExpr "bvShl" [x, y]
    BVLshr _ x y -> ppSExpr "bvLshr" [x, y]
    BVAshr _ x y -> ppSExpr "bvAshr" [x, y]
    BVRol  _ x y -> ppSExpr "bvRol" [x, y]
    BVRor  _ x y -> ppSExpr "bvRor" [x, y]

    BVZext w x -> prettyApp "bvZext"   [showPrettyArg w, exprPrettyArg x]
    BVSext w x -> prettyApp "bvSext"   [showPrettyArg w, exprPrettyArg x]
    BVFill w p -> prettyApp "bvFill"   [showPrettyArg w, exprPrettyArg p]

    BVPopcount w x -> prettyApp "bvPopcount" [showPrettyArg w, exprPrettyArg x]
    BVCountLeadingZeros w x -> prettyApp "bvCountLeadingZeros" [showPrettyArg w, exprPrettyArg x]
    BVCountTrailingZeros w x -> prettyApp "bvCountTrailingZeros" [showPrettyArg w, exprPrettyArg x]

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
        prettyApp "arrayMap" (foldr ppEntry [exprPrettyArg d] (AUM.toList m))
      where ppEntry (k,e) l = showPrettyArg k : exprPrettyArg e : l
    ConstantArray _ _ v ->
      prettyApp "constArray" [exprPrettyArg v]
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

    RoundReal x -> ppSExpr "round" [x]
    FloorReal x -> ppSExpr "floor" [x]
    CeilReal  x -> ppSExpr "ceil"  [x]

    IntegerToNat x   -> ppSExpr "integerToNat" [x]
    IntegerToBV x w -> prettyApp "integerToBV" [exprPrettyArg x, showPrettyArg w]

    RealToInteger x   -> ppSExpr "realToInteger" [x]

    ------------------------------------------------------------------------
    -- String operations

    StringIndexOf x y k ->
       prettyApp "string-index-of" [exprPrettyArg x, exprPrettyArg y, exprPrettyArg k]
    StringContains x y -> ppSExpr "string-contains" [x, y]
    StringIsPrefixOf x y -> ppSExpr "string-is-prefix-of" [x, y]
    StringIsSuffixOf x y -> ppSExpr "string-is-suffix-of" [x, y]
    StringSubstring _ x off len ->
       prettyApp "string-substring" [exprPrettyArg x, exprPrettyArg off, exprPrettyArg len]
    StringAppend _ xs -> prettyApp "string-append" (map f (SSeq.toList xs))
          where f (SSeq.StringSeqLiteral l) = showPrettyArg l
                f (SSeq.StringSeqTerm t)    = exprPrettyArg t
    StringLength x -> ppSExpr "string-length" [x]

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


instance Eq (NonceApp t (Expr t) tp) where
  x == y = isJust (testEquality x y)

instance TestEquality (NonceApp t (Expr t)) where
  testEquality =
    $(structuralTypeEquality [t|NonceApp|]
           [ (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (DataArg 1 `TypeApp` AnyType, [|testEquality|])
           , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|Nonce|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
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
  hashWithSaltF = $(structuralHashWithSalt [t|NonceApp|] [])

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

instance HasAbsValue Dummy where
  getAbsValue _ = error "you made a magic Dummy value!"

instance FoldableFC App where
  foldMapFC f0 t = getConst (traverseApp (g f0) t)
    where g :: (f tp -> a) -> f tp -> Const a (Dummy tp)
          g f v = Const (f v)

traverseApp :: (Applicative m, OrdF f, Eq (f (BaseBoolType)), HashableF f, HasAbsValue f)
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
    , ( ConType [t|BVOrSet|] `TypeApp` AnyType `TypeApp` AnyType
      , [| traverseBVOrSet |]
      )
    , ( ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseProdVars |]
      )
    , ( ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
      , [| AUM.traverseArrayUpdateMap |]
      )
    , ( ConType [t|SSeq.StringSeq|] `TypeApp` AnyType `TypeApp` AnyType
      , [| SSeq.traverseStringSeq |]
      )
    , ( ConType [t|BoolMap|] `TypeApp` AnyType
      , [| BM.traverseVars |]
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

  SemiRingProd pd
    | SR.SemiRingBVRepr SR.BVBitsRepr _ <- WSum.prodRepr pd -> False
    | otherwise -> True

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

-- Special case, ignore the BV semiring flavor for this purpose
compareExpr (SemiRingLiteral (SR.SemiRingBVRepr _ wx) x _) (SemiRingLiteral (SR.SemiRingBVRepr _ wy) y _) =
  case compareF wx wy of
    LTF -> LTF
    EQF -> fromOrdering (compare x y)
    GTF -> GTF
compareExpr (SemiRingLiteral srx x _) (SemiRingLiteral sry y _) =
  case compareF srx sry of
    LTF -> LTF
    EQF -> fromOrdering (SR.sr_compare srx x y)
    GTF -> GTF
compareExpr SemiRingLiteral{} _ = LTF
compareExpr _ SemiRingLiteral{} = GTF

compareExpr (StringExpr x _) (StringExpr y _) =
  case compareF x y of
    LTF -> LTF
    EQF -> EQF
    GTF -> GTF

compareExpr StringExpr{} _ = LTF
compareExpr _ StringExpr{} = GTF

compareExpr (BoolExpr x _) (BoolExpr y _) = fromOrdering (compare x y)
compareExpr BoolExpr{} _ = LTF
compareExpr _ BoolExpr{} = GTF

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
  hashWithSalt s (BoolExpr b _) = hashWithSalt (hashWithSalt s (0::Int)) b
  hashWithSalt s (SemiRingLiteral sr x _) =
    case sr of
      SR.SemiRingNatRepr     -> hashWithSalt (hashWithSalt s (1::Int)) x
      SR.SemiRingIntegerRepr -> hashWithSalt (hashWithSalt s (2::Int)) x
      SR.SemiRingRealRepr    -> hashWithSalt (hashWithSalt s (3::Int)) x
      SR.SemiRingBVRepr _ w  -> hashWithSalt (hashWithSaltF (hashWithSalt s (4::Int)) w) x

  hashWithSalt s (StringExpr x _) = hashWithSalt (hashWithSalt s (5::Int)) x
  hashWithSalt s (AppExpr x)      = hashWithSalt (hashWithSalt s (6::Int)) (appExprId x)
  hashWithSalt s (NonceAppExpr x) = hashWithSalt (hashWithSalt s (7::Int)) (nonceExprId x)
  hashWithSalt s (BoundVarExpr x) = hashWithSalt (hashWithSalt s (8::Int)) x

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
countOccurrences' visited (SemiRingLiteral SR.SemiRingRealRepr r _) = do
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
   = FixedPPExpr !Doc ![Doc] !Int
     -- ^ A fixed doc with length.
   | AppPPExpr !AppPPExpr
     -- ^ A doc that can be let bound.

-- | Pretty print a AppPPExpr
apeDoc :: AppPPExpr -> (Doc, [Doc])
apeDoc a = (text (Text.unpack (apeName a)), ppExprDoc True <$> apeExprs a)

textPPExpr :: Text -> PPExpr
textPPExpr t = FixedPPExpr (text (Text.unpack t)) [] (Text.length t)

stringPPExpr :: String -> PPExpr
stringPPExpr t = FixedPPExpr (text t) [] (length t)

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
ppExprDoc b (FixedPPExpr d a _) = parenIf b d a
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
        let nm_expr = FixedPPExpr (text nm) (map text args) len
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
      renderArg (PrettyArg e) = getBindings e
      renderArg (PrettyText txt) = return (textPPExpr txt)
      renderArg (PrettyFunc nm args) =
        do exprs0 <- traverse renderArg args
           let total_width = Text.length nm + sum ((\e -> 1 + ppExprLength e) <$> exprs0)
           (exprs1, cur_width) <- fixLength total_width exprs0
           let exprs = map (ppExprDoc True) exprs1
           return (FixedPPExpr (text (Text.unpack nm)) exprs cur_width)

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
          Just d -> return (PrettyText d)
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
            return $! PrettyText d

      -- Collect definitions for all applications that occur multiple times
      -- in term.
      getBindings :: Expr t u -> ST s PPExpr
      getBindings (SemiRingLiteral sr x l) =
        case sr of
          SR.SemiRingNatRepr ->
            return $ stringPPExpr (show x)
          SR.SemiRingIntegerRepr ->
            return $ stringPPExpr (show x)
          SR.SemiRingRealRepr -> cacheResult (RatPPIndex x) l app
             where n = numerator x
                   d = denominator x
                   app | d == 1      = prettyApp (fromString (show n)) []
                       | use_decimal = prettyApp (fromString (show (fromRational x :: Double))) []
                       | otherwise   = prettyApp "divReal"  [ showPrettyArg n, showPrettyArg d ]
          SR.SemiRingBVRepr _ w ->
            return $ stringPPExpr $ "0x" ++ (N.showHex x []) ++ ":[" ++ show w ++ "]"

      getBindings (StringExpr x _) =
        return $ stringPPExpr $ (show x)
      getBindings (BoolExpr b _) =
        return $ stringPPExpr (if b then "true" else "false")
      getBindings (NonceAppExpr e) =
        cacheResult (ExprPPIndex (indexValue (nonceExprId e))) (nonceExprLoc e)
          =<< ppNonceApp bindFn (nonceExprApp e)
      getBindings (AppExpr e) =
        cacheResult (ExprPPIndex (indexValue (appExprId e)))
                    (appExprLoc e)
                    (ppApp' (appExprApp e))
      getBindings (BoundVarExpr i) =
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
           , (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (ConType [t|UnaryBV|]        `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|AUM.ArrayUpdateMap|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
             , [|\x y -> if x == y then Just Refl else Nothing|])
           , (ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|Ctx.Index|]      `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|StringInfoRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.SemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SR.OrderedSemiRingRepr|] `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|WSum.WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           , (ConType [t|SemiRingProduct|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|])
           ]
          )

{-# NOINLINE hashApp #-}
-- | Hash an an application.
hashApp :: Int -> App (Expr t) s -> Int
hashApp = $(structuralHashWithSalt [t|App|] [])

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
lookupIdxValue _ StringExpr{} = return Nothing
lookupIdxValue _ BoolExpr{} = return Nothing
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
-- | Remove a value from the IdxCache
deleteIdxValue :: MonadIO m => IdxCache t f -> Nonce t (tp :: BaseType) -> m ()
deleteIdxValue c e = liftIO $ stToIO $ do
  PH.delete (cMap c) e

-- | Remove all values from the IdxCache
clearIdxCache :: IdxCache t f -> IO ()
clearIdxCache c = stToIO $ PH.clear (cMap c)

exprMaybeId :: Expr t tp -> Maybe (Nonce t tp)
exprMaybeId SemiRingLiteral{} = Nothing
exprMaybeId StringExpr{} = Nothing
exprMaybeId BoolExpr{} = Nothing
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
            -> SR.SemiRingRepr sr
            -> SR.Coefficient sr
            -> IO (Expr t (SR.SemiRingBase sr))
semiRingLit sb sr x = do
  l <- curProgramLoc sb
  return $! SemiRingLiteral sr x l

sbMakeExpr :: ExprBuilder t st fs -> App (Expr t) tp -> IO (Expr t tp)
sbMakeExpr sym a = do
  s <- readIORef (curAllocator sym)
  pc <- curProgramLoc sym
  let v = abstractEval exprAbsValue a
  when (isNonLinearApp a) $
    modifyIORef' (sbNonLinearOps sym) (+1)
  case appType a of
    -- Check if abstract interpretation concludes this is a constant.
    BaseBoolRepr | Just b <- v -> return $ backendPred sym b
    BaseNatRepr  | Just c <- asSingleNatRange v -> natLit sym c
    BaseIntegerRepr | Just c <- asSingleRange v -> intLit sym c
    BaseRealRepr | Just c <- asSingleRange (ravRange v) -> realLit sym c
    BaseBVRepr w | Just x <- BVD.asSingleton v -> bvLit sym w x
    _ -> appExpr s pc a v

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


newExprBuilder ::
  FloatModeRepr fm
  -- ^ Float interpretation mode (i.e., how are floats translated for the solver).
  -> st t
  -- ^ Current state for simple builder.
  -> NonceGenerator IO t
  -- ^ Nonce generator for names
  ->  IO (ExprBuilder t st (Flags fm))
newExprBuilder floatMode st gen = do
  st_ref <- newIORef st
  es <- newStorage gen

  let t = BoolExpr True initializationLoc
  let f = BoolExpr False initializationLoc
  let z = SemiRingLiteral SR.SemiRingRealRepr 0 initializationLoc

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
               , sbFloatMode = floatMode
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

bvBinDivOp :: (1 <= w)
            => (Integer -> Integer -> Integer)
            -> (NatRepr w -> BVExpr t w -> BVExpr t w -> App (Expr t) (BaseBVType w))
            -> ExprBuilder t st fs
            -> BVExpr t w
            -> BVExpr t w
            -> IO (BVExpr t w)
bvBinDivOp f c sb x y = do
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
    BaseIte _ _ c x y -> baseTypeIte sym c x y
    BaseEq _ x y -> isEq sym x y

    NotPred x -> notPred sym x
    ConjPred bm ->
      case BM.viewBoolMap bm of
        BoolMapDualUnit -> return $ falsePred sym
        BoolMapUnit     -> return $ truePred sym
        BoolMapTerms tms ->
          do let pol (p, Positive) = return p
                 pol (p, Negative) = notPred sym p
             x:|xs <- mapM pol tms
             foldM (andPred sym) x xs

    SemiRingSum s ->
      case WSum.sumRepr s of
        SR.SemiRingNatRepr ->
          WSum.evalM (natAdd sym) (\c x -> natMul sym x =<< natLit sym c) (natLit sym) s
        SR.SemiRingIntegerRepr ->
          WSum.evalM (intAdd sym) (\c x -> intMul sym x =<< intLit sym c) (intLit sym) s
        SR.SemiRingRealRepr ->
          WSum.evalM (realAdd sym) (\c x -> realMul sym x =<< realLit sym c) (realLit sym) s
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          WSum.evalM (bvAdd sym) (\c x -> bvMul sym x =<< bvLit sym w c) (bvLit sym w) s
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          WSum.evalM (bvXorBits sym) (\c x -> bvAndBits sym x =<< bvLit sym w c) (bvLit sym w) s

    SemiRingProd pd ->
      case WSum.prodRepr pd of
        SR.SemiRingNatRepr ->
          maybe (natLit sym 1) return =<< WSum.prodEvalM (natMul sym) return pd
        SR.SemiRingIntegerRepr ->
          maybe (intLit sym 1) return =<< WSum.prodEvalM (intMul sym) return pd
        SR.SemiRingRealRepr ->
          maybe (realLit sym 1) return =<< WSum.prodEvalM (realMul sym) return pd
        SR.SemiRingBVRepr SR.BVArithRepr w ->
          maybe (bvLit sym w 1) return =<< WSum.prodEvalM (bvMul sym) return pd
        SR.SemiRingBVRepr SR.BVBitsRepr w ->
          maybe (bvLit sym w (maxUnsigned w)) return =<< WSum.prodEvalM (bvAndBits sym) return pd

    SemiRingLe SR.OrderedSemiRingRealRepr x y -> realLe sym x y
    SemiRingLe SR.OrderedSemiRingIntegerRepr x y -> intLe sym x y
    SemiRingLe SR.OrderedSemiRingNatRepr x y -> natLe sym x y

    RealIsInteger x -> isInteger sym x

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

    BVOrBits w bs ->
      case bvOrToList bs of
        [] -> bvLit sym w 0
        (x:xs) -> foldM (bvOrBits sym) x xs

    BVTestBit i e -> testBitBV sym i e
    BVSlt x y -> bvSlt sym x y
    BVUlt x y -> bvUlt sym x y
    BVUnaryTerm x -> bvUnary sym x
    BVConcat _ x y -> bvConcat sym x y
    BVSelect idx n x -> bvSelect sym idx n x
    BVUdiv _ x y -> bvUdiv sym x y
    BVUrem _ x y -> bvUrem sym x y
    BVSdiv _ x y -> bvSdiv sym x y
    BVSrem _ x y -> bvSrem sym x y
    BVShl _ x y  -> bvShl  sym x y
    BVLshr _ x y -> bvLshr sym x y
    BVAshr _ x y -> bvAshr sym x y
    BVRol  _ x y -> bvRol sym x y
    BVRor  _ x y -> bvRor sym x y
    BVZext  w x  -> bvZext sym w x
    BVSext  w x  -> bvSext sym w x
    BVPopcount _ x -> bvPopcount sym x
    BVFill w p -> bvFill sym w p
    BVCountLeadingZeros _ x -> bvCountLeadingZeros sym x
    BVCountTrailingZeros _ x -> bvCountTrailingZeros sym x

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

    ArrayMap _ _ m def_map ->
      arrayUpdateAtIdxLits sym m def_map
    ConstantArray idx_tp _ e -> constantArray sym idx_tp e
    SelectArray _ a i     -> arrayLookup sym a i
    UpdateArray _ _ a i v -> arrayUpdate sym a i v

    NatToInteger x -> natToInteger sym x
    IntegerToNat x -> integerToNat sym x
    IntegerToReal x -> integerToReal sym x
    RealToInteger x -> realToInteger sym x

    BVToNat x       -> bvToNat sym x
    BVToInteger x   -> bvToInteger sym x
    SBVToInteger x  -> sbvToInteger sym x
    IntegerToBV x w -> integerToBV sym x w

    RoundReal x -> realRound sym x
    FloorReal x -> realFloor sym x
    CeilReal  x -> realCeil sym x

    Cplx c     -> mkComplex sym c
    RealPart x -> getRealPart sym x
    ImagPart x -> getImagPart sym x

    StringIndexOf x y k -> stringIndexOf sym x y k
    StringContains x y -> stringContains sym x y
    StringIsPrefixOf x y -> stringIsPrefixOf sym x y
    StringIsSuffixOf x y -> stringIsSuffixOf sym x y
    StringSubstring _ x off len -> stringSubstring sym x off len

    StringAppend si xs ->
       do e <- stringEmpty sym si
          let f x (SSeq.StringSeqLiteral l) = stringConcat sym x =<< stringLit sym l
              f x (SSeq.StringSeqTerm y) = stringConcat sym x y
          foldM f e (SSeq.toList xs)

    StringLength x -> stringLength sym x

    StructCtor _ args -> mkStruct sym args
    StructField s i _ -> structField sym s i


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
    StringExpr{} -> return e0
    BoolExpr{} -> return e0
    AppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      let a = appExprApp ae
      a' <- traverseApp (evalBoundVars' tbls sym) a
      if a == a' then
        return e0
       else
        reduceApp sym a'
    NonceAppExpr ae -> cachedEval (exprTable tbls) e0 $ do
      case nonceExprApp ae of
        Annotation tpr n a -> do
          a' <- evalBoundVars' tbls sym a
          if a == a' then
            return e0
          else
            sbNonceExpr sym $ Annotation tpr n a'
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
  | Just (ArrayMap _ _ entry_map def) <- asApp arr0
  , Just cidx <- mcidx =
      case AUM.lookup cidx entry_map of
        Just v -> return v
        Nothing -> sbConcreteLookup sym def mcidx idx
    -- Evaluate function arrays on ground values.
  | Just (ArrayFromFn f) <- asNonceApp arr0 = do
      betaReduce sym f idx

    -- Lookups on constant arrays just return value
  | Just (ConstantArray _ _ v) <- asApp arr0 = do
      return v
    -- Lookups on mux arrays just distribute over mux.
  | Just (BaseIte _ _ p x y) <- asApp arr0 = do
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

-- | Evaluate a weighted sum of natural number values.
natSum :: ExprBuilder t st fs -> WeightedSum (Expr t) SR.SemiRingNat -> IO (NatExpr t)
natSum sym s = semiRingSum sym s

-- | Evaluate a weighted sum of integer values.
intSum :: ExprBuilder t st fs -> WeightedSum (Expr t) SR.SemiRingInteger -> IO (IntegerExpr t)
intSum sym s = semiRingSum sym s

-- | Evaluate a weighted sum of real values.
realSum :: ExprBuilder t st fs -> WeightedSum (Expr t) SR.SemiRingReal -> IO (RealExpr t)
realSum sym s = semiRingSum sym s

bvSum :: ExprBuilder t st fs -> WeightedSum (Expr t) (SR.SemiRingBV flv w) -> IO (BVExpr t w)
bvSum sym s = semiRingSum sym s

conjPred :: ExprBuilder t st fs -> BoolMap (Expr t) -> IO (BoolExpr t)
conjPred sym bm =
  case BM.viewBoolMap bm of
    BoolMapUnit     -> return $ truePred sym
    BoolMapDualUnit -> return $ falsePred sym
    BoolMapTerms ((x,p):|[]) ->
      case p of
        Positive -> return x
        Negative -> notPred sym x
    _ -> sbMakeExpr sym $ ConjPred bm

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
  | SemiRingLiteral (SR.SemiRingBVRepr _ w) v _ <- e = Just $ UnaryBV.constant sym w v
  | otherwise = Nothing

-- | This create a unary bitvector representing if the size is not too large.
sbTryUnaryTerm :: (1 <= w, ?unaryThreshold :: Int)
               => ExprBuilder t st fs
               -> Maybe (IO (UnaryBV (BoolExpr t) w))
               -> IO (BVExpr t w)
               -> IO (BVExpr t w)
sbTryUnaryTerm _sym Nothing fallback = fallback
sbTryUnaryTerm sym (Just mku) fallback =
  do u <- mku
     if UnaryBV.size u < ?unaryThreshold then
       bvUnary sym u
     else
       fallback

semiRingProd ::
  ExprBuilder t st fs ->
  SemiRingProduct (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingProd sym pd
  | WSum.nullProd pd = semiRingLit sym (WSum.prodRepr pd) (SR.one (WSum.prodRepr pd))
  | Just v <- WSum.asProdVar pd = return v
  | otherwise = sbMakeExpr sym $ SemiRingProd pd

semiRingSum ::
  ExprBuilder t st fs ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingSum sym s
    | Just c <- WSum.asConstant s = semiRingLit sym (WSum.sumRepr s) c
    | Just r <- WSum.asVar s      = return r
    | otherwise                   = sum' sym s

sum' ::
  ExprBuilder t st fs ->
  WeightedSum (Expr t) sr ->
  IO (Expr t (SR.SemiRingBase sr))
sum' sym s = sbMakeExpr sym $ SemiRingSum s
{-# INLINE sum' #-}

scalarMul ::
   ExprBuilder t st fs ->
   SR.SemiRingRepr sr ->
   SR.Coefficient sr ->
   Expr t (SR.SemiRingBase sr) ->
   IO (Expr t (SR.SemiRingBase sr))
scalarMul sym sr c x
  | SR.eq sr (SR.zero sr) c = semiRingLit sym sr (SR.zero sr)
  | SR.eq sr (SR.one sr)  c = return x
  | Just r <- asSemiRingLit sr x =
    semiRingLit sym sr (SR.mul sr c r)
  | Just s <- asSemiRingSum sr x =
    sum' sym (WSum.scale sr c s)
  | otherwise =
    sum' sym (WSum.scaledVar sr c x)

semiRingIte ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t BaseBoolType ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingIte sym sr c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = semiRingIte sym sr c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

    -- Try to extract common sum information.
  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) = do
    xr <- semiRingSum sym x'
    yr <- semiRingSum sym y'
    let sz = 1 + iteSize xr + iteSize yr
    r <- sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c xr yr)
    semiRingSum sym $! WSum.addVar sr z r

    -- final fallback, create the ite term
  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (SR.semiRingBase sr) sz c x y)


mkIte ::
  ExprBuilder t st fs ->
  Expr t BaseBoolType ->
  Expr t bt ->
  Expr t bt ->
  IO (Expr t bt)
mkIte sym c x y
    -- evaluate as constants
  | Just True  <- asConstantPred c = return x
  | Just False <- asConstantPred c = return y

    -- reduce negations
  | Just (NotPred c') <- asApp c
  = mkIte sym c' y x

    -- remove the ite if the then and else cases are the same
  | x == y = return x

  | otherwise =
      let sz = 1 + iteSize x + iteSize y in
      sbMakeExpr sym (BaseIte (exprType x) sz c x y)

semiRingLe ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
      {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingLe sym osr rec x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)

      -- Strength reductions on a non-linear constraint to piecewise linear.
    | Just c <- asSemiRingLit sr x
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp y
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonneg sym osr pd

      -- Another strength reduction
    | Just c <- asSemiRingLit sr y
    , SR.eq sr c (SR.zero sr)
    , Just (SemiRingProd pd) <- asApp x
    , Just Refl <- testEquality sr (WSum.prodRepr pd)
    = prodNonpos sym osr pd

      -- Push some comparisons under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    = join (itePred sym c <$> rec x a <*> rec x b)

      -- Push some comparisons under if/then/else
    | Just (BaseIte tp _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    , Just Refl <- testEquality tp (SR.semiRingBase sr)
    = join (itePred sym c <$> rec a y <*> rec b y)

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) = do
      xr <- semiRingSum sym x'
      yr <- semiRingSum sym y'
      rec xr yr

      -- Default case
    | otherwise = sbMakeExpr sym $ SemiRingLe osr x y

 where sr = SR.orderedSemiRing osr


semiRingEq ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  (Expr t (SR.SemiRingBase sr) -> Expr t (SR.SemiRingBase sr) -> IO (Expr t BaseBoolType))
    {- ^ recursive call for simplifications -} ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t BaseBoolType)
semiRingEq sym sr rec x y
  -- Check for syntactic equality.
  | x == y = return (truePred sym)

    -- Push some equalities under if/then/else
  | SemiRingLiteral _ _ _ <- x
  , Just (BaseIte _ _ c a b) <- asApp y
  = join (itePred sym c <$> rec x a <*> rec x b)

    -- Push some equalities under if/then/else
  | Just (BaseIte _ _ c a b) <- asApp x
  , SemiRingLiteral _ _ _ <- y
  = join (itePred sym c <$> rec a y <*> rec b y)

  | (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
  , not (WSum.isZero sr z) =
    case (WSum.asConstant x', WSum.asConstant y') of
      (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
      _ -> do xr <- semiRingSum sym x'
              yr <- semiRingSum sym y'
              sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

  | otherwise =
    sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min x y) (max x y)

semiRingAdd ::
  forall t st fs sr.
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingAdd sym sr x y =
    case (viewSemiRing sr x, viewSemiRing sr y) of
      (SR_Constant c, _) | SR.eq sr c (SR.zero sr) -> return y
      (_, SR_Constant c) | SR.eq sr c (SR.zero sr) -> return x

      (SR_Constant xc, SR_Constant yc) ->
        semiRingLit sym sr (SR.add sr xc yc)

      (SR_Constant xc, SR_Sum ys) ->
        sum' sym (WSum.addConstant sr ys xc)
      (SR_Sum xs, SR_Constant yc) ->
        sum' sym (WSum.addConstant sr xs yc)

      (SR_Constant xc, _)
        | Just (BaseIte _ _ cond a b) <- asApp y
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            xa <- semiRingAdd sym sr x a
            xb <- semiRingAdd sym sr x b
            semiRingIte sym sr cond xa xb
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr y) xc)

      (_, SR_Constant yc)
        | Just (BaseIte _ _ cond a b) <- asApp x
        , isConstantSemiRingExpr a || isConstantSemiRingExpr b -> do
            ay <- semiRingAdd sym sr a y
            by <- semiRingAdd sym sr b y
            semiRingIte sym sr cond ay by
        | otherwise ->
            sum' sym (WSum.addConstant sr (WSum.var sr x) yc)

      (SR_Sum xs, SR_Sum ys) -> semiRingSum sym (WSum.add sr xs ys)
      (SR_Sum xs, _)         -> semiRingSum sym (WSum.addVar sr xs y)
      (_ , SR_Sum ys)        -> semiRingSum sym (WSum.addVar sr ys x)
      _                      -> semiRingSum sym (WSum.addVars sr x y)
  where isConstantSemiRingExpr :: Expr t (SR.SemiRingBase sr) -> Bool
        isConstantSemiRingExpr (viewSemiRing sr -> SR_Constant _) = True
        isConstantSemiRingExpr _ = False

semiRingMul ::
  ExprBuilder t st fs ->
  SR.SemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) ->
  Expr t (SR.SemiRingBase sr) ->
  IO (Expr t (SR.SemiRingBase sr))
semiRingMul sym sr x y =
  case (viewSemiRing sr x, viewSemiRing sr y) of
    (SR_Constant c, _) -> scalarMul sym sr c y
    (_, SR_Constant c) -> scalarMul sym sr c x

    (SR_Sum (WSum.asAffineVar -> Just (c,x',o)), _) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x' y
         oy  <- scalarMul sym sr o y
         semiRingAdd sym sr cxy oy

    (_, SR_Sum (WSum.asAffineVar -> Just (c,y',o))) ->
      do cxy <- scalarMul sym sr c =<< semiRingMul sym sr x y'
         ox  <- scalarMul sym sr o x
         semiRingAdd sym sr cxy ox

    (SR_Prod px, SR_Prod py) -> semiRingProd sym (WSum.prodMul px py)
    (SR_Prod px, _)          -> semiRingProd sym (WSum.prodMul px (WSum.prodVar sr y))
    (_, SR_Prod py)          -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) py)
    _                        -> semiRingProd sym (WSum.prodMul (WSum.prodVar sr x) (WSum.prodVar sr y))


prodNonneg ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonneg sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     fst <$> computeNonnegNonpos sym osr zero pd

prodNonpos ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType)
prodNonpos sym osr pd =
  do let sr = SR.orderedSemiRing osr
     zero <- semiRingLit sym sr (SR.zero sr)
     snd <$> computeNonnegNonpos sym osr zero pd

computeNonnegNonpos ::
  ExprBuilder t st fs ->
  SR.OrderedSemiRingRepr sr ->
  Expr t (SR.SemiRingBase sr) {- zero element -} ->
  WSum.SemiRingProduct (Expr t) sr ->
  IO (Expr t BaseBoolType, Expr t BaseBoolType)
computeNonnegNonpos sym osr zero pd =
   fromMaybe (truePred sym, falsePred sym) <$> WSum.prodEvalM merge single pd
 where

 single x = (,) <$> reduceApp sym (SemiRingLe osr zero x) -- nonnegative
                <*> reduceApp sym (SemiRingLe osr x zero) -- nonpositive

 merge (nn1, np1) (nn2, np2) =
   do nn <- join (orPred sym <$> andPred sym nn1 nn2 <*> andPred sym np1 np2)
      np <- join (orPred sym <$> andPred sym nn1 np2 <*> andPred sym np1 nn2)
      return (nn, np)



arrayResultIdxType :: BaseTypeRepr (BaseArrayType (idx ::> itp) d)
                   -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
arrayResultIdxType (BaseArrayRepr idx _) = idx

-- | This decomposes A ExprBuilder array expression into a set of indices that
-- have been updated, and an underlying index.
data ArrayMapView i f tp
   = ArrayMapView { _arrayMapViewIndices :: !(AUM.ArrayUpdateMap f i tp)
                  , _arrayMapViewExpr    :: !(f (BaseArrayType i tp))
                  }

-- | Construct an 'ArrayMapView' for an element.
viewArrayMap :: Expr t (BaseArrayType i tp)
             -> ArrayMapView i (Expr t) tp
viewArrayMap  x
  | Just (ArrayMap _ _ m c) <- asApp x = ArrayMapView m c
  | otherwise = ArrayMapView AUM.empty x

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
            Set.union s (AUM.keysSet m)
          | otherwise = s

data NatLit tp = (tp ~ BaseNatType) => NatLit Natural

asNatBounds :: Ctx.Assignment (Expr t) idx -> Maybe (Ctx.Assignment NatLit idx)
asNatBounds = traverseFC f
  where f :: Expr t tp -> Maybe (NatLit tp)
        f (SemiRingLiteral SR.SemiRingNatRepr n _) = Just (NatLit n)
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

-- | Examine the list of terms, and determine if any one of them
--   appears in the given @BoolMap@ with the same polarity.
checkAbsorption ::
  BoolMap (Expr t) ->
  [(BoolExpr t, Polarity)] ->
  Bool
checkAbsorption _bm [] = False
checkAbsorption bm ((x,p):_)
  | Just p' <- BM.contains bm x, p == p' = True
checkAbsorption bm (_:xs) = checkAbsorption bm xs

-- | If @tryAndAbsorption x y@ returns @True@, that means that @y@
-- implies @x@, so that the conjunction @x AND y = y@. A @False@
-- result gives no information.
tryAndAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryAndAbsorption (asApp -> Just (NotPred (asApp -> Just (ConjPred as)))) (asConjunction -> bs)
  = checkAbsorption (BM.reversePolarities as) bs
tryAndAbsorption _ _ = False


-- | If @tryOrAbsorption x y@ returns @True@, that means that @x@
-- implies @y@, so that the disjunction @x OR y = y@. A @False@
-- result gives no information.
tryOrAbsorption ::
  BoolExpr t ->
  BoolExpr t ->
  Bool
tryOrAbsorption (asApp -> Just (ConjPred as)) (asDisjunction -> bs)
  = checkAbsorption as bs
tryOrAbsorption _ _ = False


-- | A slightly more aggressive syntactic equality check than testEquality,
--   `sameTerm` will recurse through a small collection of known syntax formers.
sameTerm :: Expr t a -> Expr t b -> Maybe (a :~: b)

sameTerm (asApp -> Just (FloatToBinary fppx x)) (asApp -> Just (FloatToBinary fppy y)) =
  do Refl <- testEquality fppx fppy
     Refl <- sameTerm x y
     return Refl

sameTerm x y = testEquality x y

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

  annotateTerm sym e =
    case e of
      NonceAppExpr (nonceExprApp -> Annotation _ n _) -> return (n, e)
      _ -> do
        let tpr = exprType e
        n <- sbFreshIndex sym
        e' <- sbNonceExpr sym (Annotation tpr n e)
        return (n, e')

  ----------------------------------------------------------------------
  -- Program location operations

  getCurrentProgramLoc = curProgramLoc
  setCurrentProgramLoc sym l = writeIORef (sbProgramLoc sym) l

  ----------------------------------------------------------------------
  -- Bool operations.

  truePred  = sbTrue
  falsePred = sbFalse

  notPred sym x
    | Just b <- asConstantPred x
    = return (backendPred sym $! not b)

    | Just (NotPred x') <- asApp x
    = return x'

    | otherwise
    = sbMakeExpr sym (NotPred x)

  eqPred sym x y
    | x == y
    = return (truePred sym)

    | Just (NotPred x') <- asApp x
    = xorPred sym x' y

    | Just (NotPred y') <- asApp y
    = xorPred sym x y'

    | otherwise
    = case (asConstantPred x, asConstantPred y) of
        (Just False, _)    -> notPred sym y
        (Just True, _)     -> return y
        (_, Just False)    -> notPred sym x
        (_, Just True)     -> return x
        _ -> sbMakeExpr sym $ BaseEq BaseBoolRepr (min x y) (max x y)

  xorPred sym x y = notPred sym =<< eqPred sym x y

  andPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return y
      (Just False, _) -> return x
      (_, Just True)  -> return x
      (_, Just False) -> return y
      _ | x == y -> return x -- and is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (ConjPred as) <- asApp a
     , Just (ConjPred bs) <- asApp b
     = conjPred sym $ BM.combine as bs

     | tryAndAbsorption a b
     = return b

     | tryAndAbsorption b a
     = return a

     | Just (ConjPred as) <- asApp a
     = conjPred sym $ uncurry BM.addVar (asPosAtom b) as

     | Just (ConjPred bs) <- asApp b
     = conjPred sym $ uncurry BM.addVar (asPosAtom a) bs

     | otherwise
     = conjPred sym $ BM.fromVars [asPosAtom a, asPosAtom b]

  orPred sym x y =
    case (asConstantPred x, asConstantPred y) of
      (Just True, _)  -> return x
      (Just False, _) -> return y
      (_, Just True)  -> return y
      (_, Just False) -> return x
      _ | x == y -> return x -- or is idempotent
        | otherwise -> go x y

   where
   go a b
     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     , Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (BM.combine as bs)

     | tryOrAbsorption a b
     = return b

     | tryOrAbsorption b a
     = return a

     | Just (NotPred (asApp -> Just (ConjPred as))) <- asApp a
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom b) as)

     | Just (NotPred (asApp -> Just (ConjPred bs))) <- asApp b
     = notPred sym =<< conjPred sym (uncurry BM.addVar (asNegAtom a) bs)

     | otherwise
     = notPred sym =<< conjPred sym (BM.fromVars [asNegAtom a, asNegAtom b])

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

      -- ite !c x y = ite c y x
    | Just (NotPred c') <- asApp c = itePred sb c' y x

      -- ite c 1 y = c || y
    | Just True  <- asConstantPred x = orPred sb c y

      -- ite c 0 y = !c && y
    | Just False <- asConstantPred x = andPred sb y =<< notPred sb c

      -- ite c x 1 = !c || x
    | Just True  <- asConstantPred y = orPred sb x =<< notPred sb c

      -- ite c x 0 = c && x
    | Just False <- asConstantPred y = andPred sb c x

      -- Default case
    | otherwise =
        let sz = 1 + iteSize x + iteSize y in
        sbMakeExpr sb $ BaseIte BaseBoolRepr sz c x y

  ----------------------------------------------------------------------
  -- Nat operations.

  natLit sym n = semiRingLit sym SR.SemiRingNatRepr n

  natAdd sym x y = semiRingAdd sym SR.SemiRingNatRepr x y

  natSub sym x y = do
    xr <- natToInteger sym x
    yr <- natToInteger sym y
    integerToNat sym =<< intSub sym xr yr

  natMul sym x y = semiRingMul sym SR.SemiRingNatRepr x y

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

  natIte sym c x y = semiRingIte sym SR.SemiRingNatRepr c x y

  natEq sym x y
    | Just b <- natCheckEq (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingEq sym SR.SemiRingNatRepr (natEq sym) x y

  natLe sym x y
    | Just b <- natCheckLe (exprAbsValue x) (exprAbsValue y)
    = return (backendPred sym b)

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingNatRepr (natLe sym) x y

  ----------------------------------------------------------------------
  -- Integer operations.

  intLit sym n = semiRingLit sym SR.SemiRingIntegerRepr n

  intNeg sym x = scalarMul sym SR.SemiRingIntegerRepr (-1) x

  intAdd sym x y = semiRingAdd sym SR.SemiRingIntegerRepr x y

  intMul sym x y = semiRingMul sym SR.SemiRingIntegerRepr x y

  intIte sym c x y = semiRingIte sym SR.SemiRingIntegerRepr c x y

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
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minSigned w || yi > maxSigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minSigned w || xi > maxSigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if yi < minUnsigned w || yi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym xbv =<< bvLit sym w yi

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (BVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if xi < minUnsigned w || xi > maxUnsigned w
         then return (falsePred sym)
         else bvEq sym ybv =<< bvLit sym w xi

    | otherwise = semiRingEq sym SR.SemiRingIntegerRepr (intEq sym) x y

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
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minSigned w -> return (falsePred sym)
         | yi > maxSigned w -> return (truePred sym)
         | otherwise -> join (bvSle sym <$> pure xbv <*> bvLit sym w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
    , Just (SBVToInteger ybv) <- asApp x
    = let w = bvWidth ybv in
      if | xi < minSigned w -> return (truePred sym)
         | xi > maxSigned w -> return (falsePred sym)
         | otherwise -> join (bvSle sym <$> bvLit sym w xi <*> pure ybv)

    | Just (BVToInteger xbv) <- asApp x
    , Just yi <- asSemiRingLit SR.SemiRingIntegerRepr y
    = let w = bvWidth xbv in
      if | yi < minUnsigned w -> return (falsePred sym)
         | yi > maxUnsigned w -> return (truePred sym)
         | otherwise -> join (bvUle sym <$> pure xbv <*> bvLit sym w yi)

    | Just xi <- asSemiRingLit SR.SemiRingIntegerRepr x
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
    = semiRingLe sym SR.OrderedSemiRingIntegerRepr (intLe sym) x y

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
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum
    , Just yi <- asInteger y
    , yi /= 0 =
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
    | Just (SemiRingSum xsum) <- asApp x
    , SR.SemiRingIntegerRepr <- WSum.sumRepr xsum =
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

  bvLit sym w i =
    semiRingLit sym (SR.SemiRingBVRepr SR.BVArithRepr w) (toUnsigned w i)

  bvConcat sym x y =
    case (asUnsignedBV x, asUnsignedBV y) of
      -- both values are constants, just compute the concatenation
      (Just xv, Just yv) -> do
          let shft :: Int
              shft = fromIntegral (natValue (bvWidth y))
          let w' = addNat (bvWidth x) (bvWidth y)
          -- Work around to satisfy GHC typechecker.
          case isPosNat w' of
            Nothing -> fail $ "bvConcat given bad width."
            Just LeqProof -> do
              bvLit sym w' ((xv `Bits.shiftL` shft) Bits..|. yv)
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
        , Just Refl <- sameTerm a b
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
      let mask = maxUnsigned n
      let shft = fromIntegral (natValue idx)
      bvLit sb n ((xv `Bits.shiftR` shft) Bits..&. mask)

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

    -- Truncate a weighted sum: Remove terms with coefficients that
    -- would become zero after truncation.
    --
    -- Truncation of w-bit words down to n bits respects congruence
    -- modulo 2^n. Furthermore, w-bit addition and multiplication also
    -- preserve congruence modulo 2^n. This means that it is sound to
    -- replace coefficients in a weighted sum with new masked ones
    -- that are congruent modulo 2^n: the final result after
    -- truncation will be the same.
    --
    -- NOTE: This case is carefully designed to preserve sharing. Only
    -- one App node (the SemiRingSum) is ever deconstructed. The
    -- 'traverseCoeffs' call does not touch any other App nodes inside
    -- the WeightedSum. Finally, we only reconstruct a new SemiRingSum
    -- App node in the event that one of the coefficients has changed;
    -- the writer monad tracks whether a change has occurred.
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVArithRepr _w <- WSum.sumRepr s
    , Just Refl <- testEquality idx (knownNat :: NatRepr 0) =
      do let mask = maxUnsigned n
         let reduce i
               | i Bits..&. mask == 0 = writer (0, Any True)
               | otherwise            = writer (i, Any False)
         let (s', Any changed) = runWriter $ WSum.traverseCoeffs reduce s
         x' <- if changed then sbMakeExpr sb (SemiRingSum s') else return x
         sbMakeExpr sb $ BVSelect idx n x'

{-  Avoid doing work that may lose sharing...

    -- Select from a weighted XOR: push down through the sum
    | Just (SemiRingSum s) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.sumRepr s
    = do let mask = maxUnsigned n
         let shft = fromIntegral (natValue idx)
         s' <- WSum.transformSum (SR.SemiRingBVRepr SR.BVBitsRepr n)
                 (\c -> return ((c `Bits.shiftR` shft)  Bits..&. mask))
                 (bvSelect sb idx n)
                 s
         semiRingSum sb s'

    -- Select from a AND: push down through the AND
    | Just (SemiRingProd pd) <- asApp x
    , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr pd
    = do pd' <- WSum.prodEvalM
                   (bvAndBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n (maxUnsigned n)) return pd'

    -- Select from an OR: push down through the OR
    | Just (BVOrBits pd) <- asApp x
    = do pd' <- WSum.prodEvalM
                   (bvOrBits sb)
                   (bvSelect sb idx n)
                   pd
         maybe (bvLit sb n 0) return pd'
-}

    -- Truncate from a unary bitvector
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
    , i <= fromIntegral (maxBound :: Int)
    = return $! backendPred sym (yc `Bits.testBit` fromIntegral i)

    | Just (BVZext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        return $ falsePred sym
      else
        testBitBV sym i y'

    | Just (BVSext _w y') <- asApp y
    = if i >= natValue (bvWidth y') then
        testBitBV sym (natValue (bvWidth y') - 1) y'
      else
        testBitBV sym i y'

    | Just (BVFill _ p) <- asApp y
    = return p

    | Just b <- BVD.testBit (bvWidth y) (exprAbsValue y) i
    = return $! backendPred sym b

    | Just (BaseIte _ _ c a b) <- asApp y
    , isJust (asUnsignedBV a) || isJust (asUnsignedBV b) -- NB avoid losing sharing
    = do a' <- testBitBV sym i a
         b' <- testBitBV sym i b
         itePred sym c a' b'

{- These rewrites can sometimes yield significant simplifications, but
   also may lead to loss of sharing, so they are disabled...

    | Just ws <- asSemiRingSum (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = let smul c x
           | Bits.testBit c (fromIntegral i) = testBitBV sym i x
           | otherwise                       = return (falsePred sym)
          cnst c = return $! backendPred sym (Bits.testBit c (fromIntegral i))
       in WSum.evalM (xorPred sym) smul cnst ws

    | Just pd <- asSemiRingProd (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth y)) y
    = fromMaybe (truePred sym) <$> WSum.prodEvalM (andPred sym) (testBitBV sym i) pd

    | Just (BVOrBits pd) <- asApp y
    = fromMaybe (falsePred sym) <$> WSum.prodEvalM (orPred sym) (testBitBV sym i) pd
-}

    | otherwise = sbMakeExpr sym $ BVTestBit i y

  bvFill sym w p
    | Just True  <- asConstantPred p = bvLit sym w (maxUnsigned w)
    | Just False <- asConstantPred p = bvLit sym w 0
    | otherwise = sbMakeExpr sym $ BVFill w p

  bvIte sym c x y
    | Just (BVFill w px) <- asApp x
    , Just (BVFill _w py) <- asApp y =
      do z <- itePred sym c px py
         bvFill sym w z

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

    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           sbTryUnaryTerm sym
             (do ux <- asUnaryBV sym x
                 uy <- asUnaryBV sym y
                 return (UnaryBV.mux sym c ux uy))
             (case inSameBVSemiRing x y of
                Just (Some flv) ->
                  semiRingIte sym (SR.SemiRingBVRepr flv (bvWidth x)) c x y
                Nothing ->
                  mkIte sym c x y)

  bvEq sym x y
    | x == y = return $! truePred sym

    | Just (BVFill _ px) <- asApp x
    , Just (BVFill _ py) <- asApp y =
      eqPred sym px py

    | Just b <- BVD.eq (exprAbsValue x) (exprAbsValue y) = do
      return $! backendPred sym b

    -- Push some equalities under if/then/else
    | SemiRingLiteral _ _ _ <- x
    , Just (BaseIte _ _ c a b) <- asApp y
    = join (itePred sym c <$> bvEq sym x a <*> bvEq sym x b)

    -- Push some equalities under if/then/else
    | Just (BaseIte _ _ c a b) <- asApp x
    , SemiRingLiteral _ _ _ <- y
    = join (itePred sym c <$> bvEq sym a y <*> bvEq sym b y)

    | Just (Some flv) <- inSameBVSemiRing x y
    , let sr = SR.SemiRingBVRepr flv (bvWidth x)
    , (z, x',y') <- WSum.extractCommon (asWeightedSum sr x) (asWeightedSum sr y)
    , not (WSum.isZero sr z) =
        case (WSum.asConstant x', WSum.asConstant y') of
          (Just a, Just b) -> return $! backendPred sym (SR.eq sr a b)
          _ -> do xr <- semiRingSum sym x'
                  yr <- semiRingSum sym y'
                  sbMakeExpr sym $ BaseEq (SR.semiRingBase sr) (min xr yr) (max xr yr)

    | otherwise = do
        ut <- CFG.getOpt (sbUnaryThreshold sym)
        let ?unaryThreshold = fromInteger ut
        if | Just ux <- asUnaryBV sym x
           , Just uy <- asUnaryBV sym y
           -> UnaryBV.eq sym ux uy
           | otherwise
           -> sbMakeExpr sym $ BaseEq (BaseBVRepr (bvWidth x)) (min x y) (max x y)

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
    | Just b <- BVD.ult (exprAbsValue x) (exprAbsValue y) =
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

  bvRol sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) $ rotateLeft (bvWidth x) i n

   | Just n <- asUnsignedBV y
   , n `rem` intValue (bvWidth x) == 0
   = return x

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRol sym x' z

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        y' <- bvUrem sym y wbv
        n' <- bvUrem sym n wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRor sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRol w x y

  bvRor sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y
   = bvLit sym (bvWidth x) $ rotateRight (bvWidth x) i n

   | Just n <- asUnsignedBV y
   , n `rem` intValue (bvWidth x) == 0
   = return x

   | Just (BVRor w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvAdd sym n y
        bvRor sym x' z

   | Just (BVRor w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' y'
        bvRor sym x' z

   | Just (BVRol w x' n) <- asApp x
   , isPow2 (natValue w)
   = do z <- bvSub sym n y
        bvRol sym x' z

   | Just (BVRol w x' n) <- asApp x
   = do wbv <- bvLit sym w (intValue w)
        n' <- bvUrem sym n wbv
        y' <- bvUrem sym y wbv
        z <- bvAdd sym n' =<< bvSub sym wbv y'
        bvRol sym x' z

   | otherwise
   = let w = bvWidth x in
     sbMakeExpr sym $ BVRor w x y

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

  bvXorBits sym x y
    | x == y = bvLit sym (bvWidth x) 0  -- special case: x `xor` x = 0
    | otherwise
    = let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
       in semiRingAdd sym sr x y

  bvAndBits sym x y
    | x == y = return x -- Special case: idempotency of and

    | Just (BVOrBits _ bs) <- asApp x
    , bvOrContains y bs
    = return y -- absorption law

    | Just (BVOrBits _ bs) <- asApp y
    , bvOrContains x bs
    = return x -- absorption law

    | otherwise
    = let sr = SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x)
       in semiRingMul sym sr x y

  -- XOR by the all-1 constant of the bitwise semiring.
  -- This is equivalant to negation
  bvNotBits sym x
    | Just i <- asUnsignedBV x
    = bvLit sym (bvWidth x) $ i `Bits.xor` (maxUnsigned (bvWidth x))

    | otherwise
    = let sr = (SR.SemiRingBVRepr SR.BVBitsRepr (bvWidth x))
       in semiRingSum sym $ WSum.addConstant sr (asWeightedSum sr x) (maxUnsigned (bvWidth x))

  bvOrBits sym x y =
    case (asUnsignedBV x, asUnsignedBV y) of
      (Just xi, Just yi) -> bvLit sym (bvWidth x) (xi Bits..|. yi)
      (Just xi , _)
        | xi == 0 -> return y
        | xi == maxUnsigned (bvWidth x) -> return x
      (_, Just yi)
        | yi == 0 -> return x
        | yi == maxUnsigned (bvWidth x) -> return y

      _
        | x == y
        -> return x -- or is idempotent

        | Just (SemiRingProd xs) <- asApp x
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr xs
        , WSum.prodContains xs y
        -> return y   -- absorption law

        | Just (SemiRingProd ys) <- asApp y
        , SR.SemiRingBVRepr SR.BVBitsRepr _w <- WSum.prodRepr ys
        , WSum.prodContains ys x
        -> return x   -- absorption law

        | Just (BVOrBits w xs) <- asApp x
        , Just (BVOrBits _ ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrUnion xs ys

        | Just (BVOrBits w xs) <- asApp x
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert y xs

        | Just (BVOrBits w ys) <- asApp y
        -> sbMakeExpr sym $ BVOrBits w $ bvOrInsert x ys

        | otherwise
        -> sbMakeExpr sym $ BVOrBits (bvWidth x) $ bvOrInsert x $ bvOrSingleton y

  bvAdd sym x y = semiRingAdd sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvMul sym x y = semiRingMul sym sr x y
     where sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)

  bvNeg sym x
    | Just i <- asSignedBV x = bvLit sym (bvWidth x) (-i)
    | otherwise =
        do ut <- CFG.getOpt (sbUnaryThreshold sym)
           let ?unaryThreshold = fromInteger ut
           sbTryUnaryTerm sym
             (do ux <- asUnaryBV sym x
                 Just (UnaryBV.neg sym ux))
             (do let sr = SR.SemiRingBVRepr SR.BVArithRepr (bvWidth x)
                 scalarMul sym sr (toUnsigned (bvWidth x) (-1)) x)

  bvIsNonzero sym x
    | Just (BaseIte _ _ p t f) <- asApp x
    , isJust (asUnsignedBV t) || isJust (asUnsignedBV f) -- NB, avoid losing possible sharing
    = do  t' <- bvIsNonzero sym t
          f' <- bvIsNonzero sym f
          itePred sym p t' f'
    | Just (BVConcat _ a b) <- asApp x
    , isJust (asUnsignedBV a) || isJust (asUnsignedBV b) -- NB, avoid losing possible sharing
    =  do pa <- bvIsNonzero sym a
          pb <- bvIsNonzero sym b
          orPred sym pa pb
    | Just (BVZext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVSext _ y) <- asApp x =
          bvIsNonzero sym y
    | Just (BVFill _ p) <- asApp x =
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

  bvUdiv = bvBinDivOp quot BVUdiv
  bvUrem sym x y
    | Just True <- BVD.ult (exprAbsValue x) (exprAbsValue y) = return x
    | otherwise = bvBinDivOp rem BVUrem sym x y
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
    | Just True  <- asConstantPred p = return x
    | Just False <- asConstantPred p = return y
    | x == y                         = return x
    | otherwise                      = mkIte sym p x y

  --------------------------------------------------------------------
  -- String operations

  stringEmpty sym si = stringLit sym (stringLitEmpty si)

  stringLit sym s =
    do l <- curProgramLoc sym
       return $! StringExpr s l

  stringEq sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (isJust (testEquality x' y'))
  stringEq sym x y
    = sbMakeExpr sym $ BaseEq (BaseStringRepr (stringInfo x)) x y

  stringIte _sym c x y
    | Just c' <- asConstantPred c
    = if c' then return x else return y
  stringIte _sym _c x y
    | Just x' <- asString x
    , Just y' <- asString y
    , isJust (testEquality x' y')
    = return x
  stringIte sym c x y
    = mkIte sym c x y

  stringIndexOf sym x y k
    | Just x' <- asString x
    , Just y' <- asString y
    , Just k' <- asNat k
    = intLit sym $! stringLitIndexOf x' y' k'
  stringIndexOf sym x y k
    = sbMakeExpr sym $ StringIndexOf x y k

  stringContains sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitContains x' y')
    | Just b <- stringAbsContains (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b
    | otherwise
    = sbMakeExpr sym $ StringContains x y

  stringIsPrefixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsPrefixOf x' y')

    | Just b <- stringAbsIsPrefixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsPrefixOf x y

  stringIsSuffixOf sym x y
    | Just x' <- asString x
    , Just y' <- asString y
    = return $! backendPred sym (stringLitIsSuffixOf x' y')

    | Just b <- stringAbsIsSuffixOf (getAbsValue x) (getAbsValue y)
    = return $! backendPred sym b

    | otherwise
    = sbMakeExpr sym $ StringIsSuffixOf x y

  stringSubstring sym x off len
    | Just x' <- asString x
    , Just off' <- asNat off
    , Just len' <- asNat len
    = stringLit sym $! stringLitSubstring x' off' len'

    | otherwise
    = sbMakeExpr sym $ StringSubstring (stringInfo x) x off len

  stringConcat sym x y
    | Just x' <- asString x, stringLitNull x'
    = return y

    | Just y' <- asString y, stringLitNull y'
    = return x

    | Just x' <- asString x
    , Just y' <- asString y
    = stringLit sym (x' <> y')

    | Just (StringAppend si xs) <- asApp x
    , Just (StringAppend _  ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs ys)

    | Just (StringAppend si xs) <- asApp x
    = sbMakeExpr sym $ StringAppend si (SSeq.append xs (SSeq.singleton si y))

    | Just (StringAppend si ys) <- asApp y
    = sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) ys)

    | otherwise
    = let si = stringInfo x in
      sbMakeExpr sym $ StringAppend si (SSeq.append (SSeq.singleton si x) (SSeq.singleton si y))

  stringLength sym x
    | Just x' <- asString x
    = natLit sym (stringLitLength x')

    | Just (StringAppend _si xs) <- asApp x
    = do let f sm (SSeq.StringSeqLiteral l) = natAdd sym sm =<< natLit sym (stringLitLength l)
             f sm (SSeq.StringSeqTerm t)    = natAdd sym sm =<< sbMakeExpr sym (StringLength t)
         z  <- natLit sym 0
         foldM f z (SSeq.toList xs)

    | otherwise
    = sbMakeExpr sym $ StringLength x

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
        BaseArrayRepr _ ret <- return (exprType base)

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
        m <- AUM.fromAscList ret <$> mapM (\k -> (k,) <$> evalIndex f arrays k) (Set.toAscList s)
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
                  Just (ConstantArray _ _ cns) | v == cns -> AUM.delete ci m
                  _ -> AUM.insert tp ci v m
          sbMakeExpr sym $ ArrayMap idx tp new_map def
        _ -> do
          let idx = fmapFC exprType  i
          let bRepr = exprType v
          let new_map = AUM.singleton bRepr ci v
          sbMakeExpr sym $ ArrayMap idx bRepr new_map arr
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
            AUM.filter (/= default_value) m
          | otherwise = m
    if AUM.null new_map then
      return def_map
     else
      sbMakeExpr sym $ ArrayMap idx_tps baseRepr new_map def_map

  arrayIte sym p x y
       -- Extract all concrete updates out.
     | ArrayMapView mx x' <- viewArrayMap x
     , ArrayMapView my y' <- viewArrayMap y
     , not (AUM.null mx) || not (AUM.null my) = do
       case exprType x of
         BaseArrayRepr idxRepr bRepr -> do
           let both_fn _ u v = baseTypeIte sym p u v
               left_fn idx u = do
                 v <- sbConcreteLookup sym y' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
               right_fn idx v = do
                 u <- sbConcreteLookup sym x' (Just idx) =<< symbolicIndices sym idx
                 both_fn idx u v
           mz <- AUM.mergeM bRepr both_fn left_fn right_fn mx my
           z' <- arrayIte sym p x' y'

           sbMakeExpr sym $ ArrayMap idxRepr bRepr mz z'

     | otherwise = mkIte sym p x y

  arrayEq sym x y
    | x == y =
      return $! truePred sym
    | otherwise =
      sbMakeExpr sym $! BaseEq (exprType x) x y

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
    | SemiRingLiteral SR.SemiRingNatRepr n l <- x = return $! SemiRingLiteral SR.SemiRingIntegerRepr (toInteger n) l
    | Just (IntegerToNat y) <- asApp x = return y
    | otherwise = sbMakeExpr sym (NatToInteger x)

  integerToNat sb x
    | SemiRingLiteral SR.SemiRingIntegerRepr i l <- x
    , 0 <= i
    = return $! SemiRingLiteral SR.SemiRingNatRepr (fromIntegral i) l
    | Just (NatToInteger y) <- asApp x = return y
    | otherwise =
      sbMakeExpr sb (IntegerToNat x)

  integerToReal sym x
    | SemiRingLiteral SR.SemiRingIntegerRepr i l <- x = return $! SemiRingLiteral SR.SemiRingRealRepr (toRational i) l
    | Just (RealToInteger y) <- asApp x = return y
    | otherwise  = sbMakeExpr sym (IntegerToReal x)

  realToInteger sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $! SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
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
         NatEQ   -> sbMakeExpr sym (BVFill (knownNat @1) p)
         NatGT _ -> bvZext sym w =<< sbMakeExpr sym (BVFill (knownNat @1) p)
         NatLT _ -> fail "impossible case in predToBV"

  integerToBV sym xr w
    | SemiRingLiteral SR.SemiRingIntegerRepr i _ <- xr =
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
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (roundAway r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (RoundReal x)

  realFloor sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (exprAbsValue x) =
      sbMakeExpr sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeExpr sym (FloorReal x)

  realCeil sym x
      -- Ground case
    | SemiRingLiteral SR.SemiRingRealRepr r l <- x = return $ SemiRingLiteral SR.SemiRingIntegerRepr (ceiling r) l
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
    return (SemiRingLiteral SR.SemiRingRealRepr r l)

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
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = if denominator yr == 1
         then intEq sym xi =<< intLit sym (numerator yr)
         else return (falsePred sym)

    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = if denominator xr == 1
         then intEq sym yi =<< intLit sym (numerator xr)
         else return (falsePred sym)

    | otherwise
    = semiRingEq sym SR.SemiRingRealRepr (realEq sym) x y

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
    , SemiRingLiteral SR.SemiRingRealRepr yr _ <- y
    = join (intLe sym <$> pure xi <*> intLit sym (floor yr))

      -- if the lower range is a constant, do an integer comparison
      -- with @ceiling(x)@
    | SemiRingLiteral SR.SemiRingRealRepr xr _ <- x
    , Just (IntegerToReal yi) <- asApp y
    = join (intLe sym <$> intLit sym (ceiling xr) <*> pure yi)

    | otherwise
    = semiRingLe sym SR.OrderedSemiRingRealRepr (realLe sym) x y

  realIte sym c x y = semiRingIte sym SR.SemiRingRealRepr c x y

  realNeg sym x = scalarMul sym SR.SemiRingRealRepr (-1) x

  realAdd sym x y = semiRingAdd sym SR.SemiRingRealRepr x y

  realMul sym x y = semiRingMul sym SR.SemiRingRealRepr x y

  realDiv sym x y
    | Just 0 <- asRational x =
      return x
    | Just xd <- asRational x, Just yd <- asRational y, yd /= 0 = do
      realLit sym (xd / yd)
      -- Handle division by a constant.
    | Just yd <- asRational y, yd /= 0 = do
      scalarMul sym SR.SemiRingRealRepr (1 / yd) x
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
      SemiRingLiteral SR.SemiRingRealRepr r _
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
    | otherwise = floatIEEELogicBinOp (BaseEq (exprType x)) sym x y
  floatNe sym x y = notPred sym =<< floatEq sym x y
  floatFpEq sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatFpEq sym x y
  floatFpNe sym x y
    | x == y = return $ falsePred sym
    | otherwise = floatIEEELogicBinOp FloatFpNe sym x y
  floatLe sym x y
    | x == y = notPred sym =<< floatIsNaN sym x
    | otherwise = floatIEEELogicBinOp FloatLe sym x y
  floatLt sym x y
    | x == y = return $ falsePred sym
    | otherwise = floatIEEELogicBinOp FloatLt sym x y
  floatGe sym x y = floatLe sym y x
  floatGt sym x y = floatLt sym y x
  floatIte sym c x y = mkIte sym c x y
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



inSameBVSemiRing :: Expr t (BaseBVType w) -> Expr t (BaseBVType w) -> Maybe (Some SR.BVFlavorRepr)
inSameBVSemiRing x y
  | Just (SemiRingSum s1) <- asApp x
  , Just (SemiRingSum s2) <- asApp y
  , SR.SemiRingBVRepr flv1 _w <- WSum.sumRepr s1
  , SR.SemiRingBVRepr flv2 _w <- WSum.sumRepr s2
  , Just Refl <- testEquality flv1 flv2
  = Just (Some flv1)

  | otherwise
  = Nothing

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
  iFloatNaN _ _ = fail "NaN cannot be represented as a real value."
  iFloatPInf _ _ = fail "+Infinity cannot be represented as a real value."
  iFloatNInf _ _ = fail "-Infinity cannot be represented as a real value."
  iFloatLit sym _ = realLit sym
  iFloatLitSingle sym = realLit sym . toRational
  iFloatLitDouble sym = realLit sym . toRational
  iFloatLitLongDouble sym x =
     case fp80ToRational x of
       Nothing -> fail ("80-bit floating point value does not represent a rational number: " ++ show x)
       Just r  -> realLit sym r
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
  iFloatLitLongDouble sym x =
    iFloatFromBinary sym X86_80FloatRepr
      =<< (bvLit sym knownNat $ fp80ToBits x)

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
  iFloatLitLongDouble sym (X86_80Val e s) = do
    el <- bvLit sym (knownNat @16) $ toInteger e
    sl <- bvLit sym (knownNat @64) $ toInteger s
    fl <- bvConcat sym el sl
    floatFromBinary sym knownRepr fl
    -- n.b. This may not be valid semantically for operations
    -- performed on 80-bit values, but it allows them to be present in
    -- formulas.
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
  definedFn sym fn_name bound_vars result evalFn = do
    l <- curProgramLoc sym
    n <- sbFreshSymFnNonce sym
{-
    let evalFn
          | Just True  <- asConstantPred result = (\_ -> True)
          | Just False <- asConstantPred result = (\_ -> True)
          | otherwise = evalFn0
-}
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
