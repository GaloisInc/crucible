{-|
Module      : Lang.Crucible.Solver.SimpleBuilder
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

Declares the main definitions needed by the SimpleBackend and OnlineBackend
types.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Solver.SimpleBuilder
  ( SymExpr
  , Elt(..)
  , asApp
  , iteSize
  , AppElt
  , appEltId
  , appEltLoc
  , appType
  , eltId
  , eltLoc
  , eltApp
  , appEltApp
  , NonceAppElt
  , nonceEltId
  , nonceEltLoc
  , nonceEltApp
  , nonceAppType
  , BoolElt
  , NatElt
  , IntegerElt
  , RealElt
  , BVElt
  , CplxElt
  , ppElt
  , ppEltTop
  , asConjunction
  , eltMaybeId
    -- * App
  , App(..)
  , traverseApp
    -- * NonceApp
  , NonceApp(..)
    -- * Bound Variable information
  , SimpleBoundVar
  , bvarId
  , bvarLoc
  , bvarName
  , bvarType
  , bvarKind
  , VarKind(..)
  , boundVars
  , ppBoundVar
    -- * Symbolic Function
  , SimpleSymFn(..)
  , SymFnInfo(..)
  , symFnArgTypes
  , symFnReturnType
    -- * SymbolVarBitmap
  , SymbolVarBimap
  , SymbolBinding(..)
  , emptySymbolVarBimap
    -- * SimpleBuilder
  , SimpleBuilder
  , newSimpleBuilder
  , getSymbolVarBimap
  , sbMakeElt
  , sbNonceElt
  , curProgramLoc
  , sbUnaryThreshold
  , sbCacheStartSize
  , sbBVDomainRangeLimit
  , SimpleBuilderPathState(..)
  , pathState
  , IsSimpleBuilderState(..)
  , sbStateManager
  , impliesAssert
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
  , Lang.Crucible.Solver.Interface.bvWidth
  , Lang.Crucible.Solver.Interface.exprType
  , Lang.MATLAB.Utils.Nat.Nat
  ) where

import           Control.Exception (assert)
import           Control.Lens hiding (asIndex)
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import qualified Data.Bits as Bits
import           Data.Foldable
import qualified Data.HashTable.Class as H (toList)
import qualified Data.HashTable.ST.Cuckoo as H
import           Data.Hashable
import           Data.IORef
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.HashTable as PH
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Data.Ratio (numerator, denominator)
import           Data.STRef
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word (Word64)
import           GHC.Generics (Generic)
import qualified Numeric as N
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.MATLAB.Intrinsics.Solver
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Solver.WeightedSum (WeightedSum)
import qualified Lang.Crucible.Solver.WeightedSum as WSum
import           Lang.Crucible.Utils.AbstractDomains
import           Lang.Crucible.Utils.Arithmetic
import qualified Lang.Crucible.Utils.BVDomain as BVD
import           Lang.Crucible.Utils.Complex
import qualified Lang.Crucible.Utils.Hashable as Hash
import           Lang.Crucible.Utils.UnaryBV (UnaryBV)
import qualified Lang.Crucible.Utils.UnaryBV as UnaryBV
import           Lang.MATLAB.Utils.Nat (Nat)

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
-- SimpleBoundVar

-- | The Kind of a bound variable.
data VarKind
  = QuantifierVarKind
    -- ^ A variable appearing in a quantifier.
  | LatchVarKind
    -- ^ A variable appearing as a latch input.
  | UninterpVarKind
    -- ^ A variable appearing in a uninterpreted constant

-- | Information about bound variables.
data SimpleBoundVar t (tp :: BaseType) =
  BVar { bvarId  :: {-# UNPACK #-} !(Nonce t tp)
       , bvarLoc :: !ProgramLoc
       , bvarName :: !SolverSymbol
       , bvarType :: !(BaseTypeRepr tp)
       , bvarKind :: !VarKind
       }

instance TestEquality (SimpleBoundVar t) where
  testEquality x y = testEquality (bvarId x) (bvarId y)

instance OrdF (SimpleBoundVar t) where
  compareF x y = compareF (bvarId x) (bvarId y)

instance Hashable (SimpleBoundVar t tp) where
  hashWithSalt s x = hashWithSalt s (bvarId x)

instance HashableF (SimpleBoundVar t) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- NonceApp

-- | These are applications that may reference nonces.
data NonceApp t e tp where
  Forall :: !(SimpleBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType
  Exists :: !(SimpleBoundVar t tp)
         -> !(e BaseBoolType)
         -> NonceApp t e BaseBoolType

  -- Create an array from a function
  ArrayFromFn :: !(SimpleSymFn t (idx ::> itp) ret)
              -> NonceApp t e (BaseArrayType (idx ::> itp) ret)

  -- Create an array by mapping over one or more existing arrays.
  MapOverArrays :: !(SimpleSymFn t (ctx::>d) r)
                -> !(Ctx.Assignment BaseTypeRepr (idx ::> itp))
                -> !(Ctx.Assignment (ArrayResultWrapper e (idx ::> itp)) (ctx::>d))
                -> NonceApp t e (BaseArrayType (idx ::> itp) r)

  -- This returns true if all the indices satisfying the given predicate equal true.
  ArrayTrueOnEntries
    :: !(SimpleSymFn t (idx ::> itp) BaseBoolType)
    -> !(e (BaseArrayType (idx ::> itp) BaseBoolType))
    -> NonceApp t e BaseBoolType

  -- Apply a function to some arguments
  FnApp :: !(SimpleSymFn t args ret)
        -> !(Ctx.Assignment e args)
        -> NonceApp t e ret

------------------------------------------------------------------------
-- App

data App e (tp :: BaseType) where

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
  -- Basic arithmetic operations

  RealEq :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseBoolType
  RealLe :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseBoolType
  RealIsInteger :: !(e BaseRealType) -> App e BaseBoolType


  -- This represents a real number as a weighted sum of other expressions plus
  -- an offset.
  RealSum :: {-# UNPACK #-} !(WeightedSum Rational e BaseRealType)
          -> App e BaseRealType

  -- Multiplication of two real numbers
  --
  -- The SimpleBuilder should maintain the invariant that neither value is
  -- a real constant, and hence this denotes a non-linear expression.
  -- Multiplications by scalars should use the 'RealSum' constructor.
  RealMul :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType

  RealIte :: !(e BaseBoolType)
          -> !(e BaseRealType)
          -> !(e BaseRealType)
          -> App e BaseRealType

  -- This does natural number division rounded to zero.
  --
  -- NatDiv x y is equivalent to intToNat (floor (RealDiv (natToReal x) (natToReal y)))
  NatDiv :: !(e BaseNatType)  -> !(e BaseNatType) -> App e BaseNatType

  RealDiv :: !(e BaseRealType) -> !(e BaseRealType) -> App e BaseRealType

  -- @IntMod x y@ denotes the value of @x - y * floor(x ./ y)@.
  -- Is not defined when @y@ is zero.
  IntMod :: !(e BaseIntegerType)  -> !(e BaseNatType) -> App e BaseNatType

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
            => !Int -- Index of bit to test
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

  BVTrunc :: (1 <= r, r+1 <= w)
          => !(NatRepr r)
          -> !(e (BaseBVType w))
          -> App e (BaseBVType r)

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

  BVToInteger   :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType
  SBVToInteger  :: (1 <= w) => !(e (BaseBVType w)) -> App e BaseIntegerType

  -- Converts integer to signed bitvector (numbers are rounded to nearest representable result).
  IntegerToSBV :: (1 <= w) => !(e BaseIntegerType) -> NatRepr w -> App e (BaseBVType w)
  -- Converts integer to unsigned bitvector (numbers are rounded to nearest represented result).
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

data NonceAppElt t tp
   = NonceAppEltCtor { nonceEltId  :: {-# UNPACK #-} !(Nonce t tp)
                     , nonceEltLoc :: !ProgramLoc
                     , nonceEltApp :: !(NonceApp t (Elt t) tp)
                     , nonceEltAbsValue :: !(AbstractValue tp)
                     }

data AppElt t tp
   = AppEltCtor { appEltId  :: {-# UNPACK #-} !(Nonce t tp)
                , appEltLoc :: !ProgramLoc
                , appEltApp :: !(App (Elt t) tp)
                , appEltAbsValue :: !(AbstractValue tp)
                }

------------------------------------------------------------------------
-- Elt

-- | An expression for the SimpleBuilder backend.
--
-- We call it an 'Elt', because our expressions use explicit sharing and thus an
-- 'Elt' is an element of a DAG that may be shared.
data Elt t (tp :: BaseType) where
  NatElt :: {-# UNPACK #-} !Nat -> !ProgramLoc -> Elt t BaseNatType
  IntElt :: !Integer -> !ProgramLoc -> Elt t BaseIntegerType
  RatElt :: {-# UNPACK #-} !Rational -> !ProgramLoc -> Elt t BaseRealType
  BVElt  :: (1 <= w) => !(NatRepr w) -> !Integer -> !ProgramLoc -> Elt t (BaseBVType w)
  -- Application
  AppElt :: {-# UNPACK #-} !(AppElt t tp) -> Elt t tp
  -- An atomic predicate
  NonceAppElt :: {-# UNPACK #-} !(NonceAppElt t tp) -> Elt t tp
  -- A bound variable
  BoundVarElt :: !(SimpleBoundVar t tp) -> Elt t tp

{-# INLINE asApp #-}
asApp :: Elt t tp -> Maybe (App (Elt t) tp)
asApp (AppElt a) = Just (appEltApp a)
asApp _ = Nothing

{-# INLINE asNonceApp #-}
asNonceApp :: Elt t tp -> Maybe (NonceApp t (Elt t) tp)
asNonceApp (NonceAppElt a) = Just (nonceEltApp a)
asNonceApp _ = Nothing

eltId  :: AppElt t tp -> Nonce t tp
eltId = appEltId

eltApp :: AppElt t tp -> App (Elt t) tp
eltApp = appEltApp

eltLoc :: Elt t tp -> ProgramLoc
eltLoc (NatElt _ l) = l
eltLoc (IntElt _ l) = l
eltLoc (RatElt _ l) = l
eltLoc (BVElt _ _ l) = l
eltLoc (NonceAppElt a)  = nonceEltLoc a
eltLoc (AppElt a)   = appEltLoc a
eltLoc (BoundVarElt v) = bvarLoc v

mkElt :: Nonce t tp
      -> ProgramLoc
      -> App (Elt t) tp
      -> AbstractValue tp
      -> Elt t tp
mkElt n l a v = AppElt $ AppEltCtor { appEltId  = n
                                    , appEltLoc = l
                                    , appEltApp = a
                                    , appEltAbsValue = v
                                    }

type BoolElt t = Elt t BaseBoolType
type NatElt  t = Elt t BaseNatType
type BVElt t n = Elt t (BaseBVType n)
type IntegerElt t = Elt t BaseIntegerType
type RealElt t = Elt t BaseRealType
type CplxElt t = Elt t BaseComplexType

iteSize :: Elt t tp -> Integer
iteSize e =
  case asApp e of
    Just (BVIte _ 0  _ _ _) -> error "iteSize given bad BVIte"
    Just (BVIte _ sz _ _ _) -> sz
    _ -> 0

instance IsExpr (Elt t) where
  asNat (NatElt n _) = Just n
  asNat _ = Nothing

  asInteger (IntElt n _) = Just n
  asInteger _ = Nothing

  asRational (RatElt r _) = Just r
  asRational _ = Nothing

  asComplex e
    | Just (Cplx c) <- asApp e = traverse asRational c
    | otherwise = Nothing

  exprType NatElt{} = knownRepr
  exprType IntElt{} = knownRepr
  exprType RatElt{} = knownRepr
  exprType (BVElt w _ _) = BaseBVRepr w
  exprType (NonceAppElt e)  = nonceAppType (nonceEltApp e)
  exprType (AppElt e) = appType (appEltApp e)
  exprType (BoundVarElt i) = bvarType i

  asUnsignedBV (BVElt _ i _) = Just i
  asUnsignedBV _ = Nothing

  asSignedBV x = toSigned (bvWidth x) <$> asUnsignedBV x

  asConstantArray (asApp -> Just (ConstantArray _ _ def)) = Just def
  asConstantArray _ = Nothing

  printSymExpr = pretty


------------------------------------------------------------------------
-- SimpleSymFn

-- | This describes information about an undefined or defined function.
data SymFnInfo t args ret
   = UninterpFnInfo !(Ctx.Assignment BaseTypeRepr args)
                    !(BaseTypeRepr ret)
     -- ^ Information about the argument type and return type of an uninterpreted function.
   | DefinedFnInfo !(Ctx.Assignment (SimpleBoundVar t) args)
                   !(Elt t ret)
                   !(Ctx.Assignment (Elt t) args -> Bool)
     -- ^ Information about a defined function.
     -- Includes bound variables, expression associated to a defined function, and
     -- an assignment for determining when to instantiate values.
   | MatlabSolverFnInfo !(MatlabSolverFn (Elt t) args ret)
                        !(Ctx.Assignment (SimpleBoundVar t) args)
                        !(Elt t ret)
     -- ^ This is a function that corresponds to a matlab solver.  It includes the
     -- definition as a simplebuilder elt to enable export to other solvers.

-- | This represents a symbolic function in the simulator.
data SimpleSymFn t (args :: Ctx BaseType) (ret :: BaseType)
   = SimpleSymFn { symFnId :: !(Nonce t (args ::> ret))
                 -- /\ A unique identifier for the function
                 , symFnName :: !SolverSymbol
                 -- /\ Name of the function
                 , symFnInfo :: !(SymFnInfo t args ret)
                 -- /\ Information about function
                 , symFnLoc  :: !ProgramLoc
                 -- /\ Location where function was defined.
                 }

instance Show (SimpleSymFn t args ret) where
  show f | symFnName f == emptySymbol = "f" ++ show (indexValue (symFnId f))
         | otherwise                  = show (symFnName f)


symFnArgTypes :: SimpleSymFn t args ret -> Ctx.Assignment BaseTypeRepr args
symFnArgTypes f =
  case symFnInfo f of
    UninterpFnInfo tps _ -> tps
    DefinedFnInfo vars _ _ -> fmapFC bvarType vars
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverArgTypes fn_id

symFnReturnType :: SimpleSymFn t args ret -> BaseTypeRepr ret
symFnReturnType f =
  case symFnInfo f of
    UninterpFnInfo _ tp -> tp
    DefinedFnInfo _ r _ -> exprType r
    MatlabSolverFnInfo fn_id _ _ -> matlabSolverReturnType fn_id

-- | Return solver function associated with SimpleSymFn if any.
asMatlabSolverFn :: SimpleSymFn t args ret -> Maybe (MatlabSolverFn (Elt t) args ret)
asMatlabSolverFn f
  | MatlabSolverFnInfo g _ _ <- symFnInfo f = Just g
  | otherwise = Nothing



instance Hashable (SimpleSymFn t args tp) where
  hashWithSalt s f = s `hashWithSalt` symFnId f

testSimpleSymFnEq :: SimpleSymFn t a1 r1
                  -> SimpleSymFn t a2 r2
                  -> Maybe ((a1::>r1) :~: (a2::>r2))
testSimpleSymFnEq f g = testEquality (symFnId f) (symFnId g)

------------------------------------------------------------------------
-- asConjunction

-- | View a boolean 'Elt' as a conjunction.
asConjunction :: BoolElt t -> [BoolElt t]
asConjunction e = asConjunction' [e] Set.empty []

asConjunction' :: [BoolElt t]
               -> Set (BoolElt t) -- ^ Set of elements already visited.
               -> [BoolElt t] -- ^ List of elements.
               -> [BoolElt t]
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

    RealEq{} -> knownRepr
    RealLe{} -> knownRepr
    RealIsInteger{} -> knownRepr
    BVTestBit{} -> knownRepr
    BVEq{}    -> knownRepr
    BVSlt{}   -> knownRepr
    BVUlt{}   -> knownRepr
    ArrayEq{} -> knownRepr

    NatDiv{} -> knownRepr
    IntMod{} -> knownRepr

    RealSum{} -> knownRepr
    RealMul{} -> knownRepr
    RealIte{} -> knownRepr
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
    BVZext  w _ -> BaseBVRepr w
    BVSext  w _ -> BaseBVRepr w
    BVTrunc w _ -> BaseBVRepr w
    BVBitNot w _ -> BaseBVRepr w
    BVBitAnd w _ _ -> BaseBVRepr w
    BVBitOr  w _ _ -> BaseBVRepr w
    BVBitXor w _ _ -> BaseBVRepr w

    ArrayMap      idx b _ _ -> BaseArrayRepr idx b
    ConstantArray idx b _   -> BaseArrayRepr idx b
    MuxArray idx b _ _ _    -> BaseArrayRepr idx b
    SelectArray b _ _       -> b
    UpdateArray b itp _ _ _     -> BaseArrayRepr itp b

    NatToInteger{} -> knownRepr
    IntegerToReal{} -> knownRepr
    BVToInteger{} -> knownRepr
    SBVToInteger{} -> knownRepr

    IntegerToNat{} -> knownRepr
    IntegerToSBV _ w -> BaseBVRepr w
    IntegerToBV _ w -> BaseBVRepr w

    RealToInteger{} -> knownRepr

    Cplx{} -> knownRepr
    RealPart{} -> knownRepr
    ImagPart{} -> knownRepr

    StructCtor flds _     -> BaseStructRepr flds
    StructField _ _ tp    -> tp
    StructIte  flds _ _ _ -> BaseStructRepr flds

------------------------------------------------------------------------
-- EltAllocator

-- | EltAllocator provides an interface for creating expressions from
-- an applications.
data EltAllocator t
   = EltAllocator { appElt  :: forall tp
                            .  ProgramLoc
                            -> App (Elt t) tp
                            -> AbstractValue tp
                            -> IO (Elt t tp)
                  , nonceElt :: forall tp
                             .  ProgramLoc
                             -> NonceApp t (Elt t) tp
                             -> AbstractValue tp
                             -> IO (Elt t tp)
                  }

------------------------------------------------------------------------
-- SimpleBuilderPathState

data SimpleBuilderPathState st = SBPS { _pathState :: !st
                                      , sbpsLoc :: !ProgramLoc
                                      }

pathState :: Simple Lens (SimpleBuilderPathState st) st
pathState = lens _pathState (\s v -> s { _pathState = v })

instance HasProgramLoc (SimpleBuilderPathState st) where
  setProgramLoc l s = s { sbpsLoc = l }

------------------------------------------------------------------------
-- SymbolVarBimap

-- | A bijective map between vars and their canonical name for printing
-- purposes.
type SymbolVarBimap t = Bimap SolverSymbol (SymbolBinding t)

-- | This describes what a given SolverSymbol is associated with.
data SymbolBinding t
   = forall tp . VarSymbolBinding !(SimpleBoundVar t tp)
     -- ^ Solver
   | forall args ret . FnSymbolBinding  !(SimpleSymFn t args ret)

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
emptySymbolVarBimap = Bimap.empty

------------------------------------------------------------------------
-- MatlabSolverFn

data MatlabFnWrapper t c where
   MatlabFnWrapper :: !(MatlabSolverFn (Elt t) a r) -> MatlabFnWrapper t (a::> r)

instance TestEquality (MatlabFnWrapper t) where
  testEquality (MatlabFnWrapper f) (MatlabFnWrapper g) = do
    Refl <- testSolverFnEq f g
    return Refl


instance HashableF (MatlabFnWrapper t) where
  hashWithSaltF s (MatlabFnWrapper f) = hashWithSalt s f

data SimpleSymFnWrapper t c
   = forall a r . (c ~ (a ::> r)) => SimpleSymFnWrapper (SimpleSymFn t a r)

------------------------------------------------------------------------
-- SimpleBuilder

-- | Cache for storing dag terms.
data SimpleBuilder t (st :: * -> *)
   = SB { sbTrue  :: !(BoolElt t)
        , sbFalse :: !(BoolElt t)
          -- | Constant zero.
        , sbZero  :: !(RealElt t)
          -- | Flag used to tell the backend whether to evaluate
          -- ground rational values as double precision floats when
          -- a function cannot be evaluated as a rational.
        , sbFloatReduce :: !Bool
          -- | The maximum number of distinct values a term may have and use the
          -- unary representation.
        , _sbUnaryThreshold :: !Int
          -- | The maximum number of distinct ranges in a BVDomain expression.
        , _sbBVDomainRangeLimit :: !Int
          -- | The starting size when building a new cache
        , _sbCacheStartSize :: !Int
          -- | Counter to generate new unique identifiers for elements and functions.
        , eltCounter :: !(NonceGenerator IO t)
          -- | Reference to current allocator for expressions.
        , curAllocator :: !(IORef (EltAllocator t))
          -- | Additional state maintained by the state manager
        , sbStateManager :: !(IORef (st t))
          -- | Current location in program.
        , sbProgramLoc  :: !(IORef ProgramLoc)
          -- | Provides a bi-jective mapping between names and
          -- bound variables.
        , sbVarBindings :: !(IORef (SymbolVarBimap t))
          -- | Provides access to typeclass instance for @st@.
        , sbStateManagerIsBoolSolver :: forall x. (IsSimpleBuilderState st => x) -> x
          -- | Cache for Matlab functions
        , sbMatlabFnCache
          :: !(PH.HashTable RealWorld (MatlabFnWrapper t) (SimpleSymFnWrapper t))
        }

-- | Typeclass that simple build state should implement.
class IsSimpleBuilderState st where
  ----------------------------------------------------------------------
  -- Assertions

  -- | Add an assertion to the current state, and record a proof obligation.
  --
  -- This may call fail in the monad if the list of assertions is unsatisfiable.
  sbAddAssertion :: SimpleBuilder t st -> BoolElt t -> SimErrorReason -> IO ()

  -- | Add an assumption to the current state.
  sbAddAssumption :: SimpleBuilder t st -> BoolElt t -> IO ()

  -- | Return a list of all the assertions
  sbAssertionsBetween :: st t -- ^ Old path state
                      -> st t -- ^ New path state
                      -> Seq (Assertion (BoolElt t))

  -- | Return a list of all the assertions
  sbAllAssertions :: SimpleBuilder t st -> IO (BoolElt t)

  sbAppendAssertions :: SimpleBuilder t st -> Seq (Assertion (BoolElt t)) -> IO ()

  -- | Get the collection of proof obligations
  sbGetProofObligations :: SimpleBuilder t st -> IO (Seq (Seq (BoolElt t), Assertion (BoolElt t)))

  -- | Set the collection of proof obligations
  sbSetProofObligations :: SimpleBuilder t st -> Seq (Seq (BoolElt t), Assertion (BoolElt t)) -> IO ()

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Given a Boolean predicate corresponding to a brnahc, this decides
  -- what the next course of action should be for the branch.
  sbEvalBranch :: SimpleBuilder t st
               -> BoolElt t -- Predicate to branch on.
               -> IO (BranchResult (SimpleBuilder t st))

  -- | Push a branch predicate to the current state.
  sbPushBranchPred :: SimpleBuilder t st -> BoolElt t -> IO ()

  -- | Backtrack to a previous state.
  sbBacktrackToState :: SimpleBuilder t st
                     -> SimpleBuilderPathState (st t)
                     -> IO ()

  -- | Backtrack to a previous state.
  sbSwitchToState :: SimpleBuilder t st
                  -> SimpleBuilderPathState (st t)
                  -> SimpleBuilderPathState (st t)
                  -> IO ()

type instance SymFn (SimpleBuilder t st) = SimpleSymFn t
type instance SymPathState (SimpleBuilder t st) = SimpleBuilderPathState (st t)
type instance SymExpr (SimpleBuilder t st) = Elt t
type instance BoundVar (SimpleBuilder t st) = SimpleBoundVar t

-- | The maximum number of distinct values a term may have and use the
-- unary representation.
sbUnaryThreshold :: Simple Lens (SimpleBuilder t st) Int
sbUnaryThreshold = lens _sbUnaryThreshold (\s v -> s { _sbUnaryThreshold = v })

sbCacheStartSize :: Simple Lens (SimpleBuilder t st) Int
sbCacheStartSize = lens _sbCacheStartSize (\s v -> s { _sbCacheStartSize = v })

-- | The maximum number of distinct ranges in a BVDomain expression.
sbBVDomainRangeLimit :: Simple Lens (SimpleBuilder t st) Int
sbBVDomainRangeLimit = lens _sbBVDomainRangeLimit (\s v -> s { _sbBVDomainRangeLimit = v })

sbBVDomainParams :: SimpleBuilder t st -> BVD.BVDomainParams
sbBVDomainParams sym = BVD.DP { BVD.rangeLimit = sym^.sbBVDomainRangeLimit
                              }

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
    BaseComplexRepr -> "c"
    BaseArrayRepr _ _ -> "a"
    BaseStructRepr _ -> "struct"

-- | Either a argument or text or text
type PrettyArg (e :: BaseType -> *) = Either (Some e) Text

eltPrettyArg :: e tp -> PrettyArg e
eltPrettyArg e = Left $! Some e

eltPrettyIndices :: Ctx.Assignment e ctx -> [PrettyArg e]
eltPrettyIndices = toListFC eltPrettyArg

stringPrettyArg :: String -> PrettyArg e
stringPrettyArg x = Right $! Text.pack x

showPrettyArg :: Show a => a -> PrettyArg e
showPrettyArg x = stringPrettyArg $! show x

type PrettyApp e = (Text, [PrettyArg e])

prettyApp :: Text -> [PrettyArg e] -> PrettyApp e
prettyApp nm args = (nm, args)

ppNonceApp :: forall m t e tp
           . Applicative m
           => (forall ctx r . SimpleSymFn t ctx r -> m (PrettyArg e))
           -> NonceApp t e tp
           -> m (PrettyApp e)
ppNonceApp ppFn a0 = do
  case a0 of
    Forall v x -> pure $ prettyApp "forall" [ stringPrettyArg (ppBoundVar v), eltPrettyArg x ]
    Exists v x -> pure $ prettyApp "exists" [ stringPrettyArg (ppBoundVar v), eltPrettyArg x ]
    ArrayFromFn f -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayFromFn" [ f_nm ]
    MapOverArrays f _ args -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "mapArray" (f_nm : arg_nms)
            arg_nms = toListFC (\(ArrayResultWrapper a) -> eltPrettyArg a) args
    ArrayTrueOnEntries f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "arrayTrueOnEntries" [ f_nm, a_nm ]
            a_nm = eltPrettyArg a
    FnApp f a -> resolve <$> ppFn f
      where resolve f_nm = prettyApp "apply" (f_nm : toListFC eltPrettyArg a)

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
      ppSExpr f l = prettyApp f (eltPrettyArg <$> l)

      ppITE :: Text -> e BaseBoolType -> e x -> e x -> PrettyApp e
      ppITE nm c x y = prettyApp nm [eltPrettyArg c, eltPrettyArg x, eltPrettyArg y]

  case a0 of
    TrueBool    -> prettyApp "true" []
    FalseBool   -> prettyApp "false" []
    NotBool x   -> ppSExpr "boolNot" [x]
    AndBool x y -> ppSExpr "boolAnd" [x, y]
    XorBool x y -> ppSExpr "boolXor" [x, y]
    IteBool x y z -> ppITE "boolIte" x y z

    RealEq x y -> ppSExpr "realEq" [x, y]
    RealLe x y -> ppSExpr "realLe" [x, y]
    RealIsInteger x -> ppSExpr "isInteger" [x]
    BVTestBit i x   -> prettyApp "testBit"  [eltPrettyArg x, showPrettyArg i]
    BVEq  x y   -> ppSExpr "bvEq" [x, y]
    BVUlt x y -> ppSExpr "bvUlt" [x, y]
    BVSlt x y -> ppSExpr "bvSlt" [x, y]
    ArrayEq x y -> ppSExpr "arrayEq" [x, y]

    NatDiv x y -> ppSExpr "natDiv" [x, y]

    IntMod x y -> prettyApp "intMod" [eltPrettyArg x, eltPrettyArg y]

    RealMul x y -> ppSExpr "realMul" [x, y]
    RealSum s -> prettyApp "realSum" (WSum.eval (++) ppEntry ppConstant s)
      where ppConstant 0 = []
            ppConstant c = [ stringPrettyArg (ppRat c)]
            ppEntry 1 e = [ eltPrettyArg e ]
            ppEntry sm e = [ stringPrettyArg (ppRat sm ++ "*"), eltPrettyArg e ]
            ppRat r | d == 1 = show n
                    | otherwise = "(" ++ show n ++ "/" ++ show d ++ ")"
              where n = numerator r
                    d = denominator r
    RealIte x y z -> ppITE "realIte" x y z
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
            go (k,v) = [ eltPrettyArg v, showPrettyArg k ]
    BVConcat _ x y -> prettyApp "bvConcat" [eltPrettyArg x, eltPrettyArg y]
    BVSelect idx n x -> prettyApp "bvSelect" [showPrettyArg idx, showPrettyArg n, eltPrettyArg x]
    BVNeg  _ x   -> ppSExpr "bvNeg" [x]
    BVAdd  _ x y -> ppSExpr "bvAdd" [x, y]
{-
    BVSum s -> prettyApp "bvSum" (WSum.eval (++) ppEntry ppConstant s)
      where ppConstant 0 = []
            ppConstant c = [ showPrettyArg c ]
            ppEntry 1 e = [ eltPrettyArg e ]
            ppEntry sm e = [ stringPrettyArg (show sm ++ "*"), eltPrettyArg e ]
-}
    BVMul  _ x y -> ppSExpr "bvMul" [x, y]
    BVUdiv _ x y -> ppSExpr "bvUdiv" [x, y]
    BVUrem _ x y -> ppSExpr "bvUrem" [x, y]
    BVSdiv _ x y -> ppSExpr "bvSdiv" [x, y]
    BVSrem _ x y -> ppSExpr "bvSrem" [x, y]

    BVIte _ _ c x y -> ppITE "bvIte" c x y

    BVShl  _ x y -> ppSExpr "bvShl" [x, y]
    BVLshr _ x y -> ppSExpr "bvLshr" [x, y]
    BVAshr _ x y -> ppSExpr "bvAshr" [x, y]

    BVZext w x -> prettyApp "bvZext"   [showPrettyArg w, eltPrettyArg x]
    BVSext w x -> prettyApp "bvSext"   [showPrettyArg w, eltPrettyArg x]
    BVTrunc w x -> prettyApp "bvTrunc" [showPrettyArg w, eltPrettyArg x]

    BVBitNot _ x   -> ppSExpr "bvNot" [x]
    BVBitAnd _ x y -> ppSExpr "bvAnd" [x, y]
    BVBitOr  _ x y -> ppSExpr "bvOr"  [x, y]
    BVBitXor _ x y -> ppSExpr "bvXor" [x, y]

    -------------------------------------
    -- Arrays

    ArrayMap _ _ m d ->
        prettyApp "arrayMap" (Map.foldrWithKey ppEntry [eltPrettyArg d] (Hash.hashedMap m))
      where ppEntry k e l = showPrettyArg k : eltPrettyArg e : l
    ConstantArray _ _ v ->
      prettyApp "constArray" [eltPrettyArg v]
    MuxArray _ _ p x y ->
      prettyApp "muxArray" [eltPrettyArg p, eltPrettyArg x, eltPrettyArg y]
    SelectArray _ a i ->
      prettyApp "select" (eltPrettyArg a : eltPrettyIndices i)
    UpdateArray _ _ a i v ->
      prettyApp "update" ([eltPrettyArg a] ++ eltPrettyIndices i ++ [eltPrettyArg v])

    ------------------------------------------------------------------------
    -- Conversions.

    NatToInteger x  -> ppSExpr "natToInteger" [x]
    IntegerToReal x -> ppSExpr "integerToReal" [x]
    BVToInteger  x  -> ppSExpr "bvToInteger" [x]
    SBVToInteger x  -> ppSExpr "sbvToInteger" [x]

    RoundReal x -> ppSExpr "round" [x]
    FloorReal x -> ppSExpr "floor" [x]
    CeilReal  x -> ppSExpr "ceil"  [x]

    IntegerToNat x   -> ppSExpr "integerToNat" [x]
    IntegerToSBV x w -> prettyApp "integerToSBV" [eltPrettyArg x, showPrettyArg w]
    IntegerToBV x w -> prettyApp "integerToBV" [eltPrettyArg x, showPrettyArg w]

    RealToInteger x   -> ppSExpr "realToInteger" [x]

    ------------------------------------------------------------------------
    -- Complex operations

    Cplx (r :+ i) -> ppSExpr "complex" [r, i]
    RealPart x -> ppSExpr "realPart" [x]
    ImagPart x -> ppSExpr "imagPart" [x]

    ------------------------------------------------------------------------
    -- SymStruct

    StructCtor _ flds -> prettyApp "struct" (toListFC eltPrettyArg flds)
    StructField s idx _ ->
      prettyApp "field" [eltPrettyArg s, showPrettyArg idx]
    StructIte _ c x y -> ppITE "ite" c x y

------------------------------------------------------------------------
-- NonceApp operations

instance Eq (NonceApp t (Elt t) tp) where
  x == y = isJust (testEquality x y)

instance TestEquality (NonceApp t (Elt t)) where
  testEquality =
    $(structuralTypeEquality [t|NonceApp|]
           [ (DataArg 0 `TypeApp` AnyType, [|testEquality|])
           , (DataArg 1 `TypeApp` AnyType, [|testEquality|])
           , ( ConType [t|SimpleBoundVar|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           , ( ConType [t|SimpleSymFn|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
              , [|testSimpleSymFnEq|]
              )
           , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
             , [|testEquality|]
             )
           ]
          )

instance HashableF (NonceApp t (Elt t)) where
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

instance Ord (Dummy tp) where
  compare _ _ = EQ

instance HashableF Dummy where
  hashWithSaltF _ _ = 0

instance FoldableFC App where
  foldMapFC f0 t = getConst (traverseApp (g f0) t)
    where g :: (f tp -> a) -> f tp -> Const a (Dummy tp)
          g f v = Const (f v)


traverseApp :: (Applicative m, Ord (f BaseRealType), Eq (f BaseBoolType), HashableF f)
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
    , ( ConType [t|WeightedSum|] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
      , [| WSum.traverseVars
         |]
      )
    ,  ( ConType [t|Hash.Map |] `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType `TypeApp` AnyType
       , [| Hash.traverseHashedMap |]
       )
    , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
      , [|traverseFC|]
      )
    ]
   )

------------------------------------------------------------------------
-- Elt operations

{-# INLINE compareElt #-}
compareElt :: Elt t x -> Elt t y -> OrderingF x y
compareElt (NatElt x _) (NatElt y _) = fromOrdering (compare x y)
compareElt NatElt{} _ = LTF
compareElt _ NatElt{} = GTF

compareElt (IntElt x _) (IntElt y _) = fromOrdering (compare x y)
compareElt IntElt{} _ = LTF
compareElt _ IntElt{} = GTF

compareElt (RatElt x _) (RatElt y _) = fromOrdering (compare x y)
compareElt RatElt{} _ = LTF
compareElt _ RatElt{} = GTF

compareElt (BVElt wx x _) (BVElt wy y _) =
  case compareF wx wy of
    LTF -> LTF
    EQF -> fromOrdering (compare x y)
    GTF -> GTF
compareElt BVElt{} _ = LTF
compareElt _ BVElt{} = GTF

compareElt (NonceAppElt x) (NonceAppElt y) = compareF x y
compareElt NonceAppElt{} _ = LTF
compareElt _ NonceAppElt{} = GTF

compareElt (AppElt x) (AppElt y) = compareF (appEltId x) (appEltId y)
compareElt AppElt{} _ = LTF
compareElt _ AppElt{} = GTF

compareElt (BoundVarElt x) (BoundVarElt y) = compareF x y

instance TestEquality (NonceAppElt t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (NonceAppElt t)  where
  compareF x y = compareF (nonceEltId x) (nonceEltId y)

instance Eq (NonceAppElt t tp) where
  x == y = isJust (testEquality x y)

instance Ord (NonceAppElt t tp) where
  compare x y = toOrdering (compareF x y)

instance TestEquality (Elt t) where
  testEquality x y =
    case compareF x y of
      EQF -> Just Refl
      _ -> Nothing

instance OrdF (Elt t)  where
  compareF = compareElt

instance Eq (Elt t tp) where
  x == y = isJust (testEquality x y)

instance Ord (Elt t tp) where
  compare x y = toOrdering (compareF x y)

instance Hashable (Elt t tp) where
  hashWithSalt s (NatElt n _)    = hashWithSalt (hashWithSalt s (0::Int)) n
  hashWithSalt s (IntElt n _)    = hashWithSalt (hashWithSalt s (1::Int)) n
  hashWithSalt s (RatElt r _)    = hashWithSalt (hashWithSalt s (2::Int)) r
  hashWithSalt s (BVElt w x _) =
    s `hashWithSalt` (3::Int)
      `hashWithSalt` w
      `hashWithSalt` x
  hashWithSalt s (AppElt x)      = hashWithSalt (hashWithSalt s (4::Int)) (appEltId x)
  hashWithSalt s (NonceAppElt x)     = s `hashWithSalt` (5::Int) `hashWithSalt` (nonceEltId x)
  hashWithSalt s (BoundVarElt x) = hashWithSalt (hashWithSalt s (6::Int)) x

instance PH.HashableF (Elt t) where
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

countOccurrences :: Elt t tp -> Map.Map PPIndex Int
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

countOccurrences' :: forall t tp s . OccurrenceTable s -> Elt t tp -> ST s ()
countOccurrences' visited (RatElt r _) = do
  incOccurrence visited (RatPPIndex r) $
    return ()
countOccurrences' visited (AppElt e) = do
  let idx = ExprPPIndex (indexValue (appEltId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (appEltApp e)
countOccurrences' visited (NonceAppElt e) = do
  let idx = ExprPPIndex (indexValue (nonceEltId e))
  incOccurrence visited idx $ do
    traverseFC_ (countOccurrences' visited) (nonceEltApp e)
countOccurrences' _ _ = return ()

------------------------------------------------------------------------
-- boundVars

type BoundVarMap s t = H.HashTable s PPIndex (Set (Some (SimpleBoundVar t)))

cache :: (Eq k, Hashable k) => H.HashTable s k r -> k -> ST s r -> ST s r
cache h k m = do
  mr <- H.lookup h k
  case mr of
    Just r -> return r
    Nothing -> do
      r <- m
      H.insert h k r
      return r


boundVars :: Elt t tp -> ST s (BoundVarMap s t)
boundVars e0 = do
  visited <- H.new
  _ <- boundVars' visited e0
  return visited

boundVars' :: BoundVarMap s t
           -> Elt t tp
           -> ST s (Set (Some (SimpleBoundVar t)))
boundVars' visited (AppElt e) = do
  let idx = indexValue (appEltId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (appEltApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' visited (NonceAppElt e) = do
  let idx = indexValue (nonceEltId e)
  cache visited (ExprPPIndex idx) $ do
    sums <- sequence (toListFC (boundVars' visited) (nonceEltApp e))
    return $ foldl' Set.union Set.empty sums
boundVars' _ (BoundVarElt v)
  | QuantifierVarKind <- bvarKind v = return (Set.singleton (Some v))
boundVars' _ _ = return Set.empty

------------------------------------------------------------------------
-- Pretty printing

ppVar :: String -> Nonce t tp -> BaseTypeRepr tp -> String
ppVar pr i tp = pr ++ show (indexValue i) ++ ":" ++ ppVarTypeCode tp

instance Show (Elt t tp) where
  show = show . pretty

instance Pretty (Elt t tp) where
  pretty = ppElt

ppBoundVar :: SimpleBoundVar t tp -> String
ppBoundVar v =
  case bvarKind v of
    QuantifierVarKind -> ppVar "?" (bvarId  v) (bvarType v)
    LatchVarKind   -> ppVar "l" (bvarId  v) (bvarType v)
    UninterpVarKind -> ppVar "c" (bvarId  v) (bvarType v)


-- | @AppPPElt@ represents a an application, and it may be let bound.
data AppPPElt
   = APE { apeIndex :: !PPIndex
         , apeLoc :: !ProgramLoc
         , apeName :: !Text
         , apeElts :: ![PPElt]
         , apeLength :: !Int
           -- ^ Length of AppPPElt not including parenthesis.
         }

data PPElt
   = FixedPPElt !String ![String] !Int
     -- ^ A fixed doc with length.
   | AppPPElt !AppPPElt
     -- ^ A doc that can be let bound.

-- | Pretty print a AppPPElt
apeDoc :: AppPPElt -> (Doc, [Doc])
apeDoc a = (text (Text.unpack (apeName a)), ppEltDoc True <$> apeElts a)

textPPElt :: Text -> PPElt
textPPElt t = FixedPPElt (Text.unpack t) [] (Text.length t)

stringPPElt :: String -> PPElt
stringPPElt t = FixedPPElt t [] (length t)

-- | Get length of Elt including parens.
ppEltLength :: PPElt -> Int
ppEltLength (FixedPPElt _ [] n) = n
ppEltLength (FixedPPElt _ _ n) = n + 2
ppEltLength (AppPPElt a) = apeLength a + 2

parenIf :: Bool -> Doc -> [Doc] -> Doc
parenIf _ h [] = h
parenIf False h l = hsep (h:l)
parenIf True h l = parens (hsep (h:l))

-- | Pretty print PPElt
ppEltDoc :: Bool -> PPElt -> Doc
ppEltDoc b (FixedPPElt d a _) = parenIf b (text d) (fmap text a)
ppEltDoc b (AppPPElt a) = uncurry (parenIf b) (apeDoc a)

data PPEltOpts = PPEltOpts { ppElt_maxWidth :: Int
                           , ppElt_useDecimal :: Bool
                           }

defaultPPEltOpts :: PPEltOpts
defaultPPEltOpts =
  PPEltOpts { ppElt_maxWidth = 68
            , ppElt_useDecimal = True
            }

-- | Pretty print an 'Elt' using let bindings to create the term.
ppElt :: Elt t tp -> Doc
ppElt e
     | null bindings = ppEltDoc False r
     | otherwise =
         text "let" <+> align (vcat bindings) PP.<$>
         text " in" <+> align (ppEltDoc False r)
  where (bindings,r) = runST (ppElt' e defaultPPEltOpts)

instance ShowF (Elt t) where
  showsF e = shows (ppElt e)

-- | Pretty print the top part of an element.
ppEltTop :: Elt t tp -> Doc
ppEltTop e = ppEltDoc False r
  where (_,r) = runST (ppElt' e defaultPPEltOpts)

-- | Contains the elements before, the index, doc, and width and
-- the elements after.
type SplitPPEltList = Maybe ([PPElt], AppPPElt, [PPElt])

findEltToRemove :: [PPElt] -> SplitPPEltList
findEltToRemove elts0 = go [] elts0 Nothing
  where go :: [PPElt] -> [PPElt] -> SplitPPEltList -> SplitPPEltList
        go _ [] mr = mr
        go prev (e@FixedPPElt{} : elts) mr = do
          go (e:prev) elts mr
        go prev (AppPPElt a:elts) mr@(Just (_,a',_))
          | apeLength a < apeLength a' = go (AppPPElt a:prev) elts mr
        go prev (AppPPElt a:elts) _ = do
          go (AppPPElt a:prev) elts (Just (reverse prev, a, elts))


ppElt' :: forall t tp s . Elt t tp -> PPEltOpts -> ST s ([Doc], PPElt)
ppElt' e0 o = do
  let max_width = ppElt_maxWidth o
  let use_decimal = ppElt_useDecimal o
  -- Get map that counts number of elements.
  let m = countOccurrences e0
  -- Return number of times a term is referred to in dag.
  let isShared :: PPIndex -> Bool
      isShared w = fromMaybe 0 (Map.lookup w m) > 1

  -- Get bounds variables.
  bvars <- boundVars e0

  bindingsRef <- newSTRef Seq.empty

  visited <- H.new :: ST s (H.HashTable s PPIndex PPElt)
  visited_fns <- H.new :: ST s (H.HashTable s Word64 Text)

  let -- Add a binding to the list of bindings
      addBinding :: AppPPElt -> ST s PPElt
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
        let nm_elt = FixedPPElt nm args len
        H.insert visited idx $! nm_elt
        return nm_elt

  let fixLength :: Int
                -> [PPElt]
                -> ST s ([PPElt], Int)
      fixLength cur_width elts
        | cur_width > max_width
        , Just (prev_e, a, next_e) <- findEltToRemove elts = do
          r <- addBinding a
          let elts' = prev_e ++ [r] ++ next_e
          fixLength (cur_width - apeLength a + ppEltLength r) elts'
      fixLength cur_width elts = do
        return $! (elts, cur_width)

  -- Pretty print an argument.
  let renderArg :: PrettyArg (Elt t) -> ST s PPElt
      renderArg (Left (Some e)) = getBindings e
      renderArg (Right txt) = return (textPPElt txt)

      renderApp :: PPIndex
                -> ProgramLoc
                -> Text
                -> [PrettyArg (Elt t)]
                -> ST s AppPPElt
      renderApp idx loc nm args = assert (not (null args)) $ do
        elts0 <- traverse renderArg args
        -- Get width not including parenthesis of outer app.
        let total_width = Text.length nm + sum ((\e -> 1 + ppEltLength e) <$> elts0)
        (elts, cur_width) <- fixLength total_width elts0
        return APE { apeIndex = idx
                   , apeLoc = loc
                   , apeName = nm
                   , apeElts = elts
                   , apeLength = cur_width
                   }

      cacheResult :: PPIndex
                  -> ProgramLoc
                  -> PrettyApp (Elt t)
                  -> ST s PPElt
      cacheResult _ _ (nm,[]) = do
        return (textPPElt nm)
      cacheResult idx loc (nm,args) = do
        mr <- H.lookup visited idx
        case mr of
          Just d -> return d
          Nothing -> do
            a <- renderApp idx loc nm args
            if isShared idx then
              addBinding a
             else
              return (AppPPElt a)

      bindFn :: SimpleSymFn t idx ret -> ST s (PrettyArg (Elt t))
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
                let def_doc = text (show f) <+> hsep pp_vars <+> text "=" <+> ppElt rhs
                modifySTRef' bindingsRef (Seq.|> def_doc)
              MatlabSolverFnInfo fn_id _ _ -> do
                let def_doc = text (show f) <+> text "=" <+> ppMatlabSolverFn fn_id
                modifySTRef' bindingsRef (Seq.|> def_doc)

            let d = Text.pack (show f)
            H.insert visited_fns idx $! d
            return $! Right d

      -- Collect definitions for all applications that occur multiple times
      -- in term.
      getBindings :: Elt t u -> ST s PPElt
      getBindings (NatElt n _) = do
        return $ stringPPElt (show n)
      getBindings (IntElt n _) = do
        return $ stringPPElt (show n)
      getBindings (RatElt r l) = cacheResult (RatPPIndex r) l app
        where n = numerator r
              d = denominator r
              app | d == 1      = prettyApp (fromString (show n)) []
                  | use_decimal = prettyApp (fromString (show (fromRational r :: Double))) []
                  | otherwise   = prettyApp "divReal"  [ showPrettyArg n, showPrettyArg d ]
      getBindings (BVElt w n _) = do
        return $ stringPPElt $ "0x" ++ (N.showHex n []) ++ ":[" ++ show w ++ "]"
      getBindings (NonceAppElt e) = do
        cacheResult (ExprPPIndex (indexValue (nonceEltId e))) (nonceEltLoc e)
          =<< ppNonceApp bindFn (nonceEltApp e)
      getBindings (AppElt e) = do
        cacheResult (ExprPPIndex (indexValue (appEltId e)))
                    (appEltLoc e)
                    (ppApp' (appEltApp e))
      getBindings (BoundVarElt i) = do
        return $ stringPPElt $ ppBoundVar i

  r <- getBindings e0
  bindings <- toList <$> readSTRef bindingsRef
  return (toList bindings, r)

------------------------------------------------------------------------
-- Uncached storage

-- | Create a new storage that does not do hash consing.
newStorage :: NonceGenerator IO t -> IO (EltAllocator t)
newStorage g = do
  return $! EltAllocator { appElt = uncachedEltFn g
                         , nonceElt = uncachedNonceElt g
                         }

uncachedEltFn :: NonceGenerator IO t
              -> ProgramLoc
              -> App (Elt t) tp
              -> AbstractValue tp
              -> IO (Elt t tp)
uncachedEltFn g pc a v = do
  n <- freshNonce g
  return $! mkElt n pc a v

uncachedNonceElt :: NonceGenerator IO t
                 -> ProgramLoc
                 -> NonceApp t (Elt t) tp
                 -> AbstractValue tp
                 -> IO (Elt t tp)
uncachedNonceElt g pc p v = do
  n <- freshNonce g
  return $! NonceAppElt $ NonceAppEltCtor { nonceEltId = n
                                          , nonceEltLoc = pc
                                          , nonceEltApp = p
                                          , nonceEltAbsValue = v
                                          }

------------------------------------------------------------------------
-- Cached storage

cachedNonceElt :: NonceGenerator IO t
               -> PH.HashTable RealWorld (NonceApp t (Elt t)) (Elt t)
               -> ProgramLoc
               -> NonceApp t (Elt t) tp
               -> AbstractValue tp
               -> IO (Elt t tp)
cachedNonceElt g h pc p v = do
  me <- stToIO $ PH.lookup h p
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = NonceAppElt $ NonceAppEltCtor { nonceEltId = n
                                            , nonceEltLoc = pc
                                            , nonceEltApp = p
                                            , nonceEltAbsValue = v
                                            }
      seq e $ stToIO $ PH.insert h p e
      return $! e


cachedAppElt :: forall t tp
               . NonceGenerator IO t
              -> PH.HashTable RealWorld (App (Elt t)) (Elt t)
              -> ProgramLoc
              -> App (Elt t) tp
              -> AbstractValue tp
              -> IO (Elt t tp)
cachedAppElt g h pc a v = do
  me <- stToIO $ PH.lookup h a
  case me of
    Just e -> return e
    Nothing -> do
      n <- freshNonce g
      let e = mkElt n pc a v
      seq e $ stToIO $ PH.insert h a e
      return e

-- | Create a storage that does hash consing.
newCachedStorage :: forall t
                  . NonceGenerator IO t
                 -> Int
                 -> IO (EltAllocator t)
newCachedStorage g sz = stToIO $ do
  appCache  <- PH.newSized sz
  predCache <- PH.newSized sz
  return $ EltAllocator { appElt = cachedAppElt g appCache
                        , nonceElt = cachedNonceElt g predCache
                        }

------------------------------------------------------------------------
-- abstractEval

-- | Return abstract domain associated with a nonce app
quantAbsEval :: SimpleBuilder t st
             -> (forall u . Elt t u -> AbstractValue u)
             -> NonceApp t (Elt t) tp
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

abstractEval :: SimpleBuilder t st
             -> (forall u . Elt t u -> AbstractValue u)
             -> App (Elt t) tp
             -> AbstractValue tp
abstractEval sym f a0 = do
  let bvParams = sbBVDomainParams sym
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

    RealEq{} -> Nothing
    RealLe{} -> Nothing
    RealIsInteger{} -> Nothing
    BVTestBit{} -> Nothing
    BVEq{} -> Nothing
    BVSlt{} -> Nothing
    BVUlt{} -> Nothing
    ArrayEq{} -> Nothing

    ------------------------------------------------------------------------
    -- Arithmetic operations

    NatDiv x _ -> (f x)
    IntMod _ y -> natRange 0 (pred <$> natRangeHigh (f y))
    RealMul x y -> ravMul (f x) (f y)
    RealSum s -> WSum.eval ravAdd smul ravSingle s
      where smul sm e = ravScalarMul sm (f e)
    RealIte _ x y -> ravJoin (f x) (f y)

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
    BVSelect i n d -> BVD.select (natValue i) n (f d)
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
    BVTrunc w x  -> BVD.trunc bvParams (f x) w

    BVBitNot w x   -> BVD.not w (f x)
    BVBitAnd w x y -> BVD.and w (f x) (f y)
    BVBitOr  w x y -> BVD.or  w (f x) (f y)
    BVBitXor w x y -> BVD.xor w (f x) (f y)

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
    BVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where Just (lx, ux) = BVD.ubounds (bvWidth x) (f x)
    SBVToInteger x -> valueRange (Inclusive lx) (Inclusive ux)
      where Just (lx, ux) = BVD.sbounds (bvWidth x) (f x)
    RoundReal x -> mapRange roundAway (ravRange (f x))
    FloorReal x -> mapRange floor (ravRange (f x))
    CeilReal x  -> mapRange ceiling (ravRange (f x))
    IntegerToNat x ->
       case f x of
         SingleRange c              -> NatSingleRange (max 0 c)
         MultiRange Unbounded u     -> natRange 0 u
         MultiRange (Inclusive l) u -> natRange (max 0 l) u
    IntegerToSBV x w -> BVD.range w l u
      where rng = f x
            l = case rangeLowBound rng of
                  Unbounded -> minSigned w
                  Inclusive v -> max (minSigned w) v
            u = case rangeHiBound rng of
                  Unbounded -> maxSigned w
                  Inclusive v -> min (maxSigned w) v
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
eltAbsValue :: Elt t tp -> AbstractValue tp
eltAbsValue (NatElt c _)    = natSingleRange c
eltAbsValue (IntElt c _)    = singleRange c
eltAbsValue (RatElt c _)    = ravSingle c
eltAbsValue (BVElt w c _)   = BVD.singleton w c
eltAbsValue (NonceAppElt e) = nonceEltAbsValue e
eltAbsValue (AppElt e)      = appEltAbsValue e
eltAbsValue (BoundVarElt v) = unconstrainedAbsValue (bvarType v)

-- | Return an unconstrained abstract value.
unconstrainedAbsValue :: BaseTypeRepr tp -> AbstractValue tp
unconstrainedAbsValue tp = withAbstractable tp (avTop tp)

------------------------------------------------------------------------

instance PolyEq (Elt t x) (Elt t y) where
  polyEqF x y = do
    Refl <- testEquality x y
    return Refl

{-# NOINLINE appEqF #-}
-- | Check if two applications are equal.
appEqF :: App (Elt t) x -> App (Elt t) y -> Maybe (x :~: y)
appEqF = $(structuralTypeEquality [t|App|]
           [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
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
           ]
          )

{-# NOINLINE hashApp #-}
-- | Hash an an application.
hashApp :: Int -> App (Elt t) s -> Int
hashApp = $(structuralHash [t|App|])

instance Eq (App (Elt t) tp) where
  x == y = isJust (testEquality x y)

instance TestEquality (App (Elt t)) where
  testEquality = appEqF

instance HashableF (App (Elt t)) where
  hashWithSaltF = hashApp

------------------------------------------------------------------------
-- IdxCache

-- | An IdxCache is used to map expressions with type @Elt tp@ to values with a
-- corresponding type @f tp@.  It is a mutable map using an IO hash table.
newtype IdxCache t (f :: BaseType -> *)
      = IdxCache { cMap :: PH.HashTable RealWorld (Nonce t) f }

-- | Create a new IdxCache
newIdxCache :: IO (IdxCache t f)
newIdxCache = stToIO $ IdxCache <$> PH.new

{-# INLINE lookupIdxValue #-}
-- | Return the value associated to the elt in the index.
lookupIdxValue :: MonadIO m => IdxCache t f -> Elt t tp -> m (Maybe (f tp))
lookupIdxValue _ NatElt{} = return Nothing
lookupIdxValue _ IntElt{} = return Nothing
lookupIdxValue _ RatElt{} = return Nothing
lookupIdxValue _ BVElt{} = return Nothing
lookupIdxValue c (NonceAppElt e) = liftIO $ lookupIdx c (nonceEltId e)
lookupIdxValue c (AppElt e)  = liftIO $ lookupIdx c (eltId e)
lookupIdxValue c (BoundVarElt i) = liftIO $ lookupIdx c (bvarId i)

lookupIdx :: IdxCache t f -> Nonce t tp -> IO (Maybe (f tp))
lookupIdx c n = stToIO $ PH.lookup (cMap c) n

{-# INLINE insertIdxValue #-}
-- | Bind the value to the given elt in the index.
insertIdxValue :: MonadIO m => IdxCache t f -> Nonce t tp -> f tp -> m ()
insertIdxValue c e v = seq v $ liftIO $ stToIO $ PH.insert (cMap c) e v

{-# INLINE deleteIdxValue #-}
-- | Bind the value to the given elt in the index.
deleteIdxValue :: MonadIO m => IdxCache t f -> Nonce t (tp :: BaseType) -> m ()
deleteIdxValue c e = liftIO $ stToIO $ do
  PH.delete (cMap c) e

clearIdxCache :: IdxCache t f -> IO ()
clearIdxCache c = stToIO $ PH.clear (cMap c)

eltMaybeId :: Elt t tp -> Maybe (Nonce t tp)
eltMaybeId NatElt{} = Nothing
eltMaybeId IntElt{} = Nothing
eltMaybeId RatElt{} = Nothing
eltMaybeId BVElt{}  = Nothing
eltMaybeId (NonceAppElt e) = Just $! nonceEltId e
eltMaybeId (AppElt  e) = Just $! appEltId e
eltMaybeId (BoundVarElt e) = Just $! bvarId e

-- | Implements a cached evaluated using the given element.  Given an element
-- this function returns the value of the element if bound, and otherwise
-- calls the evaluation function, stores the result in the cache, and
-- returns the value.
idxCacheEval :: IdxCache t f
             -> Elt t tp
             -> IO (f tp)
             -> IO (f tp)
idxCacheEval c e m = do
  case eltMaybeId e of
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
-- SimpleBuilder operations

curProgramLoc :: SimpleBuilder t st -> IO ProgramLoc
curProgramLoc sym = readIORef (sbProgramLoc sym)

-- | Create an element from a nonce app.
sbNonceElt :: SimpleBuilder t st
           -> NonceApp t (Elt t) tp
           -> IO (Elt t tp)
sbNonceElt sym a = do
  s <- readIORef (curAllocator sym)
  pc <- curProgramLoc sym
  nonceElt s pc a (quantAbsEval sym eltAbsValue a)

sbMakeElt :: SimpleBuilder t st -> App (Elt t) tp -> IO (Elt t tp)
sbMakeElt sym a = do
  s <- readIORef (curAllocator sym)
  let v = abstractEval sym eltAbsValue a
  pc <- curProgramLoc sym
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
      appElt s pc a v

-- | Update the binding to point to the current variable.
updateVarBinding :: SimpleBuilder t st
                 -> SolverSymbol
                 -> SymbolBinding t
                 -> IO ()
updateVarBinding sym nm v
  | nm == emptySymbol = return ()
  | otherwise =
    modifyIORef' (sbVarBindings sym) $ (Bimap.insert nm $! v)

-- | Creates a new bound var.
sbMakeBoundVar :: SimpleBuilder t st
               -> SolverSymbol
               -> BaseTypeRepr tp
               -> VarKind
               -> IO (SimpleBoundVar t tp)
sbMakeBoundVar sym nm tp k = do
  n  <- sbFreshIndex sym
  pc <- curProgramLoc sym
  return $! BVar { bvarId   = n
                 , bvarLoc  = pc
                 , bvarName = nm
                 , bvarType = tp
                 , bvarKind = k
                 }

-- | Create fresh index
sbFreshIndex :: SimpleBuilder t st -> IO (Nonce t (tp::BaseType))
sbFreshIndex sb = freshNonce (eltCounter sb)

sbFreshSymFnNonce :: SimpleBuilder t st -> IO (Nonce t (ctx:: Ctx BaseType))
sbFreshSymFnNonce sb = freshNonce (eltCounter sb)

newSimpleBuilder :: IsSimpleBuilderState st
                 => st t
                    -- ^ Current state for simple builder.
                 -> NonceGenerator IO t
                    -- ^ Nonce generator for names
                 ->  IO (SimpleBuilder t st)
newSimpleBuilder st gen = do
  let sz = 100000
  st_ref <- newIORef st
  es <- newCachedStorage gen sz

  t <- appElt es initializationLoc TrueBool  (Just True)
  f <- appElt es initializationLoc FalseBool (Just False)
  let z = RatElt 0 initializationLoc
  storage_ref   <- newIORef es
  loc_ref       <- newIORef initializationLoc
  bindings_ref  <- newIORef Bimap.empty
  matlabFnCache <- stToIO $ PH.new
  return $! SB { sbTrue  = t
               , sbFalse = f
               , sbZero = z
               , sbFloatReduce = True
               , _sbUnaryThreshold = 0
               , _sbBVDomainRangeLimit = 2
               , _sbCacheStartSize = sz
               , eltCounter = gen
               , curAllocator = storage_ref
               , sbStateManager = st_ref
               , sbProgramLoc   = loc_ref
               , sbVarBindings = bindings_ref
               , sbStateManagerIsBoolSolver = \x -> x
               , sbMatlabFnCache = matlabFnCache
               }

-- | Get current variable bindings
getSymbolVarBimap :: SimpleBuilder t st -> IO (SymbolVarBimap t)
getSymbolVarBimap sym = readIORef (sbVarBindings sym)

-- | Stop caching applications in backend.
sbStopCaching :: SimpleBuilder t st -> IO ()
sbStopCaching sb = do
  s <- newStorage (eltCounter sb)
  writeIORef (curAllocator sb) s

-- | Restart caching applications in backend (clears cache if it is currently caching).
sbRestartCaching :: SimpleBuilder t st -> IO ()
sbRestartCaching sb = do
  let sz = sb^.sbCacheStartSize
  s <- newCachedStorage (eltCounter sb) sz
  writeIORef (curAllocator sb) s

-- | @impliesAssert sym b a@ returns the assertions that hold
-- if @b@ is false or all the assertions in @a@ are true.
impliesAssert :: SimpleBuilder t st
              -> BoolElt t
              -> Seq (Assertion (BoolElt t))
              -> IO (Seq (Assertion (BoolElt t)))
impliesAssert sym c = go Seq.empty
  where --
        go prev next =
          case Seq.viewr next of
            Seq.EmptyR -> return prev
            new Seq.:> a -> do
              let p = a^.assertPred
              p' <- impliesPred sym c p
              case asApp p' of
                Just TrueBool -> go prev new
                _ -> go (prev Seq.|> (a & assertPred .~ p')) new


{-# INLINE boolEltAsBool #-}
boolEltAsBool :: BoolElt t -> Maybe Bool
boolEltAsBool e
  | Just TrueBool  <- asApp e = Just True
  | Just FalseBool <- asApp e = Just False
  | otherwise = Nothing

instance IsPred (BoolElt t) where
  asConstantPred = boolEltAsBool

bvBinOp1 :: (1 <= w)
         => (Integer -> Integer -> Integer)
         -> (NatRepr w -> BVElt t w -> BVElt t w -> App (Elt t) (BaseBVType w))
         -> SimpleBuilder t st
         -> BVElt t w
         -> BVElt t w
         -> IO (BVElt t w)
bvBinOp1 f c sb x y = do
  let w = bvWidth x
  case (asUnsignedBV x, asUnsignedBV y) of
    (Just i, Just j) -> bvLit sb w $ f i j
    _ -> sbMakeElt sb $ c w x y

bvSignedBinOp :: (1 <= w)
              => (Integer -> Integer -> Integer)
              -> (NatRepr w -> BVElt t w
                            -> BVElt t w
                            -> App (Elt t) (BaseBVType w))
              -> SimpleBuilder t st
              -> BVElt t w
              -> BVElt t w
              -> IO (BVElt t w)
bvSignedBinOp f c sym x y = do
  let w = bvWidth x
  case (asSignedBV x, asSignedBV y) of
    (Just i, Just j) -> bvLit sym w $ f i j
    _ -> sbMakeElt sym $ c w x y

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
betaReduce :: SimpleBuilder t st
           -> SimpleSymFn t args ret
           -> Ctx.Assignment (Elt t) args
           -> IO (Elt t ret)
betaReduce sym f args =
  case symFnInfo f of
    UninterpFnInfo{} ->
      sbNonceElt sym $! FnApp f args
    DefinedFnInfo bound_vars e _ -> do
      evalBoundVars sym e bound_vars args
    MatlabSolverFnInfo fn_id _ _ -> do
      evalMatlabSolverFn fn_id sym args

reduceApp :: IsExprBuilder sym
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

    RealEq x y    -> realEq sym x y
    RealLe x y    -> realLe sym x y
    RealIsInteger x -> isInteger sym x
    RealSum x   -> realSum sym x
    RealMul x y -> realMul sym x y
    RealIte c x y -> realIte sym c x y

    NatDiv x y  -> natDiv  sym x y
    RealDiv x y -> realDiv sym x y
    IntMod x y  -> intMod  sym x y
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
    BVTestBit i e -> testBitBV sym (toInteger i) e
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
    BVTrunc w x  -> bvTrunc sym w x
    BVBitNot _ x -> bvNotBits sym x
    BVBitAnd _ x y -> bvAndBits sym x y
    BVBitOr  _ x y -> bvOrBits  sym x y
    BVBitXor _ x y -> bvXorBits sym x y

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

    BVToInteger x   -> bvToInteger sym x
    SBVToInteger x  -> sbvToInteger sym x
    IntegerToSBV x w -> integerToSBV sym x w
    IntegerToBV  x w -> integerToBV  sym x w

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
recordBoundVar :: PH.HashTable RealWorld (Elt t) (Elt t)
                  -> SimpleBoundVar t tp
                  -> IO ()
recordBoundVar tbl v = do
  let e = BoundVarElt v
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
    => CachedSymFn Bool (SimpleSymFn t a r)

-- | Data structure used for caching evaluation.
data EvalHashTables t
   = EvalHashTables { eltTable :: !(PH.HashTable RealWorld (Elt t) (Elt t))
                    , fnTable  :: !(PH.HashTable RealWorld (Nonce t) (CachedSymFn t))
                    }

-- | Evaluate a simple function.
--
-- This returns whether the function changed as a Boolean and the function itself.
evalSimpleFn :: EvalHashTables t
             -> SimpleBuilder t st
             -> SimpleSymFn t idx ret
             -> IO (Bool,SimpleSymFn t idx ret)
evalSimpleFn tbl sym f =
  case symFnInfo f of
    UninterpFnInfo{} -> return (False, f)
    DefinedFnInfo vars e evalFn -> do
      let n = symFnId f
      let nm = symFnName f
      CachedSymFn changed f' <-
        cachedEval (fnTable tbl) n $ do
          traverseFC_ (recordBoundVar (eltTable tbl)) vars
          e' <- evalBoundVars' tbl sym e
          if e == e' then
            return $! CachedSymFn False f
           else
            CachedSymFn True <$> definedFn sym nm vars e' evalFn
      return (changed, f')
    MatlabSolverFnInfo{} -> return (False, f)

evalBoundVars' :: forall t st ret
               .  EvalHashTables t
               -> SimpleBuilder t st
               -> Elt t ret
               -> IO (Elt t ret)
evalBoundVars' tbls sym e0 =
  case e0 of
    NatElt{} -> return e0
    IntElt{} -> return e0
    RatElt{} -> return e0
    BVElt{}  -> return e0
    AppElt ae -> cachedEval (eltTable tbls) e0 $ do
      let a = appEltApp ae
      a' <- traverseApp (evalBoundVars' tbls sym) a
      if a == a' then
        return e0
       else
        reduceApp sym a'
    NonceAppElt ae -> cachedEval (eltTable tbls) e0 $ do
      case nonceEltApp ae of
        Forall v e -> do
          recordBoundVar (eltTable tbls) v
          -- Regenerate forallPred if e is changed by evaluation.
          runIfChanged e (evalBoundVars' tbls sym) e0 (forallPred sym v)
        Exists v e -> do
          recordBoundVar (eltTable tbls) v
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
          let evalWrapper :: ArrayResultWrapper (Elt t) (idx ::> itp) utp
                          -> IO (ArrayResultWrapper (Elt t) (idx ::> itp) utp)
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

    BoundVarElt{} -> cachedEval (eltTable tbls) e0 $ return e0

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
evalBoundVars :: SimpleBuilder t st
              -> Elt t ret
              -> Ctx.Assignment (SimpleBoundVar t) args
              -> Ctx.Assignment (Elt t) args
              -> IO (Elt t ret)
evalBoundVars sym e vars elts = do
  elt_tbl <- stToIO $ initHashTable (fmapFC BoundVarElt vars) elts
  fn_tbl  <- stToIO $ PH.new
  let tbls = EvalHashTables { eltTable = elt_tbl
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
sbConcreteLookup :: forall t st d tp range
                 . SimpleBuilder t st
                   -- ^ Simple builder for creating terms.
                 -> Elt t (BaseArrayType (d::>tp) range)
                    -- ^ Array to lookup value in.
                 -> Maybe (Ctx.Assignment IndexLit (d::>tp))
                    -- ^ A concrete index that corresponds to the index or nothing
                    -- if the index is symbolic.
                 -> Ctx.Assignment (Elt t) (d::>tp)
                    -- ^ The index to lookup.
                 -> IO (Elt t range)
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
      let eval :: ArrayResultWrapper (Elt t) (d::>tp) utp
               -> IO (Elt t utp)
          eval a = sbConcreteLookup sym (unwrapArrayResult a) mcidx idx
      betaReduce sym f =<< traverseFC eval args
    -- Create select index.
  | otherwise = do
    case exprType arr0 of
      BaseArrayRepr _ range ->
        sbMakeElt sym (SelectArray range arr0 idx)

realToSBV :: (1 <= w) => SimpleBuilder t st -> NatRepr w -> RealElt t -> IO (BVElt t w)
realToSBV sym w r = do
  i <- realToInteger sym r
  integerToSBV sym i w

instance IsBoolExprBuilder (SimpleBuilder t st) where

  truePred  = sbTrue
  falsePred = sbFalse

  notPred sym x
    | Just TrueBool  <- asApp x = return $! falsePred sym
    | Just FalseBool <- asApp x = return $! truePred sym
    | Just (NotBool xn) <- asApp x = return xn
    | otherwise = sbMakeElt sym (NotBool x)

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

    | otherwise = sbMakeElt sym (AndBool (min x y) (max x y))

  xorPred sym x y
    | Just True  <- asConstantPred x = notPred sym y
    | Just False <- asConstantPred x = return y
    | Just True  <- asConstantPred y = notPred sym x
    | Just False <- asConstantPred y = return x
    | x == y = return $ falsePred sym

    | Just (NotBool xn) <- asApp x
    , Just (NotBool yn) <- asApp y = do
      sbMakeElt sym (XorBool xn yn)

    | Just (NotBool xn) <- asApp x = do
      notPred sym =<< sbMakeElt sym (XorBool xn y)

    | Just (NotBool yn) <- asApp y = do
      notPred sym =<< sbMakeElt sym (XorBool x yn)

    | otherwise = do
      sbMakeElt sym (XorBool x y)

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
      andPred sb y =<< sbMakeElt sb (NotBool c)
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
    | otherwise = sbMakeElt sb $ IteBool c x y

-----------------------------------------------------------------------
-- Defer to the enclosed state manager for IsBoolSolver operations
-- and datatypes

instance IsBoolSolver (SimpleBuilder t st) where

  evalBranch sym p = sbStateManagerIsBoolSolver sym $
    sbEvalBranch sym p

  getCurrentState sym = do
    s <- readIORef (sbStateManager sym)
    l <- readIORef (sbProgramLoc sym)
    return $! SBPS s l
  resetCurrentState sym prev_state = sbStateManagerIsBoolSolver sym $ do
    sbBacktrackToState sym prev_state
    -- Update state variables
    writeIORef (sbStateManager sym) $! (prev_state^.pathState)
    writeIORef (sbProgramLoc sym) $! sbpsLoc prev_state
  switchCurrentState sym prev_state next_state  = do
    sbStateManagerIsBoolSolver sym $ do
    sbSwitchToState sym prev_state next_state
    writeIORef (sbStateManager sym) $! (prev_state^.pathState)
    writeIORef (sbProgramLoc sym) $! sbpsLoc next_state

  pushBranchPred sym p = sbStateManagerIsBoolSolver sym $
    sbPushBranchPred sym p

  mergeState sym true_pred true_state false_state =
    sbStateManagerIsBoolSolver sym $ do

    old_ps <- getCurrentState sym

    let true_ps   = true_state^.pathState
    let false_ps  = false_state^.pathState

    let pre_state = old_ps^.pathState

    -- Drop assertions that were already present at branch.
    let cur_aseq  = sbAssertionsBetween pre_state true_ps
    t_aseq <- impliesAssert sym true_pred  cur_aseq

    let neg_aseq  = sbAssertionsBetween pre_state false_ps
    false_pred <- notPred sym true_pred
    f_aseq <- impliesAssert sym false_pred neg_aseq

    sbAppendAssertions sym (t_aseq Seq.>< f_aseq)

  ----------------------------------------------------------------------
  -- Program location operations

  getCurrentProgramLoc = curProgramLoc
  setCurrentProgramLoc sym l = writeIORef (sbProgramLoc sym) $! l

  ----------------------------------------------------------------------
  -- Assertion

  addAssertion sb =
    sbStateManagerIsBoolSolver sb $
      sbAddAssertion sb

  addAssumption sb =
    sbStateManagerIsBoolSolver sb $
      sbAddAssumption sb

  getAssertionPred sb =
    sbStateManagerIsBoolSolver sb $
      sbAllAssertions sb

  getAssertionsBetween sb old cur = do
    sbStateManagerIsBoolSolver sb $
      return $ toList $ sbAssertionsBetween (old^.pathState) (cur^.pathState)

  getProofObligations sb = do
    sbStateManagerIsBoolSolver sb $ do
      obligs <- sbGetProofObligations sb
      return [ (toList hyps, goal)
             | (hyps,goal) <- toList obligs
             ]

  setProofObligations sb obligs = do
    sbStateManagerIsBoolSolver sb $ do
      sbSetProofObligations sb $ Seq.fromList
        [ (Seq.fromList hyps, goal)
        | (hyps, goal) <- obligs
        ]

----------------------------------------------------------------------
-- Expression builder instances

asUnaryBV :: SimpleBuilder t st
          -> BVElt t n
          -> Maybe (UnaryBV (BoolElt t) n)
asUnaryBV sym e
  | Just (BVUnaryTerm u) <- asApp e = Just u
  | sym^.sbUnaryThreshold == 0 = Nothing
  | BVElt w v _ <- e = Just $ UnaryBV.constant sym w v
  | otherwise = Nothing

-- | This create a unary bitvector representing if the size is not too large.
sbTryUnaryTerm :: (1 <= w)
               => SimpleBuilder t st
               -> UnaryBV (BoolElt t) w
               -> App (Elt t) (BaseBVType w)
               -> IO (BVElt t w)
sbTryUnaryTerm sym u a
  | UnaryBV.size u < sym^.sbUnaryThreshold =
    bvUnary sym u
  | otherwise =
    sbMakeElt sym a

-- | This privides a view of a real elt as a weighted sum of values.
data SumView t
   = ConstantSum !Rational
   | LinearSum !(WeightedSum Rational (Elt t) BaseRealType)
   | GeneralSum

viewSum :: RealElt t -> SumView t
viewSum x
  | RatElt r _ <- x = ConstantSum r
  | Just (RealSum s) <- asApp x = LinearSum s
  | otherwise = GeneralSum

asWeightedSum :: HashableF (Elt t)
              => RealElt t
              -> WeightedSum Rational (Elt t) BaseRealType
asWeightedSum x
  | RatElt r _ <- x = WSum.constant r
  | Just (RealSum s) <- asApp x = s
  | otherwise = WSum.var x

realSum' :: SimpleBuilder t st
            -> WeightedSum Rational (Elt t) BaseRealType
            -> IO (RealElt t)
realSum' sym s = sbMakeElt sym $ RealSum $ s

realScalarMul :: SimpleBuilder t st
              -> Rational
              -> RealElt t
              -> IO (RealElt t)
realScalarMul sym c x
  | c == 0 =
    return $! sbZero sym
  | c == 1 =
    return x
  | Just r <- asRational x =
    realLit sym (c*r)
  | Just (RealSum s) <- asApp x =
    realSum' sym (WSum.scale c s)
  | otherwise = do
    realSum' sym (WSum.scaledVar c x)

-- Add following rule to do a strength reduction on non-linear
-- constraint non-negative constraint
--
-- (0 <= u * v)
-- -> not (u * v < 0)
-- -> not (u > 0 & v < 0 | u < 0 & v > 0)
-- -> not (u > 0 & v < 0) & not (u < 0 & v > 0)
-- -> (u <= 0 | v >= 0) & (u >= 0 | v <= 0)
-- -> (u <= 0 | 0 <= v) & (0 <= u | v <= 0)
leNonneg :: IsBoolExprBuilder sym
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
leNonpos :: IsBoolExprBuilder sym
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

pattern SBVToReal x <- (asApp -> Just (IntegerToReal (asApp -> Just (SBVToInteger x))))


arrayResultIdxType :: BaseTypeRepr (BaseArrayType (idx ::> itp) d)
                   -> Ctx.Assignment BaseTypeRepr (idx ::> itp)
arrayResultIdxType (BaseArrayRepr idx _) = idx

-- | This decomposes A SimpleBuilder array expression into a set of indices that
-- have been updated, and an underlying index.
data ArrayMapView i f tp
   = ArrayMapView { _arrayMapViewIndices :: !(Hash.Map IndexLit i f tp)
                  , _arrayMapViewElt    :: !(f (BaseArrayType i tp))
                  }

-- | Construct an 'ArrayMapView' for an element.
viewArrayMap :: Elt t (BaseArrayType i tp)
             -> ArrayMapView i (Elt t) tp
viewArrayMap  x
  | Just (ArrayMap _ _ m c) <- asApp x = ArrayMapView m c
  | otherwise = ArrayMapView Hash.mapEmpty x

-- | Construct an 'ArrayMapView' for an element.
underlyingArrayMapElt :: ArrayResultWrapper (Elt t) i tp
                      -> ArrayResultWrapper (Elt t) i tp
underlyingArrayMapElt x
  | Just (ArrayMap _ _ _ c) <- asApp (unwrapArrayResult x) = ArrayResultWrapper c
  | otherwise = x

-- | Return set of addresss in assignment that are written to by at least one
-- elt.
concreteArrayEntries :: forall t i ctx
                     .  Ctx.Assignment (ArrayResultWrapper (Elt t) i) ctx
                     -> Set (Ctx.Assignment IndexLit i)
concreteArrayEntries = foldlFC' f Set.empty
  where f :: Set (Ctx.Assignment IndexLit i)
          -> ArrayResultWrapper (Elt t) i tp
          -> Set (Ctx.Assignment IndexLit i)
        f s e
          | Just (ArrayMap _ _ m _) <- asApp (unwrapArrayResult  e) =
            Set.union s (Map.keysSet (Hash.hashedMap m))
          | otherwise = s

data NatLit tp = (tp ~ BaseNatType) => NatLit Nat

asNatBounds :: Ctx.Assignment (Elt t) idx -> Maybe (Ctx.Assignment NatLit idx)
asNatBounds = traverseFC f
  where f :: Elt t tp -> Maybe (NatLit tp)
        f (NatElt n _) = Just (NatLit n)
        f _ = Nothing

foldBoundLeM :: (r -> Nat -> IO r) -> r -> Nat -> IO r
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
  case Ctx.view bnds0 of
    Ctx.AssignEmpty -> f0 a0 Ctx.empty
    Ctx.AssignExtend bnds (NatLit b) -> foldIndicesInRangeBounds sym (g f0) a0 bnds
      where g :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> r
              -> Ctx.Assignment (SymExpr sym) idx0
              -> IO r
            g f a i = foldBoundLeM (h f i) a b

            h :: (r -> Ctx.Assignment (SymExpr sym) (idx0 ::> BaseNatType) -> IO r)
              -> Ctx.Assignment (SymExpr sym) idx0
              -> r
              -> Nat
              -> IO r
            h f i a j = do
              je <- natLit sym j
              f a (i Ctx.%> je)

{-
-- | Compute the weighted sum of two bitvectors.
bvSum :: (1 <= w)
      => sym
      -> NatRepr w
      -> WeightedSum Integer (SymBV sym w)
      -> IO (SymBV sym w)
bvSum = undefined
-}

instance IsExprBuilder (SimpleBuilder t st) where

  ----------------------------------------------------------------------
  -- Nat operations.

  natLit sb n = do
    NatElt n <$> curProgramLoc sb

  natAdd sym x y = do
    xr <- natToReal sym x
    yr <- natToReal sym y
    realToNat sym =<< realAdd sym xr yr

  natSub sym x y = do
    xr <- natToReal sym x
    yr <- natToReal sym y
    realToNat sym =<< realAdd sym xr =<< realNeg sym yr

  natMul sym x y = do
    xr <- natToReal sym x
    yr <- natToReal sym y
    realToNat sym =<< realMul sym xr yr

  natDiv sym x y
    | Just m <- asNat x, Just n <- asNat y = do
      natLit sym (m `div` n)
      -- 0 / y
    | Just 0 <- asNat x = do
      return x
      -- x / 1
    | Just 1 <- asNat y = do
      return x
    | otherwise = do
      sbMakeElt sym (NatDiv x y)

  natIte sym c x y = do
    realToNat sym =<< join (realIte sym c <$> natToReal sym x <*> natToReal sym y)

  natEq sym x y =
    join $ realEq sym <$> natToReal sym x <*> natToReal sym y

  natLe sym x y =
    join $ realLe sym <$> natToReal sym x <*> natToReal sym y

  ----------------------------------------------------------------------
  -- Integer operations.

  intLit sb n = do
    IntElt n <$> curProgramLoc sb

  intNeg sym x = do
    realToInteger sym =<< realNeg sym =<< integerToReal sym x

  intMul sym xi yi = do
    x <- integerToReal sym xi
    y <- integerToReal sym yi
    realToInteger sym =<< realMul sym x y

  intIte sym c x y =
    realToInteger sym =<< join (realIte sym c <$> integerToReal sym x <*> integerToReal sym y)

  intEq sym x y =
    join $ realEq sym <$> integerToReal sym x <*> integerToReal sym y

  intLe sym x y =
    join $ realLe sym <$> integerToReal sym x <*> integerToReal sym y

  intMod sym x y
      -- Not defined when division by 0.
    | Just 0 <- asNat y = return y
      -- Mod by 1.
    | Just 1 <- asNat y = natLit sym 0
      -- Mod 0 by anything is zero.
    | Just 0 <- asInteger x = natLit sym 0
      -- As integers.
    | Just xi <- asInteger x, Just yi <- asNat y = do
      natLit sym (fromInteger (xi `mod` toInteger yi))
      -- Return int mod.
    | otherwise = do
      sbMakeElt sym (IntMod x y)

  ---------------------------------------------------------------------
  -- Bitvector operations

  bvLit sym w i = do
    l <- curProgramLoc sym
    return $ BVElt w (toUnsigned w i) l

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
              return $ BVElt w' ((xv `Bits.shiftL` shft) Bits..|. yv) l
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
      -- concat an adjacent selects to a trunc just makes a single select
      _ | Just (BVSelect idx1 n1 a) <- asApp x
        , Just (BVTrunc n2 b) <- asApp y
        , Just Refl <- testEquality a b
        , Just Refl <- testEquality idx1 n2
        , Just LeqProof <- isPosNat (addNat n1 n2)
        , Just LeqProof <- testLeq (addNat n1 n2) (bvWidth a) ->
            bvSelect sym (knownNat :: NatRepr 0) (addNat n1 n2) a
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
        sbMakeElt sym $ BVConcat (addNat wx wy) x y

  -- bvSelect has a bunch of special cases that examine the form of the
  -- bitvector being selected from.  This can significantly reduce the size
  -- of expressions that result from the very verbose packing and unpacking
  -- operations that arise from byte-oriented memory models.
  bvSelect sb idx n x
    | Just xv <- asUnsignedBV x = do
      l <- curProgramLoc sb
      let mask = maxUnsigned n
      let shft = fromIntegral (natValue idx)
      return $ BVElt n ((xv `Bits.shiftR` shft) Bits..&. mask) l

      -- nested selects can be collapsed
    | Just (BVSelect idx' _n' b) <- asApp x
    , let idx2 = addNat idx idx'
    , Just LeqProof <- testLeq (addNat idx2 n) (bvWidth b) =
      bvSelect sb idx2 n b

      -- select of a truncate is the same select before the truncate
    | Just (BVTrunc _w b) <- asApp x
    , Just LeqProof <- testLeq (addNat idx n) (bvWidth b) =
      bvSelect sb idx n b

      -- select the entire bitvector is the identity function
    | Just _ <- testEquality idx (knownNat :: NatRepr 0)
    , Just Refl <- testEquality n (bvWidth x) =
      return x

     -- select an initial segment is a truncate
    | Just _ <- testEquality idx (knownNat :: NatRepr 0)
    , Just LeqProof <- testLeq (incNat n) (bvWidth x) =
      bvTrunc sb n x

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

      -- if none of the above apply, produce a basic select term
    | otherwise = sbMakeElt sb $ BVSelect idx n x

  testBitBV sym i y
    | i < 0 || i > toInteger (maxBound :: Int) =
      fail $ "Illegal bit index."
      -- Constant evaluation
    | Just yc <- asUnsignedBV y
    , i <= toInteger (maxBound :: Int) = do
      return $! backendPred sym (yc `Bits.testBit` fromInteger i)

    | Just b <- BVD.testBit (bvWidth y) (eltAbsValue y) i = do
      return $! backendPred sym b
    | otherwise = do
      sbMakeElt sym $ BVTestBit (fromInteger i) y

  bvIte sym c x y
    | Just TrueBool  <- asApp c = return x
    | Just FalseBool <- asApp c = return y
    | x == y = return x
    | Just (NotBool cn) <- asApp c = bvIte sym cn y x

    | Just ux <- asUnaryBV sym x
    , Just uy <- asUnaryBV sym y = do
      uz <- UnaryBV.mux sym c ux uy
      let sz = 1 + iteSize x + iteSize y
      sbTryUnaryTerm sym uz (BVIte (bvWidth x) sz c x y)

    | otherwise = do
      let sz = 1 + iteSize x + iteSize y
      sbMakeElt sym $ BVIte (bvWidth x) sz c x y

  bvEq sym x y
    | Just xc <- asUnsignedBV x
    , Just yc <- asUnsignedBV y = do
      return $! backendPred sym (xc == yc)

    | Just b <- BVD.eq (eltAbsValue x) (eltAbsValue y) = do
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

    | Just ux <- asUnaryBV sym x
    , Just uy <- asUnaryBV sym y = do
      UnaryBV.eq sym ux uy

    | otherwise = do
      sbMakeElt sym $ BVEq (min x y) (max x y)

  bvSlt sym x y
    | Just xc <- asSignedBV x
    , Just yc <- asSignedBV y =
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.slt (bvWidth x) (eltAbsValue x) (eltAbsValue y) =
      return $! backendPred sym b
    | x == y = return (falsePred sym)

      -- Unary values.
    | Just ux <- asUnaryBV sym x
    , Just uy <- asUnaryBV sym y = do
      UnaryBV.slt sym ux uy

    | otherwise = sbMakeElt sym $ BVSlt x y

  bvUlt sym x y
    | Just xc <- asUnsignedBV x
    , Just yc <- asUnsignedBV y = do
      return $! backendPred sym (xc < yc)
    | Just b <- BVD.ult (bvWidth x) (eltAbsValue x) (eltAbsValue y) =
      return $! backendPred sym b
    | x == y =
      return $! falsePred sym

      -- Unary values.
    | Just ux <- asUnaryBV sym x
    , Just uy <- asUnaryBV sym y = do
      UnaryBV.ult sym ux uy

    | otherwise = sbMakeElt sym $ BVUlt x y

  bvShl sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftL i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeElt sym $ BVShl (bvWidth x) x y

  bvLshr sym x y
   | Just i <- asUnsignedBV x, Just n <- asUnsignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftR i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeElt sym $ BVLshr (bvWidth x) x y

  bvAshr sym x y
   | Just i <- asSignedBV x, Just n <- asSignedBV y = do
     bvLit sym (bvWidth x) $ Bits.shiftR i (fromIntegral n)
   | Just 0 <- asUnsignedBV y = do
     pure x
   | otherwise = do
     sbMakeElt sym $ BVAshr (bvWidth x) x y

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
      sbMakeElt sym $ BVZext w y

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.uext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeElt sym $ BVZext w x

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
      sbMakeElt sym (BVSext w y)

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      bvUnary sym $ UnaryBV.sext u w

    | otherwise = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w
      sbMakeElt sym (BVSext w x)

  bvTrunc sym w x
    -- constant case
    | Just i <- asUnsignedBV x = bvLit sym w i

    -- truncate of a select is a shorter select
    | Just (BVSelect idx _n b) <- asApp x
    , Just LeqProof <- testLeq (addNat idx w) (bvWidth b) =
        bvSelect sym idx w b

    -- trunc of a concat gives the second argument of concat
    -- when the lengths are right
    | Just (BVConcat _w' _a b) <- asApp x
    , Just Refl <- testEquality w (bvWidth b) =
        return b

    -- trunc of a concat gives a trunc of the second argument
    -- when the trunc is shorter than that argument
    | Just (BVConcat _w' _a b) <- asApp x
    , Just LeqProof <- testLeq (incNat w) (bvWidth b) =
        bvTrunc sym w b

    -- (trunc w (concat a b)) gives (concat a' b) when w is longer
    -- than b, and where a' is an appropriately-truncated portion of a
    | Just (BVConcat _w' a b) <- asApp x
    , Just LeqProof <- testLeq (bvWidth b) w
    , let diff = subNat w (bvWidth b)
    , Just LeqProof <- isPosNat diff
    , Just Refl <- testEquality (addNat diff (bvWidth b)) w
    , Just LeqProof <- testLeq (incNat diff) (bvWidth a) = do
        a' <- bvTrunc sym diff a
        bvConcat sym a' b

    -- trunc of a zero extend is either trunc of the argument (or the argument itself)
    -- or else is just a shorter zero extend
    | Just (BVZext _ y) <- asApp x = do
      case compareF w (bvWidth y) of
        LTF -> do
          -- Add dynamic check for GHC typechecker.
          Just LeqProof <- return $ testLeq (incNat w) (bvWidth y)
          bvTrunc sym w y
        EQF -> return y
        GTF -> do
         -- Add dynamic check for GHC typechecker.
         Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
         bvZext sym w y

    -- trunc of a sign extend is either trunc of the argument (or the argument itself)
    -- or else is just a shorter sign extend
    | Just (BVSext _ y) <- asApp x = do
      case compareF w (bvWidth y) of
        LTF -> do
          -- Add dynamic check for GHC typechecker.
          Just LeqProof <- return $ testLeq (incNat w) (bvWidth y)
          bvTrunc sym w y
        EQF -> return y
        GTF -> do
         -- Add dynamic check for GHC typechecker.
         Just LeqProof <- return $ testLeq (incNat (bvWidth y)) w
         bvSext sym w y

      -- Extend unary representation.
    | Just (BVUnaryTerm u) <- asApp x = do
      -- Add dynamic check for GHC typechecker.
      Just LeqProof <- return $ isPosNat w
      u' <- UnaryBV.trunc sym u w
      bvUnary sym u'

    -- nested truncs collapse
    | Just (BVTrunc _ y) <- asApp x = do
      Just LeqProof <- return $ testLeq (incNat w) (bvWidth y)
      sbMakeElt sym (BVTrunc w y)


    -- no special case applies, just make a basic trunc expression
    | otherwise =
      sbMakeElt sym $ BVTrunc w x

  bvNotBits sym x
    | Just i <- asUnsignedBV x = do
      bvLit sym (bvWidth x) $ i `Bits.xor` (maxUnsigned (bvWidth x))
    | Just (BVBitNot _ y) <- asApp x = return y
    | otherwise = sbMakeElt sym $ BVBitNot (bvWidth x) x

  bvAndBits = bvBinOp1 (Bits..&.) BVBitAnd
  bvOrBits  = bvBinOp1 (Bits..|.) BVBitOr

  -- Special case for the self-XOR trick, which compilers sometimes will use
  -- to zero the state of a register
  bvXorBits sym x y | x == y = bvLit sym (bvWidth x) 0
  bvXorBits sym x y = bvBinOp1 Bits.xor BVBitXor sym x y

  bvNeg sym x
    | Just i <- asSignedBV x = bvLit sym (bvWidth x) (-i)
    | Just (BVNeg _ y) <- asApp x = return y

      -- Negate a unary bitvector.
    | Just ux <- asUnaryBV sym x = do
      uz <- UnaryBV.neg sym ux
      sbTryUnaryTerm sym uz (BVNeg (bvWidth x) x)

    | otherwise = sbMakeElt sym $ BVNeg (bvWidth x) x

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

    | Just ux <- asUnaryBV sym x
    , Just uy <- asUnaryBV sym y = do
      uz <- UnaryBV.add sym ux uy
      sbTryUnaryTerm sym uz (BVAdd (bvWidth x) (min x y) (max x y))

    | otherwise =
      sbMakeElt sym $ BVAdd (bvWidth x) (min x y) (max x y)

  bvMul sym x y
    | Just 0 <- asUnsignedBV x = return x
    | Just 1 <- asUnsignedBV x = return y
    | Just 0 <- asUnsignedBV y = return y
    | Just 1 <- asUnsignedBV y = return x
    | Just i <- asUnsignedBV x, Just j <- asUnsignedBV y =
      bvLit sym (bvWidth x) $ i * j
    | x <= y =
      sbMakeElt sym $ BVMul (bvWidth x) x y
    | otherwise =
      sbMakeElt sym $ BVMul (bvWidth x) y x

  bvIsNonzero sym x
    | Just (BVIte _ _ p t f) <- asApp x = do
          t' <- bvIsNonzero sym t
          f' <- bvIsNonzero sym f
          itePred sym p t' f'
    | otherwise = do
          let w = bvWidth x
          zro <- bvLit sym w 0
          notPred sym =<< bvEq sym x zro

  bvUdiv = bvBinOp1 div BVUdiv
  bvUrem = bvBinOp1 rem BVUrem
  bvSdiv = bvSignedBinOp div BVSdiv
  bvSrem = bvSignedBinOp rem BVSrem

  bvUnary sym u
    | Just v <-  UnaryBV.asConstant u =
      bvLit sym (UnaryBV.width u) v
    | otherwise =
      sbMakeElt sym (BVUnaryTerm u)

  mkStruct sym args = do
    sbMakeElt sym $ StructCtor (fmapFC exprType args) args

  structField sym s i
    | Just (StructCtor _ args) <- asApp s = return $! args Ctx.! i
    | otherwise = do
      case exprType s of
        BaseStructRepr flds ->
          sbMakeElt sym $ StructField s i (flds Ctx.! i)

  structIte sym p x y
    | Just TrueBool     <- asApp p = return x
    | Just FalseBool    <- asApp p = return y
    | Just (NotBool pn) <- asApp p = structIte sym pn y x
    | x == y    = return x
    | otherwise =
      case exprType x of
        BaseStructRepr flds -> sbMakeElt sym $ StructIte flds p x y

  --------------------------------------------------------------------
  -- Symbolic array operations

  constantArray sym idxRepr v =
    sbMakeElt sym $ ConstantArray idxRepr (exprType v) v

  arrayFromFn sym fn = do
    sbNonceElt sym $ ArrayFromFn fn

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
        base <- arrayMap sym f (fmapFC underlyingArrayMapElt arrays)

        -- This lookups a given index in an array used as an argument.
        let evalArgs :: Ctx.Assignment IndexLit (idx ::> itp)
                        -- ^ A representatio of the concrete index (if defined).
                        -> Ctx.Assignment (Elt t)  (idx ::> itp)
                           -- ^ The index to use.
                        -> ArrayResultWrapper (Elt t) (idx ::> itp) d
                           -- ^ The array to get the value at.
                        -> IO (Elt t d)
            evalArgs const_idx sym_idx a = do
              sbConcreteLookup sym (unwrapArrayResult a) (Just const_idx) sym_idx
        let evalIndex :: SimpleSymFn t ctx ret
                      -> Ctx.Assignment (ArrayResultWrapper (Elt t) (i::>itp)) ctx
                      -> Ctx.Assignment IndexLit (i::>itp)
                      -> IO (Elt t ret)
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
      sbNonceElt sym $ MapOverArrays f idx arrays

  arrayUpdate sym arr i v
      -- Update at concrete index.
    | Just ci <- asConcreteIndices i =
      case asApp arr of
        Just (ArrayMap idx tp m def) -> do
          let new_map =
                case asApp def of
                  Just (ConstantArray _ _ cns) | v == cns -> Hash.mapDelete ci m
                  _ -> Hash.mapInsert ci v m
          sbMakeElt sym $ ArrayMap idx tp new_map def
        _ -> do
          let idx = fmapFC exprType  i
          let bRepr = exprType v
          let new_map = Map.singleton ci v
          sbMakeElt sym $ ArrayMap idx bRepr (Hash.mkMap new_map) arr
    | otherwise = do
      let bRepr = exprType v
      sbMakeElt sym (UpdateArray bRepr (fmapFC exprType i)  arr i v)

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
      sbMakeElt sym $ ArrayMap idx_tps baseRepr new_map def_map

  arrayIte sym p x y
     | Just b <- asConstantPred p = return $! if b then x else y
     | x == y = return x
       --  Extract all concrete updates out.
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

           sbMakeElt sym $ ArrayMap idxRepr bRepr mz z'

     | otherwise =
       case exprType x of
         BaseArrayRepr idxRepr bRepr ->
            sbMakeElt sym (MuxArray idxRepr bRepr p x y)

  arrayEq sym x y
    | x == y =
      return $! truePred sym
    | otherwise =
      sbMakeElt sym $! ArrayEq x y


  arrayTrueOnEntries sym f a
    | Just True <- eltAbsValue a =
      return $ truePred sym
    | Just (IndicesInRange _ bnds) <- asMatlabSolverFn f
    , Just v <- asNatBounds bnds = do
      let h :: Elt t (BaseArrayType (i::>it) BaseBoolType)
            -> BoolElt t
            -> Ctx.Assignment (Elt t) (i::>it)
            -> IO (BoolElt t)
          h a0 p i = andPred sym p =<< arrayLookup sym a0 i
      foldIndicesInRangeBounds sym (h a) (truePred sym) v

    | otherwise =
      sbNonceElt sym $! ArrayTrueOnEntries f a

  ----------------------------------------------------------------------
  -- Lossless (injective) conversions

  natToInteger sym x
    | NatElt n l <- x = return $! IntElt (toInteger n) l
    | Just (IntegerToNat y) <- asApp x = return y
    | otherwise = sbMakeElt sym (NatToInteger x)

  integerToNat sb x
    | IntElt i l <- x
    , 0 <= i
    , i <= toInteger (maxBound :: Nat) = do
      return $! NatElt (fromIntegral (max 0 i)) l
    | Just (NatToInteger y) <- asApp x = return y
    | otherwise =
      sbMakeElt sb (IntegerToNat x)

  integerToReal sym x
    | IntElt i l <- x = return $! RatElt (toRational i) l
    | Just (RealToInteger y) <- asApp x = return y
    | otherwise  = sbMakeElt sym (IntegerToReal x)

  realToInteger sym x
      -- Ground case
    | RatElt r l <- x = return $! IntElt (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | otherwise =
      sbMakeElt sym (RealToInteger x)

  bvToInteger sym x
    | Just i <- asUnsignedBV x = intLit sym i
    | otherwise = sbMakeElt sym (BVToInteger x)

  sbvToInteger sym x
    | Just i <- asSignedBV x = intLit sym i
    | otherwise = sbMakeElt sym (SBVToInteger x)

  integerToSBV sym (IntElt i _) w =
    bvLit sym w i
  integerToSBV sym xr w
    | Just (SBVToInteger r) <- asApp xr = intSetWidth sym r w
  integerToSBV sym xr w =
    sbMakeElt sym (IntegerToSBV xr w)

  integerToBV sym xr w
    | IntElt i _ <- xr =
      bvLit sym w $ unsignedClamp w $ toInteger i
    | Just (BVToInteger r) <- asApp xr =
      uintSetWidth sym r w
    | otherwise =
      sbMakeElt sym (IntegerToBV xr w)

  realRound sym x
      -- Ground case
    | RatElt r l <- x = return $ IntElt (roundAway r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (eltAbsValue x) =
      sbMakeElt sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeElt sym (RoundReal x)

  realFloor sym x
      -- Ground case
    | RatElt r l <- x = return $ IntElt (floor r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (eltAbsValue x) =
      sbMakeElt sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeElt sym (FloorReal x)

  realCeil sym x
      -- Ground case
    | RatElt r l <- x = return $ IntElt (ceiling r) l
      -- Match integerToReal
    | Just (IntegerToReal xi) <- asApp x = return xi
      -- Static case
    | Just True <- ravIsInteger (eltAbsValue x) =
      sbMakeElt sym (RealToInteger x)
      -- Unsimplified case
    | otherwise = sbMakeElt sym (CeilReal x)

  ----------------------------------------------------------------------
  -- Real operations

  realLit sb r = do
    l <- curProgramLoc sb
    return (RatElt r l)

  realZero = sbZero

  realEq sym x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)
      -- Use range check
    | Just b <- ravCheckEq (eltAbsValue x) (eltAbsValue y) = do
        return $ backendPred sym b
    | SBVToReal xbv <- x, SBVToReal ybv <- y = do
      let wx = bvWidth xbv
      let wy = bvWidth ybv
      -- Sign extend to largest bitvector and compare.
      case compareNat wx wy of
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
    | SBVToReal xbv <- x, RatElt yr _ <- y = do
      let w = bvWidth xbv
      let yi = numerator yr
      case () of
            -- Return false if constant is out of range.
        _ | denominator yr /= 1 || yi < minSigned w || yi > maxSigned w -> do
            return (falsePred sym)
        -- Otherwise use bitvector comparison.
          | otherwise -> do
              bvEq sym xbv =<< bvLit sym w yi
    | SBVToReal xbv <- y, RatElt yr _ <- x = do
      let w = bvWidth xbv
      let yi = numerator yr
      case () of
            -- Return false if constant is out of range.
        _ | denominator yr /= 1 || yi < minSigned w || yi > maxSigned w -> do
            return (falsePred sym)
        -- Otherwise use bitvector comparison.
          | otherwise -> do
              bvEq sym xbv =<< bvLit sym w yi

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
    , not (WSum.isZero z) = do
      xr <- realSum sym x'
      yr <- realSum sym y'
      realEq sym xr yr

    | otherwise = do
      sbMakeElt sym $ RealEq (min x y) (max x y)

  realLe sym x y
      -- Check for syntactic equality.
    | x == y = return (truePred sym)
      -- Use range check
    | Just b <- ravCheckLe (eltAbsValue x) (eltAbsValue y) =
      return $ backendPred sym b
      -- Check with two bitvectors.
    | SBVToReal xbv <- x, SBVToReal ybv <- y = do
      let wx = bvWidth xbv
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
      -- Compare to BV lower bound.
    | SBVToReal xbv <- x = do
      let w = bvWidth xbv
      l <- curProgramLoc sym
      b_max <- realGe sym y (RatElt (toRational (maxSigned w)) l)
      b_min <- realGe sym y (RatElt (toRational (minSigned w)) l)
      orPred sym b_max =<< andPred sym b_min =<< (bvSle sym xbv =<< realToSBV sym w y)

      -- Compare to SBV upper bound.
    | SBVToReal ybv <- y = do
      let w = bvWidth ybv
      l <- curProgramLoc sym
      b_min <- realLe sym x (RatElt (toRational (minSigned w)) l)
      b_max <- realLe sym x (RatElt (toRational (maxSigned w)) l)
      orPred sym b_min
        =<< andPred sym b_max
        =<< (\xbv -> bvSle sym xbv ybv) =<< realToSBV sym w x

      -- Stength reductions on a non-linear constraint to piecewise linear.
    | RatElt 0 _ <- x, Just (RealMul u v) <- asApp y = do
      leNonneg realLe x sym u v
      -- Another strength reduction
    | Just (RealMul u v) <- asApp x, RatElt 0 _ <- y = do
      leNonpos realLe y sym u v

      -- Simplify ite expressions when one of the values is ground.
      -- This appears to occur fairly often in MATLAB due to range checks.
    | isJust (asRational x)
    , Just (RealIte yc y1 y2) <- asApp y
    , isJust (asRational y1) || isJust (asRational y2) = do
      c1 <- realLe sym x y1
      c2 <- realLe sym x y2
      itePred sym yc c1 c2

      -- Simplify ite expressions when one of the values is ground.
      -- This appears to occur fairly often in MATLAB due to range checks.
    | isJust (asRational y)
    , Just (RealIte xc x1 x2) <- asApp x
    , isJust (asRational x1) || isJust (asRational x2) = do
      c1 <- realLe sym x1 y
      c2 <- realLe sym x2 y
      itePred sym xc c1 c2


      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
    , not (WSum.isZero z) = do
      xr <- realSum sym x'
      yr <- realSum sym y'
      realLe sym xr yr

      -- Default case
    | otherwise = sbMakeElt sym $ RealLe x y

  realIte sym c x y
    | Just True  <- asConstantPred c = return x
    | Just False <- asConstantPred c = return y
    | Just (NotBool cn) <- asApp c = realIte sym cn y x
    | x == y = return x

      -- Try to extract common sum information.
    | (z, x',y') <- WSum.extractCommon (asWeightedSum x) (asWeightedSum y)
    , not (WSum.isZero z) = do
      xr <- realSum sym x'
      yr <- realSum sym y'
      r <- sbMakeElt sym (RealIte c xr yr)
      realSum sym $! z `WSum.addVar` r

    | otherwise = do
      sbMakeElt sym (RealIte c x y)

  realNeg sym x = realScalarMul sym (-1) x

  realAdd sym x y =
    case (viewSum x, viewSum y) of
      (ConstantSum 0, _) -> return y
      (_, ConstantSum 0) -> return x

      (ConstantSum xc, ConstantSum yc) ->
        realLit sym (xc + yc)

      (ConstantSum xc, LinearSum ys) ->
        realSum' sym (ys `WSum.addConstant` xc)
      (LinearSum xs, ConstantSum yc) ->
        realSum' sym (xs `WSum.addConstant` yc)

      (ConstantSum xc, GeneralSum) -> do
        realSum' sym (WSum.var y `WSum.addConstant` xc)
      (GeneralSum, ConstantSum yc) -> do
        realSum' sym (WSum.var x `WSum.addConstant` yc)

      (LinearSum xs, LinearSum ys) -> realSum sym (xs `WSum.add` ys)
      (LinearSum xs, GeneralSum)   -> realSum sym (xs `WSum.addVar` y)
      (GeneralSum, LinearSum ys)   -> realSum sym (ys `WSum.addVar` x)
      (GeneralSum, GeneralSum)     -> realSum sym (x  `WSum.addVars` y)

  realMul sym x y
    | Just xd <- asRational x =
      realScalarMul sym xd y
    | Just yd <- asRational y =
      realScalarMul sym yd x
      -- (cx*xx) * y = cx*(xx*y)
    | Just (RealMul (RatElt cx _) xx) <- asApp x = do
      realScalarMul sym cx =<< realMul sym xx y
      -- x*(cy*yy) = cy*(x*yy)
    | Just (RealMul (RatElt cy _) yy) <- asApp y = do
      realScalarMul sym cy =<< realMul sym x yy
    | otherwise =
      sbMakeElt sym $ RealMul (min x y) (max x y)

  realSum sym s
    | Just c <- WSum.asConstant s =
      realLit sym c
    | Just r <- WSum.asVar s =
      return r
    | otherwise =
      sbMakeElt sym $ RealSum s

  realDiv sym x y
    | Just 0 <- asRational x =
      return x
    | Just xd <- asRational x, Just yd <- asRational y, yd /= 0 = do
      realLit sym (xd / yd)
      -- Handle division by a constant.
    | Just yd <- asRational y, yd /= 0 = do
      realScalarMul sym (1 / yd) x
    | otherwise =
      sbMakeElt sym $ RealDiv x y

  isInteger sb x
    | Just r <- asRational x = return $ backendPred sb (denominator r == 1)
    | Just b <- ravIsInteger (eltAbsValue x) = return $ backendPred sb b
    | otherwise = sbMakeElt sb $ RealIsInteger x

  realSqrt sym x = do
    let sqrt_dbl :: Double -> Double
        sqrt_dbl = sqrt
    case x of
      RatElt r _
        | r <= 0 -> realLit sym 0
        | Just w <- tryRationalSqrt r -> realLit sym w
        | sbFloatReduce sym -> realLit sym (toRational (sqrt_dbl (fromRational r)))
      _ -> sbMakeElt sym (RealSqrt x)

  realPi sym = do
    if sbFloatReduce sym then
      realLit sym (toRational (pi :: Double))
     else
      sbMakeElt sym Pi

  realSin sym x =
    case asRational x of
      Just 0 -> realLit sym 0
      Just c | sbFloatReduce sym -> realLit sym (toRational (sin (toDouble c)))
      _ -> sbMakeElt sym (RealSin x)

  realCos sym x =
    case asRational x of
      Just 0 -> realLit sym 1
      Just c | sbFloatReduce sym -> realLit sym (toRational (cos (toDouble c)))
      _ -> sbMakeElt sym (RealCos x)

  realAtan2 sb y x = do
    case (asRational y, asRational x) of
      (Just 0, _) -> realLit sb 0
      (Just yc, Just xc) | sbFloatReduce sb -> do
        realLit sb (toRational (atan2 (toDouble yc) (toDouble xc)))
      _ -> sbMakeElt sb (RealATan2 y x)

  realSinh sb x =
    case asRational x of
      Just 0 -> realLit sb 0
      Just c | sbFloatReduce sb -> realLit sb (toRational (sinh (toDouble c)))
      _ -> sbMakeElt sb (RealSinh x)

  realCosh sb x =
    case asRational x of
      Just 0 -> realLit sb 1
      Just c | sbFloatReduce sb -> realLit sb (toRational (cosh (toDouble c)))
      _ -> sbMakeElt sb (RealCosh x)

  realExp sym x
    | Just 0 <- asRational x = realLit sym 1
    | Just c <- asRational x, sbFloatReduce sym = realLit sym (toRational (exp (toDouble c)))
    | otherwise = sbMakeElt sym (RealExp x)

  realLog sym x =
    case asRational x of
      Just c | sbFloatReduce sym -> realLit sym (toRational (log (toDouble c)))
      _ -> sbMakeElt sym (RealLog x)

  ----------------------------------------------------------------------
  -- Cplx operations

  mkComplex sym c = sbMakeElt sym (Cplx c)

  getRealPart _ e
    | Just (Cplx (r :+ _)) <- asApp e = return r
  getRealPart sym x =
    sbMakeElt sym (RealPart x)

  getImagPart _ e
    | Just (Cplx (_ :+ i)) <- asApp e = return i
  getImagPart sym x =
    sbMakeElt sym (ImagPart x)

  cplxGetParts _ e
    | Just (Cplx c) <- asApp e = return c
  cplxGetParts sym x =
    (:+) <$> sbMakeElt sym (RealPart x)
         <*> sbMakeElt sym (ImagPart x)

instance IsSymInterface (SimpleBuilder t st) where
  stopCaching = sbStopCaching
  restartCaching = sbRestartCaching

  freshConstant sym nm tp = do
    v <- sbMakeBoundVar sym nm tp UninterpVarKind
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarElt v

  freshLatch sym nm tp = do
    v <- sbMakeBoundVar sym nm tp LatchVarKind
    updateVarBinding sym nm (VarSymbolBinding v)
    return $! BoundVarElt v

  freshBoundVar sym nm tp =
    sbMakeBoundVar sym nm tp QuantifierVarKind

  varExpr _ = BoundVarElt

  forallPred sym bv e = sbNonceElt sym $ Forall bv e

  existsPred sym bv e = sbNonceElt sym $ Exists bv e

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
    let fn = SimpleSymFn { symFnId   = n
                         , symFnName = fn_name
                         , symFnInfo = DefinedFnInfo bound_vars result evalFn
                         , symFnLoc  = l
                         }
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  freshTotalUninterpFn sym fn_name arg_types ret_type = do
    n <- sbFreshSymFnNonce sym
    l <- curProgramLoc sym
    let fn = SimpleSymFn { symFnId = n
                         , symFnName = fn_name
                         , symFnInfo = UninterpFnInfo arg_types ret_type
                         , symFnLoc = l
                         }
    seq fn $ do
    updateVarBinding sym fn_name (FnSymbolBinding fn)
    return fn

  applySymFn sym fn args = do
    -- Check side conditions.
   case symFnInfo fn of
     DefinedFnInfo bound_vars e shouldEval
       | shouldEval args -> do
           evalBoundVars sym e bound_vars args
     MatlabSolverFnInfo f _ _ -> do
       evalMatlabSolverFn f sym args
     _ -> sbNonceElt sym $! FnApp fn args

--------------------------------------------------------------------------------
-- MatlabSymbolicArrayBuilder instance

instance MatlabSymbolicArrayBuilder (SimpleBuilder t st) where
  mkMatlabSolverFn sym fn_id = do
    let key = MatlabFnWrapper fn_id
    mr <- stToIO $ PH.lookup (sbMatlabFnCache sym) key
    case mr of
      Just (SimpleSymFnWrapper f) -> return f
      Nothing -> do
        let tps = matlabSolverArgTypes fn_id
        vars <- traverseFC (freshBoundVar sym emptySymbol) tps
        r <- evalMatlabSolverFn fn_id sym (fmapFC BoundVarElt vars)
--        f <- definedFn sym emptySymbol vars r (\_ -> True)

        l <- curProgramLoc sym
        n <- sbFreshSymFnNonce sym
        let f = SimpleSymFn { symFnId   = n
                            , symFnName = emptySymbol
                            , symFnInfo = MatlabSolverFnInfo fn_id vars r
                            , symFnLoc  = l
                            }
        updateVarBinding sym emptySymbol (FnSymbolBinding f)
        stToIO $ PH.insert (sbMatlabFnCache sym) key (SimpleSymFnWrapper f)
        return f
