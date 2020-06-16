-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Evaluation
-- Description      : Evaluation functions for Crucible core expressions
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides operations evaluating Crucible expressions.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Simulator.Evaluation
  ( EvalAppFunc
  , evalApp
  , selectedIndices
  , indexSymbolic
  , integerAsChar
  , complexRealAsChar
  , indexVectorWithSymNat
  , adjustVectorWithSymNat
  , updateVectorWithSymNat
  ) where

import           Prelude hiding (pred)

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad
import qualified Data.BitVector.Sized as BV
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word
import           Numeric ( showHex )
import           Numeric.Natural

import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC

import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial (pattern PE, pattern Unassigned, joinMaybePE)
import           What4.Utils.Complex
import           What4.WordMap

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MuxTree

------------------------------------------------------------------------
-- Utilities


-- | Given a list of Booleans l, @selectedIndices@ returns the indices of
-- true values in @l@.
selectedIndices :: [Bool] -> [Natural]
selectedIndices l = catMaybes $ Prelude.zipWith selectIndex l [1..]
  where selectIndex True i  = Just i
        selectIndex False _ = Nothing

------------------------------------------------------------------------
-- Coercion functions

integerAsChar :: Integer -> Word16
integerAsChar i = fromInteger ((i `max` 0) `min` (2^(16::Int)-1))

complexRealAsChar :: (MonadFail m, IsExpr val)
                  => val BaseComplexType
                  -> m Word16
complexRealAsChar v = do
  case cplxExprAsRational v of
    -- Check number is printable.
    Just r | otherwise -> return (integerAsChar (floor r))
    Nothing -> fail "Symbolic value cannot be interpreted as a character."
    -- XXX: Should this be a panic?
    -- XXX: We should move this to crucible-matlab

------------------------------------------------------------------------
-- Evaluating expressions


-- | Helper method for implementing 'indexSymbolic'
indexSymbolic' :: IsSymInterface sym
               => sym
               -> (Pred sym -> a -> a -> IO a)
                  -- ^ Function for merging valeus
               -> ([Natural] -> IO a) -- ^ Concrete index function.
               -> [Natural] -- ^ Values of processed indices (in reverse order)
               -> [(Natural,Natural)] -- ^ Bounds on remaining indices.
               -> [SymNat sym] -- ^ Remaining indices.
               -> IO a
indexSymbolic' _ _ f p [] _ = f (reverse p)
indexSymbolic' _ _ f p _ [] = f (reverse p)
indexSymbolic' sym iteFn f p ((l,h):nl) (si:il) = do
  let subIndex idx = indexSymbolic' sym iteFn f (idx:p) nl il
  case asNat si of
    Just i
      | l <= i && i <= h -> subIndex i
      | otherwise -> addFailedAssertion sym (AssertFailureSimError msg details)
        where msg = "Index outside matrix dimensions." ++ show (l,i,h)
              details = unwords ["Index", show i, "is outside of range", show (l, h)]
    Nothing ->
      do ensureInRange sym l h si "Index outside matrix dimensions."
         let predFn i = natEq sym si =<< natLit sym i
         muxRange predFn iteFn subIndex l h


ensureInRange ::
  IsSymInterface sym =>
  sym ->
  Natural ->
  Natural ->
  SymNat sym ->
  String ->
  IO ()
ensureInRange sym l h si msg =
  do l_sym <- natLit sym l
     h_sym <- natLit sym h
     inRange <- join $ andPred sym <$> natLe sym l_sym si <*> natLe sym si h_sym
     assert sym inRange (AssertFailureSimError msg details)
  where details = unwords ["Range is", show (l, h)]



-- | Lookup a value in an array that may be at a symbolic offset.
--
-- This function takes a list of symbolic indices as natural numbers
-- along with a pair of lower and upper bounds for each index.
-- It assumes that the indices are all in range.
indexSymbolic :: IsSymInterface sym
              => sym
              -> (Pred sym -> a  -> a -> IO a)
                 -- ^ Function for combining results together.
              -> ([Natural] -> IO a) -- ^ Concrete index function.
              -> [(Natural,Natural)] -- ^ High and low bounds at the indices.
              -> [SymNat sym]
              -> IO a
indexSymbolic sym iteFn f = indexSymbolic' sym iteFn f []

-- | Evaluate an indexTermterm to an index value.
evalBase :: IsSymInterface sym =>
            sym
         -> (forall utp . f utp -> IO (RegValue sym utp))
         -> BaseTerm f vtp
         -> IO (SymExpr sym vtp)
evalBase _ evalSub (BaseTerm _tp e) = evalSub e

-- | Get value stored in vector at a symbolic index.
indexVectorWithSymNat :: IsSymInterface sym
                      => sym
                      -> (Pred sym -> a -> a -> IO a)
                         -- ^ Ite function
                      -> V.Vector a
                      -> SymNat sym
                      -> IO a
indexVectorWithSymNat sym iteFn v si =
  Ex.assert (n > 0) $
  case asNat si of
    Just i | 0 <= i && i < n -> return (v V.! fromIntegral i)
           | otherwise -> addFailedAssertion sym (AssertFailureSimError msg details)
    Nothing ->
      do let predFn i = natEq sym si =<< natLit sym i
         let getElt i = return (v V.! fromIntegral i)
         ensureInRange sym 0 (n - 1) si msg
         muxRange predFn iteFn getElt 0 (n - 1)
  where
  n   = fromIntegral (V.length v)
  msg = "Vector index out of range"
  details = unwords ["Range is", show (0 :: Natural, n)]



-- | Update a vector at a given natural number index.
updateVectorWithSymNat :: IsSymInterface sym
                       => sym
                          -- ^ Symbolic backend
                       -> (Pred sym -> a -> a -> IO a)
                          -- ^ Ite function
                       -> V.Vector a
                          -- ^ Vector to update
                       -> SymNat sym
                          -- ^ Index to update
                       -> a
                          -- ^ New value to assign
                       -> IO (V.Vector a)
updateVectorWithSymNat sym iteFn v si new_val = do
  adjustVectorWithSymNat sym iteFn v si (\_ -> return new_val)

-- | Update a vector at a given natural number index.
adjustVectorWithSymNat :: IsSymInterface sym
                       => sym
                          -- ^ Symbolic backend
                       -> (Pred sym -> a -> a -> IO a)
                          -- ^ Ite function
                       -> V.Vector a
                          -- ^ Vector to update
                       -> SymNat sym
                          -- ^ Index to update
                       -> (a -> IO a)
                          -- ^ Adjustment function to apply
                       -> IO (V.Vector a)
adjustVectorWithSymNat sym iteFn v si adj =
  case asNat si of
    Just i

      | i < fromIntegral n ->
        do new_val <- adj (v V.! fromIntegral i)
           return $ v V.// [(fromIntegral i, new_val)]

      | otherwise ->
        addFailedAssertion sym $ AssertFailureSimError msg (details i)

    Nothing ->
      do ensureInRange sym 0 (fromIntegral (n-1)) si msg
         V.generateM n setFn
      where
      setFn j =
        do -- Compare si and j.
            c <- natEq sym si =<< natLit sym (fromIntegral j)
            -- Select old value or new value
            case asConstantPred c of
              Just True  -> adj (v V.! j)
              Just False -> return (v V.! j)
              Nothing ->
                do new_val <- adj (v V.! j)
                   iteFn c new_val (v V.! j)


  where
  n = V.length v
  msg = "Illegal vector index"
  details i = "Illegal index " ++ show i ++ "given to updateVectorWithSymNat"

type EvalAppFunc sym app = forall f.
  (forall tp. f tp -> IO (RegValue sym tp)) ->
  (forall tp. app f tp -> IO (RegValue sym tp))

{-# INLINE evalApp #-}
-- | Evaluate the application.
evalApp :: forall sym ext.
           ( IsSymInterface sym
           )
        => sym
        -> IntrinsicTypes sym
        -> (Int -> String -> IO ())
           -- ^ Function for logging messages.
        -> EvalAppFunc sym (ExprExtension ext)
        -> EvalAppFunc sym (App ext)
evalApp sym itefns _logFn evalExt (evalSub :: forall tp. f tp -> IO (RegValue sym tp)) a0 = do
  case a0 of

    BaseIsEq tp xe ye -> do
      x <- evalBase sym evalSub (BaseTerm tp xe)
      y <- evalBase sym evalSub (BaseTerm tp ye)
      isEq sym x y

    BaseIte tp ce xe ye -> do
      c <- evalSub ce
      case asConstantPred c of
        Just True  -> evalSub xe
        Just False -> evalSub ye
        Nothing -> do
          x <- evalBase sym evalSub (BaseTerm tp xe)
          y <- evalBase sym evalSub (BaseTerm tp ye)
          baseTypeIte sym c x y

    ----------------------------------------------------------------------
    ExtensionApp x -> evalExt evalSub x

    ----------------------------------------------------------------------
    -- ()

    EmptyApp -> return ()

    ----------------------------------------------------------------------
    -- Any

    PackAny tp x -> do
      xv <- evalSub x
      return (AnyValue tp xv)

    UnpackAny tp x -> do
      xv <- evalSub x
      case xv of
        AnyValue tpv v
          | Just Refl <- testEquality tp tpv ->
               return $! PE (truePred sym) v
          | otherwise ->
               return Unassigned

    ----------------------------------------------------------------------
    -- Bool

    BoolLit b -> return $ backendPred sym b
    Not x -> do
      r <- evalSub x
      notPred sym r
    And x y -> do
      xv <- evalSub x
      yv <- evalSub y
      andPred sym xv yv
    Or x y -> do
      xv <- evalSub x
      yv <- evalSub y
      orPred sym xv yv
    BoolXor x y -> do
      xv <- evalSub x
      yv <- evalSub y
      xorPred sym xv yv

    ----------------------------------------------------------------------
    -- Nat

    NatLit n -> natLit sym n
    NatLt xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natLt sym x y
    NatLe xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natLe sym x y
    NatAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natAdd sym x y
    NatSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natSub sym x y
    NatMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natMul sym x y
    NatDiv xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natDiv sym x y
    NatMod xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natMod sym x y

    ----------------------------------------------------------------------
    -- Int

    IntLit n -> intLit sym n
    IntLe xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intLe sym x y
    IntLt xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intLt sym x y
    IntNeg xe -> do
      x <- evalSub xe
      intNeg sym x
    IntAbs xe -> do
      x <- evalSub xe
      intAbs sym x
    IntAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intAdd sym x y
    IntSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intSub sym x y
    IntMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intMul sym x y
    IntDiv xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intDiv sym x y
    IntMod xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intMod sym x y

    --------------------------------------------------------------------
    -- Maybe

    JustValue _ e -> do
      r <- evalSub e
      return $! PE (truePred sym) r
    NothingValue _ -> do
      return Unassigned
    FromJustValue _ maybe_expr msg_expr -> do
      maybe_val <- evalSub maybe_expr
      case maybe_val of
        -- Special case to avoid forcing evaluation of msg.
        PE (asConstantPred -> Just True) v -> return v
        _ -> do
          msg <- evalSub msg_expr
          case asString msg of
            Just (UnicodeLiteral msg') -> readPartExpr sym maybe_val (GenericSimError (Text.unpack msg'))
            Nothing ->
              addFailedAssertion sym $
                Unsupported "Symbolic string in fromJustValue"

    ----------------------------------------------------------------------
    -- Recursive Types

    RollRecursive _ _ e   -> RolledType <$> evalSub e
    UnrollRecursive _ _ e -> unroll <$> evalSub e

    ----------------------------------------------------------------------
    -- Vector

    VectorLit _ v -> traverse evalSub v
    VectorReplicate _ n_expr e_expr -> do
      ne <- evalSub n_expr
      case asNat ne of
        Nothing -> addFailedAssertion sym $
                      Unsupported "vectors with symbolic length"
        Just n -> do
          e <- evalSub e_expr
          return $ V.replicate (fromIntegral n) e
    VectorIsEmpty r -> do
      v <- evalSub r
      return $ backendPred sym (V.null v)
    VectorSize v_expr -> do
      v <- evalSub v_expr
      natLit sym (fromIntegral (V.length v))
    VectorGetEntry rtp v_expr i_expr -> do
      v <- evalSub v_expr
      i <- evalSub i_expr
      indexVectorWithSymNat sym (muxRegForType sym itefns rtp) v i
    VectorSetEntry rtp v_expr i_expr n_expr -> do
      v <- evalSub v_expr
      i <- evalSub i_expr
      n <- evalSub n_expr
      updateVectorWithSymNat sym (muxRegForType sym itefns rtp) v i n
    VectorCons _ e_expr v_expr -> do
      e <- evalSub e_expr
      v <- evalSub v_expr
      return $ V.cons e v

    --------------------------------------------------------------------
    -- Symbolic Arrays

    SymArrayLookup _ a i -> do
      join $ arrayLookup sym <$> evalSub a <*> traverseFC (evalBase sym evalSub) i

    SymArrayUpdate  _ a i v -> do
      join $ arrayUpdate sym
        <$> evalSub a
        <*> traverseFC (evalBase sym evalSub) i
        <*> evalSub v

    ----------------------------------------------------------------------
    -- Handle

    HandleLit h -> return (HandleFnVal h)

    Closure _ _ h_expr tp v_expr -> do
      h <- evalSub h_expr
      v <- evalSub v_expr
      return $! ClosureFnVal h tp v

    ----------------------------------------------------------------------
    -- RealVal

    RationalLit d -> realLit sym d
    RealNeg xe -> do
      x <- evalSub xe
      realNeg sym x
    RealAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realAdd sym x y
    RealSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realSub sym x y
    RealMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realMul sym x y
    RealDiv xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realDiv sym x y
    RealMod xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realMod sym x y
    RealLt x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      realLt sym x y
    RealLe x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      realLe sym x y
    RealIsInteger x_expr -> do
      x <- evalSub x_expr
      isInteger sym x

    ----------------------------------------------------------------------
    -- Float

    FloatLit f -> iFloatLitSingle sym f
    DoubleLit d -> iFloatLitDouble sym d
    X86_80Lit ld -> iFloatLitLongDouble sym ld
    FloatNaN fi -> iFloatNaN sym fi
    FloatPInf fi -> iFloatPInf sym fi
    FloatNInf fi -> iFloatNInf sym fi
    FloatPZero fi -> iFloatPZero sym fi
    FloatNZero fi -> iFloatNZero sym fi
    FloatNeg _ (x_expr :: f (FloatType fi)) ->
      iFloatNeg @_ @fi sym =<< evalSub x_expr
    FloatAbs _ (x_expr :: f (FloatType fi)) ->
      iFloatAbs @_ @fi sym =<< evalSub x_expr
    FloatSqrt _ rm (x_expr :: f (FloatType fi)) ->
      iFloatSqrt @_ @fi sym rm =<< evalSub x_expr
    FloatAdd _ rm (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatAdd @_ @fi sym rm x y
    FloatSub _ rm (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatSub @_ @fi sym rm x y
    FloatMul _ rm (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatMul @_ @fi sym rm x y
    FloatDiv _ rm (x_expr :: f (FloatType fi)) y_expr -> do
      -- TODO: handle division by zero
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatDiv @_ @fi sym rm x y
    FloatRem _ (x_expr :: f (FloatType fi)) y_expr -> do
      -- TODO: handle division by zero
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatRem @_ @fi sym x y
    FloatMin _ (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatMin @_ @fi sym x y
    FloatMax _ (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatMax @_ @fi sym x y
    FloatFMA _ rm (x_expr :: f (FloatType fi)) y_expr z_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      z <- evalSub z_expr
      iFloatFMA @_ @fi sym rm x y z
    FloatEq (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatEq @_ @fi sym x y
    FloatFpEq (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatFpEq @_ @fi sym x y
    FloatIte _ c_expr (x_expr :: f (FloatType fi)) y_expr -> do
      c <- evalSub c_expr
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatIte @_ @fi sym c x y
    FloatLt (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatLt @_ @fi sym x y
    FloatLe (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatLe @_ @fi sym x y
    FloatGt (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatGt @_ @fi sym x y
    FloatGe (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatGe @_ @fi sym x y
    FloatNe (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatNe @_ @fi sym x y
    FloatFpNe (x_expr :: f (FloatType fi)) y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      iFloatFpNe @_ @fi sym x y
    FloatCast fi rm (x_expr :: f (FloatType fi')) ->
      iFloatCast @_ @_ @fi' sym fi rm =<< evalSub x_expr
    FloatFromBinary fi x_expr -> iFloatFromBinary sym fi =<< evalSub x_expr
    FloatToBinary fi x_expr -> iFloatToBinary sym fi =<< evalSub x_expr
    FloatFromBV fi rm x_expr -> iBVToFloat sym fi rm =<< evalSub x_expr
    FloatFromSBV fi rm x_expr -> iSBVToFloat sym fi rm =<< evalSub x_expr
    FloatFromReal fi rm x_expr -> iRealToFloat sym fi rm =<< evalSub x_expr
    FloatToBV w rm (x_expr :: f (FloatType fi)) ->
      iFloatToBV @_ @_ @fi sym w rm =<< evalSub x_expr
    FloatToSBV w rm (x_expr :: f (FloatType fi)) ->
      iFloatToSBV @_ @_ @fi sym w rm =<< evalSub x_expr
    FloatToReal (x_expr :: f (FloatType fi)) ->
      iFloatToReal @_ @fi sym =<< evalSub x_expr
    FloatIsNaN (x_expr :: f (FloatType fi)) ->
      iFloatIsNaN @_ @fi sym =<< evalSub x_expr
    FloatIsInfinite (x_expr :: f (FloatType fi)) ->
      iFloatIsInf @_ @fi sym =<< evalSub x_expr
    FloatIsZero (x_expr :: f (FloatType fi)) ->
      iFloatIsZero @_ @fi sym =<< evalSub x_expr
    FloatIsPositive (x_expr :: f (FloatType fi)) ->
      iFloatIsPos @_ @fi sym =<< evalSub x_expr
    FloatIsNegative (x_expr :: f (FloatType fi)) ->
      iFloatIsNeg @_ @fi sym =<< evalSub x_expr
    FloatIsSubnormal (x_expr :: f (FloatType fi)) ->
      iFloatIsSubnorm @_ @fi sym =<< evalSub x_expr
    FloatIsNormal (x_expr :: f (FloatType fi)) ->
      iFloatIsNorm @_ @fi sym =<< evalSub x_expr

    ----------------------------------------------------------------------
    -- Conversions

    NatToInteger x_expr -> do
      x <- evalSub x_expr
      natToInteger sym x
    IntegerToReal x_expr -> do
      x <- evalSub x_expr
      integerToReal sym x
    RealToNat x_expr -> do
      x <- evalSub x_expr
      realToNat sym x
    BvToNat _ xe -> do
      bvToNat sym =<< evalSub xe
    BvToInteger _ xe -> do
      bvToInteger sym =<< evalSub xe
    SbvToInteger _ xe -> do
      sbvToInteger sym =<< evalSub xe
    RealFloor xe ->
      realFloor sym =<< evalSub xe
    RealCeil xe ->
      realCeil sym =<< evalSub xe
    RealRound xe ->
      realRound sym =<< evalSub xe
    IntegerToBV w xe -> do
      x <- evalSub xe
      integerToBV sym x w

    ----------------------------------------------------------------------
    -- ComplexReal

    Complex r_expr i_expr -> do
      r <- evalSub r_expr
      i <- evalSub i_expr
      mkComplex sym (r :+ i)
    RealPart c_expr -> getRealPart sym =<< evalSub c_expr
    ImagPart c_expr -> getImagPart sym =<< evalSub c_expr

    --------------------------------------------------------------------
    -- BVs

    BVUndef w ->
      freshConstant sym emptySymbol (BaseBVRepr w)

    BVLit w bv -> bvLit sym w bv

    BVConcat _ _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvConcat sym x y
    -- FIXME: there are probably some worthwhile special cases to exploit in "BVSelect"
    BVSelect idx n _ xe -> do
      x <- evalSub xe
      bvSelect sym idx n x
    BVTrunc w' _ xe -> do
      x <- evalSub xe
      bvTrunc sym w' x
    BVZext w' _ xe -> do
      x <- evalSub xe
      bvZext sym w' x
    BVSext w' _ xe -> do
      x <- evalSub xe
      bvSext sym w' x
    BVNot _ xe ->
      bvNotBits sym =<< evalSub xe
    BVAnd _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAndBits sym x y
    BVOr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvOrBits sym x y
    BVXor _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvXorBits sym x y
    BVAdd _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAdd sym x y
    BVNeg _ xe -> do
      x <- evalSub xe
      bvNeg sym x
    BVSub _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSub sym x y
    BVMul _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvMul sym x y
    BVUdiv _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUdiv sym x y
    BVSdiv _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSdiv sym x y
    BVUrem _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUrem sym x y
    BVSrem _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSrem sym x y

    BVUlt _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUlt sym x y
    BVSlt _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSlt sym x y
    BoolToBV w xe -> do
      x <- evalSub xe
      one <- bvLit sym w (BV.one w)
      zro <- bvLit sym w (BV.zero w)
      bvIte sym x one zro
    BVNonzero _ xe -> do
      x <- evalSub xe
      bvIsNonzero sym x
    BVShl _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvShl sym x y
    BVLshr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvLshr sym x y
    BVAshr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAshr sym x y
    BVCarry _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> addUnsignedOF sym x y
    BVSCarry _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> addSignedOF sym x y
    BVSBorrow _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> subSignedOF sym x y
    BVUle _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUle sym x y
    BVSle _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSle sym x y
    BVUMin _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      c <- bvUle sym x y
      bvIte sym c x y
    BVUMax _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      c <- bvUgt sym x y
      bvIte sym c x y
    BVSMin _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      c <- bvSle sym x y
      bvIte sym c x y
    BVSMax _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      c <- bvSgt sym x y
      bvIte sym c x y

    --------------------------------------------------------------------
    -- Word Maps

    EmptyWordMap w tp -> do
      emptyWordMap sym w tp

    InsertWordMap w tp ie ve me -> do
      i <- evalSub ie
      v <- evalSub ve
      m <- evalSub me
      insertWordMap sym w tp i v m

    LookupWordMap tp ie me -> do
      i <- evalSub ie
      m <- evalSub me
      x <- lookupWordMap sym (bvWidth i) tp i m
      let msg = "WordMap: read an undefined index" ++
                case asBV i of
                   Nothing  -> ""
                   Just (BV.BV idx) -> " 0x" ++ showHex idx ""
      let ex = ReadBeforeWriteSimError msg
      readPartExpr sym x ex

    LookupWordMapWithDefault tp ie me de -> do
      i <- evalSub ie
      m <- evalSub me
      d <- evalSub de
      x <- lookupWordMap sym (bvWidth i) tp i m
      case x of
        Unassigned -> return d
        PE p v -> do
          muxRegForType sym itefns (baseToType tp) p v d

    ---------------------------------------------------------------------
    -- Struct

    MkStruct _ exprs -> traverseFC (\x -> RV <$> evalSub x) exprs

    GetStruct st idx _ -> do
      struct <- evalSub st
      return $ unRV $ struct Ctx.! idx

    SetStruct _ st idx x -> do
      struct <- evalSub st
      v <- evalSub x
      return $ struct & ixF idx .~ RV v

    ----------------------------------------------------------------------
    -- Variant

    InjectVariant ctx idx ve -> do
         v <- evalSub ve
         return $ injectVariant sym ctx idx v

    ProjectVariant _ctx idx ve -> do
         v <- evalSub ve
         return $ unVB $ v Ctx.! idx

    ----------------------------------------------------------------------
    -- IdentValueMap

    EmptyStringMap _ -> return Map.empty

    LookupStringMapEntry _ m_expr i_expr -> do
      i <- evalSub i_expr
      m <- evalSub m_expr
      case asString i of
        Just (UnicodeLiteral i') -> return $ joinMaybePE (Map.lookup i' m)
        Nothing -> addFailedAssertion sym $
                    Unsupported "Symbolic string in lookupStringMapEntry"

    InsertStringMapEntry _ m_expr i_expr v_expr -> do
      m <- evalSub m_expr
      i <- evalSub i_expr
      v <- evalSub v_expr
      case asString i of
        Just (UnicodeLiteral i') -> return $ Map.insert i' v m
        Nothing -> addFailedAssertion sym $
                     Unsupported "Symbolic string in insertStringMapEntry"

    --------------------------------------------------------------------
    -- Strings

    StringLit x -> stringLit sym x
    ShowValue _bt x_expr -> do
      x <- evalSub x_expr
      stringLit sym (UnicodeLiteral (Text.pack (show (printSymExpr x))))
    ShowFloat _fi x_expr -> do
      x <- evalSub x_expr
      stringLit sym (UnicodeLiteral (Text.pack (show (printSymExpr x))))
    StringConcat _si x y -> do
      x' <- evalSub x
      y' <- evalSub y
      stringConcat sym x' y'
    StringEmpty si ->
      stringEmpty sym si
    StringLength x -> do
      x' <- evalSub x
      stringLength sym x'
    StringContains x y -> do
      x' <- evalSub x
      y' <- evalSub y
      stringContains sym x' y'
    StringIsPrefixOf x y -> do
      x' <- evalSub x
      y' <- evalSub y
      stringIsPrefixOf sym x' y'
    StringIsSuffixOf x y -> do
      x' <- evalSub x
      y' <- evalSub y
      stringIsSuffixOf sym x' y'
    StringIndexOf x y k -> do
      x' <- evalSub x
      y' <- evalSub y
      k' <- evalSub k
      stringIndexOf sym x' y' k'
    StringSubstring _si x off len -> do
      x' <- evalSub x
      off' <- evalSub off
      len' <- evalSub len
      stringSubstring sym x' off' len'

    ---------------------------------------------------------------------
    -- Introspection

    IsConcrete _ v -> do
      x <- baseIsConcrete <$> evalSub v
      return $! if x then truePred sym else falsePred sym

    ---------------------------------------------------------------------
    -- References

    ReferenceEq _ ref1 ref2 -> do
      cell1 <- evalSub ref1
      cell2 <- evalSub ref2
      let f r1 r2 = return (backendPred sym (r1 == r2))
      muxTreeCmpOp sym f cell1 cell2
