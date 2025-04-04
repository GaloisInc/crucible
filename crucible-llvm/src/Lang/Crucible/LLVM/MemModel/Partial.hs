------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Partial
-- Description      : Operations on partial values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.MemModel.Partial
  ( PartLLVMVal(..)
  , partErr
  , attachSideCondition
  , attachMemoryError
  , assertSafe
  , MemoryError(..)
  , totalLLVMVal
  , bvConcat
  , consArray
  , appendArray
  , mkArray
  , mkStruct
  , HasLLVMAnn
  , LLVMAnnMap
  , BoolAnn(..)
  , annotateME
  , annotateUB
  , ptrToBv
  , projectLLVM_bv

  , floatToBV
  , doubleToBV
  , fp80ToBV
  , bvToDouble
  , bvToFloat
  , bvToX86_FP80
  , selectHighBv
  , selectLowBv
  , arrayElt
  , fieldVal
  , muxLLVMVal

  , CexExplanation(..)
  , explainCex
  ) where

import           Prelude hiding (pred)

import           Control.Lens ((^.), view)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Except (ExceptT, MonadError(..), runExceptT)
import           Control.Monad.State.Strict (StateT, get, put, runStateT)
import qualified Data.ByteString as BS
import qualified Data.Foldable as Fold
import           Data.Maybe (isJust)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Numeric.Natural

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes (toOrdering, OrdF(..))
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.Bytes (Bytes)
import qualified Lang.Crucible.LLVM.Bytes as Bytes
import           Lang.Crucible.LLVM.MemModel.MemLog (memState)
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack, getCallStack)
import           Lang.Crucible.LLVM.MemModel.Pointer ( pattern LLVMPointer, LLVMPtr, ptrIsBv )
import           Lang.Crucible.LLVM.MemModel.Type (StorageType(..), StorageTypeF(..), Field(..))
import qualified Lang.Crucible.LLVM.MemModel.Type as Type
import           Lang.Crucible.LLVM.MemModel.Value (LLVMVal(..))
import qualified Lang.Crucible.LLVM.MemModel.Value as Value
import           Lang.Crucible.LLVM.Errors
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.Errors.MemoryError (MemoryError(..), MemoryErrorReason(..), MemoryOp(..), memOpMem)
import           Lang.Crucible.Panic (panic)

import           What4.Expr
import           What4.Expr.BoolMap
import           What4.Expr.Builder
import           What4.Interface hiding (bvConcat, mkStruct, floatToBV, bvToFloat)
import qualified What4.Interface as W4I
import qualified What4.InterpretedFloatingPoint as W4IFP


newtype BoolAnn sym = BoolAnn (SymAnnotation sym BaseBoolType)

instance IsSymInterface sym => Eq (BoolAnn sym) where
  BoolAnn x == BoolAnn y = isJust (testEquality x y)
instance IsSymInterface sym => Ord (BoolAnn sym) where
  compare (BoolAnn x) (BoolAnn y) = toOrdering $ compareF x y

type LLVMAnnMap sym = Map (BoolAnn sym) (CallStack, BadBehavior sym)
type HasLLVMAnn sym = (?recordLLVMAnnotation :: CallStack -> BoolAnn sym -> BadBehavior sym -> IO ())

data CexExplanation sym (tp :: BaseType) where
  NoExplanation  :: CexExplanation sym tp
  DisjOfFailures :: [ (CallStack, BadBehavior sym) ] -> CexExplanation sym BaseBoolType

instance Semigroup (CexExplanation sym BaseBoolType) where
  NoExplanation <> y = y
  x <> NoExplanation = x
  DisjOfFailures xs <> DisjOfFailures ys = DisjOfFailures (xs ++ ys)

explainCex :: forall t st fs sym.
  (IsSymInterface sym, sym ~ ExprBuilder t st fs) =>
  sym ->
  LLVMAnnMap sym ->
  Maybe (GroundEvalFn t) ->
  IO (Pred sym -> IO (CexExplanation sym BaseBoolType))
explainCex sym bbMap evalFn =
  do posCache <- newIdxCache
     negCache <- newIdxCache
     pure (evalPos posCache negCache)

  where
  evalPos, evalNeg ::
    IdxCache t (CexExplanation sym) ->
    IdxCache t (CexExplanation sym) ->
    Expr t BaseBoolType ->
    IO (CexExplanation sym BaseBoolType)

  evalPos posCache negCache e = idxCacheEval posCache e $
    case e of
      (asNonceApp -> Just (Annotation BaseBoolRepr annId e')) ->
        case Map.lookup (BoolAnn annId) bbMap of
          Nothing -> evalPos posCache negCache e'
          Just (callStack, bb) ->
            do bb' <- case evalFn of
                        Just f  -> concBadBehavior sym (groundEval f) bb
                        Nothing -> pure bb
               pure (DisjOfFailures [ (callStack, bb') ])

      (asApp -> Just (BaseIte BaseBoolRepr _ c x y))
         | Just f <- evalFn ->
              do c' <- groundEval f c
                 if c' then
                   evalPos posCache negCache x
                 else
                   evalPos posCache negCache y
         | otherwise ->
              (<>) <$> evalPos posCache negCache x <*> evalPos posCache negCache y

      (asApp -> Just (NotPred e')) -> evalNeg posCache negCache e'

      -- We expect at least one of the contained predicates to be false, so choose one
      -- and explain that failure
      (asApp -> Just (ConjPred (viewConjMap -> Conjuncts tms))) -> go (Fold.toList tms)
        where
        go [] = pure NoExplanation
        go ((x,Positive):xs)
          | Just f <- evalFn =
              do x' <- groundEval f x
                 if x' then
                   go xs
                 else
                   evalPos posCache negCache x >>= \case
                     NoExplanation -> go xs
                     ex -> pure ex
          | otherwise =
              -- no counterexample in hand, assume this might be the problem
              evalPos posCache negCache x  >>= \case
                     NoExplanation -> go xs
                     ex -> pure ex

        go ((x,Negative):xs)
          | Just f <- evalFn =
              do x' <- groundEval f x
                 if x' then
                   evalNeg posCache negCache x >>= \case
                     NoExplanation -> go xs
                     ex -> pure ex
                 else
                   go xs
           | otherwise =
              -- no counterexample in hand, assume this might be the problem
              evalNeg posCache negCache x >>= \case
                NoExplanation -> go xs
                ex -> pure ex

      _ -> pure NoExplanation

  evalNeg posCache negCache e = idxCacheEval negCache e $
    case e of
      (asApp -> Just (BaseIte BaseBoolRepr _ c x y))
         | Just f <- evalFn ->
              do c' <- groundEval f c
                 if c' then
                   evalNeg posCache negCache x
                 else
                   evalNeg posCache negCache y
         | otherwise ->
              (<>) <$> evalNeg posCache negCache x <*> evalNeg posCache negCache y

      (asApp -> Just (NotPred e')) -> evalPos posCache negCache e'

      -- under negative polarity, we expect all members of the disjunction to be false,
      -- and we must construct an explanation for all of them
      (asApp -> Just (ConjPred (viewConjMap -> Conjuncts tms))) -> go (Fold.toList tms) NoExplanation
        where
        go [] es = pure es
        go ((x,Positive):xs) es =
          do ex <- evalNeg posCache negCache x
             go xs (ex <> es)
        go ((x,Negative):xs) es =
          do ex <- evalPos posCache negCache x
             go xs (ex <> es)

      _ -> pure NoExplanation

annotateUB :: (IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  CallStack ->
  UB.UndefinedBehavior (RegValue' sym) ->
  Pred sym ->
  IO (Pred sym)
annotateUB sym callStack ub p =
  do (n, p') <- annotateTerm sym p
     ?recordLLVMAnnotation callStack (BoolAnn n) (BBUndefinedBehavior ub)
     return p'

memOpCallStack :: MemoryOp sym w -> CallStack
memOpCallStack = getCallStack . view memState . memOpMem

annotateME :: (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  MemoryErrorReason ->
  Pred sym ->
  IO (Pred sym)
annotateME sym mop rsn p =
  do (n, p') <- annotateTerm sym p
     ?recordLLVMAnnotation
       (memOpCallStack mop)
       (BoolAnn n)
       (BBMemoryError (MemoryError mop rsn))
     return p'

-- | Assert that the given LLVM pointer value is actually a raw bitvector and
-- extract its value.
ptrToBv ::
  IsSymBackend sym bak =>
  bak ->
  -- | Error to report if casting the pointer to a bitvector fails
  SimErrorReason ->
  LLVMPtr sym w ->
  IO (SymBV sym w)
ptrToBv bak err p@(LLVMPointer _blk bv) =
  do let sym = backendGetSym bak
     isBv <- ptrIsBv sym p
     assert bak isBv err
     return bv

-- | Assert that the given LLVM pointer value is actually a raw bitvector and extract its value.
--
-- Note that this assertion has a very generic message, which can be unhelpful
-- to users when it fails. Consider using 'ptrToBv' instead.
projectLLVM_bv ::
  IsSymBackend sym bak =>
  bak -> LLVMPtr sym w -> IO (SymBV sym w)
projectLLVM_bv bak ptr =
  let err = AssertFailureSimError "Pointer value coerced to bitvector" "" in
  ptrToBv bak err ptr

------------------------------------------------------------------------
-- ** PartLLVMVal

-- | Either an 'LLVMValue' paired with a tree of predicates explaining
-- just when it is actually valid, or a type mismatch.
data PartLLVMVal sym where
  Err :: Pred sym -> PartLLVMVal sym
  NoErr :: Pred sym -> LLVMVal sym -> PartLLVMVal sym

partErr ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  MemoryErrorReason ->
  IO (PartLLVMVal sym)
partErr sym errCtx rsn =
  do p <- annotateME sym errCtx rsn (falsePred sym)
     pure (Err p)

attachSideCondition ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  CallStack ->
  Pred sym ->
  UB.UndefinedBehavior (RegValue' sym) ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
attachSideCondition sym callStack pnew ub pv =
  case pv of
    Err p -> pure (Err p)
    NoErr p v ->
      do p' <- andPred sym p =<< annotateUB sym callStack ub pnew
         return $ NoErr p' v

attachMemoryError ::
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  Pred sym ->
  MemoryOp sym w ->
  MemoryErrorReason ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
attachMemoryError sym pnew mop rsn pv =
  case pv of
    Err p -> pure (Err p)
    NoErr p v ->
      do p' <- andPred sym p =<< annotateME sym mop rsn pnew
         return $ NoErr p' v

typeOfBitvector :: IsExpr (SymExpr sym)
                => proxy sym -> SymBV sym w -> StorageType
typeOfBitvector _ =
  Type.bitvectorType . Bytes.toBytes . natValue . bvWidth

-- | An 'LLVMVal' which is always valid.
totalLLVMVal :: (IsExprBuilder sym)
             => sym
             -> LLVMVal sym
             -> PartLLVMVal sym
totalLLVMVal sym = NoErr (truePred sym)

-- | Take a partial value and assert its safety
assertSafe :: IsSymBackend sym bak
           => bak
           -> PartLLVMVal sym
           -> IO (LLVMVal sym)
assertSafe bak (NoErr p v) =
  do let rsn = AssertFailureSimError "Error during memory load" ""
     assert bak p rsn
     return v

assertSafe bak (Err p) = do
  do let sym = backendGetSym bak
     let rsn = AssertFailureSimError "Error during memory load" ""
     loc <- getCurrentProgramLoc sym
     let err = SimError loc rsn
     addProofObligation bak (LabeledPred p err)
     abortExecBecause (AssertionFailure err)

------------------------------------------------------------------------
-- ** PartLLVMVal interface
--

floatToBV ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
floatToBV _ _ (NoErr p (LLVMValUndef (StorageType Float _))) =
  return (NoErr p (LLVMValUndef (Type.bitvectorType 4)))

floatToBV sym _ (NoErr p (LLVMValZero (StorageType Float _))) =
  do nz <- W4I.natLit sym 0
     iz <- W4I.bvZero sym (knownNat @32)
     return (NoErr p (LLVMValInt nz iz))

floatToBV sym _ (NoErr p (LLVMValFloat Value.SingleSize v)) =
  do nz <- natLit sym 0
     i  <- W4IFP.iFloatToBinary sym W4IFP.SingleFloatRepr v
     return (NoErr p (LLVMValInt nz i))

floatToBV _ _ (Err p) = pure (Err p)

floatToBV sym errCtx (NoErr _ v) =
  do let msg = "While converting from a float to a bitvector"
     partErr sym errCtx $
       UnexpectedArgumentType msg [Value.llvmValStorableType v]

doubleToBV ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
doubleToBV _ _ (NoErr p (LLVMValUndef (StorageType Double _))) =
  return (NoErr p (LLVMValUndef (Type.bitvectorType 8)))

doubleToBV sym _ (NoErr p (LLVMValZero (StorageType Double _))) =
  do nz <- W4I.natLit sym 0
     iz <- W4I.bvZero sym (knownNat @64)
     return (NoErr p (LLVMValInt nz iz))

doubleToBV sym _ (NoErr p (LLVMValFloat Value.DoubleSize v)) =
  do nz <- natLit sym 0
     i  <- W4IFP.iFloatToBinary sym W4IFP.DoubleFloatRepr v
     return (NoErr p (LLVMValInt nz i))

doubleToBV _ _ (Err p) = pure (Err p)

doubleToBV sym errCtx (NoErr _ v) =
  do let msg = "While converting from a double to a bitvector"
     partErr sym errCtx $
       UnexpectedArgumentType msg [Value.llvmValStorableType v]

fp80ToBV ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
fp80ToBV _ _ (NoErr p (LLVMValUndef (StorageType X86_FP80 _))) =
  return (NoErr p (LLVMValUndef (Type.bitvectorType 10)))

fp80ToBV sym _ (NoErr p (LLVMValZero (StorageType X86_FP80 _))) =
  do nz <- W4I.natLit sym 0
     iz <- W4I.bvLit sym (knownNat @80) (BV.zero knownNat)
     return (NoErr p (LLVMValInt nz iz))

fp80ToBV sym _ (NoErr p (LLVMValFloat Value.X86_FP80Size v)) =
  do nz <- natLit sym 0
     i  <- W4IFP.iFloatToBinary sym W4IFP.X86_80FloatRepr v
     return (NoErr p (LLVMValInt nz i))

fp80ToBV _ _ (Err p) = pure (Err p)

fp80ToBV sym errCtx (NoErr _ v) =
  do let msg = "While converting from a FP80 to a bitvector"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]

-- | Convert a bitvector to a float, asserting that it is not a pointer
bvToFloat :: forall sym w.
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToFloat sym _ (NoErr p (LLVMValZero (StorageType (Bitvector 4) _))) =
  NoErr p . LLVMValFloat Value.SingleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr =<<
       W4I.bvLit sym (knownNat @32) (BV.zero knownNat))

bvToFloat sym errCtx (NoErr p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @32) = do
      pz <- natEq sym blk =<< natLit sym 0
      let ub = UB.PointerFloatCast (RV (LLVMPointer blk off)) Type.floatType
      p' <- andPred sym p =<< annotateUB sym (memOpCallStack errCtx) ub pz
      NoErr p' . LLVMValFloat Value.SingleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr off

bvToFloat _ _ (Err p) = pure (Err p)

bvToFloat sym errCtx (NoErr _ v) =
  do let msg = "While converting from a bitvector to a float"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]


-- | Convert a bitvector to a double, asserting that it is not a pointer
bvToDouble ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToDouble sym _ (NoErr p (LLVMValZero (StorageType (Bitvector 8) _))) =
  NoErr p . LLVMValFloat Value.DoubleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr =<<
       W4I.bvLit sym (knownNat @64) (BV.zero knownNat))

bvToDouble sym errCtx (NoErr p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @64) = do
      pz <- natEq sym blk =<< natLit sym 0
      let ub = UB.PointerFloatCast (RV (LLVMPointer blk off)) Type.doubleType
      p' <- andPred sym p =<< annotateUB sym (memOpCallStack errCtx) ub pz
      NoErr p' .
        LLVMValFloat Value.DoubleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr off

bvToDouble _ _ (Err p) = pure (Err p)

bvToDouble sym errCtx (NoErr _ v) =
  do let msg = "While converting from a bitvector to a double"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]


-- | Convert a bitvector to an FP80 float, asserting that it is not a pointer
bvToX86_FP80 ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToX86_FP80 sym _ (NoErr p (LLVMValZero (StorageType (Bitvector 10) _))) =
  NoErr p . LLVMValFloat Value.X86_FP80Size <$>
    (W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr =<<
       W4I.bvLit sym (knownNat @80) (BV.zero knownNat))

bvToX86_FP80 sym errCtx (NoErr p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @80) =
      do pz <- natEq sym blk =<< natLit sym 0
         let ub = UB.PointerFloatCast (RV (LLVMPointer blk off)) Type.x86_fp80Type
         p' <- andPred sym p =<< annotateUB sym (memOpCallStack errCtx) ub pz
         NoErr p' . LLVMValFloat Value.X86_FP80Size <$>
           W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr off

bvToX86_FP80 _ _ (Err p) = pure (Err p)

bvToX86_FP80 sym errCtx (NoErr _ v) =
  do let msg = "While converting from a bitvector to a X86_FP80"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]

-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcat :: forall sym w.
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvConcat sym errCtx (NoErr p1 v1) (NoErr p2 v2) =
    case (v1, v2) of
      (LLVMValInt blk_low low, LLVMValInt blk_high high) ->
        do go blk_low low blk_high high
      (LLVMValInt blk_low low, LLVMValZero t@(StorageType (Bitvector high_bytes) _)) ->
        Value.zeroInt sym high_bytes $ \case
          Nothing -> partErr sym errCtx $ TypeMismatch (typeOfBitvector (Just sym) low) t
          Just (blk_high, high) ->
            go blk_low low blk_high high
      (LLVMValZero t@(StorageType (Bitvector low_bytes) _), LLVMValInt blk_high high) ->
         Value.zeroInt sym low_bytes $ \case
           Nothing -> partErr sym errCtx $ TypeMismatch (typeOfBitvector (Just sym) high) t
           Just (blk_low, low) ->
             go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        pure $ totalLLVMVal sym (LLVMValZero (Type.bitvectorType (low_bytes + high_bytes)))
      (a, b) -> partErr sym errCtx $ UnexpectedArgumentType "While concatenating bitvectors"
                  [Value.llvmValStorableType a, Value.llvmValStorableType b]

 where
  go :: forall l h. (1 <= l, 1 <= h) =>
    SymNat sym -> SymBV sym l -> SymNat sym -> SymBV sym h -> IO (PartLLVMVal sym)
  go blk_low low blk_high high
    -- NB we check that the things we are concatenating are each an integral number of
    -- bytes.  This prevents us from concatenating together the partial-byte writes that
    -- result from e.g. writing an i1 or an i20 into memory.  This is consistent with LLVM
    -- documentation, which says that non-integral number of bytes loads will only succeed
    -- if the value was written orignally with the same type.
    | low_nat  `mod` 8 == 0
    , high_nat `mod` 8 == 0 =
      do blk0   <- natLit sym 0
         -- TODO: Why won't this pattern match fail?
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         let ub1 = UB.PointerIntCast (RV (LLVMPointer blk_low low))   low_tp
             ub2 = UB.PointerIntCast (RV (LLVMPointer blk_high high)) high_tp
             annUB = annotateUB sym (memOpCallStack errCtx)
         predLow       <- annUB ub1 =<< natEq sym blk_low blk0
         predHigh      <- annUB ub2 =<< natEq sym blk_high blk0
         bv            <- W4I.bvConcat sym high low

         p' <- andPred sym p1 =<< andPred sym p2 =<< andPred sym predLow predHigh
         return $ NoErr p' (LLVMValInt blk0 bv)

    | otherwise = partErr sym errCtx $
        UnexpectedArgumentType "Non-byte-sized bitvectors"
          [Value.llvmValStorableType v1, Value.llvmValStorableType v2]

    where low_w'  = bvWidth low
          low_nat = natValue low_w'
          low_tp  = Type.bitvectorType (Bytes.bitsToBytes low_nat)

          high_w'  = bvWidth high
          high_nat = natValue high_w'
          high_tp  = Type.bitvectorType (Bytes.bitsToBytes high_nat)

bvConcat sym _ (Err e1) (Err e2) = Err <$> andPred sym e1 e2
bvConcat _ _ _ (Err e) = pure (Err e)
bvConcat _ _ (Err e) _ = pure (Err e)

-- | Cons an element onto a partial LLVM array value.
consArray ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
consArray sym _ (NoErr p1 (LLVMValZero tp)) (NoErr p2 (LLVMValZero (StorageType (Array m tp') _)))
  | tp == tp' =
      do p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValZero (Type.arrayType (m+1) tp')

consArray sym _ (NoErr p1 hd) (NoErr p2 (LLVMValZero (StorageType (Array m tp) _)))
  | Value.llvmValStorableType hd == tp =
      do p' <- andPred sym p1 p2
         return $ NoErr p' $
           LLVMValArray tp (V.cons hd (V.replicate (fromIntegral m) (LLVMValZero tp)))

consArray sym _ (NoErr p1 (LLVMValInt blk off)) (NoErr p2 (LLVMValString bs))
  | Just Refl <- testEquality (bvWidth off) (knownNat @8)
  , Just 0    <- asNat blk
  , Just bv   <- asBV off
  = do p' <- andPred sym p1 p2
       return $ NoErr p' (LLVMValString (BS.cons (fromInteger (BV.asUnsigned bv)) bs))

consArray sym errCtx (NoErr p1 v) (NoErr p2 (LLVMValString bs))
  = consArray sym errCtx (NoErr p1 v) . NoErr p2 =<< Value.explodeStringValue sym bs

consArray sym _ (NoErr p1 hd) (NoErr p2 (LLVMValArray tp vec))
  | Value.llvmValStorableType hd == tp =
      do p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValArray tp (V.cons hd vec)

consArray sym _ (Err e1) (Err e2) = Err <$> andPred sym e1 e2
consArray _ _ (Err e) _ = pure (Err e)
consArray _ _ _ (Err e) = pure (Err e)

consArray sym errCtx _ (NoErr _ v) =
  partErr sym errCtx $ UnexpectedArgumentType "Non-array value" [Value.llvmValStorableType v]

-- | Append two partial LLVM array values.
appendArray ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
appendArray sym _
  (NoErr p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (NoErr p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
      do p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValZero (Type.arrayType (n1+n2) tp1)

appendArray sym _
  (NoErr p1 (LLVMValString bs1))
  (NoErr p2 (LLVMValString bs2))
  = do p' <- andPred sym p1 p2
       pure $ NoErr p' $ LLVMValString (bs1 <> bs2)

appendArray sym errCtx (NoErr p1 (LLVMValString bs1)) (NoErr p2 v2)
  = do bsv <- Value.explodeStringValue sym bs1
       appendArray sym errCtx (NoErr p1 bsv) (NoErr p2 v2)

appendArray sym errCtx (NoErr p1 v1) (NoErr p2 (LLVMValString bs2))
  = do bsv <- Value.explodeStringValue sym bs2
       appendArray sym errCtx (NoErr p1 v1) (NoErr p2 bsv)

appendArray sym _
  (NoErr p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (NoErr p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      do let v1 = V.replicate (fromIntegral n1) (LLVMValZero tp1)
         p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValArray tp1 (v1 V.++ v2)

appendArray sym _
  (NoErr p1 (LLVMValArray tp1 v1))
  (NoErr p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
      do let v2 = V.replicate (fromIntegral n2) (LLVMValZero tp1)
         p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValArray tp1 (v1 V.++ v2)

appendArray sym _
  (NoErr p1 (LLVMValArray tp1 v1))
  (NoErr p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      do p' <- andPred sym p1 p2
         return $ NoErr p' $ LLVMValArray tp1 (v1 V.++ v2)

appendArray sym _ (Err e1) (Err e2) = Err <$> andPred sym e1 e2
appendArray _ _ (Err e) _ = pure (Err e)
appendArray _ _ _ (Err e) = pure (Err e)

appendArray sym errCtx (NoErr _ v1) (NoErr _ v2) =
  partErr sym errCtx $ UnexpectedArgumentType "Non-array value when appending arrays"
          [Value.llvmValStorableType v1, Value.llvmValStorableType v2]

-- | Make a partial LLVM array value.
--
-- It returns 'Err' if any of the elements of the vector are
-- 'Err'. Otherwise, the 'Pred' on the returned 'NoErr' value
-- is the 'And' of all the assertions on the values.
mkArray :: forall sym. (IsExprBuilder sym, IsSymInterface sym) =>
  sym ->
  StorageType ->
  Vector (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkArray sym tp vec =
  do let f :: PartLLVMVal sym -> StateT (Pred sym) (ExceptT (Pred sym) IO) (LLVMVal sym)
         f (Err e) = throwError e
         f (NoErr p x) = do
           pd <- get     -- Current predicates
           pd' <- liftIO $ andPred sym pd p
           put pd'    -- Append this one
           return x
     (runExceptT $ flip runStateT (truePred sym) $ traverse f vec) >>= \case
        Left e -> pure $ Err e
        Right (vec', p) -> return $ NoErr p (LLVMValArray tp vec')


-- | Make a partial LLVM struct value.
--
-- It returns 'Err' if any of the struct fields are 'Err'.
-- Otherwise, the 'Pred' on the returned 'NoErr' value is the 'And' of all the
-- assertions on the values.
mkStruct :: forall sym. IsExprBuilder sym =>
  sym ->
  Vector (Field StorageType, PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkStruct sym vec =
  do let f :: (Field StorageType, PartLLVMVal sym) ->
              StateT (Pred sym) (ExceptT (Pred sym) IO) (Field StorageType, LLVMVal sym)
         f (_, Err e)       = throwError e
         f (fld, NoErr p x) = do
           pd <- get
           pd' <- liftIO $ andPred sym pd p
           put pd'
           pure (fld, x)

     (runExceptT $ flip runStateT (truePred sym) $ traverse f vec) >>= \case
       Left e -> pure (Err e)
       Right (vec',p) -> return $ NoErr p (LLVMValStruct vec')

-- | Select some of the least significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectLowBv ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectLowBv _sym _ low hi (NoErr p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ NoErr p $ LLVMValZero (Type.bitvectorType low)

selectLowBv sym errCtx low hi (NoErr p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof       <- isPosNat low_w
  , Just Refl           <- testEquality (addNat low_w hi_w) w
  , Just LeqProof       <- testLeq low_w w =
      do pz  <- natEq sym blk =<< natLit sym 0
         bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
         let ub = UB.PointerIntCast (RV (LLVMPointer blk bv)) tp
         p' <- andPred sym p =<< annotateUB sym (memOpCallStack errCtx) ub pz
         return $ NoErr p' $ LLVMValInt blk bv'
 where w = bvWidth bv
       tp = Type.bitvectorType (Bytes.bitsToBytes (natValue w))

selectLowBv sym errCtx _ _ (NoErr _ v) =
  do let msg = "While selecting the low bits of a bitvector"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]

selectLowBv _ _ _ _ (Err e) = pure (Err e)

-- | Select some of the most significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectHighBv ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectHighBv _sym _ low hi (NoErr p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ NoErr p $ LLVMValZero (Type.bitvectorType hi)

selectHighBv sym errCtx low hi (NoErr p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do pz <-  natEq sym blk =<< natLit sym 0
       bv' <- bvSelect sym low_w hi_w bv
       let ub = UB.PointerIntCast (RV (LLVMPointer blk bv)) tp
       p' <- andPred sym p =<< annotateUB sym (memOpCallStack errCtx) ub pz
       return $ NoErr p' $ LLVMValInt blk bv'
  where w = bvWidth bv
        tp = Type.bitvectorType (Bytes.bitsToBytes (natValue w))
selectHighBv _ _ _ _ (Err e) = pure (Err e)

selectHighBv sym errCtx _ _ (NoErr _ v) =
  do let msg = "While selecting the high bits of a bitvector"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]


-- | Look up an element in a partial LLVM array value.
arrayElt ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  Natural ->
  StorageType ->
  Natural ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
arrayElt _ _ sz tp idx (NoErr p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < sz =
    return $ NoErr p (LLVMValZero tp)

arrayElt sym _ sz tp idx (NoErr p (LLVMValString bs))
  | sz == fromIntegral (BS.length bs)
  , 0 <= idx
  , idx < sz
  , tp == Type.bitvectorType (Bytes.Bytes 1)
  = do blk <- natLit sym 0
       off <- bvLit sym (knownNat @8) (BV.word8 (BS.index bs (fromIntegral idx)))
       return $ NoErr p (LLVMValInt blk off)

arrayElt _ _ sz tp idx (NoErr p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ NoErr p (vec V.! fromIntegral idx)

arrayElt _ _ _ _ _ (Err e) = pure (Err e)

arrayElt sym errCtx _ _ _ (NoErr _ v) =
  do let msg = "While selecting and element of an array"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]

-- | Look up a field in a partial LLVM struct value.
fieldVal ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  MemoryOp sym w ->
  (Vector (Field StorageType)) ->
  Int ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
fieldVal _ _ flds idx (NoErr p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < V.length flds =
      return $ NoErr p $ LLVMValZero $ view Type.fieldVal $ flds V.! idx

fieldVal _ _ flds idx (NoErr p (LLVMValStruct vec))
  | flds == fmap fst vec
  , 0 <= idx
  , idx < V.length vec =
    return $ NoErr p $ snd $ (vec V.! idx)

fieldVal _ _ _ _ (Err e) = pure (Err e)

fieldVal sym errCtx _ _ (NoErr _ v) =
  do let msg = "While getting a struct field"
     partErr sym errCtx $ UnexpectedArgumentType msg [Value.llvmValStorableType v]

------------------------------------------------------------------------
-- ** Merging and muxing
--

-- | If-then-else on partial expressions.
merge :: forall sym m. (IsSymInterface sym, HasLLVMAnn sym, MonadIO m) =>
  sym ->
  (Pred sym -> LLVMVal sym -> LLVMVal sym -> m (LLVMVal sym))
    {- ^ Operation to combine inner values. The 'Pred' parameter is the
         if/then/else condition -} ->
  Pred sym {- ^ condition to merge on -} ->
  PartLLVMVal sym {- ^ 'then' value -}  ->
  PartLLVMVal sym {- ^ 'else' value -} ->
  m (PartLLVMVal sym)
merge sym _ c (Err e1) (Err e2) = Err <$> liftIO (itePred sym c e1 e2)

merge sym _ cond (NoErr p v) (Err pe) =
  do p' <- liftIO (itePred sym cond p pe)
     pure $ NoErr p' v
merge sym _ cond (Err pe) (NoErr p v) = do
  do p' <- liftIO (itePred sym cond pe p)
     pure $ NoErr p' v
merge sym f cond (NoErr px x) (NoErr py y) = do
  v <- f cond x y
  p' <- liftIO (itePred sym cond px py)
  return $ NoErr p' v

-- | Mux partial LLVM values.
--
--   Will @panic@ if the values are not structurally related.
--   This should never happen, as we only call @muxLLVMVal@
--   from inside the memory model as we read values, and the
--   shape of values is determined by the memory type
--   at which we read values.
muxLLVMVal :: forall sym.
  (IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  Pred sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
muxLLVMVal sym = merge sym muxval
  where

    muxzero :: Pred sym -> StorageType -> LLVMVal sym -> IO (LLVMVal sym)
    muxzero cond tpz val = case val of
      LLVMValZero tp -> return $ LLVMValZero tp
      LLVMValUndef tpu ->
        -- TODO: Is this the right behavior?
        panic "Cannot mux zero and undef" [ "Zero type: " ++ show tpz
                                          , "Undef type: " ++ show tpu
                                          ]

      LLVMValString bs -> muxzero cond tpz =<< Value.explodeStringValue sym bs

      LLVMValInt base off ->
        do zbase <- W4I.natLit sym 0
           zoff  <- W4I.bvZero sym (W4I.bvWidth off)
           base' <- W4I.natIte sym cond zbase base
           off'  <- W4I.bvIte sym cond zoff off
           return $ LLVMValInt base' off'
      LLVMValFloat Value.SingleSize x ->
        do zerof <- (W4IFP.iFloatLitRational sym W4IFP.SingleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.SingleFloat sym cond zerof x)
           return $ LLVMValFloat Value.SingleSize x'
      LLVMValFloat Value.DoubleSize x ->
        do zerof <- (W4IFP.iFloatLitRational sym W4IFP.DoubleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.DoubleFloat sym cond zerof x)
           return $ LLVMValFloat Value.DoubleSize x'
      LLVMValFloat Value.X86_FP80Size x ->
        do zerof <- (W4IFP.iFloatLitRational sym W4IFP.X86_80FloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.X86_80Float sym cond zerof x)
           return $ LLVMValFloat Value.X86_FP80Size x'

      LLVMValArray tp vec -> LLVMValArray tp <$>
        traverse (muxzero cond tp) vec

      LLVMValStruct flds -> LLVMValStruct <$>
        traverse (\(fld, v) -> (fld,) <$>
                     muxzero cond (fld^.Type.fieldVal) v) flds


    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> IO (LLVMVal sym)
    muxval cond (LLVMValZero tp) v = muxzero cond tp v
    muxval cond v (LLVMValZero tp) = do cond' <- notPred sym cond
                                        muxzero cond' tp v

    muxval cond (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (bvWidth off1) (bvWidth off2)
      = do base <- liftIO $ natIte sym cond base1 base2
           off  <- liftIO $ bvIte sym cond off1 off2
           pure $ LLVMValInt base off

    muxval cond (LLVMValFloat (xsz :: Value.FloatSize fi) x) (LLVMValFloat ysz y)
      | Just Refl <- testEquality xsz ysz
      = LLVMValFloat xsz <$>
          (liftIO $ W4IFP.iFloatIte @_ @fi sym cond x y)

    muxval cond (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 =
          LLVMValStruct <$>
            V.zipWithM (\(f, x) (_, y) -> (f,) <$> muxval cond x y) fls1 fls2

    muxval cond (LLVMValString bs1) (LLVMValString bs2)
      | bs1 == bs2 = pure (LLVMValString bs1)
      | BS.length bs1 == BS.length bs2
      =  do v1 <- Value.explodeStringValue sym bs1
            v2 <- Value.explodeStringValue sym bs2
            muxval cond v1 v2

    muxval cond (LLVMValString bs) v@LLVMValArray{}
      = do bsv <- Value.explodeStringValue sym bs
           muxval cond bsv v

    muxval cond v@LLVMValArray{} (LLVMValString bs)
      = do bsv <- Value.explodeStringValue sym bs
           muxval cond v bsv

    muxval cond (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          LLVMValArray tp1 <$> V.zipWithM (muxval cond) v1 v2

    muxval _ v1@(LLVMValUndef tp1) (LLVMValUndef tp2)
      | tp1 == tp2 = pure v1

    muxval _ v1 v2 =
      panic "Cannot mux LLVM values"
        [ "v1: " ++ show v1
        , "v2: " ++ show v2
        ]
