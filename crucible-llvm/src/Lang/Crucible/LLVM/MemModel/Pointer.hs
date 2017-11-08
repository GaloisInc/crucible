------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Pointer
-- Description      : Representation of pointers in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel.Pointer
( -- * Pointer bitwidth
  PtrWidth
, ptrWidth

  -- * Crucible pointer representation
, LLVMPointerType
, llvmPointerRepr
, pattern LLVMPointerRepr
, llvmPointer
, llvmPointer_bv
, llvmPointerCases
, projectLLVM_bv
, projectLLVM_pointer

  -- * LLVM Value representation
, LLVMVal(..)
, PartLLVMVal
, applyCtorFLLVMVal
, applyViewFLLVMVal
, muxLLVMVal

  -- * Operations on valid pointers
, LLVMPtr(..)
, AddrDecomposeResult(..)
, muxLLVMPtr
, ptrToPtrVal
, ptrConst
, ptrDecompose
, ptrSizeDecompose
, ptrComparable
, ptrOffsetEq
, ptrOffsetLe
, ptrEq
, ptrLe
, ptrAdd
, ptrCheckedAdd
, ptrDiff
, ptrSub
) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V
import           Numeric.Natural

import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.MemModel.Common as G


type PtrWidth = 64
ptrWidth :: NatRepr PtrWidth
ptrWidth = knownNat

type LLVMPointerType = RecursiveType "LLVM_pointer"
llvmPointerRepr :: TypeRepr LLVMPointerType
llvmPointerRepr = knownRepr

instance IsRecursiveType "LLVM_pointer" where
  type UnrollType "LLVM_pointer" =
     VariantType (EmptyCtx ::>
       BVType PtrWidth ::>
       StructType (EmptyCtx ::> NatType ::> BVType PtrWidth ::> BVType PtrWidth))
  unrollType _ =
     VariantRepr (Ctx.empty Ctx.:>
       BVRepr ptrWidth Ctx.:>
       StructRepr (Ctx.empty Ctx.:>NatRepr Ctx.:> BVRepr ptrWidth Ctx.:> BVRepr ptrWidth))


pattern LLVMPointerRepr :: () => (ty ~ LLVMPointerType) => TypeRepr ty
pattern LLVMPointerRepr <- RecursiveRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  where
    LLVMPointerRepr = llvmPointerRepr

llvmPointer ::
  IsSymInterface sym =>
  sym ->
  RegValue sym NatType ->
  RegValue sym (BVType PtrWidth) ->
  RegValue sym (BVType PtrWidth) ->
  RegValue sym LLVMPointerType
llvmPointer sym blk end off =
  RolledType $ injectVariant sym knownRepr (Ctx.natIndex @1) $
    (Ctx.empty Ctx.:> RV blk Ctx.:> RV end Ctx.:> RV off)

llvmPointer_bv ::
  IsSymInterface sym =>
  sym ->
  RegValue sym (BVType PtrWidth) ->
  RegValue sym LLVMPointerType
llvmPointer_bv sym bv =
  RolledType $ injectVariant sym knownRepr (Ctx.natIndex @0) bv

llvmPointerCases ::
  IsSymInterface sym =>
  sym ->
  (sym -> Pred sym -> a -> a -> IO a) ->
  (RegValue sym (BVType PtrWidth) -> IO a) ->
  (RegValue sym NatType ->
   RegValue sym (BVType PtrWidth) ->
   RegValue sym (BVType PtrWidth) ->
   IO a) ->
  RegValue sym LLVMPointerType ->
  IO a
llvmPointerCases sym muxFn bvCase ptrCase (RolledType v) =
  case (v^._1, v^._2) of
    (VB (PE pbv bv), VB Unassigned) ->
      do a <- bvCase bv
         addAssertion sym pbv PatternMatchFailureSimError
         return a
    (VB Unassigned, VB (PE pptr (Ctx.Empty Ctx.:> RV blk Ctx.:> RV end Ctx.:> RV off))) ->
      do a <- ptrCase blk end off
         addAssertion sym pptr PatternMatchFailureSimError
         return a
    (VB (PE pbv bv), VB (PE pptr (Ctx.Empty Ctx.:> RV blk Ctx.:> RV end Ctx.:> RV off))) ->
      do abv  <- bvCase bv
         aptr <- ptrCase blk end off
         a <- muxFn sym pbv abv aptr
         p <- orPred sym pbv pptr
         addAssertion sym p PatternMatchFailureSimError
         return a
    _ ->
      addFailedAssertion sym PatternMatchFailureSimError

projectLLVM_bv ::
  IsSymInterface sym =>
  sym ->
  RegValue sym LLVMPointerType ->
  IO (RegValue sym (BVType PtrWidth))
projectLLVM_bv sym (RolledType vs) =
  case vs^._1 of
    VB (PE p bv) ->
      do addAssertion sym p PatternMatchFailureSimError
         return bv
    _ -> addFailedAssertion sym PatternMatchFailureSimError

projectLLVM_pointer ::
  IsSymInterface sym =>
  sym ->
  RegValue sym LLVMPointerType ->
  IO (LLVMPtr sym PtrWidth)
projectLLVM_pointer sym (RolledType vs) =
  case vs^._2 of
    VB (PE p (Ctx.Empty Ctx.:> RV blk Ctx.:> RV end Ctx.:> RV off)) ->
      do addAssertion sym p PatternMatchFailureSimError
         return (LLVMPtr blk end off)
    _ -> addFailedAssertion sym PatternMatchFailureSimError


-- | This provides a view of an address as a base + offset when possible.
data AddrDecomposeResult sym w
  = Symbolic (LLVMPtr sym w)
  | ConcreteOffset Natural (SymBV sym w) Integer
  | SymbolicOffset Natural (SymBV sym w) (SymBV sym w)
--  deriving (Show)

data LLVMPtr sym w
  = LLVMPtr (SymNat sym)   --  ^ Block number
            (SymBV sym w)  --  ^ End-of-block offset (1 past end of valid bytes)
            (SymBV sym w)  --  ^ Current offset in block

instance (IsSymInterface sym) => Eq (LLVMPtr sym w) where
  x == y = compare x y == EQ

muxLLVMPtr ::
  (1 <= w) =>
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  IO (LLVMPtr sym w)
muxLLVMPtr sym p (LLVMPtr b1 end1 off1) (LLVMPtr b2 end2 off2) =
  do b   <- natIte sym p b1 b2
     end <- bvIte sym p end1 end2
     off <- bvIte sym p off1 off2
     return $ LLVMPtr b end off

-- | This is a syntactic ordering used for map lookups.
instance (IsSymInterface sym) => Ord (LLVMPtr sym w) where
  compare (LLVMPtr b1 _ off1) (LLVMPtr b2 _ off2) =
    case compareF b1 b2 of
      LTF -> LT
      GTF -> GT
      EQF ->
        case compareF off1 off2 of
          LTF -> LT
          GTF -> GT
          EQF -> EQ

ptrToPtrVal :: LLVMPtr sym w -> LLVMVal sym w
ptrToPtrVal (LLVMPtr blk end off) = LLVMValPtr blk end off

data LLVMVal sym w where
  -- NOTE! The block number '0' is special, and indicates that this value is actually a
  -- bitvector of machine word width, rather than an acutal pointer!
  LLVMValPtr :: SymNat sym -> SymBV sym w -> SymBV sym w -> LLVMVal sym w
  LLVMValInt :: (1 <= x) => NatRepr x -> SymBV sym x -> LLVMVal sym w
  LLVMValReal :: SymReal sym -> LLVMVal sym w
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym w) -> LLVMVal sym w
  LLVMValArray :: G.Type -> Vector (LLVMVal sym w) -> LLVMVal sym w

type PartLLVMVal sym w = PartExpr (Pred sym) (LLVMVal sym w)

ptrConst :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> G.Addr -> IO (SymBV sym w)
ptrConst sym w x = bvLit sym w (G.bytesToInteger x)

ptrDecompose :: (1 <= w, IsExprBuilder sym)
             => sym
             -> NatRepr w
             -> LLVMPtr sym w
             -> IO (AddrDecomposeResult sym w)
ptrDecompose _sym _w (LLVMPtr (asNat -> Just b) end (asUnsignedBV -> Just off)) =
  return $ ConcreteOffset b end off
ptrDecompose _sym _w (LLVMPtr (asNat -> Just b) end off) =
  return $ SymbolicOffset b end off
ptrDecompose _sym _w p =
  return $ Symbolic p

ptrSizeDecompose
  :: IsExprBuilder sym
  => sym
  -> NatRepr w
  -> SymBV sym w
  -> IO (Maybe Integer)
ptrSizeDecompose _ _ (asUnsignedBV -> Just off) =
  return (Just off)
ptrSizeDecompose _ _ _ = return Nothing


-- | Test whether pointers point into the same allocation unit.
ptrComparable ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrComparable sym _w (LLVMPtr base1 _ _) (LLVMPtr base2 _ _) =
  natEq sym base1 base2

-- | Test whether pointers have equal offsets (assuming they point
-- into the same allocation unit).
ptrOffsetEq ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrOffsetEq sym _w (LLVMPtr _ _ off1) (LLVMPtr _ _ off2) =
  bvEq sym off1 off2

-- | Test whether the first pointer's address is less than or equal to
-- the second (assuming they point into the same allocation unit).
ptrOffsetLe ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrOffsetLe sym _w (LLVMPtr _ _ off1) (LLVMPtr _ _ off2) =
  bvSle sym off1 off2

ptrEq :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym)
ptrEq sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do p1 <- natEq sym base1 base2
     p2 <- bvEq sym off1 off2
     andPred sym p1 p2

ptrLe :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym)
ptrLe sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do p1 <- natEq sym base1 base2
     addAssertion sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
     bvSle sym off1 off2

-- | Add an offset to a pointer.
ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrAdd sym _w (LLVMPtr base end off1) off2 =
  do off' <- bvAdd sym off1 off2
     return $ LLVMPtr base end off'

ptrCheckedAdd
       :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (Pred sym, LLVMPtr sym w)
ptrCheckedAdd sym w (LLVMPtr base end off1) off2 =
  do z <- bvLit sym w 0
     (p1, off') <- addSignedOF sym off1 off2
     p1' <- notPred sym p1
     p2 <- bvSle sym off' end
     p3 <- bvSle sym z off'
     p <- andPred sym p1' =<< andPred sym p2 p3
     return $ (p, LLVMPtr base end off')


-- | Compute the difference between two pointers. The pointers must
-- point into the same allocation block.
ptrDiff :: (1 <= w, IsSymInterface sym)
        => sym
        -> NatRepr w
        -> LLVMPtr sym w
        -> LLVMPtr sym w
        -> IO (SymBV sym w)
ptrDiff sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do p <- natEq sym base1 base2
     addAssertion sym p (AssertFailureSimError "Attempted to subtract pointers from different allocations")
     diff <- bvSub sym off1 off2
     return diff

-- | Subtract an offset from a pointer.
ptrSub :: (1 <= w, IsSymInterface sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrSub sym _w (LLVMPtr base end off1) off2 =
  do diff <- bvSub sym off1 off2
     return (LLVMPtr base end diff)


applyCtorFLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ValueCtorF (PartLLVMVal sym w)
   -> IO (PartLLVMVal sym w)
applyCtorFLLVMVal sym _w ctor =
  case ctor of
    G.ConcatBV low_w  (PE p1 (LLVMValInt low_w' low))
               high_w (PE p2 (LLVMValInt high_w' high))
       | G.bytesToBits low_w  == natValue low_w' &&
         G.bytesToBits high_w == natValue high_w' ->
           do bv <- bvConcat sym high low
              Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
              p <- andPred sym p1 p2
              return $ PE p $ LLVMValInt (addNat high_w' low_w') bv
    G.ConsArray tp (PE p1 hd) n (PE p2 (LLVMValArray tp' vec))
       | tp == tp' && n == fromIntegral (V.length vec) ->
           do p <- andPred sym p1 p2
              return $ PE p $ LLVMValArray tp' (V.cons hd vec)
    G.AppendArray tp n1 (PE p1 (LLVMValArray tp1 v1)) n2 (PE p2 (LLVMValArray tp2 v2))
       | tp == tp1 && tp == tp2 &&
         n1 == fromIntegral (V.length v1) &&
         n2 == fromIntegral (V.length v2) ->
           do p <- andPred sym p1 p2
              return $ PE p $ LLVMValArray tp (v1 V.++ v2)
    G.MkArray tp vec ->
      do let f :: PartLLVMVal sym w -> StateT (Pred sym) (MaybeT IO) (LLVMVal sym w)
             f Unassigned = mzero
             f (PE p1 x) =
               do p0 <- get
                  p <- liftIO $ andPred sym p0 p1
                  put p
                  return x
         x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
         case x of
           Nothing -> return $ Unassigned
           Just (vec',p) -> return $ PE p $ LLVMValArray tp vec'

    G.MkStruct vec ->
      do let f :: (G.Field G.Type, PartLLVMVal sym w)
               -> StateT (Pred sym) (MaybeT IO) (G.Field G.Type, LLVMVal sym w)
             f (_fld, Unassigned) = mzero
             f (fld, PE p1 x) = do
                 p0 <- get
                 p <- liftIO $ andPred sym p0 p1
                 put p
                 return (fld, x)
         x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
         case x of
           Nothing -> return $ Unassigned
           Just (vec',p) -> return $ PE p $ LLVMValStruct vec'

    _ -> return $ Unassigned

    -- G.BVToFloat _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"
    -- G.BVToDouble _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"


applyViewFLLVMVal
   :: (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ViewF (PartLLVMVal sym w)
   -> IO (PartLLVMVal sym w)
applyViewFLLVMVal sym wptr v =
  case v of
    G.SelectLowBV low hi (PE p (LLVMValPtr blk _end off))
      -> do p' <- andPred sym p =<< natEq sym blk =<< natLit sym 0
            applyViewFLLVMVal sym wptr (G.SelectLowBV low hi (PE p' (LLVMValInt wptr off)))
    G.SelectHighBV low hi (PE p (LLVMValPtr blk _end off))
      -> do p' <- andPred sym p =<< natEq sym blk =<< natLit sym 0
            applyViewFLLVMVal sym wptr (G.SelectHighBV low hi (PE p' (LLVMValInt wptr off)))
    G.SelectLowBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (G.bytesToBits low)
      , Just (Some (hi_w))  <- someNat (G.bytesToBits hi)
      , Just LeqProof <- isPosNat low_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      , Just LeqProof <- testLeq low_w w
      -> do
        bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
        return $ PE p $ LLVMValInt low_w bv'
    G.SelectHighBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (G.bytesToBits low)
      , Just (Some (hi_w))  <- someNat (G.bytesToBits hi)
      , Just LeqProof <- isPosNat hi_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      -> do
        bv' <- bvSelect sym low_w hi_w bv
        return $ PE p $ LLVMValInt hi_w bv'
    G.FloatToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.DoubleToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.ArrayElt sz tp idx (PE p (LLVMValArray tp' vec))
      | sz == fromIntegral (V.length vec)
      , 0 <= idx
      , idx < sz
      , tp == tp' ->
        return $ PE p $ (vec V.! fromIntegral idx)
    G.FieldVal flds idx (PE p (LLVMValStruct vec))
      | flds == fmap fst vec
      , 0 <= idx
      , idx < V.length vec ->
          return $ PE p $ snd $ (vec V.! idx)
    _ -> return Unassigned

muxLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> Pred sym
   -> PartLLVMVal sym w
   -> PartLLVMVal sym w
   -> IO (PartLLVMVal sym w)
muxLLVMVal sym _w p = mux
  where
    mux Unassigned Unassigned = return Unassigned
    mux Unassigned (PE p2 y)  = PE <$> (itePred sym p (falsePred sym) p2) <*> return y
    mux (PE p1 x) Unassigned  = PE <$> (itePred sym p p1 (falsePred sym)) <*> return x
    mux (PE p1 x) (PE p2 y) =
      do mz <- runMaybeT $ muxval x y
         case mz of
           Nothing -> return $ Unassigned
           Just z  -> PE <$> itePred sym p p1 p2 <*> return z

    muxval :: LLVMVal sym w -> LLVMVal sym w -> MaybeT IO (LLVMVal sym w)

    muxval (LLVMValPtr base1 end1 off1) (LLVMValPtr base2 end2 off2) =
      do base <- liftIO $ natIte sym p base1 base2
         end  <- liftIO $ bvIte sym p end1 end2
         off  <- liftIO $ bvIte sym p off1 off2
         return $ LLVMValPtr base end off

    muxval (LLVMValReal x) (LLVMValReal y) =
      do z <- liftIO $ realIte sym p x y
         return $ LLVMValReal z

    muxval (LLVMValInt wx x) (LLVMValInt wy y)
      | Just Refl <- testEquality wx wy =
        do z <- liftIO $ bvIte sym p x y
           return $ LLVMValInt wx z

    muxval (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval x y) fls1 fls2
          return $ LLVMValStruct fls

    muxval (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith muxval v1 v2
          return $ LLVMValArray tp1 v

    muxval _ _ = mzero
