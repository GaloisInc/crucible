------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Pointer
-- Description      : Representation of pointers in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- GHC 8.0 doesn't understand the COMPLETE pragma,
-- so we just kill the incomplete pattern warning
-- instead :-(
#if MIN_VERSION_base(4,10,0)
#else
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
#endif

module Lang.Crucible.LLVM.MemModel.Pointer
  ( -- * Pointer bitwidth
    HasPtrWidth
  , pattern PtrWidth
  , withPtrWidth

    -- * Crucible pointer representation
  , LLVMPointerType
  , LLVMPtr
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , pattern SizeT
  , pattern LLVMPointer
  , ptrWidth
  , llvmPointerView
  , muxLLVMPtr
  , projectLLVM_bv
  , llvmPointer_bv
  , mkNullPointer

    -- * LLVM Value representation
  , LLVMVal(..)
  , PartLLVMVal
  , FloatSize(..)
  , llvmValStorableType
  , bvConcatPartLLVMVal
  , consArrayPartLLVMVal
  , appendArrayPartLLVMVal
  , mkArrayPartLLVMVal
  , mkStructPartLLVMVal
  , selectLowBvPartLLVMVal
  , selectHighBvPartLLVMVal
  , arrayEltPartLLVMVal
  , fieldValPartLLVMVal
  , muxLLVMVal

    -- * Operations on valid pointers
  , AddrDecomposeResult(..)
  , ptrToPtrVal
  , constOffset
  , ptrDecompose
  , ptrComparable
  , ptrOffsetEq
  , ptrOffsetLe
  , ptrEq
  , ptrLe
  , ptrLt
  , ptrAdd
  , ptrDiff
  , ptrSub
  , ptrIsNull

    -- * Pretty printing
  , ppPtr
  ) where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V
import           Data.Word (Word64)
import           Numeric.Natural

import           What4.Interface
import           What4.Partial

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.Bytes as G
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import           Lang.Crucible.LLVM.Types

-- | This pattern synonym gives an easy way to construct/deconstruct runtime values of @LLVMPointerType@.
pattern LLVMPointer :: RegValue sym NatType -> RegValue sym (BVType w) -> RegValue sym (LLVMPointerType w)
pattern LLVMPointer blk offset = RolledType (Ctx.Empty Ctx.:> RV blk Ctx.:> RV offset)

-- The COMPLETE pragma was not defined until ghc 8.2.*
#if MIN_VERSION_base(4,10,0)
{-# COMPLETE LLVMPointer #-}
#endif

-- | Alternative to the @LLVMPointer@ pattern synonym, this function can be used as a view
--   constructor instead to silence incomplete pattern warnings.
llvmPointerView :: RegValue sym (LLVMPointerType w) -> (RegValue sym NatType, RegValue sym (BVType w))
llvmPointerView (LLVMPointer blk offset) = (blk, offset)

-- | Compute the width of a pointer value.
ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

-- | Assert that the given LLVM pointer value is actually a raw bitvector and extract its value.
projectLLVM_bv ::
  IsSymInterface sym =>
  sym -> RegValue sym (LLVMPointerType w) -> IO (RegValue sym (BVType w))
projectLLVM_bv sym ptr@(LLVMPointer blk bv) =
  do p <- natEq sym blk =<< natLit sym 0
     assert sym p $
        AssertFailureSimError $ unlines
          [ "Pointer value coerced to bitvector:"
          , "*** " ++ show (ppPtr ptr)
          ]
     return bv

-- | Convert a raw bitvector value into an LLVM pointer value.
llvmPointer_bv :: IsSymInterface sym
               => sym -> RegValue sym (BVType w) -> IO (RegValue sym (LLVMPointerType w))
llvmPointer_bv sym bv =
  do blk0 <- natLit sym 0
     return (LLVMPointer blk0 bv)

-- | Produce the distinguished null pointer value
mkNullPointer :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> IO (RegValue sym (LLVMPointerType w))
mkNullPointer sym w = llvmPointer_bv sym =<< bvLit sym w 0

-- | Mux function specialized to LLVM pointer values
muxLLVMPtr ::
  (1 <= w) =>
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  IO (LLVMPtr sym w)
muxLLVMPtr sym p (LLVMPointer b1 off1) (LLVMPointer b2 off2) =
  do b   <- natIte sym p b1 b2
     off <- bvIte sym p off1 off2
     return $ LLVMPointer b off

-- | Coerce a @LLVMPtr@ value into a memory-storable @LLVMVal@.
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

-- | This provides a view of an address as a base + offset when possible.
data AddrDecomposeResult sym w
  = Symbolic (LLVMPtr sym w) -- ^ A pointer with a symbolic base value
  | SymbolicOffset Natural (SymBV sym w) -- ^ A pointer with a concrete base value, but symbolic offset
  | ConcreteOffset Natural Integer       -- ^ A totally concrete pointer value

data FloatSize
  = SingleSize
  | DoubleSize
 deriving (Eq,Ord,Show)

-- | This datatype describes the variety of values that can be stored in
--   the LLVM heap.
data LLVMVal sym where
  -- NOTE! The ValInt constructor uniformly represents both pointers and
  -- raw bitvector values.  The 'SymNat' value is an allocation block number
  -- that identifies specific allocations.  The block number '0' is special,
  -- and indicates that this value is actually a bitvector.  Non-zero block
  -- numbers correspond to pointer values, where the 'SymBV' value is an
  -- offset from the base pointer of the allocation.
  LLVMValInt :: (1 <= w) => SymNat sym -> SymBV sym w -> LLVMVal sym
  LLVMValReal :: FloatSize -> SymReal sym -> LLVMVal sym
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: G.Type -> Vector (LLVMVal sym) -> LLVMVal sym

llvmValStorableType :: IsExprBuilder sym => LLVMVal sym -> G.Type
llvmValStorableType v = case v of
  LLVMValInt _ bv -> G.bitvectorType (G.bitsToBytes (natValue (bvWidth bv)))
  LLVMValReal SingleSize _ -> G.floatType
  LLVMValReal DoubleSize _ -> G.doubleType
  LLVMValStruct fs -> G.structType (fmap fst fs)
  LLVMValArray tp vs -> G.arrayType (fromIntegral (V.length vs)) tp

-- | Generate a concrete offset value from an @Addr@ value.
constOffset :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> G.Addr -> IO (SymBV sym w)
constOffset sym w x = bvLit sym w (G.bytesToInteger x)

-- | Examine a pointer and determine how much concrete information is
--   contained therein.
ptrDecompose ::
  (1 <= w, IsExprBuilder sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w ->
  AddrDecomposeResult sym w
ptrDecompose _sym _w (LLVMPointer (asNat -> Just b) (asUnsignedBV -> Just off)) =
  ConcreteOffset b off
ptrDecompose _sym _w (LLVMPointer (asNat -> Just b) off) =
  SymbolicOffset b off
ptrDecompose _sym _w p =
  Symbolic p


-- | Test whether pointers point into the same allocation unit.
ptrComparable ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrComparable sym _w (LLVMPointer base1 _) (LLVMPointer base2 _) =
  natEq sym base1 base2

-- | Test whether pointers have equal offsets (assuming they point
-- into the same allocation unit).
ptrOffsetEq ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrOffsetEq sym _w (LLVMPointer _ off1) (LLVMPointer _ off2) =
  bvEq sym off1 off2

-- | Test whether the first pointer's address is less than or equal to
-- the second (assuming they point into the same allocation unit).
ptrOffsetLe ::
    (1 <= w, IsSymInterface sym) =>
    sym -> NatRepr w -> LLVMPtr sym w -> LLVMPtr sym w -> IO (Pred sym)
ptrOffsetLe sym _w (LLVMPointer _ off1) (LLVMPointer _ off2) =
  bvUle sym off1 off2

ptrEq :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym)
ptrEq sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  do p1 <- natEq sym base1 base2
     p2 <- bvEq sym off1 off2
     andPred sym p1 p2

ptrLe :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym)
ptrLe sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  do p1 <- natEq sym base1 base2
     assert sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
     bvUle sym off1 off2

ptrLt :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym)
ptrLt sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  do p1 <- natEq sym base1 base2
     assert sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
     bvUlt sym off1 off2



-- | Add an offset to a pointer.
ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrAdd sym _w (LLVMPointer base off1) off2 =
  do off' <- bvAdd sym off1 off2
     return $ LLVMPointer base off'

-- | Compute the difference between two pointers. The pointers must
-- point into the same allocation block.
ptrDiff :: (1 <= w, IsSymInterface sym)
        => sym
        -> NatRepr w
        -> LLVMPtr sym w
        -> LLVMPtr sym w
        -> IO (SymBV sym w)
ptrDiff sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  do p <- natEq sym base1 base2
     assert sym p (AssertFailureSimError "Attempted to subtract pointers from different allocations")
     diff <- bvSub sym off1 off2
     return diff

-- | Subtract an offset from a pointer.
ptrSub :: (1 <= w, IsSymInterface sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrSub sym _w (LLVMPointer base off1) off2 =
  do diff <- bvSub sym off1 off2
     return (LLVMPointer base diff)

-- | Test if a pointer value is the null pointer
ptrIsNull :: (1 <= w, IsSymInterface sym)
          => sym
          -> NatRepr w
          -> LLVMPtr sym w
          -> IO (Pred sym)
ptrIsNull sym _w (LLVMPointer blk off) =
  do pblk <- natEq sym blk =<< natLit sym 0
     poff <- bvEq sym off =<< bvLit sym (bvWidth off) 0
     andPred sym pblk poff


----------------------------------------------------------------------
-- PartLLVMVal

-- | Partial LLVM values.
type PartLLVMVal sym = PartExpr (Pred sym) (LLVMVal sym)

-- TODO: Many of the size/type arguments to the following PartLLVMVal
-- operations are unnecessary and maybe they should be removed.

-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcatPartLLVMVal ::
  IsSymInterface sym => sym ->
  G.Bytes -> PartLLVMVal sym ->
  G.Bytes -> PartLLVMVal sym ->
  IO (PartLLVMVal sym)
bvConcatPartLLVMVal sym
  low_w (PE p1 (LLVMValInt blk_low low))
  high_w (PE p2 (LLVMValInt blk_high high))
  | G.bytesToBits low_w  == natValue low_w' &&
    G.bytesToBits high_w == natValue high_w' =
      do blk0   <- natLit sym 0
         p_blk1 <- natEq sym blk_low blk0
         p_blk2 <- natEq sym blk_high blk0
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         p <- andPred sym p1 =<< andPred sym p2 =<< andPred sym p_blk1 p_blk2
         bv <- bvConcat sym high low
         return $ PE p $ LLVMValInt blk0 bv
    where low_w' = bvWidth low
          high_w' = bvWidth high
bvConcatPartLLVMVal _ _ _ _ _ = return Unassigned

-- | Cons an element onto a partial LLVM array value.
consArrayPartLLVMVal ::
  IsSymInterface sym => sym ->
  G.Type -> PartLLVMVal sym ->
  Integer -> PartLLVMVal sym ->
  IO (PartLLVMVal sym)
consArrayPartLLVMVal sym tp (PE p1 hd) n (PE p2 (LLVMValArray tp' vec))
  | tp == tp' && n == fromIntegral (V.length vec) =
    do p <- andPred sym p1 p2
       return $ PE p $ LLVMValArray tp' (V.cons hd vec)
consArrayPartLLVMVal _ _ _ _ _ = return Unassigned

-- | Append two partial LLVM array values.
appendArrayPartLLVMVal ::
  IsSymInterface sym => sym ->
  G.Type ->
  Integer -> PartLLVMVal sym ->
  Integer -> PartLLVMVal sym ->
  IO (PartLLVMVal sym)
appendArrayPartLLVMVal sym tp
  n1 (PE p1 (LLVMValArray tp1 v1))
  n2 (PE p2 (LLVMValArray tp2 v2))
  | tp == tp1 && tp == tp2 &&
    n1 == fromIntegral (V.length v1) &&
    n2 == fromIntegral (V.length v2) =
      do p <- andPred sym p1 p2
         return $ PE p $ LLVMValArray tp (v1 V.++ v2)
appendArrayPartLLVMVal _ _ _ _ _ _ = return Unassigned

-- | Make a partial LLVM array value.
mkArrayPartLLVMVal :: forall sym .
  IsSymInterface sym => sym ->
  G.Type -> Vector (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkArrayPartLLVMVal sym tp vec =
  do let f :: PartLLVMVal sym -> StateT (Pred sym) (MaybeT IO) (LLVMVal sym)
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

-- | Make a partial LLVM struct value.
mkStructPartLLVMVal :: forall sym .
  IsSymInterface sym => sym ->
  Vector (G.Field G.Type, PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkStructPartLLVMVal sym vec =
  do let f :: (G.Field G.Type, PartLLVMVal sym)
           -> StateT (Pred sym) (MaybeT IO) (G.Field G.Type, LLVMVal sym)
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

-- | Select some of the least significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectLowBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  G.Bytes -> G.Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
selectLowBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (G.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (G.bytesToBits hi)
  , Just LeqProof <- isPosNat low_w
  , Just Refl <- testEquality (addNat low_w hi_w) w
  , Just LeqProof <- testLeq low_w w =
    do p' <- andPred sym p =<< natEq sym blk =<< natLit sym 0
       bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
       return $ PE p' (LLVMValInt blk bv')
  where w = bvWidth bv
selectLowBvPartLLVMVal _ _ _ _ = return Unassigned

-- | Select some of the most significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectHighBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  G.Bytes -> G.Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
selectHighBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (G.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (G.bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do p' <- andPred sym p =<< natEq sym blk =<< natLit sym 0
       bv' <- bvSelect sym low_w hi_w bv
       return $ PE p' $ LLVMValInt blk bv'
  where w = bvWidth bv
selectHighBvPartLLVMVal _ _ _ _ = return Unassigned

-- | Look up an element in a partial LLVM array value.
arrayEltPartLLVMVal ::
  Word64 -> G.Type -> Word64 ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
arrayEltPartLLVMVal sz tp idx (PE p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ PE p (vec V.! fromIntegral idx)
arrayEltPartLLVMVal _ _ _ _ = return Unassigned

-- | Look up a field in a partial LLVM struct value.
fieldValPartLLVMVal ::
  (Vector (G.Field G.Type)) -> Int ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
fieldValPartLLVMVal flds idx (PE p (LLVMValStruct vec))
  | flds == fmap fst vec
  , 0 <= idx
  , idx < V.length vec =
    return $ PE p $ snd $ (vec V.! idx)
fieldValPartLLVMVal _ _ _ = return Unassigned

-- | Mux partial LLVM values.
muxLLVMVal :: forall sym
    . IsSymInterface sym
   => sym
   -> Pred sym
   -> PartLLVMVal sym
   -> PartLLVMVal sym
   -> IO (PartLLVMVal sym)
muxLLVMVal sym cond = mergePartial sym (const muxval) cond
  where
    muxval :: LLVMVal sym -> LLVMVal sym -> PartialT sym IO (LLVMVal sym)

    muxval (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (bvWidth off1) (bvWidth off2)
      = do base <- liftIO $ natIte sym cond base1 base2
           off  <- liftIO $ bvIte sym cond off1 off2
           return $ LLVMValInt base off

    muxval (LLVMValReal xsz x) (LLVMValReal ysz y) | xsz == ysz =
      do z <- liftIO $ realIte sym cond x y
         return $ LLVMValReal xsz z

    muxval (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval x y) fls1 fls2
          return $ LLVMValStruct fls

    muxval (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith muxval v1 v2
          return $ LLVMValArray tp1 v

    muxval _ _ = returnUnassigned


ppPtr :: IsExpr (SymExpr sym) => LLVMPtr sym wptr -> Doc
ppPtr (llvmPointerView -> (blk, bv))
  | Just 0 <- asNat blk = printSymExpr bv
  | otherwise =
     let blk_doc = printSymExpr blk
         off_doc = printSymExpr bv
      in text "(" <> blk_doc <> text "," <+> off_doc <> text ")"


