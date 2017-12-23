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
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

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
  , pattern LLVMPointer
  , llvmPointerView
  , pattern SizeT
  , muxLLVMPtr
  , ptrWidth
  , projectLLVM_bv
  , llvmPointer_bv
  , mkNullPointer

    -- * LLVM Value representation
  , LLVMVal(..)
  , PartLLVMVal
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
  , ptrSizeDecompose
  , ptrComparable
  , ptrOffsetEq
  , ptrOffsetLe
  , ptrEq
  , ptrLe
  , ptrAdd
  , ptrDiff
  , ptrSub
  , ptrIsNull
  ) where

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
import           Data.Word (Word64)
import           Numeric.Natural

import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegValue
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.MemModel.Type as G

import           GHC.TypeLits

-- | This constraint captures the idea that there is a distinguished
--   pointer width in scope which is appropriate according to the C
--   notion of pointer, and object size. In particular, it must be at
--   least 16-bits wide (as required for the @size_t@ type).
type HasPtrWidth w = (1 <= w, 16 <= w, ?ptrWidth :: NatRepr w)

pattern PtrWidth :: HasPtrWidth w => w ~ w' => NatRepr w'
pattern PtrWidth <- (testEquality ?ptrWidth -> Just Refl)
  where PtrWidth = ?ptrWidth

withPtrWidth :: forall w a. (16 <= w) => NatRepr w -> (HasPtrWidth w => a) -> a
withPtrWidth w a =
  case leqTrans (LeqProof :: LeqProof 1 16) (LeqProof :: LeqProof 16 w) of
    LeqProof -> let ?ptrWidth = w in a

-- | Crucible type of pointers/bitvector values of width @w@.
type LLVMPointerType w = RecursiveType "LLVM_pointer" (EmptyCtx ::> BVType w)
type LLVMPtr sym w = RegValue sym (LLVMPointerType w)

-- | Type family defining how @LLVMPointerType@ unfolds.
type family LLVMPointerImpl ctx where
  LLVMPointerImpl (EmptyCtx ::> BVType w) = StructType (EmptyCtx ::> NatType ::> BVType w)
  LLVMPointerImpl ctx = TypeError ('Text "LLVM_pointer expects a single argument of BVType, but was given" ':<>:
                                   'ShowType ctx)

instance IsRecursiveType "LLVM_pointer" where
  type UnrollType "LLVM_pointer" ctx = LLVMPointerImpl ctx
  unrollType _nm (Ctx.view -> Ctx.AssignExtend (Ctx.view -> Ctx.AssignEmpty) (BVRepr w)) =
            StructRepr (Ctx.empty Ctx.:> NatRepr Ctx.:> BVRepr w)
  unrollType nm ctx = typeError nm ctx


-- | This pattern synonym makes it easy to build and destruct runtime representatives
--   of @LLVMPointerType w@.
pattern LLVMPointerRepr :: () => (1 <= w, ty ~ LLVMPointerType w) => NatRepr w -> TypeRepr ty
pattern LLVMPointerRepr w <- RecursiveRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
                                           (Ctx.Empty Ctx.:> BVRepr w)
  where
    LLVMPointerRepr w = RecursiveRepr knownSymbol (Ctx.Empty Ctx.:> BVRepr w)

-- | This pattern creates/matches against the TypeRepr for LLVM pointer values
--   that are of the distinguished pointer width.
pattern PtrRepr :: HasPtrWidth wptr => (ty ~ LLVMPointerType wptr) => TypeRepr ty
pattern PtrRepr = LLVMPointerRepr PtrWidth

-- | This pattern creates/matches against the TypeRepr for raw bitvector values
--   that are of the distinguished pointer width.
pattern SizeT :: HasPtrWidth wptr => (ty ~ BVType wptr) => TypeRepr ty
pattern SizeT = BVRepr PtrWidth

-- | This pattern synonym gives an easy way to construct/deconstruct runtime values of @LLVMPointerType@.
pattern LLVMPointer :: RegValue sym NatType -> RegValue sym (BVType w) -> RegValue sym (LLVMPointerType w)
pattern LLVMPointer blk offset = RolledType (Ctx.Empty Ctx.:> RV blk Ctx.:> RV offset)

-- The COMPLETE pragma was not defined until ghc 8.2.*
#if MIN_VERSION_base(4,10,0)
{-# COMPLETE LLVMPointer #-}
#endif

-- | Alternative to the @LLVMPointer@ pattern synonym, this function can be used as a view
--   consturctor instead to silence incomplete pattern warnings.
llvmPointerView :: RegValue sym (LLVMPointerType w) -> (RegValue sym NatType, RegValue sym (BVType w))
llvmPointerView (LLVMPointer blk offset) = (blk, offset)

-- | Compute the width of a pointer value
ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

-- | Assert that the given LLVM pointer value is actually a raw bitvector and extract its value.
projectLLVM_bv :: IsSymInterface sym => sym -> RegValue sym (LLVMPointerType w) -> IO (RegValue sym (BVType w))
projectLLVM_bv sym (LLVMPointer blk bv) =
  do p <- natEq sym blk =<< natLit sym 0
     addAssertion sym p (AssertFailureSimError "Pointer value coerced to bitvector")
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

-- | Coerce a @LLVMPtr@ value into memory-storable @LLVMVal@
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

-- | This provides a view of an address as a base + offset when possible.
data AddrDecomposeResult sym w
  = Symbolic (LLVMPtr sym w) -- ^ A pointer with a symbolic base value
  | SymbolicOffset Natural (SymBV sym w) -- ^ A pointer with a concrete base value, but symbolic offset
  | ConcreteOffset Natural Integer       -- ^ A totally concrete pointer value

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
  LLVMValReal :: SymReal sym -> LLVMVal sym
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: G.Type -> Vector (LLVMVal sym) -> LLVMVal sym

-- | Generate a concrete offset value from an @Addr@ value.
constOffset :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> G.Addr -> IO (SymBV sym w)
constOffset sym w x = bvLit sym w (G.bytesToInteger x)

-- | Examine a pointer and determine how much concrete information is
--   contained therein.
ptrDecompose :: (1 <= w, IsExprBuilder sym)
             => sym
             -> NatRepr w
             -> LLVMPtr sym w
             -> IO (AddrDecomposeResult sym w)
ptrDecompose _sym _w (LLVMPointer (asNat -> Just b) (asUnsignedBV -> Just off)) =
  return $ ConcreteOffset b off
ptrDecompose _sym _w (LLVMPointer (asNat -> Just b) off) =
  return $ SymbolicOffset b off
ptrDecompose _sym _w p =
  return $ Symbolic p

-- | Determine if the given bitvector value is a concrete offset
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
     addAssertion sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
     bvUle sym off1 off2

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
-- (low) bytes are given first.
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

-- | Select the low bytes of a partial LLVM bitvector value.
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

-- | Select the low bytes of a partial LLVM bitvector value.
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

-- | Mux partial LLVM values
muxLLVMVal :: forall sym
    . IsSymInterface sym
   => sym
   -> Pred sym
   -> PartLLVMVal sym
   -> PartLLVMVal sym
   -> IO (PartLLVMVal sym)
muxLLVMVal sym p = mergePartial sym muxval p
  where
    muxval :: LLVMVal sym -> LLVMVal sym -> PartialT sym IO (LLVMVal sym)

    muxval (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (bvWidth off1) (bvWidth off2)
      = do base <- liftIO $ natIte sym p base1 base2
           off  <- liftIO $ bvIte sym p off1 off2
           return $ LLVMValInt base off

    muxval (LLVMValReal x) (LLVMValReal y) =
      do z <- liftIO $ realIte sym p x y
         return $ LLVMValReal z

    muxval (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval x y) fls1 fls2
          return $ LLVMValStruct fls

    muxval (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith muxval v1 v2
          return $ LLVMValArray tp1 v

    muxval _ _ = returnUnassigned
