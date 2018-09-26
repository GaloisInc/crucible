------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Value
-- Description      : Representation of values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.Value
  ( -- * LLVM Value representation
    LLVMVal(..)
  , FloatSize(..)
  , G.Field
  , ptrToPtrVal

    -- * LLVM Value representation
  , PartLLVMVal
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
  ) where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict
import           Data.List (intersperse)

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V
import           Data.Word (Word64)

import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial

import           Lang.Crucible.Backend
import qualified Lang.Crucible.LLVM.Bytes as G
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.Translation.Constant

data FloatSize (fi :: FloatInfo) where
  SingleSize :: FloatSize SingleFloat
  DoubleSize :: FloatSize DoubleFloat
deriving instance Eq (FloatSize fi)
deriving instance Ord (FloatSize fi)
deriving instance Show (FloatSize fi)
instance TestEquality FloatSize where
  testEquality SingleSize SingleSize = Just Refl
  testEquality DoubleSize DoubleSize = Just Refl
  testEquality _ _ = Nothing

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
  LLVMValFloat :: FloatSize fi -> SymInterpretedFloat sym fi -> LLVMVal sym
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: G.Type -> Vector (LLVMVal sym) -> LLVMVal sym

llvmValStorableType :: IsExprBuilder sym => LLVMVal sym -> G.Type
llvmValStorableType v =
  case v of
    LLVMValInt _ bv -> G.bitvectorType (G.bitsToBytes (natValue (bvWidth bv)))
    LLVMValFloat SingleSize _ -> G.floatType
    LLVMValFloat DoubleSize _ -> G.doubleType
    LLVMValStruct fs -> G.structType (fmap fst fs)
    LLVMValArray tp vs -> G.arrayType (fromIntegral (V.length vs)) tp

-- | Coerce an 'LLVMPtr' value into a memory-storable 'LLVMVal'.
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

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
muxLLVMVal sym = mergePartial sym muxval
  where
    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> PartialT sym IO (LLVMVal sym)

    muxval cond (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (bvWidth off1) (bvWidth off2)
      = do base <- liftIO $ natIte sym cond base1 base2
           off  <- liftIO $ bvIte sym cond off1 off2
           return $ LLVMValInt base off

    muxval cond (LLVMValFloat (xsz :: FloatSize fi) x) (LLVMValFloat ysz y)
      | Just Refl <- testEquality xsz ysz
      = LLVMValFloat xsz <$> (liftIO $ iFloatIte @_ @fi sym cond x y)

    muxval cond (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval cond x y) fls1 fls2
          return $ LLVMValStruct fls

    muxval cond (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith (muxval cond) v1 v2
          return $ LLVMValArray tp1 v

    muxval _ _ _ = returnUnassigned


instance IsExpr (SymExpr sym) => Show (LLVMVal sym) where
  show (LLVMValInt blk w)
    | Just 0 <- asNat blk = "<int" ++ show (bvWidth w) ++ ">"
    | otherwise = "<ptr " ++ show (bvWidth w) ++ ">"
  show (LLVMValFloat SingleSize _) = "<float>"
  show (LLVMValFloat DoubleSize _) = "<double>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]
