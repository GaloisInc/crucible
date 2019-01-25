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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
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
  , Field
  , ptrToPtrVal
  , zeroInt

  , llvmValStorableType
  ) where

import           Data.List (intersperse)

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V

import           What4.Interface
import           What4.InterpretedFloatingPoint

import           Lang.Crucible.Backend
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Pointer

data FloatSize (fi :: FloatInfo) where
  SingleSize :: FloatSize SingleFloat
  DoubleSize :: FloatSize DoubleFloat
  X86_FP80Size :: FloatSize X86_80Float
deriving instance Eq (FloatSize fi)
deriving instance Ord (FloatSize fi)
deriving instance Show (FloatSize fi)
instance TestEquality FloatSize where
  testEquality SingleSize SingleSize = Just Refl
  testEquality DoubleSize DoubleSize = Just Refl
  testEquality X86_FP80Size X86_FP80Size = Just Refl
  testEquality _ _ = Nothing

-- | This datatype describes the variety of values that can be stored in
--   the LLVM heap.
data LLVMVal sym where
  -- | NOTE! The ValInt constructor uniformly represents both pointers and
  -- raw bitvector values.  The 'SymNat' value is an allocation block number
  -- that identifies specific allocations.  The block number '0' is special,
  -- and indicates that this value is actually a bitvector.  Non-zero block
  -- numbers correspond to pointer values, where the 'SymBV' value is an
  -- offset from the base pointer of the allocation.
  LLVMValInt :: (1 <= w) => SymNat sym -> SymBV sym w -> LLVMVal sym
  LLVMValFloat :: FloatSize fi -> SymInterpretedFloat sym fi -> LLVMVal sym
  LLVMValStruct :: Vector (Field StorageType, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: StorageType -> Vector (LLVMVal sym) -> LLVMVal sym

  -- | The zero value exists at all storage types, and represents the the value
  -- which is obtained by loading the approprite number of all zero bytes.
  -- It is useful for compactly representing large zero-initialized data structures.
  LLVMValZero :: StorageType -> LLVMVal sym

  -- | The @undef@ value exists at all storage types.
  LLVMValUndef :: StorageType -> LLVMVal sym


llvmValStorableType :: IsExprBuilder sym => LLVMVal sym -> StorageType
llvmValStorableType v =
  case v of
    LLVMValInt _ bv -> bitvectorType (bitsToBytes (natValue (bvWidth bv)))
    LLVMValFloat SingleSize _ -> floatType
    LLVMValFloat DoubleSize _ -> doubleType
    LLVMValFloat X86_FP80Size _ -> x86_fp80Type
    LLVMValStruct fs -> structType (fmap fst fs)
    LLVMValArray tp vs -> arrayType (fromIntegral (V.length vs)) tp
    LLVMValZero tp -> tp
    LLVMValUndef tp -> tp

-- | Coerce an 'LLVMPtr' value into a memory-storable 'LLVMVal'.
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

zeroInt ::
  IsSymInterface sym =>
  sym ->
  Bytes ->
  (forall w. (1 <= w) => Maybe (SymNat sym, SymBV sym w) -> IO a) ->
  IO a
zeroInt sym bytes k
   | Just (Some w) <- someNat (bytesToBits bytes)
   , Just LeqProof <- isPosNat w
   =   do blk <- natLit sym 0
          bv  <- bvLit sym w 0
          k (Just (blk, bv))
zeroInt _ _ k = k @1 Nothing

instance IsExpr (SymExpr sym) => Show (LLVMVal sym) where
  show (LLVMValZero _tp) = "0"
  show (LLVMValUndef tp) = "<undef : " ++ show tp ++ ">"
  show (LLVMValInt blk w)
    | Just 0 <- asNat blk = "<int" ++ show (bvWidth w) ++ ">"
    | otherwise = "<ptr " ++ show (bvWidth w) ++ ">"
  show (LLVMValFloat SingleSize _) = "<float>"
  show (LLVMValFloat DoubleSize _) = "<double>"
  show (LLVMValFloat X86_FP80Size _) = "<long double>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]

----------------------------------------------------------------------
-- PartLLVMVal

  {-
-- | Partial LLVM values.
type PartLLVMVal sym = PartExpr (Pred sym) (LLVMVal sym)

bvToFloatPartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToFloatPartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 4) _))) =
  PE p . LLVMValFloat SingleSize <$> (iFloatFromBinary sym SingleFloatRepr =<< bvLit sym (knownNat @32) 0)

bvToFloatPartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @32)
  = do pz <- natEq sym blk =<< natLit sym 0
       p' <- andPred sym p pz
       PE p' . LLVMValFloat SingleSize <$> iFloatFromBinary sym SingleFloatRepr off

bvToFloatPartLLVMVal _ _ = return Unassigned


bvToDoublePartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToDoublePartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 8) _))) =
  PE p . LLVMValFloat DoubleSize <$> (iFloatFromBinary sym DoubleFloatRepr =<< bvLit sym (knownNat @64) 0)

bvToDoublePartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @64)
  = do pz <- natEq sym blk =<< natLit sym 0
       p' <- andPred sym p pz
       PE p' . LLVMValFloat DoubleSize <$> iFloatFromBinary sym DoubleFloatRepr off

bvToDoublePartLLVMVal _ _ = return Unassigned

bvToX86_FP80PartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

bvToX86_FP80PartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 10) _))) =
  PE p . LLVMValFloat X86_FP80Size <$> (iFloatFromBinary sym X86_80FloatRepr =<< bvLit sym (knownNat @80) 0)

bvToX86_FP80PartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (bvWidth off) (knownNat @80)
  = do pz <- natEq sym blk =<< natLit sym 0
       p' <- andPred sym p pz
       PE p' . LLVMValFloat X86_FP80Size <$> iFloatFromBinary sym X86_80FloatRepr off

bvToX86_FP80PartLLVMVal _ _ = return Unassigned

-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcatPartLLVMVal :: forall sym.
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
bvConcatPartLLVMVal _ Unassigned _ = return Unassigned
bvConcatPartLLVMVal _ _ Unassigned = return Unassigned

bvConcatPartLLVMVal sym (PE p1 v1) (PE p2 v2) =
    case (v1, v2) of
      (LLVMValInt blk_low low, LLVMValInt blk_high high) ->
        do go blk_low low blk_high high
      (LLVMValInt blk_low low, LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        zeroInt sym high_bytes $ \case
          Nothing -> return Unassigned
          Just (blk_high, high) ->
            go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValInt blk_high high) ->
         zeroInt sym low_bytes $ \case
           Nothing -> return Unassigned
           Just (blk_low, low) ->
             go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        return (PE (truePred sym) (LLVMValZero (bitvectorType (low_bytes + high_bytes))))
      _ -> return Unassigned

 where
  go :: forall l h. (1 <= l, 1 <= h) =>
    SymNat sym -> SymBV sym l -> SymNat sym -> SymBV sym h -> IO (PartLLVMVal sym)
  go blk_low low blk_high high
    -- NB we check that the things we are concatenating are each an integral number of
    -- bytes.  This prevents us from concatenating together the partial-byte writes that
    -- result from e.g. writing an i1 or an i20 into memory.  This is consistent with LLVM
    -- documentation, which says that non-integral number of bytes loads will only succeed
    -- if the value was written orignally with the same type.
    | natValue low_w' `mod` 8 == 0
    , natValue high_w' `mod` 8 == 0 =
      do blk0   <- natLit sym 0
         p_blk1 <- natEq sym blk_low blk0
         p_blk2 <- natEq sym blk_high blk0
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         p <- andPred sym p1 =<< andPred sym p2 =<< andPred sym p_blk1 p_blk2
         bv <- bvConcat sym high low
         return $ PE p $ LLVMValInt blk0 bv
    | otherwise =
       return Unassigned

    where low_w' = bvWidth low
          high_w' = bvWidth high

-- | Cons an element onto a partial LLVM array value.
consArrayPartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
consArrayPartLLVMVal sym (PE p1 (LLVMValZero tp)) (PE p2 (LLVMValZero (StorageType (Array m tp') _)))
  | tp == tp' =
    do p <- andPred sym p1 p2
       return $ PE p $ LLVMValZero (arrayType (m+1) tp')

consArrayPartLLVMVal sym (PE p1 hd) (PE p2 (LLVMValZero (StorageType (Array m tp) _)))
  | llvmValStorableType hd == tp =
    do p <- andPred sym p1 p2
       return $ PE p $ LLVMValArray tp (V.cons hd (V.replicate (fromIntegral m) (LLVMValZero tp)))

consArrayPartLLVMVal sym (PE p1 hd) (PE p2 (LLVMValArray tp vec))
  | llvmValStorableType hd == tp =
    do p <- andPred sym p1 p2
       return $ PE p $ LLVMValArray tp (V.cons hd vec)

consArrayPartLLVMVal _ _ _ = return Unassigned

-- | Append two partial LLVM array values.
appendArrayPartLLVMVal ::
  IsSymInterface sym =>
  sym ->
  PartLLVMVal sym ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
appendArrayPartLLVMVal sym
  (PE p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PE p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
     do p <- andPred sym p1 p2
        return $ PE p $ LLVMValZero (arrayType (n1+n2) tp1)

appendArrayPartLLVMVal sym
  (PE p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PE p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
     do p <- andPred sym p1 p2
        let v1 = V.replicate (fromIntegral n1) (LLVMValZero tp1)
        return $ PE p $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal sym
  (PE p1 (LLVMValArray tp1 v1))
  (PE p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
     do p <- andPred sym p1 p2
        let v2 = V.replicate (fromIntegral n2) (LLVMValZero tp1)
        return $ PE p $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal sym
  (PE p1 (LLVMValArray tp1 v1))
  (PE p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      do p <- andPred sym p1 p2
         return $ PE p $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal _ _ _ = return Unassigned


-- | Make a partial LLVM array value.
mkArrayPartLLVMVal :: forall sym .
  IsSymInterface sym => sym ->
  StorageType ->
  Vector (PartLLVMVal sym) ->
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
  Vector (Field StorageType, PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
mkStructPartLLVMVal sym vec =
  do let f :: (Field StorageType, PartLLVMVal sym)
           -> StateT (Pred sym) (MaybeT IO) (Field StorageType, LLVMVal sym)
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
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectLowBvPartLLVMVal _sym low hi (PE p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PE p $ LLVMValZero (bitvectorType low)

selectLowBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (bytesToBits low)
  , Just (Some (hi_w))  <- someNat (bytesToBits hi)
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
  Bytes ->
  Bytes ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)

selectHighBvPartLLVMVal _sym low hi (PE p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PE p $ LLVMValZero (bitvectorType hi)

selectHighBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (bytesToBits low)
  , Just (Some (hi_w))  <- someNat (bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do p' <- andPred sym p =<< natEq sym blk =<< natLit sym 0
       bv' <- bvSelect sym low_w hi_w bv
       return $ PE p' $ LLVMValInt blk bv'
  where w = bvWidth bv
selectHighBvPartLLVMVal _ _ _ _ = return Unassigned

-- | Look up an element in a partial LLVM array value.
arrayEltPartLLVMVal ::
  Word64 ->
  StorageType ->
  Word64 ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
arrayEltPartLLVMVal sz tp idx (PE p (LLVMValZero _))
  | 0 <= idx
  , idx < sz =
    return $ PE p (LLVMValZero tp)

arrayEltPartLLVMVal sz tp idx (PE p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ PE p (vec V.! fromIntegral idx)

arrayEltPartLLVMVal _ _ _ _ = return Unassigned

-- | Look up a field in a partial LLVM struct value.
fieldValPartLLVMVal ::
  (Vector (Field StorageType)) ->
  Int ->
  PartLLVMVal sym ->
  IO (PartLLVMVal sym)
fieldValPartLLVMVal flds idx (PE p (LLVMValZero _))
  | 0 <= idx
  , idx < V.length flds =
      return $ PE p $ LLVMValZero $ view fieldVal $ flds V.! idx

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

    muxzero :: Pred sym -> StorageType -> LLVMVal sym -> PartialT sym IO (LLVMVal sym)
    muxzero cond tpz val = case val of
      LLVMValZero  tp -> return $ LLVMValZero tp
      LLVMValUndef tpu ->
        -- TODO: Is this the right behavior?
        panic "Cannot mux zero and undef" [ "Zero type: " ++ show tpz
                                          , "Undef type: " ++ show tpu
                                          ]
      LLVMValInt base off ->
        do zbase <- lift $ natLit sym 0
           zoff  <- lift $ bvLit sym (bvWidth off) 0
           base' <- lift $ natIte sym cond zbase base
           off'  <- lift $ bvIte sym cond zoff off
           return $ LLVMValInt base' off'
      LLVMValFloat SingleSize x ->
        do zerof <- lift (iFloatLit sym SingleFloatRepr 0)
           x'    <- lift (iFloatIte @_ @SingleFloat sym cond zerof x)
           return $ LLVMValFloat SingleSize x'
      LLVMValFloat DoubleSize x ->
        do zerof <- lift (iFloatLit sym DoubleFloatRepr 0)
           x'    <- lift (iFloatIte @_ @DoubleFloat sym cond zerof x)
           return $ LLVMValFloat DoubleSize x'
      LLVMValFloat X86_FP80Size x ->
        do zerof <- lift (iFloatLit sym X86_80FloatRepr 0)
           x'    <- lift (iFloatIte @_ @X86_80Float sym cond zerof x)
           return $ LLVMValFloat X86_FP80Size x'

      LLVMValArray tp vec ->
        LLVMValArray tp <$> traverse (muxzero cond tp) vec

      LLVMValStruct flds ->
        LLVMValStruct <$> traverse (\(fld, v) -> (fld,) <$> muxzero cond (fld^.fieldVal) v) flds


    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> PartialT sym IO (LLVMVal sym)

    muxval cond (LLVMValZero tp) v = muxzero cond tp v
    muxval cond v (LLVMValZero tp) =
      do cond' <- lift $ notPred sym cond
         muxzero cond' tp v

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

    muxval _ v1@(LLVMValUndef tp1) (LLVMValUndef tp2)
      | tp1 == tp2 =
        return v1

    muxval _ _ _ = returnUnassigned

-}
