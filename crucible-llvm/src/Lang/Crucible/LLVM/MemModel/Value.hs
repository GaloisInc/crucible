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
   | Some w <- mkNatRepr (bytesToBits bytes)
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
