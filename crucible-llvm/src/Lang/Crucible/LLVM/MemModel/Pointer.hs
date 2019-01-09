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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

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
  , pattern SizeT
  , pattern LLVMPointer
  , ptrWidth
  , llvmPointerView
  , llvmPointerBlock
  , llvmPointerOffset
  , muxLLVMPtr
  , projectLLVM_bv
  , llvmPointer_bv
  , mkNullPointer

    -- * Operations on valid pointers
  , constOffset
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

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr

import           What4.Interface
import           What4.InterpretedFloatingPoint

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.Bytes as G
import           Lang.Crucible.LLVM.Types

data LLVMPointer sym w =
  -- | This pattern synonym gives an easy way to construct/deconstruct runtime values of type 'LLVMPtr'.
  LLVMPointer (SymNat sym) (SymBV sym w)

llvmPointerBlock :: LLVMPtr sym w -> SymNat sym
llvmPointerBlock (LLVMPointer blk _) = blk

llvmPointerOffset :: LLVMPtr sym w -> SymBV sym w
llvmPointerOffset (LLVMPointer _ off) = off

-- | Type family defining how @LLVMPointerType@ unfolds.
type family LLVMPointerImpl sym ctx where
  LLVMPointerImpl sym (EmptyCtx ::> BVType w) = LLVMPointer sym w
  LLVMPointerImpl sym ctx = TypeError ('Text "LLVM_pointer expects a single argument of BVType, but was given" ':<>:
                                       'ShowType ctx)

instance (IsSymInterface sym) => IntrinsicClass sym "LLVM_pointer" where
  type Intrinsic sym "LLVM_pointer" ctx = LLVMPointerImpl sym ctx

  muxIntrinsic sym _iTypes _nm (Ctx.Empty Ctx.:> (BVRepr _w)) = muxLLVMPtr sym
  muxIntrinsic _ _ nm ctx = typeError nm ctx

-- | Alternative to the 'LLVMPointer' pattern synonym, this function can be used as a view
--   constructor instead to silence incomplete pattern warnings.
llvmPointerView :: LLVMPtr sym w -> (SymNat sym, SymBV sym w)
llvmPointerView (LLVMPointer blk off) = (blk, off)

-- | Compute the width of a pointer value.
ptrWidth :: IsExprBuilder sym => LLVMPtr sym w -> NatRepr w
ptrWidth (LLVMPointer _blk bv) = bvWidth bv

-- | Assert that the given LLVM pointer value is actually a raw bitvector and extract its value.
projectLLVM_bv ::
  IsSymInterface sym => sym -> LLVMPtr sym w -> IO (SymBV sym w)
projectLLVM_bv sym ptr@(LLVMPointer blk bv) =
  do p <- natEq sym blk =<< natLit sym 0
     assert sym p $
        AssertFailureSimError $ unlines
          [ "Pointer value coerced to bitvector:"
          , "*** " ++ show (ppPtr ptr)
          ]
     return bv

-- | Convert a raw bitvector value into an LLVM pointer value.
llvmPointer_bv :: IsSymInterface sym => sym -> SymBV sym w -> IO (LLVMPtr sym w)
llvmPointer_bv sym bv =
  do blk0 <- natLit sym 0
     return (LLVMPointer blk0 bv)

-- | Produce the distinguished null pointer value.
mkNullPointer :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> IO (LLVMPtr sym w)
mkNullPointer sym w = llvmPointer_bv sym =<< bvLit sym w 0

-- | Mux function specialized to LLVM pointer values.
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

-- | Generate a concrete offset value from an @Addr@ value.
constOffset :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> G.Addr -> IO (SymBV sym w)
constOffset sym w x = bvLit sym w (G.bytesToInteger x)

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

-- | Test whether two pointers are equal.
--
-- The returned predicates assert (in this order):
--  * the pointers are equal
--  * the comparison is valid: the pointers are to the same allocation
ptrEq :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym, Pred sym)
ptrEq sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  (,) <$> bvEq sym off1 off2 <*> natEq sym base1 base2

-- | Test whether one pointer is less than or equal to the other.
--
-- The returned predicates assert (in this order):
--  * the first pointer is less than or equal to the second
--  * the comparison is valid: the pointers are to the same allocation
ptrLe :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym, Pred sym)
ptrLe sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  (,) <$> bvUle sym off1 off2 <*> natEq sym base1 base2

-- | Test whether one pointer is less than or equal to the other.
--
-- The returned predicates assert (in this order):
--  * the first pointer is less than the second
--  * the comparison is valid: the pointers are to the same allocation
ptrLt :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym, Pred sym)
ptrLt sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  (,) <$> bvUlt sym off1 off2 <*> natEq sym base1 base2

-- | Add an offset to a pointer.
ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtr sym w
       -> SymBV sym w
       -> IO (LLVMPtr sym w)
ptrAdd sym _w (LLVMPointer base off1) off2 =
  LLVMPointer base <$> bvAdd sym off1 off2

-- | Compute the difference between two pointers. The returned predicate asserts
-- that the pointers point into the same allocation block.
ptrDiff :: (1 <= w, IsSymInterface sym)
        => sym
        -> NatRepr w
        -> LLVMPtr sym w
        -> LLVMPtr sym w
        -> IO (SymBV sym w, Pred sym)
ptrDiff sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2) =
  (,) <$> bvSub sym off1 off2 <*> natEq sym base1 base2

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

-- | Test if a pointer value is the null pointer.
ptrIsNull :: (1 <= w, IsSymInterface sym)
          => sym
          -> NatRepr w
          -> LLVMPtr sym w
          -> IO (Pred sym)
ptrIsNull sym _w (LLVMPointer blk off) =
  do pblk <- natEq sym blk =<< natLit sym 0
     poff <- bvEq sym off =<< bvLit sym (bvWidth off) 0
     andPred sym pblk poff


ppPtr  :: IsExpr (SymExpr sym) => LLVMPtr sym wptr -> Doc
ppPtr (llvmPointerView -> (blk, bv))
  | Just 0 <- asNat blk = printSymExpr bv
  | otherwise =
     let blk_doc = printSymExpr blk
         off_doc = printSymExpr bv
      in text "(" <> blk_doc <> text "," <+> off_doc <> text ")"
