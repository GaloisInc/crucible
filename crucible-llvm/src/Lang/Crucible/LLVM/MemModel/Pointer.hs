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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lang.Crucible.LLVM.MemModel.Pointer
  ( -- * Pointer bitwidth
    HasPtrWidth
  , pattern PtrWidth
  , withPtrWidth

    -- * Crucible pointer representation
  , LLVMPointerType
  , LLVMPtr
  , SomePointer(..)
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , pattern SizeT
  , pattern LLVMPointer
  , ptrWidth
  , llvmPointerView
  , llvmPointerBlock
  , llvmPointerOffset
  , llvmPointerType
  , muxLLVMPtr
  , llvmPointer_bv
  , mkNullPointer

    -- * Concretization
  , concBV
  , concPtr
  , concPtr'

    -- * Operations on valid pointers
  , constOffset
  , ptrEq
  , ptrLe
  , ptrAdd
  , ptrDiff
  , ptrSub
  , ptrIsNull
  , isGlobalPointer
  , isGlobalPointer'

    -- * Pretty printing
  , ppPtr

    -- * Annotation
  , annotatePointerBlock
  , annotatePointerOffset
  ) where

import           Control.Monad (guard)
import           Data.Map (Map)
import qualified Data.Map as Map (lookup)
import           Numeric.Natural
import           Prettyprinter

import           GHC.TypeLits (TypeError, ErrorMessage(..))
import           GHC.TypeNats

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import qualified Text.LLVM.AST as L

import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Expr (GroundValue)

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Types
import qualified Lang.Crucible.LLVM.Bytes as G
import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.MemModel.Options



data LLVMPointer sym w =
  -- |A pointer is a base point offset.
  LLVMPointer (SymNat sym) (SymBV sym w)

deriving instance (Show (SymNat sym), Show (SymBV sym w)) => Show (LLVMPointer sym w)

llvmPointerBlock :: LLVMPtr sym w -> SymNat sym
llvmPointerBlock (LLVMPointer blk _) = blk

llvmPointerOffset :: LLVMPtr sym w -> SymBV sym w
llvmPointerOffset (LLVMPointer _ off) = off

llvmPointerType :: IsExpr (SymExpr sym) => LLVMPtr sym w -> TypeRepr (LLVMPointerType w)
llvmPointerType ptr =
  case exprType (llvmPointerOffset ptr) of
    BaseBVRepr w -> LLVMPointerRepr w

-- | Type family defining how @LLVMPointerType@ unfolds.
type family LLVMPointerImpl sym ctx where
  LLVMPointerImpl sym (EmptyCtx ::> BVType w) = LLVMPointer sym w
  LLVMPointerImpl sym ctx = TypeError ('Text "LLVM_pointer expects a single argument of BVType, but was given" ':<>:
                                       'ShowType ctx)

-- | A pointer with an existentially-quantified width
data SomePointer sym = forall w. (1 <= w) => SomePointer !(LLVMPtr sym w)

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

-- | Convert a raw bitvector value into an LLVM pointer value.
llvmPointer_bv :: IsSymInterface sym => sym -> SymBV sym w -> IO (LLVMPtr sym w)
llvmPointer_bv sym bv =
  do blk0 <- natLit sym 0
     return (LLVMPointer blk0 bv)

-- | Produce the distinguished null pointer value.
mkNullPointer :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> IO (LLVMPtr sym w)
mkNullPointer sym w = llvmPointer_bv sym =<< bvLit sym w (BV.zero w)


concBV ::
  (IsExprBuilder sym, 1 <= w) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  SymBV sym w -> IO (SymBV sym w)
concBV sym conc bv =
  do bv' <- conc bv
     bvLit sym (bvWidth bv) bv'

concPtr ::
  (IsExprBuilder sym, 1 <= w) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  RegValue sym (LLVMPointerType w) ->
  IO (RegValue sym (LLVMPointerType w))
concPtr sym conc (LLVMPointer blk off) =
  do blk' <- integerToNat sym =<< intLit sym =<< conc =<< natToInteger sym blk
     off' <- concBV sym conc off
     pure (LLVMPointer blk' off')

concPtr' ::
  (IsExprBuilder sym, 1 <= w) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  RegValue' sym (LLVMPointerType w) ->
  IO (RegValue' sym (LLVMPointerType w))
concPtr' sym conc (RV ptr) = RV <$> concPtr sym conc ptr


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
constOffset sym w x = bvLit sym w (G.bytesToBV w x)

-- | Test whether two pointers are equal.
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

-- | Test whether one pointer is less than or equal to the other.
--
-- The returned predicates assert (in this order):
--  * the first pointer is less than or equal to the second
--  * the comparison is valid: the pointers are to the same allocation
ptrLe :: (1 <= w, IsSymInterface sym, ?memOpts :: MemOptions)
      => sym
      -> NatRepr w
      -> LLVMPtr sym w
      -> LLVMPtr sym w
      -> IO (Pred sym, Pred sym)
ptrLe sym _w (LLVMPointer base1 off1) (LLVMPointer base2 off2)
  | laxPointerOrdering ?memOpts
  = do plt <- natLt sym base1 base2
       peq <- natEq sym base1 base2
       bvle <- bvUle sym off1 off2

       p <- orPred sym plt =<< andPred sym peq bvle
       return (p, truePred sym)

  | otherwise
  = do peq <- natEq sym base1 base2
       bvle <- bvUle sym off1 off2
       return (bvle, peq)

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
ptrIsNull sym w (LLVMPointer blk off) =
  do pblk <- natEq sym blk =<< natLit sym 0
     poff <- bvEq sym off =<< bvLit sym (bvWidth off) (BV.zero w)
     andPred sym pblk poff

ppPtr :: IsExpr (SymExpr sym) => LLVMPtr sym wptr -> Doc ann
ppPtr (llvmPointerView -> (blk, bv))
  | Just 0 <- asNat blk = printSymExpr bv
  | otherwise =
     let blk_doc = printSymNat blk
         off_doc = printSymExpr bv
      in pretty "(" <> blk_doc <> pretty "," <+> off_doc <> pretty ")"

-- | Look up a pointer in the 'memImplGlobalMap' to see if it's a global.
--
-- This is best-effort and will only work if the pointer is fully concrete
-- and matches the address of the global on the nose. It is used in SAWscript
-- for friendly error messages.
isGlobalPointer ::
  forall sym w. (IsSymInterface sym) =>
  Map Natural L.Symbol {- ^ c.f. 'memImplSymbolMap' -} ->
  LLVMPtr sym w -> Maybe L.Symbol
isGlobalPointer symbolMap needle =
  do n <- asNat (llvmPointerBlock needle)
     z <- asBV (llvmPointerOffset needle)
     guard (BV.asUnsigned z == 0)
     Map.lookup n symbolMap

-- | For when you don't know @1 <= w@
isGlobalPointer' ::
  forall sym w. (IsSymInterface sym) =>
  Map Natural L.Symbol {- ^ c.f. 'memImplSymbolMap' -} ->
  LLVMPtr sym w -> Maybe L.Symbol
isGlobalPointer' symbolMap needle =
  case testLeq (knownNat :: NatRepr 1) (ptrWidth needle) of
    Nothing       -> Nothing
    Just LeqProof -> isGlobalPointer symbolMap needle

annotatePointerBlock ::
  forall sym w. (IsSymInterface sym) =>
  sym ->
  LLVMPtr sym w ->
  IO (SymAnnotation sym BaseIntegerType, LLVMPointer sym w)
annotatePointerBlock sym (LLVMPointer blk off) =
  do (annotation, annotatedBlkInt) <- annotateTerm sym =<< natToInteger sym blk
     annotatedBlkNat <- integerToNat sym annotatedBlkInt
     pure (annotation, LLVMPointer annotatedBlkNat off)

annotatePointerOffset ::
  forall sym w. (IsSymInterface sym) =>
  sym ->
  LLVMPtr sym w ->
  IO (SymAnnotation sym (BaseBVType w), LLVMPointer sym w)
annotatePointerOffset sym (LLVMPointer blk off) =
  do (annotation, annotatedOff) <- annotateTerm sym off
     pure (annotation, LLVMPointer blk annotatedOff)
