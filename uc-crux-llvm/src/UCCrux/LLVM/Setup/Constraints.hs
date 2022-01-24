{-
Module       : UCCrux.LLVM.Setup.Constraints
Description  : Generate predicates from constraints and Crucible values
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Setup.Constraints
  ( constraintToPred
  )
where

{- ORMOLU_DISABLE -}
import qualified Text.LLVM.AST as L

-- parameterized-utils
import           Data.Parameterized.NatRepr (type (<=))

-- what4
import           What4.Interface (Pred)
import qualified What4.Interface as W4I

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.MemModel.Pointer as LLVMPointer

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Constraints (Constraint(..))
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ToCrucibleType)
{- ORMOLU_ENABLE -}

-- | Take a symbolic value (a 'Crucible.RegEntry') and a 'Constraint' that
-- applies to it, and generate a 'W4I.Pred' that represents the 'Constraint'
-- as it applies to the 'Crucible.RegEntry'.
constraintToPred ::
  forall proxy m arch sym fty.
  Crucible.IsSymInterface sym =>
  ArchOk arch =>
  proxy arch ->
  sym ->
  -- | The constraint that should be assumed to be true of this value
  Constraint m fty ->
  -- | Type of the value to be constrained
  FullTypeRepr m fty ->
  -- | The value to be constrained
  Crucible.RegValue sym (ToCrucibleType arch fty) ->
  IO (Pred sym)
constraintToPred _proxy sym constraint fullTypeRepr regValue =
  case (fullTypeRepr, constraint) of
    (_, Aligned alignment) ->
      LLVMMem.isAligned sym ?ptrWidth regValue alignment
    (FTIntRepr w, BVCmp op _ bv) ->
      interpretOp op (LLVMPointer.llvmPointerOffset regValue)
        =<< W4I.bvLit sym w bv
  where
    interpretOp ::
      forall w. 1 <= w => L.ICmpOp -> W4I.SymBV sym w -> W4I.SymBV sym w -> IO (W4I.Pred sym)
    interpretOp =
      \case
        L.Ieq -> W4I.bvEq sym
        L.Ine -> W4I.bvNe sym
        L.Iult -> W4I.bvUlt sym
        L.Iule -> W4I.bvUle sym
        L.Iugt -> W4I.bvUgt sym
        L.Iuge -> W4I.bvUge sym
        L.Islt -> W4I.bvSlt sym
        L.Isle -> W4I.bvSle sym
        L.Isgt -> W4I.bvSgt sym
        L.Isge -> W4I.bvSge sym
