{-
Module           : UCCrux.LLVM.FullType.Memory
Description      : Helpers pertaining to LLVM memory
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.Memory
  ( sizeInBytes,
    arraySizeInBytes,
    sizeBv,
    arraySizeBv,
    pointerRange
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))
import           Data.BitVector.Sized (mkBV)

import           Data.Parameterized.NatRepr (NatRepr, type (+))
import qualified Data.Parameterized.Vector as PVec

-- what4
import qualified What4.Interface as What4

-- crucible
import qualified Lang.Crucible.Backend as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (memTypeSize)

-- crux
import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr, ModuleTypes, dataLayout, crucibleDataLayout)
{- ORMOLU_ENABLE -}

-- | Size in bytes of a given type.
sizeInBytes ::
  ModuleTypes m ->
  FullTypeRepr m ft ->
  Integer
sizeInBytes mts ftRepr =
  let dl = dataLayout mts
      cdl = crucibleDataLayout dl
  in bytesToInteger (memTypeSize cdl (toMemType dl ftRepr))

-- | Size in bytes of an array of a given type with a given length.
arraySizeInBytes ::
  ModuleTypes m ->
  FullTypeRepr m ft ->
  -- | Array length
  Integer ->
  Integer
arraySizeInBytes mts ftRepr size = size * sizeInBytes mts ftRepr

-- | A concrete bitvector representing the size (in bytes) of data of a given
-- type in memory.
sizeBv ::
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  ModuleContext m arch ->
  sym ->
  FullTypeRepr m ft ->
  IO (What4.SymExpr sym (What4.BaseBVType (ArchWidth arch)))
sizeBv modCtx sym ftRepr =
  What4.bvLit sym ?ptrWidth (mkBV ?ptrWidth (sizeInBytes (modCtx ^. moduleTypes) ftRepr))

-- | A concrete bitvector representing the size (in bytes) of an array of data
-- of a given type in memory.
arraySizeBv ::
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  ModuleContext m arch ->
  sym ->
  FullTypeRepr m ft ->
  -- | Array length
  Integer ->
  IO (What4.SymExpr sym (What4.BaseBVType (ArchWidth arch)))
arraySizeBv modCtx sym ftRepr size =
  What4.bvLit sym ?ptrWidth (mkBV ?ptrWidth (arraySizeInBytes (modCtx ^. moduleTypes) ftRepr size))

-- | A vector of pointers created by repeatedly adding an offset to a given base
-- pointer.
pointerRange ::
  ( ArchOk arch,
    Crucible.IsSymInterface sym
  ) =>
  proxy arch ->
  sym ->
  -- | Base pointer
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  -- | Offset to add
  What4.SymBV sym (ArchWidth arch) ->
  -- | Number of pointers to generate/times to add the offset, minus one
  NatRepr n ->
  IO (PVec.Vector (n + 1) (LLVMMem.LLVMPtr sym (ArchWidth arch)))
pointerRange _proxy sym ptr offset size = PVec.iterateNM size addOffset ptr
  where
    addOffset p = LLVMMem.ptrAdd sym ?ptrWidth p offset
         
