{-
Module           : UCCrux.LLVM.FullType.Memory
Description      : Helpers pertaining to LLVM memory
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}

module UCCrux.LLVM.FullType.Memory
  ( sizeInBytes,
    sizeBv,
    pointerRange
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (head, reverse, zip)

import           Control.Lens ((^.), to)
import           Control.Monad (foldM)
import           Data.BitVector.Sized (mkBV)
import           Data.List.NonEmpty (NonEmpty((:|)), reverse)

-- what4
import qualified What4.Interface as What4

-- crucible
import qualified Lang.Crucible.Backend as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.Bytes (bytesToInteger)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.MemType (memTypeSize)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext(llvmDataLayout))

-- crux
import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTranslation)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr)
{- ORMOLU_ENABLE -}


-- | Size in bytes of an array of a given type with a given length.
sizeInBytes ::
  ModuleContext m arch ->
  FullTypeRepr m ft ->
  -- | Array length
  Integer ->
  Integer
sizeInBytes modCtx ftRepr size =
  let dl =
        modCtx
          ^. moduleTranslation
            . LLVMTrans.transContext
            . LLVMTrans.llvmTypeCtx
            . to llvmDataLayout
  in size * bytesToInteger (memTypeSize dl (toMemType ftRepr))

-- | A concrete bitvector representing the size (in bytes) of an array of data
-- of a given type in memory.
sizeBv ::
  ( Crucible.IsSymInterface sym,
    ArchOk arch
  ) =>
  ModuleContext m arch ->
  sym ->
  FullTypeRepr m ft ->
  -- | Array length
  Integer ->
  IO (What4.SymExpr sym (What4.BaseBVType (ArchWidth arch)))
sizeBv modCtx sym ftRepr size =
  What4.bvLit sym ?ptrWidth (mkBV ?ptrWidth (sizeInBytes modCtx ftRepr size))

-- | TODO document parameters
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
  -- | Number of pointers to generate/times to add the offset
  Int ->
  IO (NonEmpty (LLVMMem.LLVMPtr sym (ArchWidth arch)))
pointerRange _proxy sym ptr offset size =
  if size == 0
    then panic "pointerRange" ["Zero size"]
    else
      reverse
        <$> foldM
          ( \(p :| ps) () ->
              do
                p' <- LLVMMem.ptrAdd sym ?ptrWidth p offset
                pure (p' :| (p : ps))
          )
          (ptr :| [])
          (replicate (size - 1) ())
