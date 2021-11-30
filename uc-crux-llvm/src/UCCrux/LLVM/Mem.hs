{-
Module       : UCCrux.LLVM.Mem
Description  : Utilities for dealing with LLVM memory using UC-Crux concepts
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

Mostly provides wrappers that use 'FullType' instead of Crucible-LLVM's
@MemType@ and @StorageType@ and Crucible's @TypeRepr@.

TODO(lb): All of these need a review on how they handle alignment.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Mem
  ( loadRaw,
    loadRaw',
    load,
    load',
    store,
    store',
    storeGlobal,
    storeGlobal',
    seekPtr
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), to)
import           Control.Monad (unless)
import           Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector as Vec

import qualified Text.LLVM.AST as L

-- parameterized-utils
import           Data.Parameterized.Classes (ixF')
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (intValue)

-- what4
import           What4.Interface (Pred)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.MemModel (LLVMPointerType, MemImpl, MemOptions, HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented, Unimplemented(SeekOffset))
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(..), toCrucibleType, translateIndex)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (ModuleTypes, FullType(FTPtr), FullTypeRepr(..), ToCrucibleType, pointedToType, asFullType)
{- ORMOLU_ENABLE -}

loadRaw ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m atTy ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
loadRaw proxy sym mem ptr fullTypeRepr =
  do let typeRepr = toCrucibleType proxy fullTypeRepr
     partVal <-
       LLVMMem.loadRaw sym mem ptr (toStorageType fullTypeRepr) noAlignment
     case partVal of
       LLVMMem.Err p -> return (p, Nothing)
       LLVMMem.NoErr p ptdToVal ->
         (p,) . Just <$> LLVMMem.unpackMemValue sym typeRepr ptdToVal

loadRaw' ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  ModuleTypes m ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
loadRaw' proxy sym mem mts ptr fullTypeRepr =
  let pointedToRepr = pointedToType mts fullTypeRepr
  in loadRaw proxy sym mem ptr pointedToRepr

load ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m atTy ->
  IO (Crucible.RegValue sym (ToCrucibleType arch atTy))
load proxy sym mem ptr fullTypeRepr =
  do let typeRepr = toCrucibleType proxy fullTypeRepr
     LLVMMem.doLoad sym mem ptr (toStorageType fullTypeRepr) typeRepr noAlignment

load' ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: MemOptions) =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  ModuleTypes m ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Crucible.RegValue sym (ToCrucibleType arch atTy))
load' proxy sym mem mts ptr fullTypeRepr =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     load proxy sym mem ptr pointedToRepr

store ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  FullTypeRepr m ft ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
store proxy sym mem fullTypeRepr ptr regValue =
  do let storageType = toStorageType fullTypeRepr
     let cType = toCrucibleType proxy fullTypeRepr
     LLVMMem.doStore sym mem ptr cType storageType noAlignment regValue

store' ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  LLVMMem.LLVMPtr sym (ArchWidth arch) ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
store' proxy sym mem mts fullTypeRepr ptr regValue =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     store proxy sym mem pointedToRepr ptr regValue

storeGlobal ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  FullTypeRepr m ft ->
  L.Symbol ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
storeGlobal proxy sym mem fullTypeRepr symb regValue =
  do ptr <- LLVMMem.doResolveGlobal sym mem symb
     let storageType = toStorageType fullTypeRepr
     let cType = toCrucibleType proxy fullTypeRepr
     LLVMMem.doStore sym mem ptr cType storageType noAlignment regValue

storeGlobal' ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  proxy arch ->
  sym ->
  MemImpl sym ->
  ModuleTypes m ->
  FullTypeRepr m ('FTPtr ft) ->
  L.Symbol ->
  Crucible.RegValue sym (ToCrucibleType arch ft) ->
  IO (MemImpl sym)
storeGlobal' proxy sym mem mts fullTypeRepr symb regValue =
  do let pointedToRepr = pointedToType mts fullTypeRepr
     storeGlobal proxy sym mem pointedToRepr symb regValue

-- | Find a pointer inside of a value
seekPtr ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  -- | Program memory
  MemImpl sym ->
  -- | Type of value that contains pointer
  FullTypeRepr m inTy ->
  -- | Value containing pointer
  Crucible.RegValue sym (ToCrucibleType arch inTy) ->
  -- | Where the pointer is inside the value
  Cursor m inTy ('FTPtr atTy) ->
  IO (Crucible.RegValue sym (LLVMPointerType (ArchWidth arch)))
seekPtr modCtx sym mem fullTypeRepr regVal cursor =
  case (fullTypeRepr, cursor) of
    (FTArrayRepr _n fullTypeRepr', Index i _ cur) ->
      -- TODO(lb): overflow...?
      let val = regVal Vec.! fromIntegral (intValue i)
      in seekPtr modCtx sym mem fullTypeRepr' val cur
    (FTStructRepr _structInfo fields, Field _fieldTypes idx cur) ->
      let ty = fields ^. ixF' idx
      in case translateIndex modCtx (Ctx.size fields) idx of
           SomeIndex idx' Refl ->
             let val = regVal ^. ixF' idx' . to Crucible.unRV
             in seekPtr modCtx sym mem ty val cur
    (FTPtrRepr ptRepr, Dereference i cur) ->
      do unless (i == 0) $
           unimplemented "seekPtr" SeekOffset
         newVal <-
           load' modCtx sym mem (modCtx ^. moduleTypes) regVal fullTypeRepr
         let ftPtdTo = asFullType (modCtx ^. moduleTypes) ptRepr
         seekPtr modCtx sym mem ftPtdTo newVal cur
    (FTPtrRepr _ptRepr, Here _) -> return regVal
