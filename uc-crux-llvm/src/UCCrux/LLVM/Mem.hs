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
    storeGlobal'
  )
where

{- ORMOLU_DISABLE -}
import qualified Text.LLVM.AST as L

-- what4
import           What4.Interface (Pred)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.MemModel (MemImpl, MemOptions, HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (ModuleTypes, FullType(FTPtr), FullTypeRepr, ToCrucibleType, pointedToType)
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
