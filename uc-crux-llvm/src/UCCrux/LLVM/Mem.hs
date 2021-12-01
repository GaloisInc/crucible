{-
Module       : UCCrux.LLVM.Mem
Description  : Utilities for dealing with LLVM memory using UC-Crux concepts
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Mem
  ( loadRaw,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.))

-- what4
import           What4.Interface (Pred)

-- crucible
import           Lang.Crucible.Backend (IsSymInterface)
import qualified Lang.Crucible.Simulator as Crucible

-- crucible-llvm
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

-- crux-llvm
import           Crux.LLVM.Overrides (ArchOk)

-- uc-crux-llvm
import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.FullType.CrucibleType (toCrucibleType)
import           UCCrux.LLVM.FullType.StorageType (toStorageType)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr, ToCrucibleType, pointedToType)
{- ORMOLU_ENABLE -}

-- TODO: Alignment...?
loadRaw ::
  forall arch m sym atTy.
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  ArchOk arch =>
  (?memOpts :: LLVMMem.MemOptions) =>
  ModuleContext m arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegValue sym (ToCrucibleType arch ('FTPtr atTy)) ->
  FullTypeRepr m ('FTPtr atTy) ->
  IO (Pred sym, Maybe (Crucible.RegValue sym (ToCrucibleType arch atTy)))
loadRaw modCtx sym mem val fullTypeRepr =
  do let pointedToRepr = pointedToType (modCtx ^. moduleTypes) fullTypeRepr
         typeRepr = toCrucibleType modCtx pointedToRepr
     -- TODO Is this alignment right?
     partVal <-
       LLVMMem.loadRaw sym mem val (toStorageType pointedToRepr) noAlignment
     case partVal of
       LLVMMem.Err p -> return (p, Nothing)
       LLVMMem.NoErr p ptdToVal ->
         (p,) . Just <$> LLVMMem.unpackMemValue sym typeRepr ptdToVal
