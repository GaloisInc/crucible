{-
Module           : UCCrux.LLVM.FullType.StorageType
Description      : Interop between 'FullType' and 'StorageType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}

module UCCrux.LLVM.FullType.StorageType
  ( toStorageType,
  )
where

{- ORMOLU_DISABLE -}
import           Lang.Crucible.LLVM.MemModel (HasPtrWidth, StorageType)
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem (toStorableType)

import           UCCrux.LLVM.FullType.Type (FullTypeRepr, DataLayout)
import           UCCrux.LLVM.FullType.MemType (toMemType)
import           UCCrux.LLVM.Errors.Panic (panic)
{- ORMOLU_ENABLE -}

toStorageType ::
  HasPtrWidth wptr =>
  DataLayout m ->
  FullTypeRepr m ft ->
  StorageType
toStorageType dl fullTypeRepr =
  let memType = toMemType dl fullTypeRepr
  in case LLVMMem.toStorableType memType of
       Nothing ->
         panic
           "Impossible: 'toMemType' returned a metadata type?"
           [ "Either that, or the failure condition of"
           , "'toStorableType' has changed."
           ]
       Just st -> st
