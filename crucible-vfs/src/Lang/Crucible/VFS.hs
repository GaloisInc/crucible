-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.VFS
-- Description      : Core definitions of the symbolic filesystem model
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.VFS where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.Trans.State
import           Control.Monad.IO.Class
import           Numeric.Natural
import           Data.IORef

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V


import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Backend
import           Lang.Crucible.Utils.MuxTree
import           Lang.Crucible.Types
import           What4.Interface
import           What4.Partial

import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.VFS.Types
import           Lang.Crucible.VFS.Extension.Syntax
import           Lang.Crucible.Panic (panic)

import           GHC.Stack


data FileDescriptor sym w where
  FileDescriptor ::
    { filePointer :: LLVMPtr sym w,
      -- ^ pointer to the start of this file in the memory filesystem
      fileSize :: SymBV sym w
      -- ^ the size of this file
    } -> FileDescriptor sym w

data VFSImpl sym =
  VFSImpl
  { vfsImplBlockSource :: BlockSource
  -- ^ nonce for file handle identifiers
  , vfsFileNames :: Map FileIdent (Some (FileDescriptor sym))
  -- ^ resolve file identifiers (names) to their manifest location
  -- in the global space of the memory filesystem
  , vfsFileBlocks :: Map Natural (Some (FileDescriptor sym))
  -- ^ map block identifiers back to their underlying
  -- descriptor
  , vfsHandleAllocator :: HandleAllocator
  -- ^ allocator for file handle reference cells
  , vfsMem :: G.Mem sym
  }

instance IntrinsicClass sym "VFS_files" where
  type Intrinsic sym "VFS_files" ctx = VFSImpl sym

  muxIntrinsic _sym _iTypes _nm _ p vfs1 vfs2 = do
    let VFSImpl blockSource fNames1 blks1 ha m1 = vfs1
    let VFSImpl _blockSource _fNames2 blks2 _ha m2 = vfs2
    return $ VFSImpl blockSource fNames1 (Map.union blks1 blks2) ha (G.mergeMem p m1 m2)

  pushBranchIntrinsic _sym _iTypes _nm _ctx vfs = do
    return $ vfs { vfsMem = G.branchMem (vfsMem vfs) }

  abortBranchIntrinsic _sym _iTypes _nm _ vfs = do
    return $ vfs { vfsMem =  G.branchAbortMem (vfsMem vfs) }


type EvalM p sym ext rtp blocks ret args a =
  StateT (CrucibleState p sym ext rtp blocks ret args) IO a

evalStmt :: forall p sym ext rtp blocks ret args wptr tp
          . (IsSymInterface sym, HasPtrWidth wptr, HasCallStack, HasLLVMAnn sym)
         => sym
         -> VFSStmt wptr (RegEntry sym) tp
         -> EvalM p sym ext rtp blocks ret args (RegValue sym tp)
evalStmt sym = eval
  where
    getFiles :: GlobalVar Files ->
                EvalM p sym ext rtp blocks ret args (VFSImpl sym)
    getFiles fvar = do
      gs <- use (stateTree.actFrame.gpGlobals)
      case lookupGlobal fvar gs of
        Just files -> return files
        Nothing -> panic "getFiles" []

    setFiles :: GlobalVar Files ->
                VFSImpl sym ->
                EvalM p sym ext rtp blocks ret args ()
    setFiles fvar files = stateTree.actFrame.gpGlobals %= insertGlobal fvar files

    -- | Resolve a file handle as a pointer to its current location in the file buffer
    getHandle :: VFSFileHandle sym wptr ->
                 EvalM p sym ext rtp blocks ret args (LLVMPtr sym wptr)
    getHandle fhandle = do
      gs <- use (stateTree.actFrame.gpGlobals)
      ctx <- use stateContext
      let iTypes = ctxIntrinsicTypes ctx
      liftIO $ readRef sym iTypes PtrRepr fhandle gs

    setHandle :: VFSFileHandle sym wptr ->
                 LLVMPtr sym wptr ->
                 EvalM p sym ext rtp blocks ret args ()
    setHandle fhandle ptr = do
      gs <- use (stateTree.actFrame.gpGlobals)
      ctx <- use stateContext
      let iTypes = ctxIntrinsicTypes ctx
      gs' <- liftIO $ alterRef sym iTypes PtrRepr fhandle (justPartExpr sym ptr) gs
      stateTree.actFrame.gpGlobals .= gs'

    eval :: VFSStmt wptr (RegEntry sym) tp ->
            EvalM p sym ext rtp blocks ret args (RegValue sym tp)
    eval (VFS_Open _w fvar fident) = do
      files <- getFiles fvar
      (ptr, files') <- liftIO $ doOpenFile sym files fident
      cell <- liftIO $ freshRefCell (vfsHandleAllocator files) PtrRepr
      stateTree.actFrame.gpGlobals %= insertRef sym cell ptr
      setFiles fvar files'
      return $ toMuxTree sym cell

    eval (VFS_Close fvar (regValue -> fhandle)) = do
      files <- getFiles fvar
      ptr <- getHandle fhandle
      files' <- liftIO $ doCloseFile sym files ptr
      setFiles fvar files'
      nullptr <- liftIO $ mkNullPointer sym PtrWidth
      setHandle fhandle nullptr

    eval (VFS_Read fvar (regValue -> fhandle) size) = do
      files <- getFiles fvar
      ptr <- getHandle fhandle
      bytes <- liftIO $ doReadFileBytes sym files ptr size
      off <- liftIO $ bvLit sym PtrWidth (bytesToInteger size)
      nextptr <- liftIO $ ptrAdd sym PtrWidth ptr off
      setHandle fhandle nextptr
      return bytes

    eval (VFS_Write fvar (regValue -> fhandle) (regValue -> bytes)) = do
      files <- getFiles fvar
      ptr <- getHandle fhandle
      files' <- liftIO $ doWriteFileBytes sym files ptr bytes
      off <- liftIO $ bvLit sym PtrWidth (fromIntegral $ V.length bytes)
      nextptr <- liftIO $ ptrAdd sym PtrWidth ptr off
      setHandle fhandle nextptr
      setFiles fvar files'

-- | Load a file into a buffer based on its identifier, returning a pointer to
-- the start of the buffer.
doOpenFile ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack) =>
  sym ->
  VFSImpl sym ->
  FileIdent ->
  IO (LLVMPtr sym wptr, VFSImpl sym)
doOpenFile sym files fident = do
  fd <- doResolveFile sym files fident
  blkId <- nextBlock (vfsImplBlockSource files)
  let mem' = G.allocMem G.HeapAlloc blkId (Just (fileSize fd)) noAlignment G.Mutable "" (vfsMem files)
  z <- bvLit sym PtrWidth 0
  blk <- natLit sym blkId
  let ptr = LLVMPointer blk z
  (mem'', p1, p2) <- G.copyMem sym PtrWidth ptr (filePointer fd) (fileSize fd) mem'
  assert sym p1 (AssertFailureSimError "Error in call to memcpy" [])
  assert sym p2 (AssertFailureSimError "Error in call to memcpy" [])
  return (ptr, files {vfsMem = mem''})


-- | Close an open file handle by first copying its buffer contents back
-- to the filesystem and then freeing the associated buffer.
doCloseFile ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack) =>
  sym ->
  VFSImpl sym ->
  LLVMPtr sym wptr ->
  IO (VFSImpl sym)
doCloseFile sym files ptr = do
  let (blk, _) = llvmPointerView ptr
  z <- liftIO $ bvLit sym PtrWidth 0
  let start_ptr = LLVMPointer blk z
  fd <- liftIO $ getFileDescriptor sym files ptr
  (mem', p1, p2) <- liftIO $ G.copyMem sym PtrWidth (filePointer fd) start_ptr (fileSize fd) (vfsMem files)
  assert sym p1 (AssertFailureSimError "Error in call to memcpy" [])
  assert sym p2 (AssertFailureSimError "Error in call to memcpy" [])

  (mem'', p3, p4) <- liftIO $ G.freeMem sym PtrWidth start_ptr mem'
  assert sym p3 (AssertFailureSimError "Error in call to freeMem" [])
  assert sym p4 (AssertFailureSimError "Error in call to freeMem" [])
  return $ files { vfsMem = mem'' }

-- | Add a new file to the filesystem with the given contents.
doAddFile ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack, HasLLVMAnn sym) =>
  sym ->
  VFSImpl sym ->
  FileIdent {- name of this file -} ->
  RegValue sym (VectorType (BVType 8)) {- initial file contents -} ->
  IO (VFSImpl sym)
doAddFile sym files fident bytes = do
  blkId <- nextBlock (vfsImplBlockSource files)
  size <- bvLit sym PtrWidth (fromIntegral $ V.length bytes)
  let mem' = G.allocMem G.GlobalAlloc blkId (Just size) noAlignment G.Mutable "" (vfsMem files)
  z <- bvLit sym PtrWidth 0
  blk <- natLit sym blkId
  let ptr = LLVMPointer blk z
  let fd = FileDescriptor ptr size
  let files' = files { vfsMem = mem', vfsFileNames = Map.insert fident (Some fd) (vfsFileNames files) }
  doWriteFileBytes sym files' ptr bytes

doWriteFileBytes ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack, HasLLVMAnn sym) =>
  sym ->
  VFSImpl sym ->
  LLVMPtr sym wptr ->
  (RegValue sym (VectorType (BVType 8))) ->
  IO (VFSImpl sym)
doWriteFileBytes sym files ptr bytes = do
  let repr = VectorRepr (BVRepr (knownNat @8))
  let store = arrayType (toBytes (V.length bytes)) (bitvectorType (toBytes (8 :: Int)))
  packed <- packMemValue sym store repr bytes
  (mem', p1, p2) <- G.writeMem sym PtrWidth ptr store noAlignment packed (vfsMem files)
  assert sym p1 (AssertFailureSimError "Error in call to writeMem" [])
  assert sym p2 (AssertFailureSimError "Error in call to writeMem" [])
  return $ files { vfsMem = mem' }

doReadFileBytes ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack, HasLLVMAnn sym) =>
  sym ->
  VFSImpl sym ->
  LLVMPtr sym wptr ->
  Bytes {- the number of bytes to read -} ->
  IO (RegValue sym (VectorType (BVType 8)))
doReadFileBytes sym files ptr size = do
  let repr = VectorRepr (BVRepr (knownNat @8))
  let store = arrayType size (bitvectorType (toBytes (8 :: Int)))
  pv <- G.readMem sym PtrWidth ptr store noAlignment (vfsMem files)
  assertSafe sym pv >>= unpackMemValue sym repr

-- | Resolve a file pointer to its underlying descriptor
getFileDescriptor ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack) =>
  sym ->
  VFSImpl sym ->
  LLVMPtr sym wptr ->
  IO (FileDescriptor sym wptr)
getFileDescriptor sym files ptr = do
  let (blkId, _) = llvmPointerView ptr
  case asNat blkId of
    Just n
      | Just (Some fd) <- Map.lookup n (vfsFileBlocks files)
      , PtrWidth <- ptrWidth (filePointer fd)
      -> return fd
    _ -> addFailedAssertion sym $ AssertFailureSimError "getFileDescriptor" []

-- | Resolve a filename as a global pointer to the start of its contents
doResolveFile ::
  (IsSymInterface sym, HasPtrWidth wptr, HasCallStack) =>
  sym ->
  VFSImpl sym ->
  FileIdent ->
  IO (FileDescriptor sym wptr)
doResolveFile sym files fident = do
  case Map.lookup fident (vfsFileNames files) of
    Just (Some fd) | PtrWidth <- ptrWidth (filePointer fd) -> return fd
    _ -> addFailedAssertion sym $ AssertFailureSimError "doResolveFile" []
