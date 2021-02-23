-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.SymIO
-- Description      : Core definitions of the symbolic filesystem model
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.SymIO
  (
    FileSystemType
  , FileHandle
  , FilePointer
  , File
  , FileSystemOps(..)
  , HasFileSystem(..)
  , initFileSystemOps
  , addFileSystemBindings
  , openFile
  , resolveFileIdent
  , readByte
  , writeByte
  , readChunk
  , writeChunk
  , closeFileHandle
  , readFromChunk
  , chunkToArray
  ) where

import           GHC.TypeNats
import           Prelude hiding ( fail )
import           Control.Monad.Trans.State ( StateT, runStateT, evalStateT )
import           Control.Monad.State hiding ( fail )
import           Control.Monad.Fail

import qualified Data.Map as Map
import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Context ( pattern (:>) )
import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.ExecutionTree as CET
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.CFG.Expr as CCE

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Backend
import           Lang.Crucible.Utils.MuxTree
import           Lang.Crucible.Types
import qualified What4.Interface as W4
import           What4.Partial

import           What4.CachedArray as CA
import           Lang.Crucible.SymIO.Types


data FileSystemOps wptr =
  FileSystemOps
    { fsOpenFile :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileType wptr) (FileHandleType wptr)
    , fsCloseFileHandle :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) UnitType
    , fsWriteByte :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType 8) UnitType
    , fsWriteChunk :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> DataChunkType wptr) UnitType
    , fsReadByte :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) (BVType 8)
    , fsReadChunk :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType wptr) (DataChunkType wptr)
    , fsResolveFileIdent :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> FileIdentType) (FileType wptr)
    , fsChunkToArray ::
          CFH.FnHandle (Ctx.EmptyCtx Ctx.::> DataChunkType wptr)
            (SymbolicArrayType (Ctx.EmptyCtx Ctx.::> BaseBVType wptr) (BaseBVType 8))
    , fsReadFromChunk :: CFH.FnHandle (Ctx.EmptyCtx Ctx.::> DataChunkType wptr Ctx.::> BVType wptr) (BVType 8)
    }

callFSOp1 ::
  CCE.IsSyntaxExtension ext =>
  Monad m =>
  FileSystemOps wptr ->
  (FileSystemOps wptr -> CFH.FnHandle (Ctx.EmptyCtx Ctx.::> arg) ret) ->
  CCG.Expr ext s arg ->
  CCG.Generator ext s t ret' m (CCG.Expr ext s ret)
callFSOp1 ops f arg = CCG.call (CCG.App (CCE.HandleLit (f ops))) (Ctx.empty Ctx.:> arg)

callFSOp2 ::
  CCE.IsSyntaxExtension ext =>
  Monad m =>
  FileSystemOps wptr ->
  (FileSystemOps wptr -> CFH.FnHandle (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2) ret) ->
  CCG.Expr ext s arg1 ->
  CCG.Expr ext s arg2 ->
  CCG.Generator ext s t ret' m (CCG.Expr ext s ret)
callFSOp2 ops f arg1 arg2 = CCG.call (CCG.App (CCE.HandleLit (f ops))) (Ctx.empty Ctx.:> arg1 Ctx.:> arg2)


class HasFileSystem wptr s | s -> wptr where
  getFileSystemOps :: s -> FileSystemOps wptr


openFile ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileType wptr) ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (FileHandleType wptr))
openFile arg = do
  st <- get
  callFSOp1 (getFileSystemOps st) fsOpenFile arg


closeFileHandle ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileHandleType wptr) ->
  CCG.Generator ext s t ret m ()
closeFileHandle arg = do
  st <- get
  _ <- callFSOp1 (getFileSystemOps st) fsCloseFileHandle arg
  return ()

writeByte ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileHandleType wptr) ->
  CCG.Expr ext s (BVType 8) ->
  CCG.Generator ext s t ret m ()
writeByte fhdl byte = do
  st <- get
  _ <- callFSOp2 (getFileSystemOps st) fsWriteByte fhdl byte
  return ()

writeChunk ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileHandleType wptr) ->
  CCG.Expr ext s (DataChunkType wptr) ->
  CCG.Generator ext s t ret m ()
writeChunk fhdl chunk = do
  st <- get
  _ <- callFSOp2 (getFileSystemOps st) fsWriteChunk fhdl chunk
  return ()

readByte ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileHandleType wptr) ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (BVType 8))
readByte fhdl = do
  st <- get
  callFSOp1 (getFileSystemOps st) fsReadByte fhdl

readChunk ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (FileHandleType wptr) ->
  CCG.Expr ext s (BVType wptr) ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (DataChunkType wptr))
readChunk fhdl sz = do
  st <- get
  callFSOp2 (getFileSystemOps st) fsReadChunk fhdl sz

readFromChunk ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (DataChunkType wptr) ->
  CCG.Expr ext s (BVType wptr) ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (BVType 8))
readFromChunk chunk idx = do
  st <- get
  callFSOp2 (getFileSystemOps st) fsReadFromChunk chunk idx

chunkToArray ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s (DataChunkType wptr) ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (SymbolicArrayType (Ctx.EmptyCtx Ctx.::> BaseBVType wptr) (BaseBVType 8)))
chunkToArray chunk = do
  st <- get
  callFSOp1 (getFileSystemOps st) fsChunkToArray chunk

resolveFileIdent ::
  HasFileSystem wptr (t s) =>
  Monad m =>
  CCE.IsSyntaxExtension ext =>
  CCG.Expr ext s FileIdentType ->
  CCG.Generator ext s t ret m (CCG.Expr ext s (FileType wptr))
resolveFileIdent ident = do
  st <- get
  callFSOp1 (getFileSystemOps st) fsResolveFileIdent ident

initFileSystemOps ::
  (KnownNat wptr, 1 <= wptr) =>
  CFH.HandleAllocator ->
  IO (FileSystemOps wptr)
initFileSystemOps halloc =
  FileSystemOps
     <$> CFH.mkHandle halloc "openFile"
     <*> CFH.mkHandle halloc "closeFileHandle"
     <*> CFH.mkHandle halloc "writeByte"
     <*> CFH.mkHandle halloc "writeChunk"
     <*> CFH.mkHandle halloc "readByte"
     <*> CFH.mkHandle halloc "readChunk"
     <*> CFH.mkHandle halloc "resolveFileIdent"
     <*> CFH.mkHandle halloc "chunkToArray"
     <*> CFH.mkHandle halloc "readFromChunk"

addFileSystemBindings ::
  (KnownNat wptr, 1 <= wptr) =>
  IsSymInterface sym =>
  -- | Handles to bind filesystem operations to
  FileSystemOps wptr ->
  -- | Variable tracking the filesystem state
  GlobalVar (FileSystemType wptr) ->
  CET.FunctionBindings p sym ext ->
  CET.FunctionBindings p sym ext
addFileSystemBindings fops fs binds =
  CFH.insertHandleMap (fsOpenFile fops)
    (CET.UseOverride $ C.mkOverride "openFile" (openFileOv fs))
  $ CFH.insertHandleMap (fsCloseFileHandle fops)
    (CET.UseOverride $ C.mkOverride "closeFileHandle" (closeFileHandleOv fs))  
  $ CFH.insertHandleMap (fsWriteByte fops)
    (CET.UseOverride $ C.mkOverride "writeByte" (writeByteOv fs))    
  $ CFH.insertHandleMap (fsWriteChunk fops)
    (CET.UseOverride $ C.mkOverride "writeChunk" (writeChunkOv fs))
  $ CFH.insertHandleMap (fsReadByte fops)
    (CET.UseOverride $ C.mkOverride "readByte" (readByteOv fs))
  $ CFH.insertHandleMap (fsReadChunk fops)
    (CET.UseOverride $ C.mkOverride "readChunk" (readChunkOv fs))
  $ CFH.insertHandleMap (fsResolveFileIdent fops)
    (CET.UseOverride $ C.mkOverride "resolveFileIdent" (resolveFileIdentOv fs))
  $ CFH.insertHandleMap (fsChunkToArray fops)
    (CET.UseOverride $ C.mkOverride "chunkToArray" chunkToArrayOv)
  $ CFH.insertHandleMap (fsReadFromChunk fops)
    (CET.UseOverride $ C.mkOverride "readFromChunk" readFromChunkOv)
  binds
  
---------------------------------------
-- Interface

-- | Open a file by creating a fresh file handle to its contents
openFileOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileType wptr) ret (FileHandle sym wptr)
openFileOv fvar = do
  rm <- C.getOverrideArgs
  let file = regVal rm lastReg
  fs <- C.readGlobal fvar
  sym <- C.getSymInterface
  let repr = fsPtrSize fs
  zero <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 0)
  ref <- toMuxTree sym <$> C.newEmptyRef (MaybeRepr (FilePointerRepr repr))
  evalFileM fs $ setHandle ref (FilePointer file zero)
  return ref

-- | Close a file by invalidating its file handle
closeFileHandleOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret ()
closeFileHandleOv fvar = do
  rm <- C.getOverrideArgs
  let fhdl = regVal rm lastReg
  fs <- C.readGlobal fvar
  sym <- C.getSymInterface
  let repr = fsPtrSize fs
  C.writeMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhdl (maybePartExpr sym Nothing)

data AsOrd f tp where
  AsOrd :: OrdF f => { _unAsOrd :: f tp } -> AsOrd f tp

instance Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) = case compareF a b of
    EQF -> True
    _ -> False

instance Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

-- | Resolve a file identifier to a 'File'
resolveFileIdentOv ::
  IsSymInterface sym =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileIdentType) ret (File sym wptr)
resolveFileIdentOv fsVar = do
  rm <- C.getOverrideArgs
  let ident = regVal rm lastReg
  sym <- C.getSymInterface
  fs <- C.readGlobal fsVar
  let missingErr = AssertFailureSimError "missing file" "resolveFileIdent attempted to lookup a file handle that does not exist"
  case W4.asString ident of
    Just (W4.UnicodeLiteral i') -> case Map.lookup i' (fsFileNames fs) of
      Just n -> liftIO $ readPartExpr sym n missingErr
      Nothing -> liftIO $  addFailedAssertion sym missingErr
                    
    Nothing -> liftIO $ addFailedAssertion sym $
      Unsupported "Symbolic string in lookupStringMapEntry"

writeByteOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType 8) ret ()
writeByteOv fsVar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> byte) <- C.getOverrideArgs
  runFileM fsVar $ do
    ptr <- getHandle (regValue fhdl)
    writeBytePointer ptr (regValue byte)
    nextPtr <- nextPointer ptr
    setHandle (regValue fhdl) nextPtr

writeChunkOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> DataChunkType wptr) ret ()
writeChunkOv fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> chunk) <- C.getOverrideArgs
  runFileM fvar $ do
    ptr <- getHandle (regValue fhdl)
    writeChunkPointer ptr (regValue chunk)
    ptr' <- addToPointer (chunkSize (regValue chunk)) ptr
    setHandle (regValue fhdl) ptr'

readByteOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret (W4.SymBV sym 8)
readByteOv fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl) <- C.getOverrideArgs
  runFileM fvar $ do
    ptr <- getHandle (regValue fhdl)
    v <- readBytePointer ptr
    nextPtr <- nextPointer ptr
    setHandle (regValue fhdl) nextPtr
    return v

readChunkOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType wptr) ret (DataChunk sym wptr) 
readChunkOv fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> sz) <- C.getOverrideArgs
  runFileM fvar $ do
    ptr <- getHandle (regValue fhdl)
    chunk <- readChunkPointer ptr (regValue sz)
    ptr' <- addToPointer (regValue sz) ptr
    setHandle (regValue fhdl) ptr'
    return chunk

readFromChunkOv ::
  (IsSymInterface sym, 1 <= wptr) =>
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> DataChunkType wptr Ctx.::> BVType wptr) ret (W4.SymBV sym 8)
readFromChunkOv = do
  RegMap (Ctx.Empty Ctx.:> chunk Ctx.:> idx) <- C.getOverrideArgs
  sym <- C.getSymInterface
  inBounds <- liftIO $ W4.bvUlt sym (regValue idx) (chunkSize (regValue chunk))
  let err = AssertFailureSimError "Out of bounds read from data chunk" "readFromChunkOv attempted read beyond the size of the chunk."
  liftIO $ assert sym inBounds err
  liftIO $ W4.arrayLookup sym (chunkArray (regValue chunk)) (Ctx.empty Ctx.:> (regValue idx))

chunkToArrayOv ::
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> DataChunkType wptr) ret (W4.SymArray sym (EmptyCtx ::> BaseBVType wptr) (BaseBVType 8)) 
chunkToArrayOv = do
  RegMap (Ctx.Empty Ctx.:> chunk) <- C.getOverrideArgs
  return $ chunkArray $ regValue chunk

-----------------------------------------
-- Internal operations


newtype FileM_ p arch r args ret sym wptr a = FileM { _unFM :: StateT (FileSystem sym wptr) (C.OverrideSim p sym arch r args ret) a }
  deriving
     ( Applicative
     , Functor
     , Monad
     , MonadIO
     , MonadState (FileSystem sym wptr)
     )

instance MonadFail (FileM_ p arch r args ret sym wpt) where
  fail str = useConstraints $ do
    sym <- getSym
    liftIO $ addFailedAssertion sym $ GenericSimError $ str

type FileM p arch r args ret sym wptr a =
  (IsSymInterface sym, 1 <= wptr) =>
  FileM_ p arch r args ret sym wptr a

useConstraints ::
  FileM p arch r args ret sym wptr a ->
  FileM_ p arch r args ret sym wptr a
useConstraints f = do
  st <- get
  fsConstraints st $ f

liftOV ::
  C.OverrideSim p sym arch r args ret a ->
  FileM p arch r args ret sym wptr a
liftOV f = FileM $ lift f

runFileM ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileM_ p arch r args ret sym wptr a ->
  C.OverrideSim p sym arch r args ret a
runFileM fvar (FileM f) = do
  fs <- C.readGlobal fvar
  (a, fs') <- runStateT f fs
  C.writeGlobal fvar fs'
  return a

evalFileM ::
  (IsSymInterface sym, 1 <= wptr) =>
  FileSystem sym wptr ->
  FileM p arch r args ret sym wptr a ->
  C.OverrideSim p sym arch r args ret a
evalFileM fs (FileM f) = evalStateT f fs

getSym :: FileM p arch r args ret sym wptr sym
getSym = liftOV $ C.getSymInterface

getPtrSz :: FileM p arch r args ret sym wptr (NatRepr wptr)
getPtrSz = gets fsPtrSize

-- | Retrieve the pointer that the handle is currently at
getHandle ::
  FileHandle sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr)
getHandle fhandle = do
  sym <- getSym
  repr <- getPtrSz 
  liftOV (C.readMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhandle) >>= \case
    PE p v -> do
      liftIO $ assert sym p $ GenericSimError $ "Read from closed file handle."
      return v
    Unassigned -> fail "Read from closed file handle."

setHandle ::
  FileHandle sym wptr ->
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr ()
setHandle fhandle ptr = do
  sym <- getSym
  repr <- getPtrSz 
  let ptr' = justPartExpr sym ptr
  liftOV $ C.writeMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhandle ptr'

nextPointer ::
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr)
nextPointer ptr = do
  sym <- getSym
  repr <- getPtrSz
  one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 1)
  addToPointer one ptr

addToPointer ::
  W4.SymBV sym wptr ->
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr)
addToPointer i (FilePointer n off) = do
  sym <- getSym
  off' <- liftIO $ W4.bvAdd sym off i
  return $ FilePointer n off'


writeBytePointer ::
  FilePointer sym wptr ->
  W4.SymBV sym 8 ->
  FileM p arch r args ret sym wptr ()
writeBytePointer fptr bv = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- gets fsSymData
  dataArr' <- liftIO $ CA.writeSingle sym idx bv dataArr  
  modify $ \fs -> fs { fsSymData = dataArr' }

readBytePointer ::
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym 8)
readBytePointer fptr = do
  sym <- getSym
  let idx = filePointerIdx fptr
  dataArr <- gets fsSymData
  liftIO $ CA.readSingle sym idx dataArr


writeChunkPointer ::
  FilePointer sym wptr ->
  DataChunk sym wptr ->
  FileM p arch r args ret sym wptr ()
writeChunkPointer fptr chunk = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- gets fsSymData
  dataArr' <- liftIO $ CA.writeRange sym idx (chunkSize chunk) (chunkArray chunk)  dataArr  
  modify $ \fs -> fs { fsSymData = dataArr' }


readChunkPointer ::
  FilePointer sym wptr ->
  -- | Number of bytes to read
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr (DataChunk sym wptr)
readChunkPointer fptr sz = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- gets fsSymData
  rawChunk <- liftIO $ CA.readRange sym idx sz dataArr
  return $ DataChunk rawChunk sz 

filePointerIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  FileSystemIndex sym wptr
filePointerIdx (FilePointer (File _ n) off) = Ctx.empty :> n :> off

  
_asConcreteIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  Maybe (Integer, BV.BV wptr)
_asConcreteIdx fptr = do
  ConcreteFilePointer (ConcreteFile _ cn) coff <- asConcretePointer fptr
  return $ (cn, coff)

asConcretePointer ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  Maybe (ConcreteFilePointer wptr)
asConcretePointer (FilePointer file off) = do
  cfile <- asConcreteFile file
  coff <- W4.asBV off
  return $ ConcreteFilePointer cfile coff

asConcreteFile ::
  IsSymInterface sym =>
  File sym w ->
  Maybe (ConcreteFile w)
asConcreteFile (File w n) = do
  cn <- W4.asInteger n
  return $ ConcreteFile w cn
