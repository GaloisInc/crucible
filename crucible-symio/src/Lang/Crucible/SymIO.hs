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
  -- * Filesystem types
  -- $filetypes
    FileSystemType
  , FileHandle
  , FileHandleType
  , FilePointer
  , FilePointerType
  -- * Filesystem operations
  -- $fileops
  , openFile
  , openFile'
  , readByte
  , readByte'
  , writeByte
  , writeByte'
  , readChunk
  , readChunk'
  , writeChunk
  , writeChunk'
  , closeFileHandle
  , closeFileHandle'
  , readFromChunk
  , readFromChunk'
  , chunkToArray
  , chunkToArray'
  , arrayToChunk
  , arrayToChunk'
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

import           Lang.Crucible.Backend
import           Lang.Crucible.Utils.MuxTree
import qualified What4.Interface as W4
import           What4.Partial

import           What4.CachedArray as CA
import           Lang.Crucible.SymIO.Types

---------------------------------------
-- Interface

-- $fileops
-- Top-level overrides for filesystem operations. Each operation defines two variants:
-- a "prime" variant which implements the filesystem operation in any 'C.OverrideSim'
-- context, and a non-prime variant which wraps these as crucible-level overrides,
-- represented in the 'args' type parameter.

-- $filetypes
-- The associated crucible types used to interact with the filesystem.

-- | Close a file by invalidating its file handle
closeFileHandle ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret ()
closeFileHandle fvar = do
  rm <- C.getOverrideArgs
  let fhdl = regVal rm lastReg
  closeFileHandle' fvar fhdl

closeFileHandle' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret ()
closeFileHandle' fvar fhdl = do
  fs <- C.readGlobal fvar
  sym <- C.getSymInterface
  let repr = fsPtrSize fs
  C.writeMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhdl (maybePartExpr sym Nothing)

-- | Open a file by resolving a 'FileIdent' into a 'File' and then allocating a fresh
-- 'FileHandle' pointing to the start of its contents.
openFile ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileIdentType) ret (FileHandle sym wptr)
openFile fsVar = do
  rm <- C.getOverrideArgs
  let ident = regVal rm lastReg
  openFile' fsVar ident

openFile' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent sym ->
  C.OverrideSim p sym arch r args ret (FileHandle sym wptr)
openFile' fsVar ident = runFileM fsVar $ do
  file <- resolveFileIdent ident
  openResolvedFile file

-- | Write a single byte to the given 'FileHandle' and increment it
writeByte ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType 8) ret ()
writeByte fsVar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> byte) <- C.getOverrideArgs
  writeByte' fsVar (regValue fhdl) (regValue byte)

writeByte' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym 8 ->
  C.OverrideSim p sym arch r args ret ()
writeByte' fsVar fhdl byte = do
  runFileM fsVar $ do
    ptr <- getHandle fhdl
    writeBytePointer ptr byte
    nextPtr <- nextPointer ptr
    setHandle fhdl nextPtr

-- | Write a 'DataChunk' to the given 'FileHandle' and increment it to the end of
-- the written data.
writeChunk ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> DataChunkType wptr) ret ()
writeChunk fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> chunk) <- C.getOverrideArgs
  writeChunk' fvar (regValue fhdl) (regValue chunk)

writeChunk' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  DataChunk sym wptr ->
  C.OverrideSim p sym arch r args ret ()
writeChunk' fvar fhdl chunk = runFileM fvar $ do
  ptr <- getHandle fhdl
  writeChunkPointer ptr chunk 
  ptr' <- addToPointer (chunkSize chunk) ptr
  setHandle fhdl ptr'

-- | Read a byte from a given 'FileHandle' and increment it.
readByte ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret (W4.SymBV sym 8)
readByte fvar = liftArgs1 (readByte' fvar)

readByte' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret (W4.SymBV sym 8)
readByte' fvar fhdl = runFileM fvar $ do
  ptr <- getHandle fhdl
  v <- readBytePointer ptr
  nextPtr <- nextPointer ptr
  setHandle fhdl nextPtr
  return v

-- | Read a 'DataChunk' from a given 'FileHandle' of the given size, and increment the
-- handle by the size.
readChunk ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType wptr) ret (DataChunk sym wptr) 
readChunk fvar = liftArgs2 (readChunk' fvar)

readChunk' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (DataChunk sym wptr) 
readChunk' fvar fhdl sz = runFileM fvar $ do
  ptr <- getHandle fhdl
  chunk <- readChunkPointer ptr sz
  ptr' <- addToPointer sz ptr
  setHandle fhdl ptr'
  return chunk

-- | Read from a 'DataChunk'
readFromChunk ::
  (IsSymInterface sym, 1 <= wptr) =>
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> DataChunkType wptr Ctx.::> BVType wptr) ret (W4.SymBV sym 8)
readFromChunk = liftArgs2 readFromChunk'

readFromChunk' ::
  (IsSymInterface sym, 1 <= wptr) =>
  DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (W4.SymBV sym 8)
readFromChunk' chunk idx = do
  sym <- C.getSymInterface
  inBounds <- liftIO $ W4.bvUlt sym idx (chunkSize chunk)
  let err = AssertFailureSimError "Out of bounds read from data chunk" "readFromChunkOv attempted read beyond the size of the chunk."
  liftIO $ assert sym inBounds err
  liftIO $ W4.arrayLookup sym (chunkArray chunk) (Ctx.empty Ctx.:> idx)

-- | Convert a 'DataChunk' into an array
chunkToArray ::
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> DataChunkType wptr) ret (W4.SymArray sym (EmptyCtx ::> BaseBVType wptr) (BaseBVType 8)) 
chunkToArray = liftArgs1 chunkToArray'

chunkToArray' ::
  DataChunk sym wptr ->
  C.OverrideSim p sym arch r args ret (W4.SymArray sym (EmptyCtx ::> BaseBVType wptr) (BaseBVType 8))
chunkToArray' chunk = return $ chunkArray chunk

-- | Convert an array into a 'DataChunk' of the given size.
arrayToChunk ::
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> (SymbolicArrayType (EmptyCtx ::> BaseBVType wptr) (BaseBVType 8)) Ctx.::> BVType wptr) ret (DataChunk sym wptr)
arrayToChunk = liftArgs2 arrayToChunk'

arrayToChunk' ::
  W4.SymArray sym (EmptyCtx ::> BaseBVType wptr) (BaseBVType 8) ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (DataChunk sym wptr)
arrayToChunk' array sz = return $ DataChunk array sz

liftArgs1 ::
  (forall args. RegValue sym tp -> C.OverrideSim p sym arch r args ret a) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> tp) ret a
liftArgs1 f = do
  RegMap (Ctx.Empty Ctx.:> a) <- C.getOverrideArgs
  f (regValue a)

liftArgs2 ::
  (forall args. RegValue sym tp1 ->  RegValue sym tp2 -> C.OverrideSim p sym arch r args ret a) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> tp1 Ctx.::> tp2) ret a
liftArgs2 f = do
  RegMap (Ctx.Empty Ctx.:> a1 Ctx.:> a2) <- C.getOverrideArgs
  f (regValue a1) (regValue a2)

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


-- | Resolve a file identifier to a 'File'
resolveFileIdent ::
  FileIdent sym ->
  FileM p arch r args ret sym wptr (File sym wptr)
resolveFileIdent ident = do  
  sym <- getSym
  m <- gets fsFileNames
  let missingErr = AssertFailureSimError "missing file" "resolveFileIdent attempted to lookup a file handle that does not exist"
  case W4.asString ident of
    Just (W4.UnicodeLiteral i') -> case Map.lookup i' m of
      Just n -> liftIO $ readPartExpr sym n missingErr
      Nothing -> liftIO $  addFailedAssertion sym missingErr
    Nothing -> liftIO $ addFailedAssertion sym $
      Unsupported "Symbolic string in lookupStringMapEntry"

openResolvedFile ::
  File sym wptr ->
  FileM p arch r args ret sym wptr (FileHandle sym wptr)
openResolvedFile file = do
  sym <- getSym
  repr <- getPtrSz
  zero <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 0)
  ref <- toMuxTree sym <$> (liftOV $ C.newEmptyRef (MaybeRepr (FilePointerRepr repr)))
  setHandle ref (FilePointer file zero)
  return ref

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
filePointerIdx (FilePointer (File _ n) off) = Ctx.empty :> off :> n
