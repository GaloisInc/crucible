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
  , DataChunk
  -- * Filesystem operations
  -- $fileops
  , openFile
  , openFile'
  , readByte
  , readByte'
  , writeByte
  , writeByte'
  , readArray
  , readArray'
  , readToArray
  , readToArray'
  , writeArray
  , writeArray'
  , closeFileHandle
  , closeFileHandle'
  , isHandleOpen
  , isHandleOpen'
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
import qualified Lang.Crucible.FunctionHandle as CFH

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
    sym <- getSym
    repr <- getPtrSz
    one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 1)
    incHandleWrite fhdl one



-- | Write an array to the given 'FileHandle' and increment it to the end of
-- the written data.
writeArray ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> DataChunkType wptr Ctx.::> BVType wptr) ret ()
writeArray fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> chunk Ctx.:> sz) <- C.getOverrideArgs
  writeArray' fvar (regValue fhdl) (regValue chunk) (regValue sz)

writeArray' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret ()
writeArray' fvar fhdl chunk sz = runFileM fvar $ do
  ptr <- getHandle fhdl
  writeChunkPointer ptr chunk sz
  incHandleWrite fhdl sz

-- | Read a byte from a given 'FileHandle' and increment it.
readByte ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret (PartExpr (W4.Pred sym) (W4.SymBV sym 8))
readByte fvar = liftArgs1 (readByte' fvar)

readByte' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret (PartExpr (W4.Pred sym) (W4.SymBV sym 8))
readByte' fvar fhdl = runFileM fvar $ do
  ptr <- getHandle fhdl
  v <- readBytePointer ptr
  sym <- getSym
  repr <- getPtrSz
  one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 1)
  readBytes <- incHandleRead fhdl one
  valid <- liftIO $ W4.isEq sym one readBytes
  return $ mkPE valid v

-- | Read an array from a given 'FileHandle' of the given size, and increment the
-- handle by the size. Returns a struct containing the array contents, and the number
-- of bytes read.
readArray ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType wptr) ret (SizedDataChunk sym wptr)
readArray fvar = do
  (chunk, sz) <- liftArgs2 (readArray' fvar)
  sym <- C.getSymInterface
  liftIO $ W4.mkStruct sym (Ctx.empty Ctx.:> chunk Ctx.:> sz)

readArray' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (DataChunk sym wptr, W4.SymBV sym wptr)
readArray' fvar fhdl sz = runFileM fvar $ do
  ptr <- getHandle fhdl
  chunk <- readChunkPointer ptr sz
  readSz <- incHandleRead fhdl sz
  return (chunk, readSz)


-- | Read an array from a given 'FileHandle' of the given size, and increment the
-- handle by the size. Assigns the resulting array to the given reference, and returns
-- the resulting size.
readToArray ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr Ctx.::> BVType wptr Ctx.::> ReferenceType (DataChunkType wptr)) ret (W4.SymBV sym wptr)
readToArray fvar = do
  RegMap (Ctx.Empty Ctx.:> fhdl Ctx.:> sz Ctx.:> cell) <- C.getOverrideArgs
  (chunk, readSz) <- readArray' fvar (regValue fhdl) (regValue sz)
  let ReferenceRepr repr = regType cell
  C.writeMuxTreeRef repr (regValue cell) chunk
  return readSz

readToArray' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  CFH.RefCell (DataChunkType wptr) ->
  C.OverrideSim p sym arch args r ret (W4.SymBV sym wptr)
readToArray' fvar fhdl sz cell = do
  (chunk, readSz) <- readArray' fvar fhdl sz
  C.writeRef cell chunk
  return readSz

isHandleOpen ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch r (Ctx.EmptyCtx Ctx.::> FileHandleType wptr) ret (W4.Pred sym)
isHandleOpen fvar = liftArgs1 (isHandleOpen' fvar)


isHandleOpen' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch args r ret (W4.Pred sym)
isHandleOpen' fvar fhdl = runFileM fvar $ do
  sym <- getSym
  repr <- getPtrSz
  liftOV (C.readMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhdl) >>= \case
    PE p _ -> return p
    Unassigned -> return (W4.falsePred sym)

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

getFileSize :: FileHandle sym wptr -> FileM p arch r args ret sym wptr (W4.SymBV sym wptr)
getFileSize fhdl = do
  (FilePointer (File _ fileid) _, _) <- readHandle fhdl
  szArray <- gets fsFileSizes
  sym <- getSym
  liftIO $ W4.arrayLookup sym szArray (Ctx.empty Ctx.:> fileid)

readHandle ::
  FileHandle sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr, W4.Pred sym)
readHandle fhandle = do
  sym <- getSym
  repr <- getPtrSz
  liftOV (C.readMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhandle) >>= \case
    PE p v -> return (v, p)
    Unassigned -> liftIO $ addFailedAssertion sym $ AssertFailureSimError "Read from closed file handle." "readHandle: Unassigned file handle."


-- | Retrieve the pointer that the handle is currently at
getHandle ::
  FileHandle sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr)
getHandle fhandle = do
  sym <- getSym
  (v, p) <- readHandle fhandle
  liftIO $ assert sym p $ AssertFailureSimError "Read from closed file handle." "getHandle: File handle assertion failed."
  return v


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
  setHandle ref (FilePointer file zero) (W4.truePred sym)
  return ref

setHandle ::
  FileHandle sym wptr ->
  FilePointer sym wptr ->
  W4.Pred sym ->
  FileM p arch r args ret sym wptr ()
setHandle fhandle ptr valid = do
  repr <- getPtrSz 
  let ptr' = mkPE valid ptr
  liftOV $ C.writeMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhandle ptr'

-- | True if the read remains in bounds, if false, the result is the number of
-- bytes that were overrun
bytesOverrun ::
  FileHandle sym wptr ->
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (W4.Pred sym, W4.SymBV sym wptr)
bytesOverrun fhandle (FilePointer _ ptrOff) = do
  sz <- getFileSize fhandle
  sym <- getSym
  inbounds <- liftIO $ W4.bvUle sym ptrOff sz
  overrun <- liftIO $ W4.bvSub sym ptrOff sz
  return $ (inbounds, overrun)

-- | Increment the filehandle by the given amount, returning the
-- number of bytes that were actually incremented. This is less than
-- the number requested if the read is over the end of the file.
incHandleRead ::
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym wptr)
incHandleRead fhandle sz = do
  sym <- getSym
  (basePtr, _) <- readHandle fhandle
  ptr <- addToPointer sz basePtr
  (inbounds, overrun) <- bytesOverrun fhandle ptr
  setHandle fhandle ptr inbounds
  off <- liftIO $ W4.bvSub sym sz overrun
  liftIO $ W4.baseTypeIte sym inbounds sz off

incHandleWrite ::
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr ()
incHandleWrite fhandle sz = do
  (basePtr, p) <- readHandle fhandle
  ptr <- addToPointer sz basePtr
  setHandle fhandle ptr p
  updateFileSize fhandle

updateFileSize ::
  FileHandle sym wptr ->
  FileM p arch r args ret sym wptr ()
updateFileSize fhdl = do
  (FilePointer (File _ fileid) off, _) <- readHandle fhdl
  szArray <- gets fsFileSizes
  sym <- getSym
  oldsz <- liftIO $ W4.arrayLookup sym szArray (Ctx.empty Ctx.:> fileid)
  szArray' <- liftIO $ W4.arrayUpdate sym szArray (Ctx.empty Ctx.:> fileid) off
  outbounds <- liftIO $ W4.bvUlt sym oldsz off
  szArray'' <- liftIO $ W4.baseTypeIte sym outbounds szArray' szArray
  modify $ \arr -> arr { fsFileSizes = szArray'' }

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
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr ()
writeChunkPointer fptr chunk sz = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- gets fsSymData
  dataArr' <- liftIO $ CA.writeRange sym idx sz chunk dataArr
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
  liftIO $ CA.readRange sym idx sz dataArr

filePointerIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  FileSystemIndex sym wptr
filePointerIdx (FilePointer (File _ n) off) = Ctx.empty :> off :> n
