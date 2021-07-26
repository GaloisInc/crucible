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
  -- * Setup
    FDTarget(..)
  , InitialFileSystemContents(..)
  -- * Filesystem types
  -- $filetypes
  , FileSystemType
  , FileHandle
  , FileHandleType
  , FilePointer
  , FilePointerType
  , FileIdent
  , DataChunk
  , CA.mkArrayChunk
  -- ** Reprs
  , pattern FileRepr
  , pattern FileSystemRepr
  -- * Filesystem operations
  -- $fileops
  , initFS
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
  , isHandleOpen
  , invalidFileHandle
  , symIOIntrinsicTypes
  , CA.chunkToArray
  , CA.arrayToChunk
  -- * Error conditions
  , FileIdentError(..)
  , FileHandleError(..)
  ) where

import           GHC.TypeNats

import           Control.Arrow ( first )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.State as CMS
import qualified Control.Monad.Trans as CMT

import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Traversable as DT
import qualified Data.Map as Map
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.Simulator.RegMap ( RegMap(..), emptyRegMap, RegEntry(..), unconsReg, regMapSize )
import           Lang.Crucible.Simulator.SimError
import qualified Lang.Crucible.Simulator.OverrideSim as C

import           Lang.Crucible.Backend
import           Lang.Crucible.Utils.MuxTree
import qualified What4.Interface as W4
import qualified What4.Concrete as W4C
import           What4.Partial

import qualified What4.CachedArray as CA
import           Lang.Crucible.SymIO.Types

---------------------------------------
-- Interface

data FDTarget = FileTarget FilePath
              | StdinTarget
              deriving (Eq, Ord, Show)

-- | Convert an 'FDTarget' to 'T.Text'
--
-- We need to do this because filenames are stored in a Crucible StringMap, so
-- we can't use our custom ADT.  We have to do some custom namespacing here to
-- avoid collisions between named files and our special files.
--
-- We will adopt the convention that /all/ actual files will have absolute paths
-- in the symbolic filesystem.  The special files will have names that are not
-- valid absolute paths.
--
-- FIXME: Add some validation somewhere so that we actually enforce the absolute
-- path property
fdTargetToText :: FDTarget -> Text.Text
fdTargetToText t =
  case t of
    FileTarget f -> Text.pack f
    StdinTarget -> Text.pack "<stdin>"

data InitialFileSystemContents sym =
  InitialFileSystemContents { concreteFiles :: Map.Map FDTarget BS.ByteString
                            , symbolicFiles :: Map.Map FDTarget [W4.SymBV sym 8]
                            }

-- $fileops
-- Top-level overrides for filesystem operations.

-- $filetypes
-- The associated crucible types used to interact with the filesystem.

-- | Create an initial 'FileSystem' based on files with initial symbolic and
-- concrete contents
initFS
  :: forall sym wptr
   .(1 <= wptr, IsSymInterface sym)
  => sym
  -- ^ The symbolic backend
  -> NatRepr wptr
  -- ^ A type-level representative of the pointer width
  -> InitialFileSystemContents sym
  -- ^ The initial contents of the filesystem
  -> IO (FileSystem sym wptr)
initFS sym ptrSize initContents = do
  let symContents = Map.toList (symbolicFiles initContents)
  let concContents = Map.toList (concreteFiles initContents)
  symContents' <- DT.forM concContents $ \(name, bytes) -> do
    bytes' <- bytesToSym bytes
    return (name, bytes')
  let
    contentsIdx = zip [0..] (symContents ++ symContents')
    flatContents =
      concat $ map (\(fileIdx, (_, bytes)) ->
        map (\(offset, byte) -> (fileIdx, offset, byte)) (zip [0..] bytes))
        contentsIdx

  initArray <- CA.initArrayConcrete sym (W4.BaseBVRepr (knownNat @8))
    (map mkFileEntry flatContents)

  sizes <- DT.forM contentsIdx $ \(fileIdx, (_, bytes)) -> do
    size_bv <- W4.bvLit sym ptrSize (BV.mkBV ptrSize (fromIntegral (length bytes)))
    return $ (Ctx.empty :> W4C.ConcreteInteger fileIdx, size_bv)

  sizes_arr <- CA.initArrayConcrete sym (W4.BaseBVRepr ptrSize) sizes

  names <- DT.forM contentsIdx $ \(fileIdx, (name, _)) -> do
    fileIdx_int <- W4.intLit sym fileIdx
    return $ (name, justPartExpr sym (File ptrSize fileIdx_int))

  return $ FileSystem
    { fsPtrSize = ptrSize
    , fsFileNames = Map.fromList (fmap (first fdTargetToText) names)
    , fsFileSizes = sizes_arr
    , fsSymData = initArray
    , fsConstraints = id
    }

  where
    bytesToSym :: BS.ByteString -> IO [W4.SymBV sym 8]
    bytesToSym bs = mapM (\w -> W4.bvLit sym (knownNat @8) (BV.word8 w)) (BS.unpack bs)

    mkFileEntry ::
      -- | file identifier,  offset into file, byte value
      (Integer, Integer, W4.SymBV sym 8) ->
      (Ctx.Assignment W4C.ConcreteVal (EmptyCtx ::> BaseBVType wptr ::> BaseIntegerType),
       W4.SymBV sym 8)
    mkFileEntry (fileIdent, offset, byte) =
      (Ctx.empty :> W4C.ConcreteBV ptrSize (BV.mkBV ptrSize offset) :> W4C.ConcreteInteger fileIdent, byte)

-- | Close a file by invalidating its file handle

closeFileHandle ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  (forall args'. Maybe FileHandleError -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
closeFileHandle fvar fhdl cont = runFileMHandleCont fvar fhdl emptyRegMap (\a -> cont (eitherToMaybeL a)) $ \_ fhdl' -> do
  sz <- getPtrSz
  sym <- getSym
  liftOV $ C.writeMuxTreeRef (MaybeRepr (FilePointerRepr sz)) fhdl' (maybePartExpr sym Nothing)


-- | Partial version of 'closeFileHandle' that asserts success.
closeFileHandle' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret ()
closeFileHandle' fvar fhdl = closeFileHandle fvar fhdl $ \merr ->
  case merr of
    Nothing -> return ()
    Just FileHandleClosed -> do
      sym <- C.getSymInterface
      liftIO $ addFailedAssertion sym $ AssertFailureSimError "Attempted to close already closed file handle." "closeFileHandle': Unassigned file handle."

eitherToMaybeL :: Either a b -> Maybe a
eitherToMaybeL (Left a) = Just a
eitherToMaybeL _ = Nothing

-- | Open a file by resolving a 'FileIdent' into a 'File' and then allocating a fresh
-- 'FileHandle' pointing to the start of its contents.
openFile ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent sym ->
  (forall args'. Either FileIdentError (FileHandle sym wptr) -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
openFile fsVar ident cont = runFileMIdentCont fsVar ident cont $ \ident' -> do
  file <- resolveFileIdent ident'
  openResolvedFile file

-- | Partial version of 'openFile' that asserts success.
openFile' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent sym ->
  C.OverrideSim p sym arch r args ret (FileHandle sym wptr)
openFile' fsVar ident = openFile fsVar ident $ \case
  Left FileNotFound -> do
      sym <- C.getSymInterface
      liftIO $ addFailedAssertion sym $ AssertFailureSimError "Could not open file." ("openFile': Invalid file identifier: " ++ show (W4.printSymExpr ident))
  Right fhdl -> return fhdl

-- | Write a single byte to the given 'FileHandle' and increment it
writeByte ::
  forall p sym arch r args ret wptr a.
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym 8 ->
  (forall args'. Maybe FileHandleError -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
writeByte fsVar fhdl byte cont = do
  let args = RegMap (Empty :> RegEntry (BVRepr (knownNat @8)) byte)
  runFileMHandleCont fsVar fhdl args (\a -> cont (eitherToMaybeL a)) $ \(RegMap (Empty :> RegEntry _ byte')) fhdl' -> do
    ptr <- getHandle fhdl'
    writeBytePointer ptr byte'
    sym <- getSym
    repr <- getPtrSz
    one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 1)
    incHandleWrite fhdl' one

-- | Partial version of 'writeByte' that asserts success.
writeByte' ::
  forall p sym arch r args ret wptr.
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym 8 ->
  C.OverrideSim p sym arch r args ret ()
writeByte' fsVar fhdl byte = writeByte fsVar fhdl byte $ \case
  Just FileHandleClosed -> do
    sym <- C.getSymInterface
    liftIO $ addFailedAssertion sym $ AssertFailureSimError "Failed to write byte due to closed file handle." "writeByte': Closed file handle"
  Nothing -> return ()

-- | Write a chunk to the given 'FileHandle' and increment it to the end of
-- the written data. Returns the number of bytes written.
writeChunk ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  (forall args'. Either FileHandleError (W4.SymBV sym wptr) -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
writeChunk fsVar fhdl chunk sz cont = do
  W4.BaseBVRepr ptrSz <- return $ W4.exprType sz
  let args = RegMap (Empty :> RegEntry (BVRepr ptrSz) sz)
  runFileMHandleCont fsVar fhdl args cont $ \(RegMap (Empty :> RegEntry _ sz')) fhdl' -> do
    ptr <- getHandle fhdl'
    writeChunkPointer ptr chunk sz'
    incHandleWrite fhdl' sz'

-- | Partial version of 'writeArray' that asserts success.
writeChunk' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (W4.SymBV sym wptr)
writeChunk' fsVar fhdl chunk sz = writeChunk fsVar fhdl chunk sz $ \case
  Left FileHandleClosed -> do
    sym <- C.getSymInterface
    liftIO $ addFailedAssertion sym $ AssertFailureSimError "Failed to write array due to closed file handle." "writeArray': Closed file handle"
  Right sz' -> return sz'

-- | Read a byte from a given 'FileHandle' and increment it.
-- The partial result is undefined if the read yields no results.
readByte ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  (forall args'. Either FileHandleError (PartExpr (W4.Pred sym) (W4.SymBV sym 8)) -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
readByte fsVar fhdl cont = runFileMHandleCont fsVar fhdl emptyRegMap cont $ \_ fhdl' -> do
  ptr <- getHandle fhdl'
  v <- readBytePointer ptr
  sym <- getSym
  repr <- getPtrSz
  one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 1)
  readBytes <- incHandleRead fhdl' one
  valid <- liftIO $ W4.isEq sym one readBytes
  return $ mkPE valid v

-- | Total version of 'readByte' that asserts success.
readByte' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret (PartExpr (W4.Pred sym) (W4.SymBV sym 8))
readByte' fsVar fhdl = readByte fsVar fhdl $ \case
  Left FileHandleClosed -> do
    sym <- C.getSymInterface
    liftIO $ addFailedAssertion sym $ AssertFailureSimError "Failed to read byte due to closed file handle." "readByte': Closed file handle"
  Right r -> return r

-- | Read a chunk from a given 'FileHandle' of the given size, and increment the
-- handle by the size. Returns a struct containing the array contents, and the number
-- of bytes read.
readChunk ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  (forall args'. Either FileHandleError (DataChunk sym wptr, W4.SymBV sym wptr) -> C.OverrideSim p sym arch r args' ret a) ->
  C.OverrideSim p sym arch r args ret a
readChunk fsVar fhdl sz cont = do
  W4.BaseBVRepr ptrSz <- return $ W4.exprType sz
  let args = RegMap (Empty :> RegEntry (BVRepr ptrSz) sz)
  runFileMHandleCont fsVar fhdl args cont $ \(RegMap (Empty :> RegEntry _ sz')) fhdl' -> do
    ptr <- getHandle fhdl'
    chunk <- readChunkPointer ptr sz'
    readSz <- incHandleRead fhdl' sz'
    return (chunk, readSz)

-- | Partial version of 'readArray' that asserts success.
readChunk' ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  C.OverrideSim p sym arch r args ret (DataChunk sym wptr, W4.SymBV sym wptr)
readChunk' fsVar fhdl sz = readChunk fsVar fhdl sz $ \case
  Left FileHandleClosed -> do
    sym <- C.getSymInterface
    liftIO $ addFailedAssertion sym $ AssertFailureSimError "Failed to read array due to closed file handle." "readArray': Closed file handle"
  Right arr -> return arr

-- | Returns a predicate indicating whether or not the file handle
-- has hit the end-of-file.
isHandleOpen ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch args r ret (W4.Pred sym)
isHandleOpen fvar fhdl = runFileM fvar $ do
  sym <- getSym
  repr <- getPtrSz
  liftOV (C.readMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhdl) >>= \case
    PE p _ -> return p
    Unassigned -> return (W4.falsePred sym)

-- | Return a file handle that is already closed (i.e. any file operations
-- on it will necessarily fail).
invalidFileHandle ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  C.OverrideSim p sym arch args r ret (FileHandle sym wptr)
invalidFileHandle fvar = runFileM fvar $ do
  repr <- getPtrSz
  sym <- getSym
  toMuxTree sym <$> (liftOV $ C.newEmptyRef (MaybeRepr (FilePointerRepr repr)))


-- | Returns a predicate indicating whether or not the file identifier
-- represents a valid file.
isFileIdentValid ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent sym ->
  C.OverrideSim p sym arch args r ret (W4.Pred sym)
isFileIdentValid fvar ident = runFileM fvar $ do
  sym <- getSym
  m <- CMS.gets fsFileNames
  case W4.asString ident of
    Just (W4.Char8Literal i')
      | Right str <- Text.decodeUtf8' i'
      -> case Map.lookup str m of
      Just _ -> return $ W4.truePred sym
      Nothing -> return $ W4.falsePred sym
    _ -> return $ W4.falsePred sym

-----------------------------------------
-- Internal operations

-- | This internal monad defines a stateful context in which file operations are executed
--
-- Operations in this monad have full access to the symbolic filesystem (which
-- is normally carried throughout the symbolic execution).
--
-- Note that most operations actually use 'FileM' instead, which fixes some
-- useful constraints on top of the monad.
newtype FileM_ p arch r args ret sym wptr a = FileM { _unFM :: CMS.StateT (FileSystem sym wptr) (C.OverrideSim p sym arch r args ret) a }
  deriving
     ( Applicative
     , Functor
     , Monad
     , MonadIO
     , CMS.MonadState (FileSystem sym wptr)
     )

data FileHandleError = FileHandleClosed
data FileIdentError = FileNotFound

-- | The monad in which all filesystem operations run
type FileM p arch r args ret sym wptr a =
  (IsSymInterface sym, 1 <= wptr) =>
  FileM_ p arch r args ret sym wptr a

liftOV ::
  C.OverrideSim p sym arch r args ret a ->
  FileM p arch r args ret sym wptr a
liftOV f = FileM $ CMT.lift f

-- | Run a 'FileM_' action in the 'C.OverrideSim' monad
--
-- This extracts the current filesystem state and threads it appropriately
-- through the 'FileM_' monad context.
runFileM ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileM_ p arch r args ret sym wptr a ->
  C.OverrideSim p sym arch r args ret a
runFileM fvar (FileM f) = do
  fs <- C.readGlobal fvar
  (a, fs') <- CMS.runStateT f fs
  C.writeGlobal fvar fs'
  return a


runFileMHandleCont ::
  forall p sym arch r args args' ret a b wptr.
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  RegMap sym args' ->
  (forall args''. Either FileHandleError a -> C.OverrideSim p sym arch r (args <+> args'') ret b) ->
  (forall args''. RegMap sym args' -> FileHandle sym wptr -> FileM_ p arch r (args <+> args'') ret sym wptr a) ->
  C.OverrideSim p sym arch r args ret b
runFileMHandleCont fvar fhdl (RegMap args') cont f = do
  fs <- C.readGlobal fvar
  p <- isHandleOpen fvar fhdl
  sym <- C.getSymInterface
  args <- C.getOverrideArgs
  let
    cont' = cont @(args' ::> FileHandleType wptr)
    args'' = RegMap (args' :> RegEntry (FileHandleRepr (fsPtrSize fs)) fhdl)
    resultCase :: C.OverrideSim p sym arch r (args <+> (args' ::> FileHandleType wptr)) ret b
    resultCase = do
      (args_args', RegEntry _ fhdl') <- unconsReg <$> C.getOverrideArgs
      let (_, args'_) = splitRegs (regMapSize args) (Ctx.size args') args_args'
      a <- runFileM fvar (f @(args' ::> FileHandleType wptr) args'_ fhdl')
      cont' (Right a)

  C.symbolicBranches args''
    [(p, resultCase, Nothing)
    ,(W4.truePred sym, cont' (Left FileHandleClosed), Nothing)
    ]

splitRegs ::
  Ctx.Size ctx ->
  Ctx.Size ctx' ->
  RegMap sym (ctx <+> ctx') ->
  (RegMap sym ctx, RegMap sym ctx')
splitRegs sz sz' (RegMap m) = (RegMap (Ctx.take sz sz' m), RegMap (Ctx.drop sz sz' m))

runFileMIdentCont ::
  forall p sym arch r args ret a b wptr.
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent sym ->
  (forall args'. Either FileIdentError a -> C.OverrideSim p sym arch r (args <+> args') ret b) ->
  (forall args'. FileIdent sym -> FileM_ p arch r (args <+> args') ret sym wptr a) ->
  C.OverrideSim p sym arch r args ret b
runFileMIdentCont fvar ident cont f = do
  p <- isFileIdentValid fvar ident
  sym <- C.getSymInterface
  let
    cont' = cont @(EmptyCtx ::> FileIdentType)
    args' = RegMap (Empty :> RegEntry (StringRepr Char8Repr) ident)
    resultCase :: C.OverrideSim p sym arch r (args ::> FileIdentType) ret b
    resultCase = do
      (_, RegEntry _ fhdl') <- unconsReg <$> C.getOverrideArgs
      a <- runFileM fvar (f @(EmptyCtx ::> FileIdentType) fhdl')
      cont' (Right a)

  C.symbolicBranches args'
    [(p, resultCase, Nothing)
    ,(W4.truePred sym, cont' (Left FileNotFound), Nothing)
    ]

getSym :: FileM p arch r args ret sym wptr sym
getSym = liftOV C.getSymInterface

getPtrSz :: FileM p arch r args ret sym wptr (NatRepr wptr)
getPtrSz = CMS.gets fsPtrSize

-- | Get the (possibly symbolic) size in bytes of the given file
getFileSize :: FileHandle sym wptr -> FileM p arch r args ret sym wptr (W4.SymBV sym wptr)
getFileSize fhdl = do
  (FilePointer (File _ fileid) _, _) <- readHandle fhdl
  szArray <- CMS.gets fsFileSizes
  sym <- getSym
  liftIO $ CA.readSingle sym (Ctx.empty Ctx.:> fileid) szArray

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
--
-- Note that this adds a failing assertion if:
--
-- - The file does not exist (or the the filename is symbolic)
-- - The filename is malformed (i.e., not utf8)
resolveFileIdent ::
  FileIdent sym ->
  FileM p arch r args ret sym wptr (File sym wptr)
resolveFileIdent ident = do
  sym <- getSym
  m <- CMS.gets fsFileNames
  let missingErr = AssertFailureSimError "missing file" "resolveFileIdent attempted to lookup a file handle that does not exist"
  case W4.asString ident of
    Just (W4.Char8Literal i')
      | Right str <- Text.decodeUtf8' i'
      -> case Map.lookup str m of
      Just n -> liftIO $ readPartExpr sym n missingErr
      Nothing -> liftIO $ addFailedAssertion sym missingErr
    _ -> liftIO $ addFailedAssertion sym $
      Unsupported "Unsupported string in resolveFileIdent"


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
  repr <- getPtrSz
  sym <- getSym
  let ptr' = justPartExpr sym ptr
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

-- | Increment the filehandle by the number of bytes read, returning the
-- number of bytes that were actually incremented. This is less than
-- the number requested if the read is over the end of the file.
incHandleRead ::
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym wptr)
incHandleRead fhandle sz = do
  sym <- getSym
  basePtr <- getHandle fhandle
  ptr <- addToPointer sz basePtr
  (inbounds, overrun) <- bytesOverrun fhandle ptr
  off <- liftIO $ W4.bvSub sym sz overrun
  readBytes <- liftIO $ W4.baseTypeIte sym inbounds sz off
  ptr' <- addToPointer readBytes basePtr
  setHandle fhandle ptr'
  return readBytes

-- | Increment the filehandle by the number of bytes written. Currently
-- this is exactly the given value, since writing has no failure cases.
incHandleWrite ::
  FileHandle sym wptr ->
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym wptr)
incHandleWrite fhandle sz = do
  basePtr <- getHandle fhandle
  ptr <- addToPointer sz basePtr
  setHandle fhandle ptr
  updateFileSize fhandle
  return sz

-- | Update the file size of the given file handle if it now points past
-- the end of the file (i.e. after a successful write).
updateFileSize ::
  FileHandle sym wptr ->
  FileM p arch r args ret sym wptr ()
updateFileSize fhdl = do
  (FilePointer (File _ fileid) off, _) <- readHandle fhdl
  szArray <- CMS.gets fsFileSizes
  sym <- getSym
  oldsz <- liftIO $ CA.readSingle sym (Ctx.empty Ctx.:> fileid) szArray
  szArray' <- liftIO $ CA.writeSingle sym (Ctx.empty Ctx.:> fileid) off szArray
  outbounds <- liftIO $ W4.bvUlt sym oldsz off
  szArray'' <- liftIO $ CA.muxArrays sym outbounds szArray' szArray
  CMS.modify' $ \arr -> arr { fsFileSizes = szArray'' }

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
  dataArr <- CMS.gets fsSymData
  dataArr' <- liftIO $ CA.writeSingle sym idx bv dataArr  
  CMS.modify' $ \fs -> fs { fsSymData = dataArr' }

readBytePointer ::
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym 8)
readBytePointer fptr = do
  sym <- getSym
  let idx = filePointerIdx fptr
  dataArr <- CMS.gets fsSymData
  liftIO $ CA.readSingle sym idx dataArr


writeChunkPointer ::
  FilePointer sym wptr ->
  DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr ()
writeChunkPointer fptr chunk sz = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- CMS.gets fsSymData
  dataArr' <- liftIO $ CA.writeChunk sym idx sz chunk dataArr
  CMS.modify' $ \fs -> fs { fsSymData = dataArr' }


readChunkPointer ::
  FilePointer sym wptr ->
  -- | Number of bytes to read
  W4.SymBV sym wptr ->
  FileM p arch r args ret sym wptr (DataChunk sym wptr)
readChunkPointer fptr sz = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- CMS.gets fsSymData
  liftIO $ CA.readChunk sym idx sz dataArr

filePointerIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  FileSystemIndex sym wptr
filePointerIdx (FilePointer (File _ n) off) = Ctx.empty :> off :> n
