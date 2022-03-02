-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.SymIO
-- Description      : Exporting SymbolicIO operations as Override templates
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
--
--
-- This module wraps the crucible-symio interface suitably for use within the
-- LLVM frontend to crucible. It provides overrides for the following functions:
--
--   * @open@
--   * @read@
--   * @write@
--   * @close@
--
-- as specified by POSIX. Note that it does not yet cover the C stdio functions.
-- This additional layer on top of crucible-symio is necessary to bridge the gap
-- between LLVMPointer arguments and more primitive argument types (including
-- that filenames need to be read from the LLVM memory model before they can be
-- interpreted).
--
-- The limitations of this library are enumerated in the README for crux-llvm,
-- which is the user-facing documentation for this functionality.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lang.Crucible.LLVM.SymIO
  ( -- * Types
    llvmSymIOIntrinsicTypes
  , LLVMFileSystem(..)
  , SomeOverrideSim(..)
  , initialLLVMFileSystem
  -- * Overrides
  , symio_overrides
  , openFile
  , callOpenFile
  , closeFile
  , callCloseFile
  , readFileHandle
  , callReadFileHandle
  , writeFileHandle
  , callWriteFileHandle
  -- * File-related utilities
  , allocateFileDescriptor
  , lookupFileHandle
  )
  where

import           Control.Monad ( forM, foldM, when )
import           Control.Monad.IO.Class (liftIO)
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.Context
                   ( pattern (:>), pattern Empty, (::>), EmptyCtx, uncurryAssignment )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.SymbolRepr as PS
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import qualified Data.Text.IO as Text.IO
import           GHC.Natural ( Natural )
import           GHC.TypeNats ( type (<=) )
import qualified System.IO as IO

import qualified Lang.Crucible.FunctionHandle as LCF
import           Lang.Crucible.Types ( IntrinsicType, BVType, TypeRepr(..) )
import qualified Lang.Crucible.Utils.MuxTree as CMT
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Backend as C
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import qualified Lang.Crucible.Simulator.GlobalState as LCSG

import           Lang.Crucible.LLVM.Bytes (toBytes)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Extension ( ArchWidth )
import           Lang.Crucible.LLVM.DataLayout ( noAlignment )
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.QQ( llvmOvr )

import qualified What4.Interface as W4
import qualified What4.Partial as W4P

import qualified Lang.Crucible.SymIO as SymIO

-- | A representation of the filesystem for the LLVM frontend
--
-- This contains the underlying SymIO filesystem as well as the infrastructure
-- for allocating fresh file handles
data LLVMFileSystem ptrW =
  LLVMFileSystem
    { llvmFileSystem :: GlobalVar (SymIO.FileSystemType ptrW)
    -- ^ The underlying symbolic filesystem
    , llvmFileDescMap :: GlobalVar (FDescMapType ptrW)
    -- ^ Maintains the mapping from file descriptors to low-level crucible-symio
    -- 'SymIO.FileHandle's
    , llvmHandles :: Map.Map Natural IO.Handle
    -- ^ Handles that concrete output will be mirrored to; if this is empty, no
    -- mirroring will be performed
    , llvmFilePointerRepr :: PN.NatRepr ptrW
    }

-- | Contains the mapping from file descriptors to the underlying 'SymIO.FileHandle'
--
-- This also tracks the next file descriptor to hand out.  See Note [File
-- Descriptor Sequence].
data FDescMap sym ptrW where
  FDescMap ::
    { fDescNext :: Natural
    -- ^ The next file descriptor to hand out
    --
    -- Note that these are truncated to 32 bit bitvectors when they are handed
    -- out; we don't have any guards against overflow on that right now
    , fDescMap :: Map.Map Natural (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW))
    } -> FDescMap sym ptrW

-- | A wrapper around a RankN 'OverrideSim' action
--
-- This enables us to make explicit that all of the type variables are free and
-- can be instantiated at any types since this override action has to be
-- returned from the 'initialLLVMFileSystem' function.
newtype SomeOverrideSim sym a where
  SomeOverrideSim :: (forall p ext rtp args ret . OverrideSim p sym ext rtp args ret a) -> SomeOverrideSim sym a

targetToFD :: SymIO.FDTarget k -> Maybe Natural
targetToFD t =
  case t of
    SymIO.StdinTarget -> Just 0
    SymIO.StdoutTarget -> Just 1
    SymIO.StderrTarget -> Just 2
    _ -> Nothing

-- | Create an initial 'LLVMFileSystem' based on given concrete and symbolic file contents
--
-- Note that this function takes a 'LCSG.SymGlobalState' because it needs to
-- allocate a few distinguished global variables for its own bookkeeping. It
-- adds them to the given global state and returns an updated global state,
-- which must not be discarded.
--
-- The returned 'LLVMFileSystem' is a wrapper around that global state, and is
-- required to initialize the symbolic I/O overrides.
--
-- This function also returns an 'OverrideSim' action (wrapped in a
-- 'SomeOverrideSim') that must be run to initialize any standard IO file
-- descriptors that have been requested.  This action should be run *before* the
-- entry point of the function that is being verified is invoked.
--
-- See Note [Standard IO Setup] for details
initialLLVMFileSystem
  :: forall sym ptrW
   . (HasPtrWidth ptrW, C.IsSymInterface sym)
  => LCF.HandleAllocator
  -> sym
  -> PN.NatRepr ptrW
  -- ^ The pointer width for the platform
  -> SymIO.InitialFileSystemContents sym
  -- ^ The initial contents of the symbolic filesystem
  -> [(SymIO.FDTarget SymIO.Out, IO.Handle)]
  -- ^ A mapping from file targets to handles, to which output should be
  -- mirrored. This is intended to support mirroring symbolic stdout/stderr to
  -- concrete stdout/stderr, but could be more flexible in the future (e.g.,
  -- handling sockets).
  --
  -- Note that the writes to the associated underlying symbolic files are still
  -- recorded in the symbolic filesystem
  -> LCSG.SymGlobalState sym
  -- ^ The current globals, which will be updated with necessary bindings to support the filesystem
  -> IO (LLVMFileSystem ptrW, LCSG.SymGlobalState sym, SomeOverrideSim sym ())
initialLLVMFileSystem halloc sym ptrW initContents handles globals0 = do
  fs0 <- SymIO.initFS sym ptrW initContents
  let fdm0 = FDescMap { fDescNext = 0
                      , fDescMap = Map.empty
                      }
  fsVar <- freshGlobalVar halloc (Text.pack "llvmFileSystem_Global") (SymIO.FileSystemRepr ptrW)
  fdmVar <- freshGlobalVar halloc (Text.pack "llvmFileDescMap_Global") (FDescMapRepr ptrW)
  let llfs = LLVMFileSystem { llvmFileSystem = fsVar
                            , llvmFileDescMap = fdmVar
                            , llvmFilePointerRepr = ptrW
                            , llvmHandles = Map.fromList [ (fd, hdl)
                                                         | (tgt, hdl) <- handles
                                                         , Just fd <- return (targetToFD tgt)
                                                         ]
                            }
  let globals1 = LCSG.insertGlobal fdmVar fdm0 $ LCSG.insertGlobal fsVar fs0 globals0
  let bootstrapStdio :: OverrideSim p sym ext rtp args ret ()
      bootstrapStdio = do
        -- Allocate the file handles for the standard IO streams in order such
        -- that they are in file descriptors 0, 1, and 2 respectively
        --
        -- We discard the actual file descriptors because they are accessed via
        -- literals in the program.  The 'allocateFileDescriptor' function
        -- handles mapping the underlying FileHandle to an int file descriptor
        -- internally.
        let toLit = W4.Char8Literal . TextEncoding.encodeUtf8 . SymIO.fdTargetToText
        when (Map.member SymIO.StdinTarget (SymIO.concreteFiles initContents) || Map.member SymIO.StdinTarget (SymIO.symbolicFiles initContents)) $ do
          stdinFilename <- liftIO $ W4.stringLit sym (toLit SymIO.StdinTarget)
          _inFD <- SymIO.openFile' fsVar stdinFilename >>= allocateFileDescriptor llfs
          return ()
        when (SymIO.useStdout initContents) $ do
          stdoutFilename <- liftIO $ W4.stringLit sym (toLit SymIO.StdoutTarget)
          _outFD <- SymIO.openFile' fsVar stdoutFilename >>= allocateFileDescriptor llfs
          return ()
        when (SymIO.useStderr initContents) $ do
          stderrFilename <- liftIO $ W4.stringLit sym (toLit SymIO.StderrTarget)
          _errFD <- SymIO.openFile' fsVar stderrFilename >>= allocateFileDescriptor llfs
          return ()

  return (llfs, globals1, SomeOverrideSim bootstrapStdio)

type FDescMapType w = IntrinsicType "LLVM_fdescmap" (EmptyCtx ::> BVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "LLVM_fdescmap" where
  type Intrinsic sym "LLVM_fdescmap" (EmptyCtx ::> BVType w) = FDescMap sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) = muxFDescMap sym
  muxIntrinsic _ _ nm ctx = \_ _ _ -> typeError nm ctx

pattern FDescMapRepr :: () => (1 <= w, ty ~ FDescMapType w) => PN.NatRepr w -> TypeRepr ty
pattern FDescMapRepr w <- IntrinsicRepr (PC.testEquality (PS.knownSymbol @"LLVM_fdescmap") -> Just PC.Refl) (Empty :> BVRepr w)
  where
    FDescMapRepr w = IntrinsicRepr PS.knownSymbol (Empty :> BVRepr w)

muxFDescMap
  :: IsSymInterface sym
  => sym
  -> W4.Pred sym
  -> FDescMap sym ptrW
  -> FDescMap sym ptrW
  -> IO (FDescMap sym ptrW)
muxFDescMap sym p (FDescMap nextT mapT) (FDescMap nextF mapF) = do
  let
    keys = Set.toList $ Set.union (Map.keysSet mapT) (Map.keysSet mapF)
    next = max nextT nextF
  fmap (FDescMap next . Map.fromList) $ forM keys $ \k -> do
    let vT = W4P.joinMaybePE (Map.lookup k mapT)
    let vF = W4P.joinMaybePE (Map.lookup k mapF)
    r <- mergePartExpr sym (CMT.mergeMuxTree sym) p vT vF
    return (k,r)

-- | The intrinsics supporting symbolic I/O in LLVM
--
-- Note that this includes the base intrinsic types from crucible-symio, so
-- those do not need to be added again.
llvmSymIOIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmSymIOIntrinsicTypes = id
  . MapF.insert (PS.knownSymbol :: PS.SymbolRepr "LLVM_fdescmap") IntrinsicMuxFn
  $ SymIO.symIOIntrinsicTypes

-- | Resolve a symbolic file descriptor to a known allocated file handle.
-- The partial result is undefined if the descriptor is not found in the
-- file handle table.
getHandle
  :: forall sym ptrW
   . IsSymInterface sym
  => sym
  -> W4.SymBV sym 32
  -> FDescMap sym ptrW
  -> IO (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW))
getHandle sym fdesc (FDescMap _ m) = case W4.asBV fdesc of
  Just fdesc_lit | Just fhdl <- Map.lookup (BVS.asNatural fdesc_lit) m -> return fhdl
  _ -> do
    cases <- mapM go (Map.assocs m)
    foldM (\a (p, b) -> mergePartExpr sym (CMT.mergeMuxTree sym) p b a) W4P.Unassigned cases
  where
    go :: (Natural, (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW)))
       -> IO (W4.Pred sym, (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW)))
    go (n, fhdl) = do
      n_sym <- W4.bvLit sym PN.knownNat (BVS.mkBV PN.knownNat (toInteger n))
      fdesc_eq <- W4.bvEq sym n_sym fdesc
      return $ (fdesc_eq, fhdl)

-- | Construct a 'SymIO.DataChunk' from a pointer
--
-- Note that this is a lazy construct that does not load memory immediately. An
-- 'SymIO.DataChunk' is a wrapper around a function to peek memory at a given
-- offset one byte at a time.
chunkFromMemory
  :: forall sym bak wptr
   . (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (SymIO.DataChunk sym wptr)
chunkFromMemory bak mem ptr =
  let sym = backendGetSym bak in
  SymIO.mkArrayChunk sym $ \offset -> do
    ptr' <- ptrAdd sym PtrWidth ptr offset
    llbytes <- doLoad bak mem ptr' (bitvectorType (toBytes (1 :: Integer))) (LLVMPointerRepr (PN.knownNat @8)) noAlignment
    projectLLVM_bv bak llbytes

-- | Retrieve the 'SymIO.FileHandle' that the given descriptor represents,
-- calling the continuation with 'Nothing' if the descriptor does not represent
-- a valid handle. Notably, a successfully resolved handle may itself still be closed.
--
-- Note that the continuation may be called multiple times if it is used within
-- a symbolic branch. As a result, any side effects in the continuation may be
-- performed multiple times.
lookupFileHandle
  :: IsSymInterface sym
  => LLVMFileSystem wptr
  -> W4.SymBV sym 32
  -> RegMap sym args''
  -> (forall args'. Maybe (SymIO.FileHandle sym wptr) -> RegMap sym args'' -> OverrideSim p sym ext r args' ret a)
  -> OverrideSim p sym ext r args ret a
lookupFileHandle fsVars fdesc args cont = do
  descMap <- readGlobal (llvmFileDescMap fsVars)
  sym <- getSymInterface
  (liftIO $ getHandle sym fdesc descMap) >>= \case
    W4P.PE p fhdl -> do
      symbolicBranch p
        args (getOverrideArgs >>= \args' -> cont (Just fhdl) args') Nothing
        args (getOverrideArgs >>= \args' -> cont Nothing args') Nothing
    W4P.Unassigned -> cont Nothing args


-- | Allocate a fresh (integer/bitvector(32)) file descriptor that is associated with the given 'SymIO.FileHandle'
--
-- NOTE that this is a file descriptor in the POSIX sense, rather than a @FILE*@
-- or the underlying 'SymIO.FileHandle'.
--
-- NOTE that we truncate the file descriptor source to 32 bits in this function;
-- it could in theory overflow.
--
-- NOTE that the file descriptor counter is incremented monotonically as the
-- simulator hits calls to @open@; this means that calls to @open@ in parallel
-- control flow branches would get sequential file descriptor values whereas the
-- real program would likely allocate the same file descriptor value on both
-- branches. This could be relevant for some bug finding scenarios.
--
-- TODO It would be interesting if we could add a symbolic offset to these
-- values so that we can't make any concrete assertions about them. It isn't
-- clear if that ever happens in real code. If we do that, we need an escape
-- hatch to let us allocate file descriptors 0, 1, and 2 if needed.
allocateFileDescriptor
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> SymIO.FileHandle sym wptr
  -> OverrideSim p sym ext r args ret (W4.SymBV sym 32)
allocateFileDescriptor fsVars fh = do
  sym <- getSymInterface
  modifyGlobal (llvmFileDescMap fsVars) $ \(FDescMap next descMap) -> do
    fdesc <-  liftIO $ W4.bvLit sym (PN.knownNat @32) (BVS.mkBV (PN.knownNat @32) (toInteger next))
    let ptrMap' = Map.insert next (W4P.justPartExpr sym fh) descMap
    return (fdesc, FDescMap (next + 1) ptrMap')

loadFileIdent
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions)
  => GlobalVar Mem
  -> LLVMPtr sym wptr
  -> OverrideSim p sym ext r args ret (SymIO.FileIdent sym)
loadFileIdent memOps filename_ptr =
  ovrWithBackend $ \bak ->
   do mem <- readGlobal memOps
      filename_bytes <- liftIO $ loadString bak mem filename_ptr Nothing
      liftIO $ W4.stringLit (backendGetSym bak) (W4.Char8Literal (BS.pack filename_bytes))

returnIOError32
  :: IsSymInterface sym
  => OverrideSim p sym ext r args ret (W4.SymBV sym 32)
returnIOError32 = do
  sym <- getSymInterface
  liftIO $ W4.bvLit sym (PN.knownNat @32) (BVS.mkBV (PN.knownNat @32) (-1))

returnIOError
  :: forall wptr p sym ext r args ret
  . (IsSymInterface sym, HasPtrWidth wptr)
  => OverrideSim p sym ext r args ret (W4.SymBV sym wptr)
returnIOError = do
  sym <- getSymInterface
  liftIO $ W4.bvLit sym PtrWidth (BVS.mkBV PtrWidth (-1))

openFile
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> BVType 32)
           (BVType 32)
openFile fsVars =
  [llvmOvr| i32 @open( i8*, i32 ) |]
  -- TODO add mode support by making this a varargs function
  (\memOps bak args -> uncurryAssignment (callOpenFile bak memOps fsVars) args)

callOpenFile ::
  (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions) =>
  bak ->
  GlobalVar Mem ->
  LLVMFileSystem wptr ->
  RegEntry sym (LLVMPointerType wptr) ->
  RegEntry sym (BVType 32) ->
  OverrideSim p sym ext rtp args ret (RegValue sym (BVType 32))
callOpenFile _bak memOps fsVars filename_ptr _flags =
  do fileIdent <- loadFileIdent memOps (regValue filename_ptr)
     SymIO.openFile (llvmFileSystem fsVars) fileIdent $ \case
       Left SymIO.FileNotFound -> returnIOError32
       Right fileHandle -> allocateFileDescriptor fsVars fileHandle

closeFile
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> BVType 32)
           (BVType 32)
closeFile fsVars =
  [llvmOvr| i32 @close( i32 ) |]
  (\memOps bak args -> uncurryAssignment (callCloseFile bak memOps fsVars) args)

callCloseFile ::
  (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr) =>
  bak ->
  GlobalVar Mem ->
  LLVMFileSystem wptr ->
  RegEntry sym (BVType 32) ->
  OverrideSim p sym ext rtp args ret (RegValue sym (BVType 32))
callCloseFile bak _memOps fsVars filedesc =
  do let sym = backendGetSym bak
     lookupFileHandle fsVars (regValue filedesc) emptyRegMap $ \case
       Just fileHandle -> \_ ->
         SymIO.closeFileHandle (llvmFileSystem fsVars) fileHandle $ \case
           Just SymIO.FileHandleClosed -> returnIOError32
           Nothing -> liftIO $ W4.bvLit sym (PN.knownNat @32) (BVS.mkBV (PN.knownNat @32) 0)
       Nothing -> \_ -> returnIOError32

readFileHandle
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> BVType 32
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (BVType wptr)
readFileHandle fsVars =
  [llvmOvr| ssize_t @read( i32, i8*, size_t ) |]
  (\memOps bak args -> uncurryAssignment (callReadFileHandle bak memOps fsVars) args)

callReadFileHandle ::
  (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr) =>
  bak ->
  GlobalVar Mem ->
  LLVMFileSystem wptr ->
  RegEntry sym (BVType 32) ->
  RegEntry sym (LLVMPointerType wptr) ->
  RegEntry sym (BVType wptr) ->
  OverrideSim p sym ext rtp args ret (RegValue sym (BVType wptr))
callReadFileHandle bak memOps fsVars filedesc buf count =
  do let sym = backendGetSym bak
     let args = Empty :> filedesc :> buf :> count
     lookupFileHandle fsVars (regValue filedesc) (RegMap args) $ \case
       Just fileHandle -> \(RegMap (Empty :> _ :> buffer_ptr :> size)) ->
         SymIO.readChunk (llvmFileSystem fsVars) fileHandle (regValue size) $ \case
           Left SymIO.FileHandleClosed -> returnIOError
           Right (chunk, bytesRead) -> do
             modifyGlobal memOps $ \mem -> liftIO $ do
               chunkArray <- SymIO.chunkToArray sym (W4.BaseBVRepr PtrWidth) chunk
               mem' <- doArrayStore bak mem (regValue buffer_ptr) noAlignment chunkArray bytesRead
               return (bytesRead, mem')
       Nothing -> \_ -> returnIOError

-- | If the write is to a concrete FD for which we have an associated 'IO.Handle', mirror the write to that Handle
--
-- This is intended to support mirroring stdout/stderr in a user-visible way
-- (noting that symbolic IO can be repeated due to the simulator branching).
-- Note also that only writes of a concrete length are mirrored reasonably;
-- writes with symbolic length are denoted with a substitute token. Likewise
-- individual symbolic bytes are printed as @?@ characters.
doConcreteWrite
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => PN.NatRepr wptr
  -> Map.Map Natural IO.Handle
  -> RegValue sym (BVType 32)
  -> SymIO.DataChunk sym wptr
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext rtp args ret ()
doConcreteWrite ptrw handles symFD chunk size =
  case W4.asBV symFD of
    Just (BVS.asNatural -> fd)
      | Just hdl <- Map.lookup fd handles
      , Just numBytes <- BVS.asUnsigned <$> W4.asBV (regValue size) -> do
          -- We have a concrete size of the write and an IO Handle to write
          -- to. Write each byte that is concrete, or replace it with a '?'
          sym <- getSymInterface
          F.forM_ [0..numBytes - 1] $ \idx -> do
            idxBV <- liftIO $ W4.bvLit sym ptrw (BVS.mkBV ptrw idx)
            byteVal <- liftIO $ SymIO.evalChunk chunk idxBV
            case W4.asBV byteVal of
              Just (BVS.asUnsigned -> concByte) -> liftIO $ BS.hPut hdl (BS.pack [fromIntegral concByte])
              Nothing -> liftIO $ BS.hPut hdl (BSC.pack ['?'])
      | Just hdl <- Map.lookup fd handles -> do
          -- In this case, we have a write of symbolic size.  We can't really
          -- write that out, but do our best
          liftIO $ Text.IO.hPutStr hdl (Text.pack "[‽]")
    _ -> return ()

writeFileHandle
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> BVType 32
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (BVType wptr)
writeFileHandle fsVars =
  [llvmOvr| ssize_t @write( i32, i8*, size_t ) |]
  (\memOps bak args -> uncurryAssignment (callWriteFileHandle bak memOps fsVars) args)

callWriteFileHandle ::
  (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr, ?memOpts :: MemOptions) =>
  bak ->
  GlobalVar Mem ->
  LLVMFileSystem wptr ->
  RegEntry sym (BVType 32) ->
  RegEntry sym (LLVMPointerType wptr) ->
  RegEntry sym (BVType wptr) ->
  OverrideSim p sym ext rtp args ret (RegValue sym (BVType wptr))
callWriteFileHandle bak memOps fsVars filedesc buf count =
  do let args = Empty :> filedesc :> buf :> count
     lookupFileHandle fsVars (regValue filedesc) (RegMap args) $ \case
       Just fileHandle -> \(RegMap (Empty :> _ :> buffer_ptr :> size)) -> do
         mem <- readGlobal memOps
         chunk <- liftIO $ chunkFromMemory bak mem (regValue buffer_ptr)
         doConcreteWrite (llvmFilePointerRepr fsVars) (llvmHandles fsVars) (regValue filedesc) chunk size
         SymIO.writeChunk (llvmFileSystem fsVars) fileHandle chunk (regValue size) $ \case
           Left SymIO.FileHandleClosed -> returnIOError
           Right bytesWritten -> return bytesWritten
       Nothing -> \_ -> returnIOError

-- | The file handling overrides
--
-- See the 'initialLLVMFileSystem' function for creating the initial filesystem state
symio_overrides
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?memOpts :: MemOptions)
  => LLVMFileSystem wptr
  -> [OverrideTemplate p sym arch rtp l a]
symio_overrides fs =
  [ basic_llvm_override $ openFile fs
  , basic_llvm_override $ closeFile fs
  , basic_llvm_override $ readFileHandle fs
  , basic_llvm_override $ writeFileHandle fs
  ]

{- Note [Standard IO Setup]

The underlying symbolic IO library hands out abstract 'FileHande's, which are an
internal type that do not correspond to any source-level data values.  Frontends
must map them to something from the target programming language.  In this
module, that means we must map them to POSIX file descriptors (represented as C
ints).

In particular, when setting up the symbolic execution engine, we want to be able
to map standard input, standard output, and standard error to their prescribed
file descriptors (0, 1, and 2 respectively).  We can do that by simply
allocating them in order, as we start the file descriptor counter at 0 (see
'FDescMap').  Note that we just reuse the existing infrastructure to allocate
file descriptors (in particular, 'allocateFileDescriptor'). Note that we do
*not* use the 'openFile' function defined in this module because it expects the
filename to be stored in the LLVM memory, which our magic names for the standard
streams are not.

Note that if we start the symbolic execution engine without standard
in/out/error, we could potentially hand out file descriptors at these usually
reserved numbers. That isn't necessarily a problem, but it could be. We could
one day provide a method for forcing file descriptors to start at 3 even if
these special files are not allocated (i.e., start off closed).  We should
investigate the behavior of the OS and mimic it (or make it an option).

As a note on file names, the standard IO streams do not have prescribed names
that can be opened. We use synthetic names defined in the underlying
architecture-independent symbolic IO library.  We do not need to know what they
are here, but they are arranged to not collide with any valid names for actual
files in the symbolic filesystem.

-}

{- Note [File Descriptor Sequence]

This code uses a global counter to provide the next file descriptor to hand out
when a file is opened.  This can lead to a subtle difference in behavior
compared to a real program.

Consider the case where a program contains a symbolic branch where both branches
open files.  The symbolic I/O system will allocate each of the opened files a
different file descriptor.  In contrast, a real system would only assign one of
those file descriptors because it would only see one branch.  This means that
later opened files would differ from the real program.

This should only be observable if the program makes control decisions based on
the values in file descriptors, which it really should not. However, it is
possible in the real world.

-}
