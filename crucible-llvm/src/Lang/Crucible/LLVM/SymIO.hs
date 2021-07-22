-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.SymIO
-- Description      : Exporting SymbolicIO operations as Override templates
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
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
  ( llvmSymIOIntrinsicTypes
  , symio_overrides
  )
  where

import           GHC.Natural ( Natural )

import           Control.Monad.IO.Class (liftIO)
import           Control.Monad ( forM, foldM )

import qualified Data.ByteString as BS
import qualified Data.BitVector.Sized as BVS
import qualified Data.Set as Set
import qualified Data.Map as Map

import           Data.Parameterized.Context ( pattern (:>), pattern Empty, (::>), EmptyCtx )

import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.SymbolRepr

import           Lang.Crucible.Types ( IntrinsicType, BVType, TypeRepr(..) )
import qualified Lang.Crucible.Utils.MuxTree as CMT
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Backend as C
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap

import           Lang.Crucible.LLVM.Bytes (toBytes)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Extension ( ArchWidth )
import           Lang.Crucible.LLVM.DataLayout ( noAlignment )
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.QQ( llvmOvr )

import qualified What4.Interface as W4
import qualified What4.Partial as W4P

import qualified Lang.Crucible.SymIO as SymIO

data LLVMFileSystem ptrW =
  LLVMFileSystem
    { llvmFileSystem :: GlobalVar (SymIO.FileSystemType ptrW)
    -- | we represent filesystem pointers as LLVMpointers on the outside, where
    -- we need to maintain the mapping to internal handles here
    , llvmFileDescMap :: GlobalVar (FDescMapType ptrW)
    }

data FDescMap sym ptrW where
  FDescMap ::
    { _fDescNext :: Natural
    , _fDescMap :: Map.Map Natural (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW))
    } -> FDescMap sym ptrW

type FDescMapType w = IntrinsicType "LLVM_fdescmap" (EmptyCtx ::> BVType w)

instance (IsSymInterface sym) => IntrinsicClass sym "LLVM_fdescmap" where
  type Intrinsic sym "LLVM_fdescmap" (EmptyCtx ::> BVType w) = FDescMap sym w

  muxIntrinsic sym _iTypes _nm (Empty :> (BVRepr _w)) = muxHandleMap sym
  muxIntrinsic _ _ nm ctx = \_ _ _ -> typeError nm ctx


muxHandleMap
  :: IsSymInterface sym
  => sym
  -> W4.Pred sym
  -> FDescMap sym ptrW
  -> FDescMap sym ptrW
  -> IO (FDescMap sym ptrW)
muxHandleMap sym p (FDescMap nextT mapT) (FDescMap nextF mapF) = do
  let
    keys = Set.toList $ Set.union (Map.keysSet mapT) (Map.keysSet mapF)
    next = max nextT nextF
  fmap (FDescMap next . Map.fromList) $ forM keys $ \k -> do
    let vT = W4P.joinMaybePE (Map.lookup k mapT)
    let vF = W4P.joinMaybePE (Map.lookup k mapF)
    r <- mergePartExpr sym (CMT.mergeMuxTree sym) p vT vF
    return (k,r)


llvmSymIOIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmSymIOIntrinsicTypes = id
  . MapF.insert (knownSymbol :: SymbolRepr "LLVM_fdescmap") IntrinsicMuxFn
  $ SymIO.symIOIntrinsicTypes

-- | Resolve a symbolic file descriptor to a known allocated file handle.
-- The partial result is undefined if the descriptor is not found in the
-- file handle table.
getHandle
  :: forall sym ptrW
   . IsSymInterface sym
  => sym
  -> W4.SymNat sym
  -> FDescMap sym ptrW
  -> IO (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW))
getHandle sym fdesc (FDescMap _ m) = case W4.asNat fdesc of
  Just fdesc_lit | Just fhdl <- Map.lookup fdesc_lit m -> return fhdl
  _ -> do
    cases <- mapM go (Map.assocs m)
    foldM (\a (p, b) -> mergePartExpr sym (CMT.mergeMuxTree sym) p b a) W4P.Unassigned cases
  where
    go :: (Natural, (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW)))
       -> IO (W4.Pred sym, (W4P.PartExpr (W4.Pred sym) (SymIO.FileHandle sym ptrW)))
    go (n, fhdl) = do
      n_sym <- W4.natLit sym n
      fdesc_eq <- W4.natEq sym n_sym fdesc
      return $ (fdesc_eq, fhdl)


chunkFromMemory
  :: forall sym wptr
   . (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (SymIO.DataChunk sym wptr)
chunkFromMemory sym mem ptr = SymIO.mkArrayChunk sym $ \offset -> do
  ptr' <- ptrAdd sym PtrWidth ptr offset
  doLoad sym mem ptr' (bitvectorType (toBytes (1 :: Integer))) (BVRepr (knownNat @8)) noAlignment

-- | Retrieve the 'SymIO.FileHandle' that the given descriptor represents,
-- calling the continuation with 'Nothing' if the descriptor does not represent
-- a valid handle. Notably, a successfully resolved handle may itself still be closed.
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
  fdesc_nat <- liftIO $ W4.bvToNat sym fdesc
  (liftIO $ getHandle sym fdesc_nat descMap) >>= \case
    W4P.PE p fhdl -> do
      symbolicBranch p
        args (getOverrideArgs >>= \args' -> cont (Just fhdl) args') Nothing
        args (getOverrideArgs >>= \args' -> cont Nothing args') Nothing
    W4P.Unassigned -> cont Nothing args


-- | Allocate a fresh 'LLVMPtr' that is associated with the given 'SymIO.FileHandle'
-- TODO: we should add a symbolic offset to these values so that we can't make any
-- concrete assertions about them.
allocateFileHandle
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> SymIO.FileHandle sym wptr
  -> OverrideSim p sym ext r args ret (W4.SymBV sym 32)
allocateFileHandle fsVars fh = do
  sym <- getSymInterface
  modifyGlobal (llvmFileDescMap fsVars) $ \(FDescMap next descMap) -> do
    fdesc <-  liftIO $ W4.bvLit sym (knownNat @32) (BVS.mkBV (knownNat @32) (toInteger next))
    let ptrMap' = Map.insert next (W4P.justPartExpr sym fh) descMap
    return (fdesc, FDescMap (next + 1) ptrMap')

loadFileIdent
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => GlobalVar Mem
  -> LLVMPtr sym wptr
  -> OverrideSim p sym ext r args ret (SymIO.FileIdent sym)
loadFileIdent memOps filename_ptr = do
  mem <- readGlobal memOps
  sym <- getSymInterface
  filename_bytes <- liftIO $ loadString sym mem filename_ptr Nothing
  liftIO $ W4.stringLit sym (W4.Char8Literal (BS.pack filename_bytes))

returnIOError32
  :: IsSymInterface sym
  => OverrideSim p sym ext r args ret (W4.SymBV sym 32)
returnIOError32 = do
  sym <- getSymInterface
  liftIO $ W4.bvLit sym (knownNat @32) (BVS.mkBV (knownNat @32) (-1))

returnIOError
  :: forall wptr p sym ext r args ret
  . (IsSymInterface sym, HasPtrWidth wptr)
  => OverrideSim p sym ext r args ret (W4.SymBV sym wptr)
returnIOError = do
  sym <- getSymInterface
  liftIO $ W4.bvLit sym PtrWidth (BVS.mkBV PtrWidth (-1))

openFile
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> BVType 32)
           (BVType 32)
openFile fsVars =
  [llvmOvr| i32 @open( i8*, i32 ) |]
  -- TODO add mode support
  (\memOps _sym (Empty :> filename_ptr :> _flags) ->
       do
         fileIdent <- loadFileIdent memOps (regValue filename_ptr)
         SymIO.openFile (llvmFileSystem fsVars) fileIdent $ \case
           Left SymIO.FileNotFound -> returnIOError32
           Right fileHandle -> allocateFileHandle fsVars fileHandle
  )

closeFile
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> BVType 32)
           (BVType 32)
closeFile fsVars =
  [llvmOvr| i32 @close( i32 ) |]
  (\_memOps sym (Empty :> filedesc ) ->
       do
         lookupFileHandle fsVars (regValue filedesc) emptyRegMap $ \case
           Just fileHandle -> \_ ->
             SymIO.closeFileHandle (llvmFileSystem fsVars) fileHandle $ \case
               Just SymIO.FileHandleClosed -> returnIOError32
               Nothing -> liftIO $ W4.bvLit sym (knownNat @32) (BVS.mkBV (knownNat @32) 0)
           Nothing -> \_ -> returnIOError32
  )


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
  (\memOps sym args@(Empty :> filedesc :> _ :> _ ) ->
       do
         lookupFileHandle fsVars (regValue filedesc) (RegMap args) $ \case
           Just fileHandle -> \(RegMap (Empty :> _ :> buffer_ptr :> size)) ->
             SymIO.readChunk (llvmFileSystem fsVars) fileHandle (regValue size) $ \case
               Left SymIO.FileHandleClosed -> returnIOError
               Right (chunk, bytesRead) -> do
                 modifyGlobal memOps $ \mem -> liftIO $ do
                   chunkArray <- SymIO.chunkToArray sym (W4.BaseBVRepr PtrWidth) chunk
                   mem' <- doArrayStore sym mem (regValue buffer_ptr) noAlignment chunkArray bytesRead
                   return (bytesRead, mem')
           Nothing -> \_ -> returnIOError
  )


writeFileHandle
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMFileSystem wptr
  -> LLVMOverride p sym
           (EmptyCtx ::> BVType 32
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (BVType wptr)
writeFileHandle fsVars =
  [llvmOvr| ssize_t @write( i32, i8*, size_t ) |]
  (\memOps sym args@(Empty :> filedesc :> _ :> _ ) ->
       do
         lookupFileHandle fsVars (regValue filedesc) (RegMap args) $ \case
           Just fileHandle -> \(RegMap (Empty :> _ :> buffer_ptr :> size)) -> do
             mem <- readGlobal memOps
             chunk <- liftIO $ chunkFromMemory sym mem (regValue buffer_ptr)
             SymIO.writeChunk (llvmFileSystem fsVars) fileHandle chunk (regValue size) $ \case
               Left SymIO.FileHandleClosed -> returnIOError
               Right bytesWritten -> return bytesWritten
           Nothing -> \_ -> returnIOError
  )


symio_overrides
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMFileSystem wptr
  -> [OverrideTemplate p sym arch rtp l a]
symio_overrides fs =
  [ basic_llvm_override $ openFile fs
  , basic_llvm_override $ closeFile fs
  , basic_llvm_override $ readFileHandle fs
  , basic_llvm_override $ writeFileHandle fs
  ]
