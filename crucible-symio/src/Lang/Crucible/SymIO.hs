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

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.SymIO
  (
    FileSystemType
  , FileHandle
  , FilePointer
  , File
  , openFile
  , resolveFileIdent
  , readBytes
  , writeBytes
  , closeFileHandle
  ) where

import           Prelude hiding ( fail )
import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.Trans.State ( StateT, runStateT, evalStateT )
import           Control.Monad.State hiding ( fail )
import           Control.Monad.Fail
import           Numeric.Natural

import qualified Data.Map as Map
import qualified Data.Parameterized.Vector as V
import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Context ( pattern (:>) )
import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.Simulator.SimError
import qualified Lang.Crucible.Simulator.OverrideSim as C
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Backend
import           Lang.Crucible.Utils.MuxTree
import           Lang.Crucible.Types
import qualified What4.Interface as W4
import           What4.Partial

import           What4.CachedArray as CA
import           Lang.Crucible.SymIO.Types



---------------------------------------
-- Interface

-- | Open a file by creating a fresh file handle to its contents
openFile ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  File sym wptr ->
  C.OverrideSim p sym arch r args ret (FileHandle sym wptr)
openFile fvar file = do
  fs <- C.readGlobal fvar
  sym <- C.getSymInterface
  let repr = fsPtrSize fs
  zero <- liftIO $ W4.bvLit sym repr (BV.mkBV repr 0)
  ref <- toMuxTree sym <$> C.newEmptyRef (MaybeRepr (FilePointerRepr repr))
  evalFileM fs $ setHandle ref (FilePointer file zero)
  return ref

-- | Close a file by invalidating its file handle
closeFileHandle ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->
  FileHandle sym wptr ->
  C.OverrideSim p sym arch r args ret ()
closeFileHandle fvar fhdl = do
  fs <- C.readGlobal fvar
  sym <- C.getSymInterface
  let repr = fsPtrSize fs
  C.writeMuxTreeRef (MaybeRepr (FilePointerRepr repr)) fhdl (maybePartExpr sym Nothing)

-- | Resolve a file identifier to a 'File'
resolveFileIdent ::
  IsSymInterface sym =>
  GlobalVar (FileSystemType wptr) ->
  FileIdent ->
  C.OverrideSim p sym arch r args ret (File sym wptr)
resolveFileIdent fsVar ident = do
  sym <- C.getSymInterface
  fs <- C.readGlobal fsVar
  case Map.lookup ident (fsFileNames fs) of
    Just n -> liftIO $ do
      n' <- W4.natLit sym n
      return $ File (fsPtrSize fs) n'
    Nothing -> liftIO $ do
      addFailedAssertion sym $ GenericSimError $ "Missing file: " ++ (show ident)

writeBytes ::
  (IsSymInterface sym, 1 <= wptr) =>
  GlobalVar (FileSystemType wptr) ->  
  FileHandle sym wptr ->
  V.Vector n (W4.SymBV sym 8) ->
  C.OverrideSim p sym arch r args ret ()
writeBytes fvar fhdl vs = do
  runFileM fvar $ do
    initPtr <- getHandle fhdl
    let
      go ptr v = do
        writeBytePointer ptr v
        nextPointer ptr
    lastPtr <- foldM go initPtr vs
    setHandle fhdl lastPtr

readBytes ::
  (IsSymInterface sym, 1 <= wptr, 1 <= n) =>
  GlobalVar (FileSystemType wptr) ->  
  FileHandle sym wptr ->
  NatRepr n ->
  C.OverrideSim p sym arch r args ret (V.Vector n (W4.SymBV sym 8))  
readBytes fvar fhdl n = do
  Refl <- return $ W4.minusPlusCancel n (knownNat @1)
  runFileM fvar $ do
    initPtr <- getHandle fhdl
    V.generateM (W4.decNat n) $ \n' -> do
      ptr <- addToPointer (W4.intValue n') initPtr
      readBytePointer ptr   

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
nextPointer = addToPointer 1


addToPointer ::
  Integer ->
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (FilePointer sym wptr)
addToPointer i (FilePointer n off) = do
  sym <- getSym
  repr <- getPtrSz   
  one <- liftIO $ W4.bvLit sym repr (BV.mkBV repr i)
  off' <- liftIO $ W4.bvAdd sym off one
  return $ FilePointer n off'


writeBytePointer ::
  FilePointer sym wptr ->
  W4.SymBV sym 8 ->
  FileM p arch r args ret sym wptr ()
writeBytePointer fptr bv = do
  let idx = filePointerIdx fptr
  sym <- getSym
  dataArr <- gets fsSymData
  dataArr' <- liftIO $ CA.writeArray sym idx bv dataArr  
  modify $ \fs -> fs { fsSymData = dataArr' }

readBytePointer ::
  FilePointer sym wptr ->
  FileM p arch r args ret sym wptr (W4.SymBV sym 8)
readBytePointer fptr = do
  sym <- getSym
  let idx = filePointerIdx fptr
  dataArr <- gets fsSymData
  liftIO $ CA.readArray sym idx dataArr

filePointerIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  FileSystemIndex sym wptr
filePointerIdx (FilePointer (File _ n) off) = Ctx.empty :> n :> off

  
_asConcreteIdx ::
  IsSymInterface sym =>
  FilePointer sym wptr ->
  Maybe (Natural, BV.BV wptr)
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
  cn <- W4.asNat n
  return $ ConcreteFile w cn
