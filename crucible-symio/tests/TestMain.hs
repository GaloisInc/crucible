-----------------------------------------------------------------------
-- |
-- Module           : TestMain
-- Description      : Test module for SymIO
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module Main where

import           GHC.TypeNats

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.NatRepr as NR

import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Data.BitVector.Sized as BVS
import qualified Data.Text as Text

import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Lang.Crucible.Backend.Simple as CB
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.CFG.SSAConversion as CCS
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified What4.Concrete as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Config as W4C
import qualified What4.Solver.Yices as W4Y
import qualified What4.ProgramLoc as W4
import qualified What4.Partial as W4

import qualified What4.CachedArray as CA
import qualified Lang.Crucible.SymIO as SymIO
import qualified Lang.Crucible.SymIO.Types as SymIO

import qualified System.IO as IO

main :: IO ()
main = T.defaultMain fsTests


fsTests :: T.TestTree
fsTests = T.testGroup "Filesystem Tests"
  [ T.testCase "Concrete Reads" (runFSTest testConcReads)
  , T.testCase "Concrete Writes" (runFSTest testConcWrites)
  , T.testCase "Symbolic Reads" (runFSTest testSymReads)
  , T.testCase "Symbolic Writes" (runFSTest testSymWrites)
  ]

runFSTest :: FSTest wptr -> IO ()
runFSTest fsTest = do
  Some gen <- N.newIONonceGenerator
  sym <- CB.newSimpleBackend W4B.FloatRealRepr gen
  runFSTest' gen sym fsTest

runFSTest' ::
  forall sym wptr t.
  CB.IsSymInterface sym =>
  ShowF (W4.SymExpr sym) =>
  N.NonceGenerator IO t ->
  sym ->
  FSTest wptr ->
  IO ()
runFSTest' gen sym fsTest@FSTest{} = do
  let config = W4.getConfiguration sym
  W4C.extendConfig W4Y.yicesOptions config
  let
    nRepr = NR.knownNat @wptr
    ptrRepr = W4.BaseBVRepr nRepr
    bvLit i = W4.bvLit sym nRepr (BVS.mkBV nRepr i)
    concEntry (file, addr, val) = do
      valByte <- W4.bvLit sym (NR.knownNat @8) (BVS.mkBV (NR.knownNat @8) val)
      return $ (Ctx.empty Ctx.:> W4.ConcreteInteger file Ctx.:> W4.ConcreteBV nRepr (BVS.mkBV nRepr addr), valByte)
  
  sizesArr <- W4.freshConstant sym W4.emptySymbol (W4.BaseArrayRepr (Ctx.empty Ctx.:> W4.BaseIntegerRepr) ptrRepr) 
  zero <- W4.intLit sym 0
  one <- W4.intLit sym 1
  twoBV <- bvLit 2
  threeBV <- bvLit 3
  
  
  sizesArr_1 <- W4.arrayUpdate sym sizesArr (Ctx.empty Ctx.:> zero) twoBV
  sizesArr_2 <- W4.arrayUpdate sym sizesArr_1 (Ctx.empty Ctx.:> one) threeBV

  -- start with some concrete file contents
  entries <- Map.fromList <$> mapM concEntry [ (0, 0, 0), (0, 1, 1), (1, 0, 3), (1, 1, 4), (1, 2, 5) ]
  initArray <- CA.initArrayConcrete sym entries
  
  let
    mkFile :: (Text.Text, Integer) -> IO (Text.Text, W4.PartExpr (W4.Pred sym) (SymIO.File sym wptr))
    mkFile (nm, i) = do
        e <- W4.intLit sym i
        return $ (nm, W4.justPartExpr sym (SymIO.File nRepr e))
        
  files <- Map.fromList <$> mapM mkFile [("test0", 0), ("test1", 1)]
  let
    fs = SymIO.FileSystem
           { SymIO.fsPtrSize = nRepr
           , SymIO.fsFileNames = files
           , SymIO.fsFileSizes = sizesArr_2
           , SymIO.fsSymData = initArray
           , SymIO.fsConstraints = id
           }
  halloc <- CFH.newHandleAllocator
  fsvar <- CC.freshGlobalVar halloc "fileSystem" (SymIO.FileSystemRepr nRepr)
  fsOps <- SymIO.initFileSystemOps @wptr halloc

  handle <- CFH.mkHandle halloc "cfg"
  (CCG.SomeCFG cfg', _) <- CCG.defineFunction W4.InternalPos (Some gen) handle (fsTestCrucFun fsOps fsTest)
  CC.SomeCFG cfg <- return $ CCS.toSSA cfg'
  
  let
    binds = SymIO.addFileSystemBindings fsOps fsvar CFH.emptyHandleMap
    
    initCtx = CS.initSimContext sym SymIO.symIOIntrinsicTypes halloc IO.stderr binds CS.emptyExtensionImpl ()
    globals = CGS.insertGlobal fsvar fs CS.emptyGlobals
    cont = CS.runOverrideSim CT.BoolRepr (CS.regValue <$> CS.callCFG cfg (CS.RegMap Ctx.empty))
    initState = CS.InitialState initCtx globals CS.defaultAbortHandler CT.BoolRepr cont

  eres <- CS.executeCrucible [] initState
  (CS.GlobalPair v _globals') <- case eres of
    CS.TimeoutResult {} -> T.assertFailure "Timed out"
    CS.AbortedResult _ ab -> T.assertFailure $ "Aborted: " ++ showAbortedResult ab
    CS.FinishedResult _ pres -> case pres of
      CS.TotalRes gp -> return gp
      CS.PartialRes _ p gp _ -> case W4.asConstantPred p of
        Just True -> return gp
        _ -> T.assertFailure "Partial Result"
  case W4.asConstantPred (CS.regValue v) of
    Just True -> return ()
    Just False -> T.assertFailure "Failed"
    _ -> do
      putStrLn $ showF (CS.regValue v)
      T.assertFailure "Inconclusive"

showAbortedResult :: CS.AbortedResult c d -> String
showAbortedResult ar = case ar of
  CS.AbortedExec reason _ -> show reason
  CS.AbortedExit code -> show code
  CS.AbortedBranch _ _ res' res'' -> "BRANCH: " <> showAbortedResult res' <> "\n" <> showAbortedResult res''

data StoredFS wptr s = StoredFS (SymIO.FileSystemOps wptr)

instance SymIO.HasFileSystem wptr (StoredFS wptr s) where
  getFileSystemOps (StoredFS fsops) = fsops

data FSTest (wptr :: Nat) where
  FSTest :: (KnownNat wptr, 1 <= wptr) => (forall ret s. 
     CCG.Generator () s (StoredFS wptr) ret IO (CCG.Expr () s CT.BoolType)) -> FSTest wptr

fsTestCrucFun ::
  SymIO.FileSystemOps wptr ->
  FSTest wptr ->
  Ctx.Assignment (CCG.Atom s) Ctx.EmptyCtx ->
  (StoredFS wptr s, CCG.Generator () s (StoredFS wptr) ret IO (CCG.Expr () s CT.BoolType))
fsTestCrucFun fsOps (FSTest f) _ = (StoredFS fsOps, f)

testConcReads :: FSTest 32
testConcReads = FSTest $ do
  test0File <- SymIO.resolveFileIdent (CCG.App $ CCE.StringLit "test0")
  test0FileHandle <- SymIO.openFile test0File
  byte0_0 <- SymIO.readByte test0FileHandle
  byte0_1 <- SymIO.readByte test0FileHandle

  let test0Valid = allExpr [expect byte0_0 0, expect byte0_1 1]

  test1File <- SymIO.resolveFileIdent (CCG.App $ CCE.StringLit "test1")
  test1FileHandle <- SymIO.openFile test1File
  byte1_0 <- SymIO.readByte test1FileHandle
  chunk_1_1to2 <- SymIO.readChunk test1FileHandle (mkbv 2)

  byte1_1 <- SymIO.readFromChunk chunk_1_1to2 (mkbv 0)
  byte1_2 <- SymIO.readFromChunk chunk_1_1to2 (mkbv 1)
  let test1Valid = allExpr [expect byte1_0 3, expect byte1_1 4, expect byte1_2 5]
  return $ allExpr [test0Valid, test1Valid]

byte :: Integer -> CCG.Expr ext s (CT.BVType 8)
byte = mkbv @8

mkbv :: forall wptr ext s . (KnownNat wptr, 1 <= wptr) => Integer -> CCG.Expr ext s (CT.BVType wptr)
mkbv i = CCG.App $ CCE.BVLit (W4.knownRepr :: W4.NatRepr wptr) (BVS.mkBV W4.knownRepr i)

mkbasebv :: forall wptr ext s . (KnownNat wptr, 1 <= wptr) => Integer -> CCE.BaseTerm (CCG.Expr ext s) (CT.BaseBVType wptr)
mkbasebv i = CCE.BaseTerm W4.knownRepr (CCG.App $ CCE.BVLit (W4.knownRepr :: W4.NatRepr wptr) (BVS.mkBV W4.knownRepr i))

-- | Inclusive
boundedbv ::
  (KnownNat w, 1 <= w) =>
  (Integer, Integer) ->
  CCG.Generator () s t ret IO (CCG.Atom s (CT.BVType w))
boundedbv (lo, hi) = do
  bv <- CCG.mkFresh W4.knownRepr Nothing
  let
    aboveLo = CCG.App $ CCE.BVUle W4.knownRepr (mkbv lo) (CCG.AtomExpr bv)
    underHi = CCG.App $ CCE.BVUle W4.knownRepr (CCG.AtomExpr bv) (mkbv hi)
  CCG.assumeExpr (allExpr [aboveLo, underHi]) (CCG.App $ CCE.StringLit "bounded")
  return bv

expect :: CCG.Expr ext s (CT.BVType 8) -> Integer -> CCG.Expr ext s CT.BoolType
expect e i = CCG.App (CCE.BaseIsEq W4.knownRepr e (byte i))

allExpr :: [CCG.Expr ext s CT.BoolType] -> CCG.Expr ext s CT.BoolType
allExpr (e : es) = CCG.App $ CCE.And e (allExpr es)
allExpr [] = CCG.App $ CCE.BoolLit True

someExpr :: [CCG.Expr ext s CT.BoolType] -> CCG.Expr ext s CT.BoolType
someExpr (e : es) = CCG.App $ CCE.Or e (allExpr es)
someExpr [] = CCG.App $ CCE.BoolLit False

mkConcreteChunk ::
  (KnownNat wptr, 1 <= wptr) =>
  [Integer] ->
  CCG.Generator () s (StoredFS wptr) ret IO (CCG.Atom s (SymIO.DataChunkType wptr))
mkConcreteChunk bytes = do
  arr <- CCG.mkFresh W4.knownRepr Nothing
  let
    sz = mkbv (fromIntegral $ length bytes)
    arr'' = foldr (\(idx, i) arr' -> CCG.App $ CCE.SymArrayUpdate W4.knownRepr arr' (Ctx.empty Ctx.:> mkbasebv idx) (byte i)) (CCG.AtomExpr arr) (zip [0..] bytes)
  CCG.mkAtom =<< SymIO.arrayToChunk arr'' sz

testConcWrites :: FSTest 32
testConcWrites = FSTest $ do
  test1File <- SymIO.resolveFileIdent (CCG.App $ CCE.StringLit "test1")
  test1FileHandle <- SymIO.openFile test1File
  chunk_8_9 <- mkConcreteChunk [8, 9]
  _ <- SymIO.readByte test1FileHandle
  SymIO.writeChunk test1FileHandle (CCG.AtomExpr chunk_8_9)

  test1FileHandle2 <- SymIO.openFile test1File
  byte1 <- SymIO.readByte test1FileHandle2
  byte2 <- SymIO.readByte test1FileHandle2
  byte3 <- SymIO.readByte test1FileHandle2  
  
  return $ allExpr [expect byte1 3, expect byte2 8, expect byte3 9]

maybeSeekOne ::
  CCG.Expr () s (SymIO.FileHandleType wptr) ->
  CCG.Generator () s (StoredFS wptr) ret IO ()
maybeSeekOne fhdl = do
  b <- CCG.mkFresh W4.BaseBoolRepr Nothing
  CCG.ifte_ (CCG.AtomExpr b) (SymIO.readByte fhdl >> return ()) (return ())

testSymReads :: FSTest 32
testSymReads = FSTest $ do
  test0File <- SymIO.resolveFileIdent (CCG.App $ CCE.StringLit "test0")
  test0FileHandle <- SymIO.openFile test0File
  maybeSeekOne test0FileHandle
  byte0_or_1 <- SymIO.readByte test0FileHandle
  -- FIXME: why does this succeed?
  CCG.assertExpr (CCG.App $ CCE.BoolLit False ) (CCG.App $ CCE.StringLit "false")
  return $ someExpr [expect byte0_or_1 0, expect byte0_or_1 1]


testSymWrites :: FSTest 32
testSymWrites = FSTest $ do
  test1File <- SymIO.resolveFileIdent (CCG.App $ CCE.StringLit "test1")
  test1FileHandle <- SymIO.openFile test1File
  chunk_8_9 <- mkConcreteChunk [8, 9]
  maybeSeekOne test1FileHandle
  SymIO.writeChunk test1FileHandle (CCG.AtomExpr chunk_8_9)

  test1FileHandle2 <- SymIO.openFile test1File
  byte1 <- SymIO.readByte test1FileHandle2
  byte2 <- SymIO.readByte test1FileHandle2
  byte3 <- SymIO.readByte test1FileHandle2
  let
    seekCase = allExpr [expect byte1 3, expect byte2 8, expect byte3 9]
    nonSeekCase = allExpr [expect byte1 8, expect byte2 9, expect byte3 5]
    
  return $ someExpr [seekCase, nonSeekCase]
