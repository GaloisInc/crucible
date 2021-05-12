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
{-# LANGUAGE LambdaCase #-}

module Main where

import           GHC.TypeNats
import           Control.Lens ( (^..), (^.) )

import           Control.Monad (foldM )
import           Control.Monad.IO.Class (liftIO)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.NatRepr as NR


import qualified Data.Sequence as Seq
import qualified Data.ByteString as BS

import qualified Data.BitVector.Sized as BVS

import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Lang.Crucible.Backend.Simple as CB
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.OverrideSim as CSO
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator.GlobalState as CGS

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B
import qualified What4.Config as W4C
import qualified What4.Solver.Yices as W4Y
import qualified What4.Solver.Adapter as WSA
import qualified What4.SatResult as W4R
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
  , T.testCase "Overlapping Symbolic Writes" (runFSTest testOverlappingWritesSingle)
  , T.testCase "Overlapping Symbolic Write Ranges" (runFSTest testOverlappingWritesRange)
  , T.testCase "Unknown File" (runFSTest testUnknownFile)
  , T.testCase "End Of File" (runFSTest testEOF)
  ]

runFSTest :: FSTest wptr -> IO ()
runFSTest fsTest = do
  Some gen <- N.newIONonceGenerator
  sym <- CB.newSimpleBackend W4B.FloatRealRepr gen
  runFSTest' sym fsTest

tobs :: [Integer] -> BS.ByteString
tobs is = BS.pack (map fromIntegral is)

runFSTest' ::
  forall sym wptr t st fs.
  (sym ~ W4B.ExprBuilder t st fs) =>
  CB.IsSymInterface sym =>
  ShowF (W4.SymExpr sym) =>
  sym ->
  FSTest wptr ->
  IO ()
runFSTest' sym (FSTest fsTest) = do
  let config = W4.getConfiguration sym
  W4C.extendConfig W4Y.yicesOptions config
  let
    nRepr = NR.knownNat @wptr

  fs <- SymIO.initFS sym nRepr [] [("test0", tobs [0,1,2]), ("test1", tobs [3,4,5,6])]
  halloc <- CFH.newHandleAllocator
  fsvar <- CC.freshGlobalVar halloc "fileSystem" (SymIO.FileSystemRepr nRepr)
  
  let    
    initCtx = CS.initSimContext sym SymIO.symIOIntrinsicTypes halloc IO.stderr (CSO.fnBindingsFromList []) CS.emptyExtensionImpl ()
    globals = CGS.insertGlobal fsvar fs CS.emptyGlobals
    cont = CS.runOverrideSim CT.UnitRepr (fsTest fsvar)
    initState = CS.InitialState initCtx globals CS.defaultAbortHandler CT.UnitRepr cont

  eres <- CS.executeCrucible [] initState
  case eres of
    CS.TimeoutResult {} -> T.assertFailure "Timed out"
    CS.AbortedResult _ ab -> T.assertFailure $ "Aborted: " ++ showAbortedResult ab
    CS.FinishedResult _ pres -> case pres of
      CS.TotalRes _ -> return ()
      CS.PartialRes _ p _ _ -> case W4.asConstantPred p of
        Just True -> return ()
        _ -> do
          putStrLn $ showF p
          T.assertFailure "Partial Result"
  goals <- CB.proofGoalsToList <$> CB.getProofObligations sym
  mapM_ (proveGoal sym W4Y.yicesAdapter) goals


proveGoal ::
  (sym ~ W4B.ExprBuilder t st fs) =>
  CB.IsSymInterface sym =>
  sym ->
  WSA.SolverAdapter st ->
  CB.ProofGoal (CB.LabeledPred (W4.Pred sym) CB.AssumptionReason) (CB.LabeledPred (W4.Pred sym) CS.SimError) ->
  IO ()
proveGoal sym adapter (CB.ProofGoal asms goal) = do
  let
    asmPreds = asms ^.. traverse . CB.labeledPred 
    goalPred = goal ^. CB.labeledPred 
  notgoal <- W4.notPred sym goalPred
  WSA.solver_adapter_check_sat adapter sym WSA.defaultLogData(notgoal:asmPreds) $ \sr ->
    case sr of
      W4R.Unsat _ -> return ()
      W4R.Unknown -> T.assertFailure "Inconclusive"
      W4R.Sat _ -> do
        mapM_ (\e -> putStrLn $ showF e) asmPreds
        putStrLn (show $ Seq.length asms)
        putStrLn $ showF goalPred
        T.assertFailure "Assertion Failure"

showAbortedResult :: CS.AbortedResult c d -> String
showAbortedResult ar = case ar of
  CS.AbortedExec reason _ -> show reason
  CS.AbortedExit code -> show code
  CS.AbortedBranch _ _ res' res'' -> "BRANCH: " <> showAbortedResult res' <> "\n" <> showAbortedResult res''

data FSTest (wptr :: Nat)   where
  FSTest :: (KnownNat wptr, 1 <= wptr) => (forall sym. (CB.IsSymInterface sym, ShowF (W4.SymExpr sym)) => CS.GlobalVar (SymIO.FileSystemType wptr) -> CS.OverrideSim () sym () (CS.RegEntry sym CT.UnitType) Ctx.EmptyCtx CT.UnitType ()) -> FSTest wptr

readOne ::
  (CB.IsSymInterface sym, 1 <= wptr) =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  SymIO.FileHandle sym wptr ->
  CS.OverrideSim p sym arch r args ret (W4.SymBV sym 8)
readOne fsVar fhdl = do
  mval <- SymIO.readByte' fsVar fhdl
  sym <- CS.getSymInterface
  liftIO $ CB.readPartExpr sym mval (CS.AssertFailureSimError "readOne" "readOne")

readFromChunk ::
  (CB.IsSymInterface sym, 1 <= wptr) =>
  SymIO.DataChunk sym wptr ->
  W4.SymBV sym wptr ->
  CS.OverrideSim p sym arch r args ret (W4.SymBV sym 8)
readFromChunk chunk bv = liftIO $ CA.evalChunk chunk bv

testConcReads :: FSTest 32
testConcReads = FSTest $ \fsVar -> do
  sym <- CS.getSymInterface
  test0_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test0")
  test0FileHandle <- SymIO.openFile' fsVar test0_name
  byte0_0 <- readOne fsVar test0FileHandle
  byte0_1 <- readOne fsVar test0FileHandle

  expect byte0_0 0
  expect byte0_1 1

  test1_name <-  liftIO $  W4.stringLit sym (W4.Char8Literal "test1")
  test1FileHandle <- SymIO.openFile' fsVar test1_name
  zero <- mkbv 0
  one <- mkbv 1
  two <- mkbv 2
  three <- mkbv 3
  
  byte1_0 <- readOne fsVar test1FileHandle
  (chunk_1_1to3, _) <- SymIO.readChunk' fsVar test1FileHandle three

  byte1_1 <- readFromChunk chunk_1_1to3 zero
  byte1_2 <- readFromChunk chunk_1_1to3 one
  byte1_3 <- readFromChunk chunk_1_1to3 two
  
  expect byte1_0 3
  expect byte1_1 4
  expect byte1_2 5
  expect byte1_3 6

  mkCase fsVar "test1" (3, 4, 5, 6)

expect ::
  CB.IsSymInterface sym =>
  KnownNat w =>
  1 <= w =>
  W4.SymBV sym w ->
  Integer ->
  CS.OverrideSim p sym arch r args ret ()
expect bv i = do
  sym <- CS.getSymInterface
  expectIf (return $ W4.truePred sym) bv i

expectIf ::
  CB.IsSymInterface sym =>
  KnownNat w =>
  1 <= w =>
  IO (W4.Pred sym) ->
  W4.SymBV sym w ->
  Integer ->
  CS.OverrideSim p sym arch r args ret ()
expectIf test bv i = do
  test' <- liftIO $ test
  sym <- CS.getSymInterface
  bv' <- liftIO $ W4.bvLit sym W4.knownRepr (BVS.mkBV W4.knownRepr i)
  check <- liftIO $ W4.isEq sym bv bv'
  check' <- liftIO $ W4.impliesPred sym test' check
  liftIO $ CB.assert sym check' (CS.AssertFailureSimError "expect failure" "expect failure")
  return ()

expectOne ::
  forall p sym arch r args ret.
  CB.IsSymInterface sym => W4.SymBV sym 8 -> [Integer] -> CS.OverrideSim p sym arch r args ret ()
expectOne bv is = do
  sym <- CS.getSymInterface
  check <- foldM (\p i -> mkcheck i >>= \p' -> liftIO $ W4.orPred sym p p') (W4.falsePred sym) is
  liftIO $ CB.assert sym check (CS.AssertFailureSimError "expect failure" "expect failure")
  where
    mkcheck :: Integer -> CS.OverrideSim p sym arch r args ret (W4.Pred sym)
    mkcheck i = do
      sym <- CS.getSymInterface
      bv' <- liftIO $ W4.bvLit sym W4.knownRepr (BVS.mkBV W4.knownRepr i)
      liftIO $ W4.isEq sym bv bv'

mkbv ::
  forall wptr p sym arch r args ret.
  CB.IsSymInterface sym =>
  (KnownNat wptr, 1 <= wptr) =>
  Integer ->
  CS.OverrideSim p sym arch r args ret (W4.SymBV sym wptr)
mkbv i = do
  sym <- CS.getSymInterface
  liftIO $ W4.bvLit sym (W4.knownRepr :: W4.NatRepr wptr) (BVS.mkBV W4.knownRepr i)


maybeSeekOne ::
  1 <= wptr =>
  CB.IsSymInterface sym =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  SymIO.FileHandle sym wptr ->
  CS.OverrideSim p sym arch r args ret (W4.Pred sym)
maybeSeekOne fsVar fhdl = do
  sym <- CS.getSymInterface
  b <- liftIO $ W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
  args <- CS.getOverrideArgs
  CS.symbolicBranch b args (SymIO.readByte' fsVar fhdl >> return b) Nothing args (return b) Nothing

-- Nondeterministically seeking, but with a mux join
maybeSeekOne' ::
  forall sym wptr p arch r args ret.
  1 <= wptr =>
  CB.IsSymInterface sym =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  SymIO.FileHandle sym wptr ->
  CS.OverrideSim p sym arch r args ret (W4.Pred sym)
maybeSeekOne' fsVar fhdl = do
  halloc <- CS.simHandleAllocator <$> CS.getContext
  handle <- liftIO $ CFH.mkHandle halloc "maybeSeekOne"
  ov <- return $ CS.mkOverride "maybeSeekOne" (maybeSeekOne fsVar fhdl)
  (b :: CS.RegEntry sym CT.BoolType) <- CS.callOverride handle ov (CS.RegMap Ctx.empty)
  return $ CS.regValue b

neither ::
  CB.IsSymInterface sym =>
  sym ->
  W4.Pred sym ->
  W4.Pred sym ->
  IO (W4.Pred sym)
neither sym p1 p2 = do
  not_p1 <- W4.notPred sym p1
  not_p2 <- W4.notPred sym p2
  W4.andPred sym not_p1 not_p2

testOverlappingWritesSingle :: FSTest 32
testOverlappingWritesSingle = FSTest $ \fsVar -> do
  sym <- CS.getSymInterface
  test1_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test1")
  
  test1FileHandle <- SymIO.openFile' fsVar test1_name
  seek_1 <- maybeSeekOne' fsVar test1FileHandle
  eight <- mkbv 8
  SymIO.writeByte' fsVar test1FileHandle eight

  test1FileHandle2 <- SymIO.openFile' fsVar test1_name
  seek_2 <- maybeSeekOne' fsVar test1FileHandle2
  nine <- mkbv 9
  SymIO.writeByte' fsVar test1FileHandle2 nine

  mkCases2 fsVar "test1" seek_1 seek_2
    (3, 9, 5, 6)
    (9, 8, 5, 6)
    (8, 9, 5, 6)
    (9, 4, 5, 6)
 
  return ()

testOverlappingWritesRange :: FSTest 32
testOverlappingWritesRange = FSTest $ \fsVar -> do
  sym <- CS.getSymInterface
  test1_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test1")
  
  test1FileHandle <- SymIO.openFile' fsVar test1_name
  seek_1 <- maybeSeekOne' fsVar test1FileHandle
  (chunk_8_9, two) <- mkConcreteChunk [8,9]
  
  _ <- SymIO.writeChunk' fsVar test1FileHandle chunk_8_9 two

  mkCases1 fsVar "test1" seek_1
    (3, 8, 9, 6)
    (8, 9, 5, 6)

  test1FileHandle2 <- SymIO.openFile' fsVar test1_name
  (chunk_10_11, _) <- mkConcreteChunk [10,11]
  seek_2 <- maybeSeekOne' fsVar test1FileHandle2
  _ <- SymIO.writeChunk' fsVar test1FileHandle2 chunk_10_11 two
  
  mkCases2 fsVar "test1" seek_1 seek_2
    (3, 10, 11, 6)
    (10, 11, 9, 6)
    (8, 10, 11, 6)
    (10, 11, 5, 6)


testUnknownFile :: FSTest 32
testUnknownFile = FSTest $ \fsVar -> do
  sym <- CS.getSymInterface
  fhdl <- getSomeFile' fsVar
  byte0 <- readOne fsVar fhdl
  byte1 <- readOne fsVar fhdl
  expectOne byte0 [0, 3]
  zero <- mkbv 0
  three <- mkbv 3
  expectIf (W4.isEq sym byte0 zero) byte1 1
  expectIf (W4.isEq sym byte0 three) byte1 4


testEOF :: FSTest 32
testEOF = FSTest $ \fsVar -> do
  sym <- CS.getSymInterface
  let err = CS.AssertFailureSimError "expect EOF" "expect EOF"
  test0_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test0")
  fhdl <- SymIO.openFile' fsVar test0_name
  _ <- readOne fsVar fhdl
  _ <- readOne fsVar fhdl
  _ <- readOne fsVar fhdl
  eof <- SymIO.readByte' fsVar fhdl
  assertNone eof err
  isOpen <- SymIO.isHandleOpen fsVar fhdl
  liftIO $ CB.assert sym isOpen err

  fhdl2 <- SymIO.openFile' fsVar test0_name
  _ <- readOne fsVar fhdl2
  three <- mkbv 3
  zero <- mkbv 0
  one <- mkbv 1

  (chunk_2to3, readBytes) <- SymIO.readChunk' fsVar fhdl2 three
  expect readBytes 2
  byte_2 <- readFromChunk chunk_2to3 zero
  byte_3 <- readFromChunk chunk_2to3 one

  expect byte_2 1
  expect byte_3 2
  (_, readBytes2) <- SymIO.readChunk' fsVar fhdl2 three
  expect readBytes2 0

  isOpen2 <- SymIO.isHandleOpen fsVar fhdl2
  liftIO $ CB.assert sym isOpen2 err
  fhdl3 <- SymIO.openFile' fsVar test0_name
  SymIO.closeFileHandle' fsVar fhdl3
  isOpen3 <- SymIO.isHandleOpen fsVar fhdl3
  assertNot isOpen3 err

  fhdl4 <- SymIO.openFile' fsVar test0_name
  SymIO.writeByte' fsVar fhdl4 =<< mkbv 8
  SymIO.writeByte' fsVar fhdl4 =<< mkbv 9
  SymIO.writeByte' fsVar fhdl4 =<< mkbv 10
  SymIO.writeByte' fsVar fhdl4 =<< mkbv 11
  eof' <- SymIO.readByte' fsVar fhdl4
  assertNone eof' err

  mkCase fsVar "test0" (8, 9, 10, 11)



assertNot ::
  CB.IsSymInterface sym =>
  W4.Pred sym ->
  CS.SimErrorReason ->
  CS.OverrideSim p sym arch r args ret ()
assertNot p er = do
  sym <- CS.getSymInterface
  notp <- liftIO $ W4.notPred sym p
  liftIO $ CB.assert sym notp er

assertNone ::
  CB.IsSymInterface sym =>
  W4.PartExpr (W4.Pred sym) v ->
  CS.SimErrorReason ->
  CS.OverrideSim p sym arch r args ret ()
assertNone pe er = case pe of
  W4.Unassigned -> return ()
  W4.PE p _ -> assertNot p er


getSomeFile ::
  forall sym wptr p arch r args ret.
  1 <= wptr =>
  CB.IsSymInterface sym =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  CS.OverrideSim p sym arch r args ret (SymIO.FileHandle sym wptr)
getSomeFile fsVar = do
  sym <- CS.getSymInterface
  b <- liftIO $ W4.freshConstant sym W4.emptySymbol W4.BaseBoolRepr
  args <- CS.getOverrideArgs
  test0_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test0")
  test1_name <- liftIO $ W4.stringLit sym (W4.Char8Literal "test1")
  
  CS.symbolicBranch b args (SymIO.openFile' fsVar test0_name) Nothing args (SymIO.openFile' fsVar test1_name) Nothing

getSomeFile' ::
  forall sym wptr p arch r args ret.
  1 <= wptr =>
  KnownNat wptr =>
  CB.IsSymInterface sym =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  CS.OverrideSim p sym arch r args ret (SymIO.FileHandle sym wptr)
getSomeFile' fsVar = do
  halloc <- CS.simHandleAllocator <$> CS.getContext
  handle <- liftIO $ CFH.mkHandle halloc "getSomeFile"
  ov <- return $ CS.mkOverride "getSomeFile" (getSomeFile fsVar)
  (b :: CS.RegEntry sym (SymIO.FileHandleType wptr)) <- CS.callOverride handle ov (CS.RegMap Ctx.empty)
  return $ CS.regValue b

mkConcreteChunk ::
  forall sym wptr p arch r args ret.
  KnownNat wptr =>
  1 <= wptr =>
  CB.IsSymInterface sym =>
  [Integer] ->
  CS.OverrideSim p sym arch r args ret (SymIO.DataChunk sym wptr, W4.SymBV sym wptr)
mkConcreteChunk bytes = do
  sym <- CS.getSymInterface
  arr <- liftIO $ W4.freshConstant sym W4.emptySymbol W4.knownRepr
  sz <- mkbv (fromIntegral $ length bytes)
  arr' <- foldM go arr (zip [0..] bytes)
  chunk <- liftIO $ CA.arrayToChunk sym arr'
  return (chunk, sz)
  where
    go ::
      W4.SymArray sym (Ctx.EmptyCtx Ctx.::> W4.BaseBVType wptr) (W4.BaseBVType 8) ->
      (Integer, Integer) ->
      CS.OverrideSim p sym arch r args ret (W4.SymArray sym (Ctx.EmptyCtx Ctx.::> W4.BaseBVType wptr) (W4.BaseBVType 8))
    go arr (idx, val) = do
      idxbv <- mkbv idx
      valbv <- mkbv val
      sym <- CS.getSymInterface
      liftIO $ W4.arrayUpdate sym arr (Ctx.empty Ctx.:> idxbv) valbv

mkCase ::
  forall p sym arch r args ret wptr.
  CB.IsSymInterface sym =>
  1 <= wptr =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  BS.ByteString ->
  (Integer, Integer, Integer, Integer) ->
  CS.OverrideSim p sym arch r args ret ()
mkCase fsVar nm case_ = do
  sym <- CS.getSymInterface
  mkCases1 fsVar nm (W4.truePred sym) case_ case_  

mkCases1 ::
  forall p sym arch r args ret wptr.
  CB.IsSymInterface sym =>
  1 <= wptr =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  BS.ByteString ->
  W4.Pred sym ->
  (Integer, Integer, Integer, Integer) ->
  (Integer, Integer, Integer, Integer) ->
  CS.OverrideSim p sym arch r args ret ()
mkCases1 fsVar nm seek case1 case2 = do
  sym <- CS.getSymInterface
  mkCases2 fsVar nm seek (W4.truePred sym) case1 case1 case2 case2  

mkCases2 ::
  forall p sym arch r args ret wptr.
  CB.IsSymInterface sym =>
  1 <= wptr =>
  CS.GlobalVar (SymIO.FileSystemType wptr) ->
  BS.ByteString ->
  W4.Pred sym ->
  W4.Pred sym ->
  (Integer, Integer, Integer, Integer) ->
  (Integer, Integer, Integer, Integer) ->
  (Integer, Integer, Integer, Integer) ->
  (Integer, Integer, Integer, Integer) ->
  CS.OverrideSim p sym arch r args ret ()
mkCases2 fsVar nm seek_1 seek_2 case1 case2 case3 case4 = do
  sym <- CS.getSymInterface
  name <- liftIO $ W4.stringLit sym (W4.Char8Literal nm)
  fhdl <- SymIO.openFile' fsVar name
  byte1 <- readOne fsVar fhdl
  byte2 <- readOne fsVar fhdl
  byte3 <- readOne fsVar fhdl
  byte4 <- readOne fsVar fhdl
  let
    assertCase ::
      (Integer, Integer, Integer, Integer) ->
      CS.OverrideSim p sym arch r args ret ()
    assertCase (i1, i2, i3, i4) = do
      expect byte1 i1
      expect byte2 i2
      expect byte3 i3
      expect byte4 i4

  args <- CS.getOverrideArgs
  CS.symbolicBranch seek_1 args
   (CS.symbolicBranch seek_2 args (assertCase case1) Nothing
                             args (assertCase case2) Nothing)
   Nothing
   args
   (CS.symbolicBranch seek_2 args (assertCase case3) Nothing
                             args (assertCase case4) Nothing)
   Nothing
    


