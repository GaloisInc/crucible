{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty
import Test.Tasty.HUnit


import           Control.Exception (bracket, try, SomeException)
import           Control.Monad (void)
import qualified Data.ByteString as BS
import qualified Data.Binary.IEEE754 as IEEE754
import           Data.Foldable
import qualified Data.Map as Map (empty, singleton)
import           Data.Versions (Version(Version))
import qualified Data.Versions as Versions

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           System.IO

import What4.BaseTypes
import What4.Config
import What4.Expr
import What4.Interface
import What4.InterpretedFloatingPoint
import What4.Protocol.Online
import What4.Protocol.SMTLib2
import What4.SatResult
import What4.Solver.Adapter
import qualified What4.Solver.CVC4 as CVC4
import qualified What4.Solver.Z3 as Z3
import qualified What4.Solver.Yices as Yices
import What4.Utils.StringLiteral

data State t = State
data SomePred = forall t . SomePred (BoolExpr t)
deriving instance Show SomePred
type SimpleExprBuilder t fs = ExprBuilder t State fs


debugOutputFiles :: Bool
debugOutputFiles = False
--debugOutputFiles = True

maybeClose :: Maybe Handle -> IO ()
maybeClose Nothing = return ()
maybeClose (Just h) = hClose h


userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e       -> error $ show e
  Right symbol -> symbol

withSym :: FloatModeRepr fm -> (forall t . SimpleExprBuilder t (Flags fm) -> IO a) -> IO a
withSym floatMode pred_gen = withIONonceGenerator $ \gen ->
  pred_gen =<< newExprBuilder floatMode State gen

withYices :: (forall t. SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t (Yices.Connection t) -> IO ()) -> IO ()
withYices action = withSym FloatRealRepr $ \sym ->
  do extendConfig Yices.yicesOptions (getConfiguration sym)
     bracket
       (do h <- if debugOutputFiles then Just <$> openFile "yices.out" WriteMode else return Nothing
           s <- startSolverProcess Yices.yicesDefaultFeatures h sym
           return (h,s))
       (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s >> maybeClose h))
       (\(_,s) -> action sym s)

withZ3 :: (forall t . SimpleExprBuilder t (Flags FloatIEEE) -> Session t Z3.Z3 -> IO ()) -> IO ()
withZ3 action = withIONonceGenerator $ \nonce_gen -> do
  sym <- newExprBuilder FloatIEEERepr State nonce_gen
  extendConfig Z3.z3Options (getConfiguration sym)
  Z3.withZ3 sym "z3" defaultLogData { logCallbackVerbose = (\_ -> putStrLn) } (action sym)

withOnlineZ3
  :: (forall t . SimpleExprBuilder t (Flags FloatIEEE) -> SolverProcess t (Writer Z3.Z3) -> IO a)
  -> IO a
withOnlineZ3 action = withSym FloatIEEERepr $ \sym -> do
  extendConfig Z3.z3Options (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "z3.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures Z3.Z3) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s >> maybeClose h))
    (\(_,s) -> action sym s)

withCVC4
  :: (forall t . SimpleExprBuilder t (Flags FloatReal) -> SolverProcess t (Writer CVC4.CVC4) -> IO a)
  -> IO a
withCVC4 action = withSym FloatRealRepr $ \sym -> do
  extendConfig CVC4.cvc4Options (getConfiguration sym)
  bracket
    (do h <- if debugOutputFiles then Just <$> openFile "cvc4.out" WriteMode else return Nothing
        s <- startSolverProcess (defaultFeatures CVC4.CVC4) h sym
        return (h,s))
    (\(h,s) -> void $ try @SomeException (shutdownSolverProcess s >> maybeClose h))
    (\(_,s) -> action sym s)

withModel
  :: Session t Z3.Z3
  -> BoolExpr t
  -> ((forall tp . What4.Expr.Expr t tp -> IO (GroundValue tp)) -> IO ())
  -> IO ()
withModel s p action = do
  assume (sessionWriter s) p
  runCheckSat s $ \case
    Sat (GroundEvalFn {..}, _) -> action groundEval
    Unsat _                    -> "unsat" @?= ("sat" :: String)
    Unknown                    -> "unknown" @?= ("sat" :: String)

-- exists y . (x + 2.0) + (x + 2.0) < y
iFloatTestPred
  :: (  forall t
      . (IsInterpretedFloatExprBuilder (SimpleExprBuilder t fs))
     => SimpleExprBuilder t fs
     -> IO SomePred
     )
iFloatTestPred sym = do
  x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
  e0 <- iFloatLit sym SingleFloatRepr 2.0
  e1 <- iFloatAdd @_ @SingleFloat sym RNE x e0
  e2 <- iFloatAdd @_ @SingleFloat sym RTZ e1 e1
  y  <- freshFloatBoundVar sym (userSymbol' "y") SingleFloatRepr
  e3 <- iFloatLt @_ @SingleFloat sym e2 $ varExpr sym y
  SomePred <$> existsPred sym y e3

floatSinglePrecision :: FloatPrecisionRepr Prec32
floatSinglePrecision = knownRepr

floatDoublePrecision :: FloatPrecisionRepr Prec64
floatDoublePrecision = knownRepr

floatSingleType :: BaseTypeRepr (BaseFloatType Prec32)
floatSingleType = BaseFloatRepr floatSinglePrecision

floatDoubleType :: BaseTypeRepr (BaseFloatType Prec64)
floatDoubleType = BaseFloatRepr floatDoublePrecision

testInterpretedFloatReal :: TestTree
testInterpretedFloatReal = testCase "Float interpreted as real" $ do
  actual   <- withSym FloatRealRepr iFloatTestPred
  expected <- withSym FloatRealRepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- realLit sym 2.0
    e1 <- realAdd sym x e0
    e2 <- realAdd sym e1 e1
    y  <- freshBoundVar sym (userSymbol' "y") knownRepr
    e3 <- realLt sym e2 $ varExpr sym y
    SomePred <$> existsPred sym y e3
  show actual @?= show expected

testFloatUninterpreted :: TestTree
testFloatUninterpreted = testCase "Float uninterpreted" $ do
  actual   <- withSym FloatUninterpretedRepr iFloatTestPred
  expected <- withSym FloatUninterpretedRepr $ \sym -> do
    let bvtp = BaseBVRepr $ knownNat @32
    rne_rm           <- natLit sym $ fromIntegral $ fromEnum RNE
    rtz_rm           <- natLit sym $ fromIntegral $ fromEnum RTZ
    x                <- freshConstant sym (userSymbol' "x") knownRepr
    real_to_float_fn <- freshTotalUninterpFn
      sym
      (userSymbol' "uninterpreted_real_to_float")
      (Ctx.empty Ctx.:> BaseNatRepr Ctx.:> BaseRealRepr)
      bvtp
    e0 <- realLit sym 2.0
    e1 <- applySymFn sym real_to_float_fn $ Ctx.empty Ctx.:> rne_rm Ctx.:> e0
    add_fn <- freshTotalUninterpFn
      sym
      (userSymbol' "uninterpreted_float_add")
      (Ctx.empty Ctx.:> BaseNatRepr Ctx.:> bvtp Ctx.:> bvtp)
      bvtp
    e2    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rne_rm Ctx.:> x Ctx.:> e1
    e3    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rtz_rm Ctx.:> e2 Ctx.:> e2
    y     <- freshBoundVar sym (userSymbol' "y") knownRepr
    lt_fn <- freshTotalUninterpFn sym
                                  (userSymbol' "uninterpreted_float_lt")
                                  (Ctx.empty Ctx.:> bvtp Ctx.:> bvtp)
                                  BaseBoolRepr
    e4 <- applySymFn sym lt_fn $ Ctx.empty Ctx.:> e3 Ctx.:> varExpr sym y
    SomePred <$> existsPred sym y e4
  show actual @?= show expected

testInterpretedFloatIEEE :: TestTree
testInterpretedFloatIEEE = testCase "Float interpreted as IEEE float" $ do
  actual   <- withSym FloatIEEERepr iFloatTestPred
  expected <- withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- floatLit sym floatSinglePrecision 2.0
    e1 <- floatAdd sym RNE x e0
    e2 <- floatAdd sym RTZ e1 e1
    y  <- freshBoundVar sym (userSymbol' "y") knownRepr
    e3 <- floatLt sym e2 $ varExpr sym y
    SomePred <$> existsPred sym y e3
  show actual @?= show expected

-- x <= 0.5 && x >= 1.5
testFloatUnsat0 :: TestTree
testFloatUnsat0 = testCase "Unsat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLit sym floatSinglePrecision 0.5
  e1 <- floatLit sym knownRepr 1.5
  p0 <- floatLe sym x e0
  p1 <- floatGe sym x e1
  assume (sessionWriter s) p0
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x * x < 0
testFloatUnsat1 :: TestTree
testFloatUnsat1 = testCase "Unsat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") floatSingleType
  e0 <- floatMul sym RNE x x
  p0 <- floatIsNeg sym e0
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x + y >= x && x != infinity && y > 0 with rounding to +infinity
testFloatUnsat2 :: TestTree
testFloatUnsat2 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") floatSingleType
  y  <- freshConstant sym (userSymbol' "y") knownRepr
  p0 <- notPred sym =<< floatIsInf sym x
  p1 <- floatIsPos sym y
  p2 <- notPred sym =<< floatIsZero sym y
  e0 <- floatAdd sym RTP x y
  p3 <- floatGe sym x e0
  p4 <- foldlM (andPred sym) (truePred sym) [p1, p2, p3]
  assume (sessionWriter s) p4
  runCheckSat s $ \res -> isSat res @? "sat"
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x == 2.5 && y == +infinity
testFloatSat0 :: TestTree
testFloatSat0 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLit sym floatSinglePrecision 2.5
  p0 <- floatEq sym x e0
  y <- freshConstant sym (userSymbol' "y") knownRepr
  e1 <- floatPInf sym floatSinglePrecision
  p1 <- floatEq sym y e1
  p2 <- andPred sym p0 p1
  withModel s p2 $ \groundEval -> do
    (@?=) (toInteger $ IEEE754.floatToWord 2.5) =<< groundEval x
    y_val <- IEEE754.wordToFloat . fromInteger <$> groundEval y
    assertBool ("expected y = +infinity, actual y = " ++ show y_val) $
      isInfinite y_val && 0 < y_val

-- x >= 0.5 && x <= 1.5
testFloatSat1 :: TestTree
testFloatSat1 = testCase "Sat float formula" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatLit sym floatSinglePrecision 0.5
  e1 <- floatLit sym knownRepr 1.5
  p0 <- floatGe sym x e0
  p1 <- floatLe sym x e1
  p2 <- andPred sym p0 p1
  withModel s p2 $ \groundEval -> do
    x_val <- IEEE754.wordToFloat . fromInteger <$> groundEval x
    assertBool ("expected x in [0.5, 1.5], actual x = " ++ show x_val) $
      0.5 <= x_val && x_val <= 1.5

testFloatToBinary :: TestTree
testFloatToBinary = testCase "float to binary" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  y  <- freshConstant sym (userSymbol' "y") knownRepr
  e0 <- floatToBinary sym x
  e1 <- bvAdd sym e0 y
  e2 <- floatFromBinary sym floatSinglePrecision e1
  p0 <- floatNe sym x e2
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isSat res @? "sat"
  p1 <- notPred sym =<< bvIsNonzero sym y
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

testFloatFromBinary :: TestTree
testFloatFromBinary = testCase "float from binary" $ withZ3 $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") knownRepr
  e0 <- floatFromBinary sym floatSinglePrecision x
  e1 <- floatToBinary sym e0
  p0 <- bvNe sym x e1
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isSat res @? "sat"
  p1 <- notPred sym =<< floatIsNaN sym e0
  assume (sessionWriter s) p1
  runCheckSat s $ \res -> isUnsat res @? "unsat"

testFloatBinarySimplification :: TestTree
testFloatBinarySimplification = testCase "float binary simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- floatToBinary sym x
    e1 <- floatFromBinary sym floatSinglePrecision e0
    e1 @?= x

testRealFloatBinarySimplification :: TestTree
testRealFloatBinarySimplification =
  testCase "real float binary simplification" $
    withSym FloatRealRepr $ \sym -> do
      x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
      e0 <- iFloatToBinary sym SingleFloatRepr x
      e1 <- iFloatFromBinary sym SingleFloatRepr e0
      e1 @?= x

testFloatCastSimplification :: TestTree
testFloatCastSimplification = testCase "float cast simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatSingleType
    e0 <- floatCast sym floatDoublePrecision RNE x
    e1 <- floatCast sym floatSinglePrecision RNE e0
    e1 @?= x

testFloatCastNoSimplification :: TestTree
testFloatCastNoSimplification = testCase "float cast no simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatDoubleType
    e0 <- floatCast sym floatSinglePrecision RNE x
    e1 <- floatCast sym floatDoublePrecision RNE e0
    e1 /= x @? ""

testBVSelectShl :: TestTree
testBVSelectShl = testCase "select shl simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvLit sym (knownNat @64) 0
    e1 <- bvConcat sym e0 x
    e2 <- bvShl sym e1 =<< bvLit sym knownRepr 64
    e3 <- bvSelect sym (knownNat @64) (knownNat @64) e2
    e3 @?= x

testBVSelectLshr :: TestTree
testBVSelectLshr = testCase "select lshr simplification" $
  withSym FloatIEEERepr $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvConcat sym x =<< bvLit sym (knownNat @64) 0
    e1 <- bvLshr sym e0 =<< bvLit sym knownRepr 64
    e2 <- bvSelect sym (knownNat @0) (knownNat @64) e1
    e2 @?= x

testUninterpretedFunctionScope :: TestTree
testUninterpretedFunctionScope = testCase "uninterpreted function scope" $
  withOnlineZ3 $ \sym s -> do
    fn <- freshTotalUninterpFn sym (userSymbol' "f") knownRepr BaseIntegerRepr
    x  <- freshConstant sym (userSymbol' "x") BaseIntegerRepr
    y  <- freshConstant sym (userSymbol' "y") BaseIntegerRepr
    e0 <- applySymFn sym fn (Ctx.empty Ctx.:> x)
    e1 <- applySymFn sym fn (Ctx.empty Ctx.:> y)
    p0 <- intEq sym x y
    p1 <- notPred sym =<< intEq sym e0 e1
    p2 <- andPred sym p0 p1
    res1 <- checkSatisfiable s "test" p2
    isUnsat res1 @? "unsat"
    res2 <- checkSatisfiable s "test" p2
    isUnsat res2 @? "unsat"

testBVIteNesting :: TestTree
testBVIteNesting = testCase "nested bitvector ites" $ withZ3 $ \sym s -> do
  bv0 <- bvLit sym (knownNat @32) 0
  let setSymBit bv idx = do
        c1 <- freshConstant sym (userSymbol' ("c1_" ++ show idx)) knownRepr
        c2 <- freshConstant sym (userSymbol' ("c2_" ++ show idx)) knownRepr
        c3 <- freshConstant sym (userSymbol' ("c3_" ++ show idx)) knownRepr
        tt1 <- freshConstant sym (userSymbol' ("tt1_" ++ show idx)) knownRepr
        tt2 <- freshConstant sym (userSymbol' ("tt2_" ++ show idx)) knownRepr
        tt3 <- freshConstant sym (userSymbol' ("tt3_" ++ show idx)) knownRepr
        tt4 <- freshConstant sym (userSymbol' ("tt4_" ++ show idx)) knownRepr
        ite1 <- itePred sym c1 tt1 tt2
        ite2 <- itePred sym c2 tt3 tt4
        ite3 <- itePred sym c3 ite1 ite2
        bvSet sym bv idx ite3
  bv1 <- foldlM setSymBit bv0 [0..31]
  p <- testBitBV sym 0 bv1
  assume (sessionWriter s) p
  runCheckSat s $ \res -> isSat res @? "sat"

testRotate1 :: TestTree
testRotate1 = testCase "rotate test1" $ withOnlineZ3 $ \sym s -> do
  bv <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @32))

  bv1 <- bvRol sym bv =<< bvLit sym knownNat 8
  bv2 <- bvRol sym bv1 =<< bvLit sym knownNat 16
  bv3 <- bvRol sym bv2 =<< bvLit sym knownNat 8
  bv4 <- bvRor sym bv2 =<< bvLit sym knownNat 24
  bv5 <- bvRor sym bv2 =<< bvLit sym knownNat 28

  res <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isUnsat res @? "unsat1"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv4
  isUnsat res1 @? "unsat2"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv5
  isSat res2 @? "sat"

testRotate2 :: TestTree
testRotate2 = testCase "rotate test2" $ withOnlineZ3 $ \sym s -> do
  bv  <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @32))
  amt <- freshConstant sym (userSymbol' "amt") (BaseBVRepr (knownNat @32))

  bv1 <- bvRol sym bv amt
  bv2 <- bvRor sym bv1 amt
  bv3 <- bvRol sym bv =<< bvLit sym knownNat 20

  bv == bv2 @? "syntactic equality"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv2
  isUnsat res1 @? "unsat"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isSat res2 @? "sat"

testRotate3 :: TestTree
testRotate3 = testCase "rotate test3" $ withOnlineZ3 $ \sym s -> do
  bv  <- freshConstant sym (userSymbol' "bv") (BaseBVRepr (knownNat @7))
  amt <- freshConstant sym (userSymbol' "amt") (BaseBVRepr (knownNat @7))

  bv1 <- bvRol sym bv amt
  bv2 <- bvRor sym bv1 amt
  bv3 <- bvRol sym bv =<< bvLit sym knownNat 3

  -- Note, because 7 is not a power of two, this simplification doesn't quite
  -- work out... it would probably be significant work to make it do so.
  -- bv == bv2 @? "syntactic equality"

  res1 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv2
  isUnsat res1 @? "unsat"

  res2 <- checkSatisfiable s "test" =<< notPred sym =<< bvEq sym bv bv3
  isSat res2 @? "sat"

testSymbolPrimeCharZ3 :: TestTree
testSymbolPrimeCharZ3 = testCase "z3 symbol prime (') char" $
  withZ3 $ \sym s -> do
    x <- freshConstant sym (userSymbol' "x'") knownRepr
    y <- freshConstant sym (userSymbol' "y'") knownRepr
    p <- natLt sym x y
    assume (sessionWriter s) p
    runCheckSat s $ \res -> isSat res @? "sat"

expectFailure :: IO a -> IO ()
expectFailure f = try @SomeException f >>= \case
  Left _ -> return ()
  Right _ -> assertFailure "expectFailure"

testBoundVarAsFree :: TestTree
testBoundVarAsFree = testCase "boundvarasfree" $ withOnlineZ3 $ \sym s -> do
  x <- freshBoundVar sym (userSymbol' "x") BaseBoolRepr
  y <- freshBoundVar sym (userSymbol' "y") BaseBoolRepr
  pz <- freshConstant sym (userSymbol' "pz") BaseBoolRepr

  let px = varExpr sym x
  let py = varExpr sym y

  expectFailure $ checkSatisfiable s "test" px
  expectFailure $ checkSatisfiable s "test" py
  checkSatisfiable s "test" pz >>= \res -> isSat res @? "sat"

  inNewFrameWithVars s [Some x] $ do
    checkSatisfiable s "test" px >>= \res -> isSat res @? "sat"
    expectFailure $ checkSatisfiable s "test" py

  -- Outside the scope of inNewFrameWithVars we can no longer
  -- use the bound variable as free
  expectFailure $ checkSatisfiable s "test" px
  expectFailure $ checkSatisfiable s "test" py

zeroTupleTest ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
zeroTupleTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr Ctx.Empty)
       s <- mkStruct sym Ctx.Empty

       f <- freshTotalUninterpFn sym (userSymbol' "f")
             (Ctx.Empty Ctx.:> BaseStructRepr Ctx.Empty)
             BaseBoolRepr

       fu <- applySymFn sym f (Ctx.Empty Ctx.:> u)
       fs <- applySymFn sym f (Ctx.Empty Ctx.:> s)

       p <- eqPred sym fu fs

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isUnsat res2 @? "unsat"

oneTupleTest ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
oneTupleTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr))
       s <- mkStruct sym (Ctx.Empty Ctx.:> backendPred sym False)

       f <- freshTotalUninterpFn sym (userSymbol' "f")
             (Ctx.Empty Ctx.:> BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr))
             BaseBoolRepr

       fu <- applySymFn sym f (Ctx.Empty Ctx.:> u)
       fs <- applySymFn sym f (Ctx.Empty Ctx.:> s)

       p <- eqPred sym fu fs

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isSat res2 @? "neg sat"


pairTest ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
pairTest sym solver =
    do u <- freshConstant sym (userSymbol' "u") (BaseStructRepr (Ctx.Empty Ctx.:> BaseBoolRepr Ctx.:> BaseRealRepr))
       r <- realLit sym 42.0
       s <- mkStruct sym (Ctx.Empty Ctx.:> backendPred sym True Ctx.:> r )

       p <- structEq sym u s

       res1 <- checkSatisfiable solver "test" p
       isSat res1 @? "sat"

       res2 <- checkSatisfiable solver "test" =<< notPred sym p
       isSat res2 @? "neg sat"

stringTest1 ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest1 sym solver =
  do let bsx = "asdf\nasdf"
     let bsz = "qwe\x1crty"
     let bsw = "QQ\"QQ"

     x <- stringLit sym (Char8Literal bsx)
     y <- freshConstant sym (userSymbol' "str") (BaseStringRepr Char8Repr)
     z <- stringLit sym (Char8Literal bsz)
     w <- stringLit sym (Char8Literal bsw)

     s <- stringConcat sym x =<< stringConcat sym y z
     s' <- stringConcat sym s w

     l <- stringLength sym s'

     n <- natLit sym 25
     p <- natEq sym n l

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do Char8Literal slit <- groundEval fn s'
            llit <- groundEval fn n

            (fromIntegral (BS.length slit) == llit) @? "model string length"
            BS.isPrefixOf bsx slit @? "prefix check"
            BS.isSuffixOf (bsz <> bsw) slit @? "suffix check"

       _ -> fail "expected satisfiable model"

     p2 <- natEq sym l =<< natLit sym 20
     checkSatisfiableWithModel solver "test" p2 $ \case
       Unsat () -> return ()
       _ -> fail "expected unsatifiable model"


stringTest2 ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest2 sym solver =
  do let bsx = "asdf\nasdf"
     let bsz = "qwe\x1crty"
     let bsw = "QQ\"QQ"

     q <- freshConstant sym (userSymbol' "q") BaseBoolRepr

     x <- stringLit sym (Char8Literal bsx)
     z <- stringLit sym (Char8Literal bsz)
     w <- stringLit sym (Char8Literal bsw)

     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr Char8Repr)
     b <- freshConstant sym (userSymbol' "strb") (BaseStringRepr Char8Repr)

     ax <- stringConcat sym x a

     zw <- stringIte sym q z w
     bzw <- stringConcat sym b zw

     l <- stringLength sym zw
     n <- natLit sym 7

     p1 <- stringEq sym ax bzw
     p2 <- natLt sym l n
     p  <- andPred sym p1 p2

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do axlit <- groundEval fn ax
            bzwlit <- groundEval fn bzw
            qlit <- groundEval fn q

            qlit == False @? "correct ite"
            axlit == bzwlit @? "equal strings"

       _ -> fail "expected satisfable model"

stringTest3 ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest3 sym solver =
  do let bsz = "qwe\x1crtyQQ\"QQ"
     z <- stringLit sym (Char8Literal bsz)

     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr Char8Repr)
     b <- freshConstant sym (userSymbol' "strb") (BaseStringRepr Char8Repr)
     c <- freshConstant sym (userSymbol' "strc") (BaseStringRepr Char8Repr)

     pfx <- stringIsPrefixOf sym a z
     sfx <- stringIsSuffixOf sym b z

     cnt1 <- stringContains sym z c
     cnt2 <- notPred sym =<< stringContains sym c =<< stringLit sym (Char8Literal "Q")
     cnt3 <- notPred sym =<< stringContains sym c =<< stringLit sym (Char8Literal "q")
     cnt  <- andPred sym cnt1 =<< andPred sym cnt2 cnt3

     lena <- stringLength sym a
     lenb <- stringLength sym b
     lenc <- stringLength sym c

     n <- natLit sym 9

     rnga <- natEq sym lena n
     rngb <- natEq sym lenb n
     rngc <- natEq sym lenc =<< natLit sym 6
     rng  <- andPred sym rnga =<< andPred sym rngb rngc

     p <- andPred sym pfx =<<
          andPred sym sfx =<<
          andPred sym cnt rng

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do alit <- fromChar8Lit <$> groundEval fn a
            blit <- fromChar8Lit <$> groundEval fn b
            clit <- fromChar8Lit <$> groundEval fn c

            alit == (BS.take 9 bsz) @? "correct prefix"
            blit == (BS.drop (BS.length bsz - 9) bsz) @? "correct suffix"
            clit == (BS.take 6 (BS.drop 1 bsz)) @? "correct middle"

       _ -> fail "expected satisfable model"


stringTest4 ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest4 sym solver =
  do let bsx = "str"
     x <- stringLit sym (Char8Literal bsx)
     a <- freshConstant sym (userSymbol' "stra") (BaseStringRepr Char8Repr)
     i <- stringIndexOf sym a x =<< natLit sym 5

     zero <- intLit sym 0
     p <- intLe sym zero i

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
          do alit <- fromChar8Lit <$> groundEval fn a
             ilit <- groundEval fn i

             BS.isPrefixOf bsx (BS.drop (fromIntegral ilit) alit) @? "correct index"
             ilit >= 5 @? "index large enough"

       _ -> fail "expected satisfable model"

     np <- notPred sym p
     lena <- stringLength sym a
     fv <- natLit sym 5
     plen <- natLe sym fv lena
     q <- andPred sym np plen

     checkSatisfiableWithModel solver "test" q $ \case
       Sat fn ->
          do alit <- fromChar8Lit <$> groundEval fn a
             ilit <- groundEval fn i

             not (BS.isInfixOf bsx alit) @? "substring not found"
             ilit == (-1) @? "expected neg one"

       _ -> fail "expected satisfable model"

stringTest5 ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
stringTest5 sym solver =
  do a <- freshConstant sym (userSymbol' "a") (BaseStringRepr Char8Repr)
     off <- freshConstant sym (userSymbol' "off") BaseNatRepr
     len <- freshConstant sym (userSymbol' "len") BaseNatRepr

     n5 <- natLit sym 5
     n20 <- natLit sym 20

     let qlit = "qwerty"

     sub <- stringSubstring sym a off len
     p1 <- stringEq sym sub =<< stringLit sym (Char8Literal qlit)
     p2 <- natLe sym n5 off
     p3 <- natLe sym n20 =<< stringLength sym a

     p <- andPred sym p1 =<< andPred sym p2 p3

     checkSatisfiableWithModel solver "test" p $ \case
       Sat fn ->
         do alit <- fromChar8Lit <$> groundEval fn a
            offlit <- groundEval fn off
            lenlit <- groundEval fn len

            let q = BS.take (fromIntegral lenlit) (BS.drop (fromIntegral offlit) alit)

            q == qlit @? "correct substring"

       _ -> fail "expected satisfable model"


forallTest ::
  OnlineSolver t solver =>
  SimpleExprBuilder t fs ->
  SolverProcess t solver ->
  IO ()
forallTest sym solver =
    do x <- freshConstant sym (userSymbol' "x") BaseBoolRepr
       y <- freshBoundVar sym (userSymbol' "y") BaseBoolRepr
       p <- forallPred sym y =<< orPred sym x (varExpr sym y)
       np <- notPred sym p

       checkSatisfiableWithModel solver "test" p $ \case
         Sat fn ->
           do b <- groundEval fn x
              (b == True) @? "true result"

         _ -> fail "expected satisfible model"

       checkSatisfiableWithModel solver "test" np $ \case
         Sat fn ->
           do b <- groundEval fn x
              (b == False) @? "false result"

         _ -> fail "expected satisfible model"

-- | These tests simply ensure that no exceptions are raised.
testSolverInfo :: TestTree
testSolverInfo = testGroup "solver info queries" $
  [ testCase "test get solver version" $ withOnlineZ3 $ \_ proc -> do
      let conn = solverConn proc
      getVersion conn
      _ <- versionResult conn (solverResponse proc)
      pure ()
  , testCase "test get solver name" $ withOnlineZ3 $ \_ proc -> do
      let conn = solverConn proc
      getName conn
      nm <- nameResult conn (solverResponse proc)
      nm @?= "Z3"
  ]

testSolverVersion :: TestTree
testSolverVersion = testCase "test solver version bounds" $
  withOnlineZ3 $ \_ proc -> do
    let v = Version { _vEpoch = Nothing
                    , _vChunks = [[Versions.Digits 0]]
                    , _vRel = [] }
    checkSolverVersion' (Map.singleton "Z3" v) Map.empty proc >> return ()

main :: IO ()
main = defaultMain $ testGroup "Tests"
  [ testInterpretedFloatReal
  , testFloatUninterpreted
  , testInterpretedFloatIEEE
  , testFloatUnsat0
  , testFloatUnsat1
  , testFloatUnsat2
  , testFloatSat0
  , testFloatSat1
  , testFloatToBinary
  , testFloatFromBinary
  , testFloatBinarySimplification
  , testRealFloatBinarySimplification
  , testFloatCastSimplification
  , testFloatCastNoSimplification
  , testBVSelectShl
  , testBVSelectLshr
  , testUninterpretedFunctionScope
  , testBVIteNesting
  , testRotate1
  , testRotate2
  , testRotate3
  , testSymbolPrimeCharZ3
  , testBoundVarAsFree
  , testSolverInfo
  , testSolverVersion

  , testCase "Yices 0-tuple" $ withYices zeroTupleTest
  , testCase "Yices 1-tuple" $ withYices oneTupleTest
  , testCase "Yices pair"    $ withYices pairTest

  , testCase "Z3 0-tuple" $ withOnlineZ3 zeroTupleTest
  , testCase "Z3 1-tuple" $ withOnlineZ3 oneTupleTest
  , testCase "Z3 pair"    $ withOnlineZ3 pairTest

  -- TODO, enable this test when we figure out why it
  -- doesnt work...
  --  , testCase "CVC4 0-tuple" $ withCVC4 zeroTupleTest
  , testCase "CVC4 1-tuple" $ withCVC4 oneTupleTest
  , testCase "CVC4 pair"    $ withCVC4 pairTest

  , testCase "Z3 forall binder" $ withOnlineZ3 forallTest
  , testCase "CVC4 forall binder" $ withCVC4 forallTest

  , testCase "Z3 string1" $ withOnlineZ3 stringTest1
  , testCase "Z3 string2" $ withOnlineZ3 stringTest2
  , testCase "Z3 string3" $ withOnlineZ3 stringTest3
  , testCase "Z3 string4" $ withOnlineZ3 stringTest4
  , testCase "Z3 string5" $ withOnlineZ3 stringTest5

  , testCase "CVC4 string1" $ withCVC4 stringTest1
  , testCase "CVC4 string2" $ withCVC4 stringTest2
  , testCase "CVC4 string3" $ withCVC4 stringTest3
  , testCase "CVC4 string4" $ withCVC4 stringTest4
  , testCase "CVC4 string5" $ withCVC4 stringTest5
  ]
