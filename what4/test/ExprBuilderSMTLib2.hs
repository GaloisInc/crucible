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

import           Control.Monad (void)
import qualified Data.Binary.IEEE754 as IEEE754
import           Data.Foldable
import qualified Data.Map as Map (empty, singleton)
import           Data.Versions (Version(Version))
import qualified Data.Versions as Versions

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce

import What4.BaseTypes
import What4.Config
import What4.Expr
import What4.Interface
import What4.InterpretedFloatingPoint
import What4.Protocol.Online
import What4.Protocol.SMTLib2
import What4.SatResult
import What4.Solver.Adapter
import What4.Solver.Z3

data State t = State
data SomePred = forall t . SomePred (BoolExpr t)
deriving instance Show SomePred
type SimpleExprBuilder t fs = ExprBuilder t State fs

userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e       -> error $ show e
  Right symbol -> symbol

withSym :: (forall t . SimpleExprBuilder t fs -> IO a) -> IO a
withSym pred_gen = withIONonceGenerator $ \gen ->
  pred_gen =<< newExprBuilder State gen

withZ3' :: (forall t . SimpleExprBuilder t fs -> Session t Z3 -> IO ()) -> IO ()
withZ3' action = withIONonceGenerator $ \nonce_gen -> do
  sym <- newExprBuilder State nonce_gen
  extendConfig z3Options (getConfiguration sym)
  withZ3 sym "z3" defaultLogData { logCallbackVerbose = (\_ -> putStrLn) } (action sym)

withOnlineZ3'
  :: (forall t . SimpleExprBuilder t fs -> SolverProcess t (Writer Z3) -> IO a)
  -> IO a
withOnlineZ3' action = withSym $ \sym -> do
  extendConfig z3Options (getConfiguration sym)
  s <- startSolverProcess (defaultFeatures Z3) Nothing sym
  res <- action sym s
  void (shutdownSolverProcess s)
  return res

withModel
  :: Session t Z3
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
  actual   <- withSym $ iFloatTestPred @(Flags FloatReal)
  expected <- withSym $ \sym -> do
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
  actual   <- withSym $ iFloatTestPred @(Flags FloatUninterpreted)
  expected <- withSym $ \sym -> do
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
  actual   <- withSym $ iFloatTestPred @(Flags FloatIEEE)
  expected <- withSym $ \sym -> do
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
testFloatUnsat0 = testCase "Unsat float formula" $ withZ3' $ \sym s -> do
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
testFloatUnsat1 = testCase "Unsat float formula" $ withZ3' $ \sym s -> do
  x  <- freshConstant sym (userSymbol' "x") floatSingleType
  e0 <- floatMul sym RNE x x
  p0 <- floatIsNeg sym e0
  assume (sessionWriter s) p0
  runCheckSat s $ \res -> isUnsat res @? "unsat"

-- x + y >= x && x != infinity && y > 0 with rounding to +infinity
testFloatUnsat2 :: TestTree
testFloatUnsat2 = testCase "Sat float formula" $ withZ3' $ \sym s -> do
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
testFloatSat0 = testCase "Sat float formula" $ withZ3' $ \sym s -> do
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
testFloatSat1 = testCase "Sat float formula" $ withZ3' $ \sym s -> do
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
testFloatToBinary = testCase "float to binary" $ withZ3' $ \sym s -> do
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
testFloatFromBinary = testCase "float from binary" $ withZ3' $ \sym s -> do
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
  withSym $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- floatToBinary sym x
    e1 <- floatFromBinary sym floatSinglePrecision e0
    e1 @?= x

testRealFloatBinarySimplification :: TestTree
testRealFloatBinarySimplification =
  testCase "real float binary simplification" $
    withSym $ \(sym :: SimpleExprBuilder t (Flags FloatReal)) -> do
      x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
      e0 <- iFloatToBinary sym SingleFloatRepr x
      e1 <- iFloatFromBinary sym SingleFloatRepr e0
      e1 @?= x

testFloatCastSimplification :: TestTree
testFloatCastSimplification = testCase "float cast simplification" $
  withSym $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatSingleType
    e0 <- floatCast sym floatDoublePrecision RNE x
    e1 <- floatCast sym floatSinglePrecision RNE e0
    e1 @?= x

testFloatCastNoSimplification :: TestTree
testFloatCastNoSimplification = testCase "float cast no simplification" $
  withSym $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") floatDoubleType
    e0 <- floatCast sym floatSinglePrecision RNE x
    e1 <- floatCast sym floatDoublePrecision RNE e0
    e1 /= x @? ""

testBVSelectShl :: TestTree
testBVSelectShl = testCase "select shl simplification" $
  withSym $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvLit sym (knownNat @64) 0
    e1 <- bvConcat sym e0 x
    e2 <- bvShl sym e1 =<< bvLit sym knownRepr 64
    e3 <- bvSelect sym (knownNat @64) (knownNat @64) e2
    e3 @?= x

testBVSelectLshr :: TestTree
testBVSelectLshr = testCase "select lshr simplification" $
  withSym $ \sym -> do
    x  <- freshConstant sym (userSymbol' "x") knownRepr
    e0 <- bvConcat sym x =<< bvLit sym (knownNat @64) 0
    e1 <- bvLshr sym e0 =<< bvLit sym knownRepr 64
    e2 <- bvSelect sym (knownNat @0) (knownNat @64) e1
    e2 @?= x

testUninterpretedFunctionScope :: TestTree
testUninterpretedFunctionScope = testCase "uninterpreted function scope" $
  withOnlineZ3' $ \sym s -> do
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
testBVIteNesting = testCase "nested bitvector ites" $ withZ3' $ \sym s -> do
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
testRotate1 = testCase "rotate test1" $ withOnlineZ3' $ \sym s -> do
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
testRotate2 = testCase "rotate test2" $ withOnlineZ3' $ \sym s -> do
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
testRotate3 = testCase "rotate test3" $ withOnlineZ3' $ \sym s -> do
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
  withZ3' $ \sym s -> do
    x <- freshConstant sym (userSymbol' "x'") knownRepr
    y <- freshConstant sym (userSymbol' "y'") knownRepr
    p <- natLt sym x y
    assume (sessionWriter s) p
    runCheckSat s $ \res -> isSat res @? "sat"

-- | These tests simply ensure that no exceptions are raised.
testSolverInfo :: TestTree
testSolverInfo = testGroup "solver info queries" $
  [ testCase "test get solver version" $ withOnlineZ3' $ \_ proc -> do
      let conn = solverConn proc
      getVersion conn
      _ <- versionResult conn (solverResponse proc)
      pure ()
  , testCase "test get solver name" $ withOnlineZ3' $ \_ proc -> do
      let conn = solverConn proc
      getName conn
      nm <- nameResult conn (solverResponse proc)
      nm @?= "Z3"
  ]

testSolverVersion :: TestTree
testSolverVersion = testCase "test solver version bounds" $
  withOnlineZ3' $ \_ proc -> do
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
  , testSolverInfo
  , testSolverVersion

  ]
