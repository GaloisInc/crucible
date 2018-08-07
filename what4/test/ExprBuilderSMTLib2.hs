{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Binary.IEEE754 as IEEE754
import           Data.Foldable
import qualified Data.Text as T

import Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce

import What4.BaseTypes
import What4.Expr
import What4.Interface
import What4.InterpretedFloatingPoint
import What4.Protocol.SMTLib2
import What4.SatResult
import What4.Solver.Z3

data State t = State
type SimpleExprBuilder t fs = ExprBuilder t State fs

userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e       -> error $ show e
  Right symbol -> symbol

withSym :: (forall t . SimpleExprBuilder t fs -> IO (BoolExpr t)) -> IO String
withSym pred_gen = withIONonceGenerator $ \gen ->
  show <$> (pred_gen =<< newExprBuilder State gen)

withZ3' :: (forall t . SimpleExprBuilder t fs -> Session t Z3 -> IO a) -> IO a
withZ3' action = withIONonceGenerator $ \nonce_gen -> do
  sym <- newExprBuilder State nonce_gen
  withZ3 sym "z3" putStrLn $ action sym

withModel
  :: Session t Z3
  -> BoolExpr t
  -> ((forall tp . What4.Expr.Expr t tp -> IO (GroundValue tp)) -> IO ())
  -> IO ()
withModel s p action = do
  assume (sessionWriter s) p
  runCheckSat s $ \case
    Sat (GroundEvalFn {..}, _) -> action groundEval
    Unsat                      -> "unsat" @?= "sat"
    Unknown                    -> "unknown" @?= "sat"

-- exists y . (x + 2.0) + (x + 2.0) < y
iFloatTestPred
  :: (  forall t
      . (IsInterpretedFloatExprBuilder (SimpleExprBuilder t fs))
     => SimpleExprBuilder t fs
     -> IO (BoolExpr t)
     )
iFloatTestPred sym = do
  x  <- freshFloatConstant sym (userSymbol' "x") SingleFloatRepr
  e0 <- iFloatLit sym SingleFloatRepr 2.0
  e1 <- iFloatAdd @_ @SingleFloat sym RNE x e0
  e2 <- iFloatAdd @_ @SingleFloat sym RTZ e1 e1
  y  <- freshFloatBoundVar sym (userSymbol' "y") SingleFloatRepr
  e3 <- iFloatLt @_ @SingleFloat sym e2 $ varExpr sym y
  existsPred sym y e3

floatSinglePrecision :: FloatPrecisionRepr (FloatingPointPrecision 8 24)
floatSinglePrecision = knownRepr

floatSingleType :: BaseTypeRepr (BaseFloatType (FloatingPointPrecision 8 24))
floatSingleType = BaseFloatRepr floatSinglePrecision

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
    existsPred sym y e3
  actual @?= expected

testFloatUninterpreted :: TestTree
testFloatUninterpreted = testCase "Float uninterpreted" $ do
  actual   <- withSym $ iFloatTestPred @(Flags FloatUninterpreted)
  expected <- withSym $ \sym -> do
    let bvtp = BaseBVRepr $ knownNat @32
    rne_rm           <- stringLit sym $ T.pack "RNE"
    rtz_rm           <- stringLit sym $ T.pack "RTZ"
    x                <- freshConstant sym (userSymbol' "x") knownRepr
    real_to_float_fn <- freshTotalUninterpFn
      sym
      (userSymbol' "uninterpreted_real_to_float")
      (Ctx.empty Ctx.:> BaseStringRepr Ctx.:> BaseRealRepr)
      bvtp
    e0 <- realLit sym 2.0
    e1 <- applySymFn sym real_to_float_fn $ Ctx.empty Ctx.:> rne_rm Ctx.:> e0
    add_fn <- freshTotalUninterpFn
      sym
      (userSymbol' "uninterpreted_float_add")
      (Ctx.empty Ctx.:> BaseStringRepr Ctx.:> bvtp Ctx.:> bvtp)
      bvtp
    e2    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rne_rm Ctx.:> x Ctx.:> e1
    e3    <- applySymFn sym add_fn $ Ctx.empty Ctx.:> rtz_rm Ctx.:> e2 Ctx.:> e2
    y     <- freshBoundVar sym (userSymbol' "y") knownRepr
    lt_fn <- freshTotalUninterpFn sym
                                  (userSymbol' "uninterpreted_float_lt")
                                  (Ctx.empty Ctx.:> bvtp Ctx.:> bvtp)
                                  BaseBoolRepr
    e4 <- applySymFn sym lt_fn $ Ctx.empty Ctx.:> e3 Ctx.:> varExpr sym y
    existsPred sym y e4
  actual @?= expected

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
    existsPred sym y e3
  actual @?= expected

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
  p4 <- foldlM (andPred sym) (truePred sym) [p0, p1, p2, p3]
  assume (sessionWriter s) p4
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
  ]
