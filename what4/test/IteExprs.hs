{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : IteExprs test
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This module provides verification of the various bool operations and
ite (if/then/else) operations.  There are a number of simplifications,
subsumptions, and other rewrite rules used for these What4
expressions; this module is intended to verify the correctness of
those.
-}

import           Control.Monad.IO.Class ( liftIO )
import           Data.List ( isInfixOf )
import           Data.Parameterized.Nonce
import           GenWhat4Expr
import           Hedgehog
import qualified Hedgehog.Internal.Gen as IGen
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog
import           What4.Concrete
import           What4.Expr
import           What4.Expr.Builder
import           What4.Interface


data State t fs = State
type IteExprBuilder t fs = ExprBuilder State t fs

withTestSolver :: (forall t. IteExprBuilder t (Flags FloatIEEE DummyAnn) -> IO a) -> IO a
withTestSolver f = withIONonceGenerator $ \nonce_gen ->
  f =<< newExprBuilder FloatIEEERepr State nonce_gen

-- | What branch (arm) is expected from the ITE evaluation?
data ExpITEArm = Then | Else
  deriving Show

type BuiltCond  = String
type ActualCond = String

data ITETestCond = ITETestCond { iteCondDesc :: BuiltCond
                               , expect :: ExpITEArm
                               , cond :: forall sym. (IsExprBuilder sym) => sym -> IO (Pred sym)
                               }

instance IsTestExpr ITETestCond where
  type HaskellTy ITETestCond = ExpITEArm
  desc = iteCondDesc
  testval = expect


instance Show ITETestCond where
  -- Needed for property checking to display failed inputs.
  show itc = "ITETestCond { " <> show (desc itc) <> ", " <> show (expect itc) <> ", condFun = ... }"


type CalcReturn t = IO (Maybe (ConcreteVal t), ConcreteVal t, BuiltCond, ActualCond)


-- | Create an ITE whose type is Bool and return the concrete value,
-- the expected value, and the string description
calcBoolIte :: ITETestCond -> CalcReturn BaseBoolType
calcBoolIte itc =
  withTestSolver $ \sym -> do
  let l = falsePred sym
      r = truePred sym
  c <- cond itc sym
  i <- baseTypeIte sym c l r
  let e = case expect itc of
            Then -> False
            Else -> True
  return (asConcrete i, ConcreteBool e, desc itc, show c)

-- | Create an ITE whose type is Nat and return the concrete value,
-- the expected value, and the string description
calcNatIte :: ITETestCond -> CalcReturn BaseNatType
calcNatIte itc =
  withTestSolver $ \sym -> do
  l <- natLit sym 1
  r <- natLit sym 2
  c <- cond itc sym
  i <- baseTypeIte sym c l r
  let e = case expect itc of
            Then -> 1
            Else -> 2
  return (asConcrete i, ConcreteNat e, desc itc, show c)

-- | Create an ITE whose type is BV and return the concrete value, the
-- expected value, and the string description
calcBVIte :: ITETestCond -> CalcReturn (BaseBVType 16)
calcBVIte itc =
  withTestSolver $ \sym -> do
  let w = knownRepr :: NatRepr 16
  l <- bvLit sym w 12890
  r <- bvLit sym w 8293
  c <- cond itc sym
  i <- baseTypeIte sym c l r
  let e = case expect itc of
            Then -> 12890
            Else -> 8293
  return (asConcrete i, ConcreteBV w e, desc itc, show c)

-- | Given a function that returns a condition, generate ITE's of
-- various types and ensure that the ITE's all choose the same arm to
-- execute.
checkIte :: ITETestCond -> TestTree
checkIte itc =
  let what = desc itc in
  testGroup ("Typed " <> what)
  [
    testCase ("concrete Bool " <> what) $
    do (i,e,_,_) <- calcBoolIte itc
       case i of
         Just v -> v @?= e
         Nothing -> assertBool ("no concrete ITE Bool result for " <> what) False

  , testCase ("concrete Nat " <> what) $
    do (i,e,_,_) <- calcNatIte  itc
       case i of
         Just v -> v @?= e
         Nothing -> assertBool ("no concrete ITE Nat result for " <> what) False

  , testCase ("concrete BV " <> what) $
    do (i,e,_,_) <- calcBVIte  itc
       case i of
         Just v -> v @?= e
         Nothing -> assertBool ("no concrete ITE BV16 result for " <> what) False
  ]


----------------------------------------------------------------------


testConcretePredTrue :: TestTree
testConcretePredTrue = checkIte $ ITETestCond "pred true" Then $ return . truePred

testConcretePredFalse :: TestTree
testConcretePredFalse = checkIte $ ITETestCond "pred false" Else $ return . falsePred

testConcretePredNegation :: TestTree
testConcretePredNegation = testGroup "ConcretePredNegation"
  [
    checkIte $ ITETestCond "not true"  Else $ \sym -> notPred sym (truePred sym)
  , checkIte $ ITETestCond "not false" Then $ \sym -> notPred sym (falsePred sym)
  , checkIte $ ITETestCond "not not true"  Then $ \sym -> notPred sym =<< notPred sym (truePred sym)
  , checkIte $ ITETestCond "not not false" Else $ \sym -> notPred sym =<< notPred sym (falsePred sym)
  ]

testConcretePredOr :: TestTree
testConcretePredOr = testGroup "ConcretePredOr"
  [
    checkIte $ ITETestCond "or true  true"  Then $ \sym -> orPred sym (truePred sym)  (truePred sym)
  , checkIte $ ITETestCond "or true  false" Then $ \sym -> orPred sym (truePred sym)  (falsePred sym)
  , checkIte $ ITETestCond "or false true"  Then $ \sym -> orPred sym (falsePred sym) (truePred sym)
  , checkIte $ ITETestCond "or false false" Else $ \sym -> orPred sym (falsePred sym) (falsePred sym)
  , checkIte $ ITETestCond "or true  (not true)" Then $ \sym -> orPred sym (truePred sym) =<< notPred sym (truePred sym)
  , checkIte $ ITETestCond "or (not false) false" Then $ \sym -> do
      a <- notPred sym (falsePred sym)
      let b = falsePred sym
      orPred sym a b
  -- missing: other 'or' argument negations
  , checkIte $ ITETestCond "not (or false false)" Then $ \sym -> do
      let a = falsePred sym
      let b = falsePred sym
      c <- orPred sym a b
      notPred sym c
  -- missing: other 'or' argument result negations
  ]

testConcretePredAnd :: TestTree
testConcretePredAnd = testGroup "ConcretePredAnd"
  [
    checkIte $ ITETestCond "and true  true"  Then $ \sym -> andPred sym (truePred sym)  (truePred sym)
  , checkIte $ ITETestCond "and true  false" Else $ \sym -> andPred sym (truePred sym)  (falsePred sym)
  , checkIte $ ITETestCond "and false true"  Else $ \sym -> andPred sym (falsePred sym) (truePred sym)
  , checkIte $ ITETestCond "and false false" Else $ \sym -> andPred sym (falsePred sym) (falsePred sym)
  , checkIte $ ITETestCond "and true  (not true)" Else $ \sym -> andPred sym (truePred sym) =<< notPred sym (truePred sym)
  , checkIte $ ITETestCond "and (not false) true" Then $ \sym -> do
      a <- notPred sym (falsePred sym)
      let b = truePred sym
      andPred sym a b
  -- missing: other 'and' argument negations
  , checkIte $ ITETestCond "not (and false true)" Then $ \sym -> do
      let a = falsePred sym
      let b = truePred sym
      c <- andPred sym a b
      notPred sym c
  -- missing: other 'and' argument result negations
  ]

testConcreteEqPred :: TestTree
testConcreteEqPred = testGroup "ConcreteEqPred"
  [
    checkIte $ ITETestCond "equal trues"   Then $ \sym -> eqPred sym (truePred sym)  (truePred sym)
  , checkIte $ ITETestCond "equal falses"  Then $ \sym -> eqPred sym (falsePred sym) (falsePred sym)
  -- missing: other 'eq' argument combinations
  , checkIte $ ITETestCond "not equal"     Else $ \sym -> eqPred sym (truePred sym)  (falsePred sym)
  , checkIte $ ITETestCond "eq right neg"  Then $ \sym -> eqPred sym (falsePred sym) =<< notPred sym (truePred sym)
  , checkIte $ ITETestCond "eq left neq"   Then $ \sym -> do
      a <- notPred sym (falsePred sym)
      let b = truePred sym
      eqPred sym a b
  -- missing: other 'eq' argument negations
  , checkIte $ ITETestCond "not (eq false true)" Then $ \sym -> do
      let a = falsePred sym
      let b = truePred sym
      c <- eqPred sym a b
      notPred sym c
  -- missing: other 'eq' argument result negations
  ]

testConcreteXORPred :: TestTree
testConcreteXORPred = testGroup "ConcreteXORPred"
  [
    checkIte $ ITETestCond "xor trues"     Else $ \sym -> xorPred sym (truePred sym)  (truePred sym)
  , checkIte $ ITETestCond "xor falses"    Else $ \sym -> xorPred sym (falsePred sym) (falsePred sym)
  , checkIte $ ITETestCond "xor t f"       Then $ \sym -> xorPred sym (truePred sym)  (falsePred sym)
    -- missing: other 'xor' argument combinations
  , checkIte $ ITETestCond "xor right neg" Then $ \sym -> xorPred sym (truePred sym) =<< notPred sym (truePred sym)
  , checkIte $ ITETestCond "xor left neq"  Else $ \sym -> do
      a <- notPred sym (falsePred sym)
      let b = truePred sym
      xorPred sym a b
  -- missing: other 'xor' argument negations
  , checkIte $ ITETestCond "not (xor f t)" Else $ \sym -> do
      let a = falsePred sym
      let b = truePred sym
      c <- xorPred sym a b
      notPred sym c
  -- missing: other 'xor' argument result negations
  ]


-- ----------------------------------------------------------------------

genITETestCond :: Monad m => GenT m ITETestCond
genITETestCond = do TE_Bool c <- IGen.filterT isBoolTestExpr genBoolCond
                    return $ ITETestCond (desc c)
                      (if testval c then Then else Else)
                      (predexp c)

----------------------------------------------------------------------


testConcretePredProps :: TestTree
testConcretePredProps = testGroup "generated concrete predicates" $
  let tt n f = testProperty (n <> " mux") $
               -- withConfidence (10^9) $

               -- increase the # of tests because What4 exprs are
               -- complex and so an increased number of tests is
               -- needed to get reasonable coverage.
               withTests 500 $

               property $ do itc <- forAll genITETestCond
                             -- these cover statements just ensure
                             -- that enough tests have been run to see
                             -- most What4 expression elements.
                             cover 2 "and cases" $ "and" `isInfixOf` (desc itc)
                             cover 2 "or cases" $ "or" `isInfixOf` (desc itc)
                             cover 2 "eq cases" $ "eq" `isInfixOf` (desc itc)
                             cover 2 "xor cases" $ "xor" `isInfixOf` (desc itc)
                             cover 2 "not cases" $ "not" `isInfixOf` (desc itc)
                             cover 2 "natEq cases" $ "natEq" `isInfixOf` (desc itc)
                             cover 2 "natLe cases" $ "nat.<=" `isInfixOf` (desc itc)
                             cover 2 "natLt cases" $ "nat.< " `isInfixOf` (desc itc)
                             cover 2 "natAdd cases" $ "nat.+" `isInfixOf` (desc itc)
                             cover 2 "natSub cases" $ "nat.-" `isInfixOf` (desc itc)
                             cover 2 "natMul cases" $ "nat.*" `isInfixOf` (desc itc)
                             cover 2 "natDiv cases" $ "nat./" `isInfixOf` (desc itc)
                             cover 2 "natMod cases" $ "nat.mod" `isInfixOf` (desc itc)
                             cover 2 "natIte cases" $ "nat.?" `isInfixOf` (desc itc)
                             cover 2 "bvCount... cases" $ "bvCount" `isInfixOf` (desc itc)
                             annotateShow itc
                             (i, e, c, ac) <- liftIO $ f itc
                             footnote $ "What4 returns " <> show ac <> " for eval of " <> c
                             i === Just e
  in
  [
    tt "bool" calcBoolIte
  , tt "nat" calcNatIte
  , tt "bv16" calcBVIte
  ]

----------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "Ite Expressions"
  [
    -- Baseline functionality
    testConcretePredTrue
  , testConcretePredFalse
  , testConcretePredNegation
  , testConcretePredAnd
  , testConcretePredOr
  , testConcreteEqPred
  , testConcreteXORPred
  , testConcretePredProps
  ]
