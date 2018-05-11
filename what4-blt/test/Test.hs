{-# LANGUAGE FlexibleInstances #-}

module Main where

import Data.Either (isLeft)
import qualified Data.Map.Strict as Map

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import What4.Solver.BLT
import BLT.Binding

main :: IO ()
main = defaultMain suite

suite :: TestTree
suite = testGroup "crucible-blt tests"
  [ testGroup "units"
      [ testCase "parse empty params" test_parse_empty
      , testCase "parse scale param"  test_parse_s
      , testCase "parse prec param"   test_parse_p
      , testCase "empty bounds"       test_bounds0
      , testCase "simple bounds"      test_bounds1
      , testCase "more bounds"        test_bounds2
      , testCase "make canonical bounds" test_bounds3
      ]
  , testGroup "QuickCheck tests"
      [ testProperty "addBLTE commutes"  prop_addBLTE_comm
      , testProperty "addBLTE id"        prop_addBLTE_id
      , testProperty "addBLTE consts"    prop_addBLTE_consts
      , testProperty "addBLTE homogs"    prop_addBLTE_homog
      -- multBLTE
      , testProperty "multBLTE commutes" prop_multBLTE_comm
      , testProperty "multBLTE id"       prop_multBLTE_id
      , testProperty "multBLTE homogs"   prop_multBLTE_homog
      -- normalize
      , testProperty "normalizeLEQ"      prop_normalize
      ]
  ]


------------------------------------------------------------------------
-- Unit Tests
------------------------------------------------------------------------

-- TODO
test_parse_empty, test_parse_s, test_parse_p :: Assertion
test_parse_empty = parseBLTParams "" @?= Right (BLTParams RatID False False)
test_parse_s = parseBLTParams "-s 28" @?= Right (BLTParams (RatFixed 28) False False)
test_parse_p = parseBLTParams "-p 14" @?= Right (BLTParams (RatApprox 14) False False)

test_parse_rubbish :: Assertion
test_parse_rubbish = assertBool "isLeft parseBLTParams rubbish" $
  isLeft (parseBLTParams "foobar 53")

test_bounds0 :: Assertion
test_bounds0 = do
  b <- newHandle bltDefaultParams >>= isCompleteBounds
  assertBool "empty bounds are complete" b

test_bounds1 :: Assertion
test_bounds1 = do
  h <- newHandle bltDefaultParams
  let vars = map BLTVar [0, 1]
      e    = BLTExpr (Map.fromList $ zip vars (repeat 1)) 0

  recordLowerBound h 0 e
  b <- isCompleteBounds h
  assertBool "one bounds are not complete" (not b)

  recordUpperBound h 2 e
  b' <- isCompleteBounds h
  assertBool "one bounds are complete" b'

test_bounds2 :: Assertion
test_bounds2 = do
  h <- newHandle bltDefaultParams
  let vars = map BLTVar [0, 1]
      e1   = BLTExpr (Map.fromList $ zip vars (repeat 1)) 0
      e2   = BLTExpr (Map.fromList $ zip vars (repeat (-3))) 14

  recordLowerBound h 0 e1
  recordUpperBound h 2 e1

  recordLowerBound h 10 e2
  recordUpperBound h 15 e2

  b' <- isCompleteBounds h
  assertBool "two bounds are complete" b'

test_bounds3 :: Assertion
test_bounds3 = do
  h <- newHandle bltDefaultParams
  let v = map BLTVar [0, 1]
      e = BLTExpr (Map.fromList $ zip v [100, 101]) (-2)
      e'= multBLTE (2 :: Int) e

  recordLowerBound h 0 e
  recordUpperBound h 4 e'  -- counts as an upper bound for 'e'
  recordLowerBound h 3 e'  -- redundant

  b' <- isCompleteBounds h
  assertBool "made canonical bounds are complete" b'


------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

instance Arbitrary BLTExpr where
  arbitrary = BLTExpr <$> arbitrary <*> arbitrary
  --shrink (BLTExpr m c) = [ BLTExpr Map.empty c ]
  --                    ++ [ BLTExpr m 0 ]
  --                    ++ [ BLTExpr m' c' | (m', c') <- shrink (m, c) ]

instance Arbitrary BLTVar where
  arbitrary = BLTVar <$> arbitrary

prop_addBLTE_comm :: BLTExpr -> BLTExpr -> Bool
prop_addBLTE_comm x y = addBLTE x y == addBLTE y x

prop_addBLTE_id :: BLTExpr -> Bool
prop_addBLTE_id x = addBLTE x _z == x && addBLTE _z x == x
  where _z = 0 :: Rational

prop_addBLTE_consts :: Rational -> Rational -> Bool
prop_addBLTE_consts r s = isBLTConst $ addBLTE r s

prop_addBLTE_homog :: BLTExpr-> BLTExpr -> Property
prop_addBLTE_homog x y = isBLTHomog x && isBLTHomog y ==> isBLTHomog $ addBLTE x y

prop_multBLTE_comm :: Rational -> BLTExpr -> Bool
prop_multBLTE_comm r b = multBLTE r b == multBLTE b r

prop_multBLTE_id :: BLTExpr -> Bool
prop_multBLTE_id x = multBLTE x _z == x && multBLTE _z x == x
  where _z = 1 :: Rational

prop_multBLTE_homog :: Rational -> BLTExpr -> Property
prop_multBLTE_homog r b = isBLTHomog b ==> isBLTHomog (multBLTE r b)

prop_normalize :: BLTExpr -> BLTExpr -> Property
prop_normalize x y =
  (not . isBLTConst $ x) || (not . isBLTConst $ y) ==>
    (isBLTConst x' && isBLTHomog y' && leadingCoeff y' > 0) ||
    (isBLTHomog x' && leadingCoeff x' > 0 && isBLTConst y')
  where (x', y') = normalizeLEQ x y
