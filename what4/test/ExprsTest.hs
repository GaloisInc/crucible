{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

{-|
Module      : ExprsTest test
Copyright   : (c) Galois Inc, 2020
License     : BSD3
Maintainer  : kquick@galois.com

This module provides some verification of selected What4 Expressions.
There are a number of simplifications, subsumptions, and other rewrite
rules used for these What4 expressions; this module is intended to
verify the correctness of those.
-}

import           Control.Monad.IO.Class ( liftIO )
import           Data.Bits
import           Data.Parameterized.Nonce
import           GenWhat4Expr
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.Hedgehog
import           What4.Concrete
import           What4.Expr
import           What4.Interface


data State t fs = State
type IteExprBuilder t fs = ExprBuilder State t fs
data DummyAnn (tp :: BaseType)

withTestSolver :: (forall t. IteExprBuilder t (Flags FloatIEEE DummyAnn) -> IO a) -> IO a
withTestSolver f = withIONonceGenerator $ \nonce_gen ->
  f =<< newExprBuilder FloatIEEERepr State nonce_gen


-- | Test natDiv and natMod properties described at their declaration
-- site in What4.Interface
testNatDivModProps :: TestTree
testNatDivModProps =
  testProperty "d <- natDiv sym x y; m <- natMod sym x y ===> y * d + m == x and m < y" $
  property $ do
    xn <- forAll $ Gen.integral $ Range.linear 0 1000
    yn <- forAll $ Gen.integral $ Range.linear 1 2000  -- no zero; avoid div-by-zero
    dm <- liftIO $ withTestSolver $ \sym -> do
      x <- natLit sym xn
      y <- natLit sym yn
      d <- natDiv sym x y
      m <- natMod sym x y
      return (asConcrete d, asConcrete m)
    case dm of
      (Just dnc, Just mnc) -> do
        let dn = fromConcreteNat dnc
        let mn = fromConcreteNat mnc
        annotateShow (xn, yn, dn, mn)
        yn * dn + mn === xn
        diff mn (<) yn
      _ -> failure


testBvIsNeg :: TestTree
testBvIsNeg = testGroup "bvIsNeg"
  [
    -- bvLit value is an Integer; the Integer itself is signed.
    -- Verify that signed Integers count as negative values.

    testCase "-1.32 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) ((-1) .&. allbits32)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "-1 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) (-1)
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

    -- Check a couple of corner cases

  , testCase "0xffffffff bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) allbits32
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "0x80000000 bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) 0x80000000
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) @=? r

  , testCase "0x7fffffff !bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) 0x7fffffff
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) @=? r

  , testCase "0 !bvIsNeg.32" $ do
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) 0
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) @=? r

  , testProperty "bvIsNeg.32" $ property $ do
      i <- forAll $ Gen.integral $ Range.linear (-10) (-1)
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) i
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool True) === r

  , testProperty "!bvIsNeg.32" $ property $ do
      i <- forAll $ Gen.integral $ Range.linear 0 10
      r <- liftIO $ withTestSolver $ \sym -> do
        v <- bvLit sym (knownRepr :: NatRepr 32) i
        asConcrete <$> bvIsNeg sym v
      Just (ConcreteBool False) === r
  ]

----------------------------------------------------------------------

main :: IO ()
main = defaultMain $ testGroup "What4 Expressions"
  [
    testNatDivModProps
  , testBvIsNeg
  ]
