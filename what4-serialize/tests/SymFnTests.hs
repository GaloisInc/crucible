{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module SymFnTests where

import           Control.Monad.IO.Class ( MonadIO, liftIO )

import           Data.Parameterized.Context ( pattern (:>), (!) )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import qualified Data.Text as T
import           Hedgehog

import qualified What4.Utils.Log as Log
import           Test.Tasty
-- import           Test.Tasty.HUnit ( assertEqual, testCase, (@?=) )
import           Test.Tasty.Hedgehog
import           TestUtils
import qualified What4.Expr.Builder as S
import           What4.BaseTypes
import qualified What4.Interface as WI -- ( getConfiguration )
import qualified What4.Utils.Util as U

import qualified What4.Serialize.Printer as WP
import qualified What4.Serialize.Parser as WP


import           Prelude


symFnTests :: [TestTree]
symFnTests = [
  testGroup "SymFns" $
    testBasicArguments
    <> testFunctionCalls
    <> testGlobalReplacement
    <> testExpressions
  ]

data BuilderData t = NoBuilderData

testBasicArguments :: [TestTree]
testBasicArguments =
    [ testProperty "same argument type" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseIntegerRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let i2 = bvs ! Ctx.i2of2
          WI.intAdd sym i1 i2
    , testProperty "different argument types" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let b1 = bvs ! Ctx.i2of2
          WI.baseTypeIte sym b1 i1 i1
    ]


testFunctionCalls :: [TestTree]
testFunctionCalls =
    [ testProperty "no arguments" $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") Ctx.empty BaseBoolRepr
          WI.applySymFn sym ufn Ctx.empty
    , testProperty "two inner arguments" $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    , testProperty "argument passthrough" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseBoolRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i2of2
          let b1 = bvs ! Ctx.i1of2
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    ]

testGlobalReplacement :: [TestTree]
testGlobalReplacement =
    [ testProperty "simple replacement" $
        property $ mkEquivalenceTest' Ctx.empty $ \sym _ -> do
          i1 <- WI.freshConstant sym (WI.safeSymbol "globalInt") BaseIntegerRepr
          return (i1, i1, [("globalInt", Some i1)])
    ,  testProperty "different input and output expression" $
        property $ mkEquivalenceTest' Ctx.empty $ \sym _ -> do
          gi1 <- WI.freshConstant sym (WI.safeSymbol "globalInt1") BaseIntegerRepr
          gi2 <- WI.freshConstant sym (WI.safeSymbol "globalInt2") BaseIntegerRepr
          return (gi1, gi2, [("globalInt1", Some gi2)])
    ]

testExpressions :: [TestTree]
testExpressions =
    [ testProperty "negative ints" $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          WI.intLit sym (-1)
    , testProperty "simple struct" $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          WI.mkStruct sym (Ctx.empty :> i1 :> b1)
    , testProperty "struct field access" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseStructRepr (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr)) $ \sym bvs -> do
          let struct = bvs ! Ctx.baseIndex
          i1 <- WI.structField sym struct Ctx.i1of2
          b1 <- WI.structField sym struct Ctx.i2of2
          WI.mkStruct sym (Ctx.empty :> b1 :> i1)
    --, testProperty "simple constant array" $
    --    property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
    --      i1 <- WI.intLit sym 1
    --      WI.constantArray sym (Ctx.empty :> BaseIntegerRepr) i1
    , testProperty "array update" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseArrayRepr (Ctx.empty :> BaseIntegerRepr) BaseIntegerRepr) $ \sym bvs -> do
          i1 <- WI.intLit sym 1
          i2 <- WI.intLit sym 2
          let arr = bvs ! Ctx.baseIndex
          WI.arrayUpdate sym arr (Ctx.empty :> i1) i2
    , testProperty "integer to bitvector" $
        property $ mkEquivalenceTest (Ctx.empty :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.baseIndex
          WI.integerToBV sym i1 (WI.knownNat @32)
    ]

mkEquivalenceTest :: forall m args ret
                   . (MonadTest m, MonadIO m)
                  => Ctx.Assignment BaseTypeRepr args
                  -> (forall sym
                       . WI.IsSymExprBuilder sym
                      => sym
                      -> Ctx.Assignment (WI.SymExpr sym) args
                      -> IO (WI.SymExpr sym ret))
                  -> m ()
mkEquivalenceTest argTs getExpr = mkEquivalenceTest' argTs $ \sym args -> do
  expr <- getExpr sym args
  return (expr, expr, [])


mkEquivalenceTest' :: forall m args ret
                   . (MonadTest m, MonadIO m)
                  => Ctx.Assignment BaseTypeRepr args
                  -> (forall sym
                       . WI.IsSymExprBuilder sym
                      => sym
                      -> Ctx.Assignment (WI.SymExpr sym) args
                      -> IO (WI.SymExpr sym ret, WI.SymExpr sym ret, [(T.Text, Some (S.SymExpr sym))]))
                  -> m ()
mkEquivalenceTest' argTs getExpr = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ S.newExprBuilder S.FloatRealRepr NoBuilderData r
  liftIO $ S.startCaching sym
  bvs <- liftIO $ forFC argTs $ \repr -> do
    n <- freshNonce r
    let nm = "bv" ++ show (indexValue n)
    WI.freshBoundVar sym (WI.safeSymbol nm) repr
  (exprin, exprout, globalLookup) <- liftIO $ getExpr sym (fmapFC (WI.varExpr sym) bvs)
  fn1 <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs exprin (const False)
  let (fnText, fenv) = WP.printSymFn' fn1
  lcfg <- liftIO $ Log.mkLogCfg "rndtrip"
  deser <- liftIO $
              Log.withLogCfg lcfg $
              WP.readSymFn sym fenv (\_ nm -> return $ lookup nm globalLookup) fnText
  debugOut $ "deserialized: " <> showSomeSym deser
  U.SomeSome fn2 <- evalEither deser
  fn1out <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs exprout (const False)
  symFnEqualityTest sym fn1out fn2

showSomeSym :: Show a => Either a (U.SomeSome (S.ExprSymFn t)) -> String
showSomeSym (Left a) = "Left (" ++ show a ++ ")"
showSomeSym (Right (U.SomeSome e)) = ("Right (" ++ show e ++ ")")


testRoundTripPrintParse :: [TestTree]
testRoundTripPrintParse =
    [ testProperty "argument type" $
        property $ success
    ]
