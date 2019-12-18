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
{-# LANGUAGE LambdaCase #-}

module SymFnTests where

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Control.Monad ( forM_ )

import           Data.Parameterized.Context ( pattern (:>), (!) )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import qualified Data.Text as T
import qualified Data.Map as Map
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
import qualified What4.Serialize.Normalize as WN

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
        withTests 1 $
        property $ mkEquivalenceTest (Ctx.empty :> BaseIntegerRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let i2 = bvs ! Ctx.i2of2
          WI.intAdd sym i1 i2
    , testProperty "different argument types" $
         withTests 1 $
         property $ mkEquivalenceTest (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i1of2
          let b1 = bvs ! Ctx.i2of2
          WI.baseTypeIte sym b1 i1 i1
    ]


testFunctionCalls :: [TestTree]
testFunctionCalls =
    [ testProperty "no arguments" $
        withTests 1 $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") Ctx.empty BaseBoolRepr
          WI.applySymFn sym ufn Ctx.empty
    , testProperty "two inner arguments" $
        withTests 1 $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    , testProperty "argument passthrough" $
         withTests 1 $
        property $ mkEquivalenceTest (Ctx.empty :> BaseBoolRepr :> BaseIntegerRepr) $ \sym bvs -> do
          let i1 = bvs ! Ctx.i2of2
          let b1 = bvs ! Ctx.i1of2
          ufn <- WI.freshTotalUninterpFn sym (WI.safeSymbol "ufn") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseBoolRepr
          WI.applySymFn sym ufn (Ctx.empty :> i1 :> b1)
    ]

testGlobalReplacement :: [TestTree]
testGlobalReplacement =
    [ testProperty "simple replacement" $
        withTests 1 $
        property $ mkEquivalenceTest' Ctx.empty $ \sym _ -> do
          i1 <- WI.freshConstant sym (WI.safeSymbol "globalInt") BaseIntegerRepr
          return (i1, i1, [("globalInt", Some i1)])
    ,  testProperty "different input and output expression" $
        withTests 1 $
        property $ mkEquivalenceTest' Ctx.empty $ \sym _ -> do
          gi1 <- WI.freshConstant sym (WI.safeSymbol "globalInt1") BaseIntegerRepr
          gi2 <- WI.freshConstant sym (WI.safeSymbol "globalInt2") BaseIntegerRepr
          return (gi1, gi2, [("globalInt1", Some gi2)])
    ]

testExpressions :: [TestTree]
testExpressions =
    [ testProperty "negative ints" $
        withTests 1 $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          WI.intLit sym (-1)
    , testProperty "simple struct" $
        withTests 1 $
        property $ mkEquivalenceTest Ctx.empty $ \sym _ -> do
          i1 <- WI.intLit sym 0
          let b1 = WI.truePred sym
          WI.mkStruct sym (Ctx.empty :> i1 :> b1)
    , testProperty "struct field access" $
        withTests 1 $
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
        withTests 1 $
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

testEnvSigs :: [TestTree]
testEnvSigs =
    [ testProperty "simple sigs" $
        withTests 1 $
        property $ mkSigTest $ \sym -> do
          intbool_int <- WI.freshTotalUninterpFn sym (WI.safeSymbol "intbool_int") (Ctx.empty :> BaseIntegerRepr :> BaseBoolRepr) BaseIntegerRepr
          boolint_bool <- WI.freshTotalUninterpFn sym (WI.safeSymbol "boolint_bool") (Ctx.empty :> BaseBoolRepr :> BaseIntegerRepr) BaseBoolRepr
          return [("intbool_int", U.SomeSome intbool_int), ("boolint_bool", U.SomeSome boolint_bool)]
    ]

-- FIXME: Unclear how to manually create a term that will change under normalization
-- testNormalization :: [TestTree]
-- testNormalization =
--     [ testProperty "normalization involutive" $
--         withTests 1 $
--         property $ do
--             Some r <- liftIO $ newIONonceGenerator
--             sym <- liftIO $ S.newExprBuilder S.FloatRealRepr NoBuilderData r
--             liftIO $ S.startCaching sym
--             i1 <- liftIO $ WI.intLit sym 1
--             i2 <- liftIO $ WI.intLit sym 2
--             expr <- liftIO $ S.sbMakeExpr sym $ S.BaseIte WI.BaseIntegerRepr 1 (WI.truePred sym) i1 i2
--             expr' <- liftIO $ WN.normExpr sym expr
--             (liftIO $ WN.testEquivExpr sym expr expr') >>= \case
--               WN.ExprNormEquivalent -> success
--               WN.ExprEquivalent -> do
--                 debugOut $ "Unexpected real equivalence."
--                 debugOut $ show expr
--                 debugOut $ show expr'
--                 failure
--               WN.ExprUnequal -> do
--                 debugOut $ "Unexpected inequality."
--                 failure
--             (liftIO $ WN.testEquivExpr sym expr' i1) >>= \case
--               WN.ExprEquivalent -> success
--               _ -> do
--                 debugOut $ "Unexpected inexact equality."
--                 failure
--     ]

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
              Log.withLogCfg lcfg $ do
                let pcfg = WP.ParserConfig fenv (\nm -> return $ lookup nm globalLookup) (\_ -> Nothing) sym
                WP.readSymFn pcfg fnText
  debugOut $ "deserialized: " <> showSomeSym deser
  U.SomeSome fn2 <- evalEither deser
  fn1out <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs exprout (const False)
  symFnEqualityTest sym fn1out fn2

showSomeSym :: Show a => Either a (U.SomeSome (S.ExprSymFn t)) -> String
showSomeSym (Left a) = "Left (" ++ show a ++ ")"
showSomeSym (Right (U.SomeSome e)) = ("Right (" ++ show e ++ ")")


symFnEnvTests :: [TestTree]
symFnEnvTests = [
  testGroup "SymFnEnv" $
    testEnvSigs
  ]

mkSigTest :: forall m
           . (MonadTest m, MonadIO m)
          => (forall sym
               . WI.IsSymExprBuilder sym
              => sym
              -> IO [(T.Text, U.SomeSome (WI.SymFn sym))])
          -> m ()
mkSigTest getSymFnEnv = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ S.newExprBuilder S.FloatRealRepr NoBuilderData r
  liftIO $ S.startCaching sym
  fenv1 <- liftIO $ Map.fromList <$> getSymFnEnv sym
  let fenvText = WP.printSymFnEnv fenv1
  lcfg <- liftIO $ Log.mkLogCfg "rndtrip"
  deser <- liftIO $
              Log.withLogCfg lcfg $
              WP.readSymFnEnv (WP.ParserConfig Map.empty (\_ -> return Nothing) (\_ -> Nothing) sym) fenvText
  fenv2 <- evalEither deser
  Map.keysSet fenv1 === Map.keysSet fenv2
  forM_ (Map.assocs fenv1) $ \(key, U.SomeSome fn1) ->
    case Map.lookup key fenv2 of
      Just (U.SomeSome fn2) -> symFnEqualityTest sym fn1 fn2
      _ -> failure
