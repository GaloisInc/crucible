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
import           Data.Maybe

import           Data.Parameterized.Context ( pattern (:>), (!) )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
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

import qualified What4.Serialize.Printer as WP
import qualified What4.Serialize.Parser as WP


import           Prelude


symFnTests :: [TestTree]
symFnTests = [
  testGroup "SymFns" $
    testBasicArguments
    <> testBasicArguments
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


mkEquivalenceTest :: forall m args ret
                   . (MonadTest m, MonadIO m)
                  => Ctx.Assignment BaseTypeRepr args
                  -> (forall sym. WI.IsSymExprBuilder sym => sym -> Ctx.Assignment (WI.SymExpr sym) args -> IO (WI.SymExpr sym ret))
                  -> m ()
mkEquivalenceTest argTs getExpr = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ S.newExprBuilder S.FloatRealRepr NoBuilderData r
  liftIO $ S.startCaching sym
  bvs <- liftIO $ forFC argTs $ \repr -> do
    n <- freshNonce r
    let nm = "bv" ++ show (indexValue n)
    WI.freshBoundVar sym (WI.safeSymbol nm) repr
  expr <- liftIO $ getExpr sym (fmapFC (WI.varExpr sym) bvs)
  fn1 <- liftIO $ WI.definedFn sym (WI.safeSymbol "fn") bvs expr (const False)
  let fnText = WP.printSymFn fn1
  lcfg <- liftIO $ Log.mkLogCfg "rndtrip"
  deser <- liftIO $
              Log.withLogCfg lcfg $
              WP.readSymFn sym Map.empty (\_ _ -> return Nothing) fnText
  debugOut $ "deserialized: " <> showSomeSym deser
  U.SomeSome fn2 <- evalEither deser
  symFnEqualityTest sym fn1 fn2

showSomeSym :: Show a => Either a (U.SomeSome (S.ExprSymFn t)) -> String
showSomeSym (Left a) = "Left (" ++ show a ++ ")"
showSomeSym (Right (U.SomeSome e)) = ("Right (" ++ show e ++ ")")


testRoundTripPrintParse :: [TestTree]
testRoundTripPrintParse =
    [ testProperty "argument type" $
        property $ success
    ]
