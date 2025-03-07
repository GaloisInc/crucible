{-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import Data.List (isInfixOf)

import Test.Hspec
import Test.Tasty
import Test.Tasty.Hspec (testSpec)
import qualified Test.Tasty.HUnit as TTH

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(Some))
import Lang.Crucible.Backend (SomeBackend(..))
import qualified Lang.Crucible.Backend as LCB
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.Panic
import What4.Expr (EmptyExprBuilderState(..))
import What4.Expr.Builder (newExprBuilder)
import qualified What4.Interface as W4I
import What4.FloatMode (FloatModeRepr(FloatIEEERepr))

import qualified Panic as P

main :: IO ()
main =
  defaultMain =<< panicTests

mkBackend :: IO (Some SomeBackend)
mkBackend = do
  Some nonceGen <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState nonceGen
  Some . SomeBackend <$> newSimpleBackend sym

backendTests :: TestTree
backendTests =
  testGroup
  "Backend"
  [ TTH.testCase "push/pop" $ do
      Some (SomeBackend bak) <- mkBackend
      asmps <- LCB.popAssumptionFrame bak =<< LCB.pushAssumptionFrame bak
      p <- LCB.assumptionsPred (LCB.backendGetSym bak) asmps
      Just True TTH.@=? W4I.asConstantPred p
  ]

panicTests :: IO TestTree
panicTests =
  do t <- testSpec "Panicking throws an exception" $
          describe "panic" $
          it "should throw an exception with the right details" $
          shouldThrow (panic "Oh no!" ["line 1", "line 2"]) acceptableExn
     pure $ testGroup "panic" [ t ]
  where
    acceptableExn :: P.Panic Crucible -> Bool
    acceptableExn e =
      let exnMessage = show e
      in isInfixOf "Crucible" exnMessage &&
         isInfixOf "github.com/GaloisInc/crucible/issues" exnMessage
