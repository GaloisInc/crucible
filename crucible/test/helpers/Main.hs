{-# LANGUAGE AllowAmbiguousTypes #-}
module Main where

import Data.List (isInfixOf)

import Test.Hspec
import Test.Tasty
import Test.Tasty.Hspec (testSpec)

import Lang.Crucible.Panic

import qualified Panic as P

main :: IO ()
main =
  defaultMain =<< panicTests

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
