{-# LANGUAGE FlexibleContexts #-}
module Main ( main ) where

import qualified Test.Tasty as T

import AI
import WTO

main :: IO ()
main = T.defaultMain $ T.testGroup "Abstract Interpretation Tests" [
  wtoTests,
  aiTests
  ]
