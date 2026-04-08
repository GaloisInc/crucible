{-# LANGUAGE ImportQualifiedPost #-}

module SymSequence (tests) where

import Test.Tasty qualified as TT

import SymSequence.Properties qualified as Properties
import SymSequence.Reverse qualified as Reverse

tests :: TT.TestTree
tests =
  TT.testGroup "SymSequence"
  [ Properties.tests
  , Reverse.tests
  ]
