{-# LANGUAGE ImportQualifiedPost #-}

module SymSequence (tests) where

import Test.Tasty qualified as TT

import SymSequence.Properties qualified as Properties

tests :: TT.TestTree
tests = Properties.tests
