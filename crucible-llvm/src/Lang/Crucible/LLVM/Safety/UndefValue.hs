-- |
-- Module           : Lang.Crucible.LLVM.Safety.Undef
-- Description      : All about LLVM @undef@ values
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
-- This module is intended to be imported qualified.
--
-- `undef` values are quite strange. See:
-- https://llvm.org/docs/LangRef.html#undefined-values
--
-- This email provides an explanation and motivation for poison and @undef@
-- values: https://lists.llvm.org/pipermail/llvm-dev/2016-October/106182.html
--------------------------------------------------------------------------

{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

module Lang.Crucible.LLVM.Safety.UndefValue
  ( UndefValue(..)
  , standard
  , cite
  , explain
  ) where

import Prelude hiding (unlines)

import Data.Text (Text, unlines, pack)
import Lang.Crucible.LLVM.MemModel.Type (StorageType)

import Lang.Crucible.LLVM.Safety.Standards

data UndefValue sym where
  UndefValue :: Text        -- ^ Where did it come from? e.g. a global var?
             -> StorageType -- ^ What type is it at?
             -> UndefValue sym

standard :: UndefValue sym -> Standard
standard =
  \case
    UndefValue _ _ -> LLVMRef LLVM8


cite :: UndefValue sym -> Text
cite =
  \case
    UndefValue _ _ -> "Undefined Values"

explain :: UndefValue sym -> Text
explain =
  \case
    UndefValue provenance storageType -> unlines $
      [ "Encountered LLVM `undef` value"
      , "Type: " <> pack (show storageType)
      , "From: " <> provenance
      ]
