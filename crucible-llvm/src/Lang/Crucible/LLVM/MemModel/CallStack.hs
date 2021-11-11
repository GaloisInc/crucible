------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.CallStack
-- Description      : Call stacks from the LLVM memory model
-- Copyright        : (c) Galois, Inc 2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.LLVM.MemModel.CallStack
  ( CallStack
  , getCallStack
  , ppCallStack
  ) where

import           Data.Foldable (toList)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Prettyprinter as PP

import           Lang.Crucible.LLVM.MemModel.MemLog (MemState(..))

newtype FunctionName =
  FunctionName { getFunctionName :: Text }
  deriving (Eq, Monoid, Ord, Semigroup)

newtype CallStack =
  CallStack { runCallStack :: Seq FunctionName }
  deriving (Eq, Monoid, Ord, Semigroup)

cons :: FunctionName -> CallStack -> CallStack
cons top (CallStack rest) = CallStack (top Seq.<| rest)

getCallStack :: MemState sym -> CallStack
getCallStack =
  \case
    EmptyMem{} -> CallStack mempty
    StackFrame _ _ nm _ rest -> cons (FunctionName nm) (getCallStack rest)
    BranchFrame _ _ _ rest -> getCallStack rest

ppCallStack :: CallStack -> PP.Doc ann
ppCallStack =
  PP.vsep . toList . fmap (PP.pretty . getFunctionName) . runCallStack
