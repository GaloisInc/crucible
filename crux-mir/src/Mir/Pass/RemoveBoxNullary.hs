{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.RemoveBoxNullary
-- Description      : MIR Rewriting pass to remove nullary boxes
-- Copyright        : (c) Galois, Inc 2017
-- License          : BSD3
-- Stability        : provisional
--
-- This module implements a MIR rewriting pass that eliminates all
-- assignments of nullary box operations.  Such operations are necessarily
-- NOPs and can be safely removed.
-----------------------------------------------------------------------
module Mir.Pass.RemoveBoxNullary
( passRemoveBoxNullary
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir

import GHC.Stack

passRemoveBoxNullary :: [Fn] -> [Fn]
passRemoveBoxNullary fns = map (& fbody %~ mblocks %~ map removeBoxNullary) fns

removeBoxNullary :: BasicBlock -> BasicBlock
removeBoxNullary (BasicBlock bbi (BasicBlockData stmts term)) =
    let stmts' = filter (\stmt -> case stmt of
                Assign _ (NullaryOp Box _) _ -> False
                _ -> True) stmts
    in BasicBlock bbi (BasicBlockData stmts' term)

