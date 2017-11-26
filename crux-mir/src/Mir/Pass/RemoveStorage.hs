{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.RemoveStorage
-- Description      : Rewriting pass for removing Storage annotations
-- Copyright        : (c) Galois, Inc 2017
-- License          : BSD3
-- Stability        : provisional
--
-- This module implements a MIR rewriting pass that eliminates calls
-- to the `StorageLive` and `StorageDead` primtives.
-----------------------------------------------------------------------
module Mir.Pass.RemoveStorage
( passRemoveStorage
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir

import GHC.Stack

-- remove storageDead / storageAlive calls
passRemoveStorage :: [Fn] -> [Fn]
passRemoveStorage fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (prs_ blocks))) fns

prs_ :: [BasicBlock] -> [BasicBlock]
prs_ bbs = map prs bbs

prs :: BasicBlock -> BasicBlock
prs (BasicBlock bbi (BasicBlockData stmts t)) =
    let ns = filter (\stmt -> case stmt of
                    StorageLive _ -> False
                    StorageDead _ -> False
                    _ -> True) stmts in
    (BasicBlock bbi (BasicBlockData ns t))
