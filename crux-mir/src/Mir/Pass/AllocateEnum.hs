{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.AllocateEnum
-- Description      : Rewriting pass for collapsing redundant reference moves
-- Copyright        : (c) Galois, Inc 2017
-- License          : BSD3
-- Stability        : provisional
--
-- This module implements a MIR rewriting pass that replaces a sequence
-- of enum initializations with an aggregate call.
-----------------------------------------------------------------------
module Mir.Pass.AllocateEnum
( passAllocateEnum
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir

import GHC.Stack

mapTransClosure :: Ord a => Map.Map a a -> Map.Map a a
mapTransClosure m = Map.map (\v -> mapIterate m v) m
    where mapIterate m v = case (Map.lookup v m) of
                             Just g -> mapIterate m g
                             Nothing -> v

passAllocateEnum :: HasCallStack => [Fn] -> [Fn]
passAllocateEnum fns = map (\(Fn a b c (MirBody d blocks) e  f) -> Fn a b c (MirBody d (pcr_ blocks)) e f) fns

pcr_ :: HasCallStack => [BasicBlock] -> [BasicBlock]
pcr_ bs = evalState (pcr bs) (Map.empty)

pcr :: HasCallStack => [BasicBlock] -> [BasicBlock]
pcr bbs = 