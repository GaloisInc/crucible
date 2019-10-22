{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.CollapseRefs
-- Description      : Rewriting pass for collapsing redundant reference moves
-- Copyright        : (c) Galois, Inc 2017
-- License          : BSD3
-- Stability        : provisional
--
-- This module implements a MIR rewriting pass that eliminates move
-- assignments of owened or reference values.  Such moves simply introduce
-- new names for the previous values (while at the same time invalidating
-- the old names for mutable or owned values).  We unwind these renamings
-- so that statements instead refer the the originating value or reference.
-----------------------------------------------------------------------
module Mir.Pass.CollapseRefs
( passCollapseRefs
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir
import Mir.GenericOps

import GHC.Stack

mapTransClosure :: Ord a => Map.Map a a -> Map.Map a a
mapTransClosure m = Map.map (\v -> mapIterate m v) m
    where mapIterate m v = case (Map.lookup v m) of
                             Just g -> mapIterate m g
                             Nothing -> v

passCollapseRefs :: HasCallStack => [Fn] -> [Fn]
passCollapseRefs fns = map (& fbody %~ mblocks %~ pcr_) fns

pcr_ :: HasCallStack => [BasicBlock] -> [BasicBlock]
pcr_ bs = evalState (pcr bs) (Map.empty)

registerStmt :: HasCallStack => Statement -> State (Map.Map Lvalue Lvalue) ()
registerStmt stmt = do
    refmap <- get
    case stmt of
      Assign lv rv _pos ->
          if (Map.notMember lv refmap) then
              case (typeOf lv) of
                  TyRef _ _ ->
                      case rv of
                        Use (Copy lv') ->
                            put $ Map.insert lv lv' refmap
                        Use (Move lv') ->
                            put $ Map.insert lv lv' refmap                            
                        Ref _ l _ -> do
                            put $ Map.insert lv l refmap
                        _ ->
                            do return ()
                  _ -> return ()
          else return ()
      _ -> return ()

pcr :: HasCallStack => [BasicBlock] -> State (Map.Map Lvalue Lvalue) [BasicBlock]
pcr bbs = do
    forM_ bbs $ \(BasicBlock bbi (BasicBlockData stmts term)) ->
        forM_ stmts registerStmt

    refmap <- get
    let refmap_ = mapTransClosure refmap
    return $ replaceList (Map.toList refmap_) bbs

