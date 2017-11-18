{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass.CollapseRefs
( passCollapseRefs
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir
import Mir.Pass

import GHC.Stack

mapTransClosure :: Ord a => Map.Map a a -> Map.Map a a
mapTransClosure m = Map.map (\v -> mapIterate m v) m
    where mapIterate m v = case (Map.lookup v m) of
                             Just g -> mapIterate m g
                             Nothing -> v

passCollapseRefs :: HasCallStack => Pass
passCollapseRefs fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (pcr_ blocks))) fns

pcr_ :: HasCallStack => [BasicBlock] -> [BasicBlock]
pcr_ bs = evalState (pcr bs) (Map.empty)

registerStmt :: HasCallStack => Statement -> State (Map.Map Lvalue Lvalue) ()
registerStmt stmt = do
    refmap <- get
    case stmt of
      Assign lv rv ->
          if (Map.notMember lv refmap) then
              case (typeOf lv) of
                  TyRef _ _ ->
                      case rv of
                        Use (Consume lv') ->
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

