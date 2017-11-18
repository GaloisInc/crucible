{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass.RemoveStorage
( passRemoveStorage
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir
import Mir.Pass

import GHC.Stack

-- remove storageDead / storageAlive calls
passRemoveStorage :: Pass
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
