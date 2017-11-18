{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass.RemoveBoxNullary
( passRemoveBoxNullary
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List

import Mir.Mir
import Mir.Pass

import GHC.Stack

passRemoveBoxNullary :: Pass
passRemoveBoxNullary fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (map removeBoxNullary blocks))) fns

removeBoxNullary :: BasicBlock -> BasicBlock
removeBoxNullary (BasicBlock bbi (BasicBlockData stmts term)) =
    let stmts' = filter (\stmt -> case stmt of
                Assign _ (NullaryOp Box _) -> False
                _ -> True) stmts
    in BasicBlock bbi (BasicBlockData stmts' term)

