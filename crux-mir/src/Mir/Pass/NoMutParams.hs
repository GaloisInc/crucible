{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.NoMutParams
-- Description      : Rewriting pass for removing mut params
-- Copyright        : (c) Galois, Inc 2019
-- License          : BSD3
-- Stability        : provisional
--
-- This module implements a MIR rewriting pass that creates new local 
-- variables that correspond to "mutable" function arguments. 
--
--   For example,
--       fn (mut x : u8) -> u8 {
--          x = 3;
--       }
--
--   is translated to
--
--       fn (x_mut : u8) -> u8 {
--          let mut x = x_mut;
--          x = 3;
--       }
--
--
-- TODO: we aren't really systematic about picking a fresh variable name
-- for now we just append "_mut" to the end of the original var name.
-----------------------------------------------------------------------
module Mir.Pass.NoMutParams
( passNoMutParams
) where
 
import Control.Lens hiding (op)
import Control.Monad.State.Lazy
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import qualified Data.List as List

import Mir.DefId
import Mir.Mir

import GHC.Stack

passNoMutParams :: [Fn] -> [Fn]
passNoMutParams fns = map go fns

go :: Fn -> Fn
go fn = fn & fbody %~ addLocals
           & fargs %~ renameArgs  where
  
  renameArgs :: [Var] -> [Var]
  renameArgs = map (\x -> maybe x id (List.lookup x renames))

  renames = zip mutVars newImmuts
  
  mutVars :: [Var]
  mutVars = List.filter (\v -> v^.varmut == Mut) (fn^.fargs)

  newImmuts :: [Var]
  newImmuts = List.map (\v -> v & varname %~ freshen) mutVars

  newStmts :: [Statement]
  newStmts =
    zipWith (\v1 v2 -> Assign (LBase v1) (Use (Copy (LBase v2)))
          "Internal variable") mutVars newImmuts
    
  addLocals :: MirBody -> MirBody
  addLocals (MirBody oldLocals (bb:oldBlocks)) =
    MirBody (mutVars ++ oldLocals) (addData bb : oldBlocks) where
      addData :: BasicBlock -> BasicBlock
      addData d = d & bbdata . bbstmts %~ (newStmts ++)

  freshen :: T.Text -> T.Text
  freshen t = t <> "_mut"
