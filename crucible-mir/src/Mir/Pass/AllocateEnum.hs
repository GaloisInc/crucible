{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

-----------------------------------------------------------------------
-- |
-- Module           : Mir.Pass.AllocateEnum
-- Description      : Rewriting pass for allocating Adts
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
import qualified Data.Text as T
import Data.List

import Mir.DefId
import Mir.Mir

import GHC.Stack

{-

Look for sequences of statements of the form

      (_0 as k).0 = use(op1);
      (_0 as k).1 = use(op2);
      set_discr(_0) = k;

and replace them with a single aggregate assignment

      _0 = RAdtAg (AdtAg adt k [op1, op2, ...])

-}



passAllocateEnum :: (HasCallStack, ?debug::Int) => Collection -> Collection
passAllocateEnum col =
  let ?col = col in
  col & functions %~ fmap (& fbody %~ mblocks %~ map pcr)


data FieldUpdate = FieldUpdate { adtLvalue :: Lvalue,
                                 discr :: Integer,
                                 fieldNum :: Int,
                                 fieldTy :: Ty,
                                 rhs :: Operand,
                                 upos :: T.Text
                               }


lookupAdt :: (?col :: Collection) => DefId -> Maybe Adt
lookupAdt defid = find (\adt -> _adtname adt == defid) (?col^.adts)


isAdtFieldUpdate :: Statement -> Maybe FieldUpdate
isAdtFieldUpdate stmt =
  case stmt ^. stmtKind of
    Assign (LProj (LProj lv (Downcast j)) (PField i ty)) (Use rhs) ->
      Just (FieldUpdate lv j i ty rhs (stmt ^. stmtPos))
    _ ->
      Nothing

-- NB: Despite the name, the second argument to SetDiscriminant is a variant
-- index, not a discriminant value.  The `Int` returned from this function
-- similarly is a variant index.
isSetDiscriminant :: (?col :: Collection) => Statement -> Maybe (Lvalue, Int, Adt)
isSetDiscriminant stmt =
  case stmt ^. stmtKind of
    SetDiscriminant lv i ->
      case typeOf lv of
        TyAdt defid _ _ -> case (lookupAdt defid) of
                              Just adt -> Just (lv,i,adt)
                              Nothing  -> Nothing
        _ -> Nothing
    _ ->
      Nothing

makeAggregate :: (?col :: Collection) => [FieldUpdate] -> (Lvalue, Int, Adt) -> Statement
makeAggregate updates (lv, k, adt) =
    Statement
      { _stmtKind = Assign lv (RAdtAg (AdtAg adt (toInteger k) ops ty Nothing))
      , _stmtPos = pos
      } where
  adt_did = _adtname adt
  ty  = typeOf lv
  pos = case updates of
          u:_ -> upos u
          []  -> "internal"
  ops = map rhs $ sortOn fieldNum updates

findAllocEnum :: (?col :: Collection) => [Statement] -> Maybe ( Statement, [Statement] )
findAllocEnum ss = f ss [] where
  f []     updates = Nothing
  f (s:ss) updates | Just (lv,i,adt) <- isSetDiscriminant s
                   = Just (makeAggregate updates (lv,i,adt), ss)
                   | Just fd         <- isAdtFieldUpdate  s  = f ss (fd : updates)
                   | otherwise                               = Nothing

pcr :: HasCallStack => (?col :: Collection) => BasicBlock -> BasicBlock
pcr (BasicBlock inf (BasicBlockData stmts term)) = BasicBlock inf (BasicBlockData (go stmts) term) where
   go :: [Statement] -> [Statement]
   go [] = []
   go stmtss@(stmt:stmts)
     | Just (stmt', stmts') <- findAllocEnum stmtss = stmt' : go stmts'
     | otherwise = stmt : go stmts
