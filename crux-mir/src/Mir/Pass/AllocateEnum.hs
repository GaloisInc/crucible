{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

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

import Mir.DefId
import Mir.Mir

import GHC.Stack

import Debug.Trace

{-

Look for sequences of statements of the form

      (_0 as k).0 = use(op1);
      (_0 as k).1 = use(op2);
      set_discr(_0) = k;

and replace them with a single aggregate assignment

      _0 = RAdtAg (AdtAg adt k [op1, op2, ...])

-}



passAllocateEnum :: HasCallStack => Collection -> [Fn] -> [Fn]
passAllocateEnum col fns =
  let ?col = col in
  map (\(Fn a b c (MirBody d blocks) e  f) -> Fn a b c (MirBody d (map pcr blocks)) e f) fns


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
isAdtFieldUpdate (Assign (LProjection (LvalueProjection (LProjection (LvalueProjection lv (Downcast j))) (PField i ty))) (Use rhs) pos) =
  Just (FieldUpdate lv j i ty rhs pos)
isAdtFieldUpdate _ = Nothing

isSetDiscriminant :: (?col :: Collection) => Statement -> Maybe (Lvalue, Int, Adt)
isSetDiscriminant (SetDiscriminant lv i) =
  case typeOf lv of
    TyAdt defid args -> case (lookupAdt defid) of
                          Just adt -> Just (lv,i,adt)
                          Nothing  -> Nothing
    _ -> Nothing
isSetDiscriminant _ = Nothing

-- TODO: if this is not a CStyle enum, the type is wrong because the substitution is empty.
-- I'm not sure we can find the right type, so we shouldn't include the type in that case.
-- However, we need the indices for cstyle-enums later, so compute them now.
makeAggregate :: (?col :: Collection) => [FieldUpdate] -> (Lvalue, Int, Adt) -> Statement
makeAggregate updates (lv, k, adt) =
      trace ("Creating aggregate for " ++ show adt_did) 
        (Assign lv (RAdtAg (AdtAg adt (toInteger k) ops ty)) pos) where
  adt_did = _adtname adt
  ty  = if isCStyle adt then TyCustom (CEnum adt_did (adtIndices adt ?col))
        else TyAdt adt_did (Substs [])
  ops = map rhs updates
  pos = case updates of
          u:_ -> upos u
          []  -> "internal"
    

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
   go s  | Just (s', ss) <- findAllocEnum s = s' : go ss
         | otherwise = head s : go (tail s)

