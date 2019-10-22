{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing -fno-warn-unused-top-binds #-}

module Mir.Pass.MutRefReturnStatic
( passMutRefReturnStatic
) where
 

import Control.Monad.Reader
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List
import Data.Maybe (catMaybes)

import Control.Lens

import Mir.Mir
import Mir.DefId
import Mir.MirTy
import Mir.GenericOps

--import GHC.Stack


exists :: (a -> Bool) -> [a] -> Bool
exists p xs = case findIndex p xs of
                Just _ -> True
                Nothing -> False

forall :: (a -> Bool) -> [a] -> Bool
forall p xs = not $ exists (not . p) xs



is_branch :: Terminator -> Bool
is_branch term = case term of
                   SwitchInt _ _ _ _ -> True
                   _ -> False


is_return_block :: BasicBlock -> Bool
is_return_block (BasicBlock _bbi (BasicBlockData _stmts term)) = (term == Return)

-- for each function, if it returns a mutable reference, and if the return is statically known to be one of the arguments, perform the corresponding substitution

type MrrsSt = Map DefId (Maybe Int) -- if component is set, the function returns a mutable reference, and needs to be fused while calling. the integer argument is which argument is the return

build_mrrs_st :: [Fn] -> MrrsSt
build_mrrs_st fns = Map.fromList $ map (\fn -> (fn^.fname, mut_info fn fns)) fns

-- determine whether the function statically returns a mutref of an argument. this is true (at least) when there are no switches in the body, and any functions called are themselves static.
mut_info :: Fn -> [Fn] ->  Maybe Int
mut_info fn fns =
    case (is_static_mut_return fns fn) of
                True -> Just (retrieve_static_mut_return fn)
                False -> Nothing

is_static_mut_return :: [Fn] -> Fn -> Bool
is_static_mut_return fns fn =
  let fblocks = fn^.fbody.mblocks in
          case exists (\(BasicBlock _ (BasicBlockData _ term)) -> is_branch term) fblocks of
            True -> False
            False ->
                forall (\(BasicBlock _ (BasicBlockData _ term)) -> (not . is_bad_call) term) fblocks

   where is_bad_call :: Terminator -> Bool
         is_bad_call term = case term of 
                              Call fnm _ _ _ ->
                                  case find (\fn -> fn^.fname == (funcNameofOp fnm)) fns of
                                    Just call_fn | isMutRefTy (call_fn^.fsig.fsreturn_ty) -> (not . (is_static_mut_return fns)) call_fn
                                    _ -> False
                              _ -> False

retrieve_static_mut_return :: Fn -> Int
retrieve_static_mut_return _fn =
    error "unimplemented" -- find most recent arg index assigned to return variable. the code is guaranteed to be straightline by now, so we can just iterate backwards through the blocks.


passMutRefReturnStatic :: [Fn] -> [Fn]
passMutRefReturnStatic fns = map (\fn -> runReader (mrrs fn) (build_mrrs_st fns)) fns

mrrs :: Fn -> Reader MrrsSt Fn
mrrs fn = do
    let (MirBody d blocks) = fn^.fbody 
    (mrrs_map :: MrrsSt) <- ask
    let subs = catMaybes $ map (\(BasicBlock _bbi (BasicBlockData _stmts term)) -> get_sub term mrrs_map) blocks

    return $ fn & fbody .~ (MirBody d (replaceList subs blocks))

   where
       get_sub :: Terminator -> MrrsSt -> Maybe (Lvalue, Lvalue)
       get_sub term mrrs_map = case term of
         Call opfunc opargs (Just (dest_lv, _dest_bbi)) _cleanup ->
             case Map.lookup (funcNameofOp opfunc) mrrs_map of
               Just (Just i) -> Just ((dest_lv, lValueofOp $ opargs !! i))
               _ -> Nothing
         _ -> Nothing
