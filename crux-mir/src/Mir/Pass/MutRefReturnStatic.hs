{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass.MutRefReturnStatic
( passMutRefReturnStatic
) where
 
import Control.Lens hiding (op)
import Control.Monad.Reader
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.List
import Data.Maybe (catMaybes)

import Mir.Mir
import Mir.Pass

import GHC.Stack


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
is_return_block (BasicBlock bbi (BasicBlockData stmts term)) = (term == Return)

-- for each function, if it returns a mutable reference, and if the return is statically known to be one of the arguments, perform the corresponding substitution

type MrrsSt = Map.Map T.Text (Maybe Int) -- if component is set, the function returns a mutable reference, and needs to be fused while calling. the integer argument is which argument is the return

build_mrrs_st :: [Fn] -> MrrsSt
build_mrrs_st fns = Map.fromList $ map (\fn -> (_fname fn, mut_info fn fns)) fns

-- determine whether the function statically returns a mutref of an argument. this is true (at least) when there are no switches in the body, and any functions called are themselves static.
mut_info :: Fn -> [Fn] ->  Maybe Int
mut_info fn fns =
    case (is_static_mut_return fns fn) of
                True -> Just (retrieve_static_mut_return fn)
                False -> Nothing

is_static_mut_return :: [Fn] -> Fn -> Bool
is_static_mut_return fns fn =
    case fn of
      Fn fname fargs fretty (MirBody internals fblocks) ->
          case exists (\(BasicBlock _ (BasicBlockData _ term)) -> is_branch term) fblocks of
            True -> False
            False ->
                forall (\(BasicBlock _ (BasicBlockData _ term)) -> (not . is_bad_call) term) fblocks

   where is_bad_call :: Terminator -> Bool
         is_bad_call term = case term of
                              Call fname _ _ _ ->
                                  case find (\(Fn n _ t _) -> n == (funcNameofOp fname)) fns of
                                    Just call_fn | isMutRefTy (_freturn_ty call_fn) -> (not . (is_static_mut_return fns)) call_fn
                                    _ -> False
                              _ -> False

retrieve_static_mut_return :: Fn -> Int
retrieve_static_mut_return (Fn fname fargs fretty (MirBody internals blocks)) =
    error "unimplemented" -- find most recent arg index assigned to return variable. the code is guaranteed to be straightline by now, so we can just iterate backwards through the blocks.


passMutRefReturnStatic :: Pass
passMutRefReturnStatic fns = map (\fn -> runReader (mrrs fn) (build_mrrs_st fns)) fns

mrrs :: Fn -> Reader MrrsSt Fn
mrrs (Fn fname fargs fretty (MirBody d blocks)) = do
    mrrs_map <- ask
    let subs = catMaybes $ map (\(BasicBlock bbi (BasicBlockData stmts term)) -> get_sub term mrrs_map) blocks

    return $ Fn fname fargs fretty (MirBody d (replaceList subs blocks))

   where
       get_sub :: Terminator -> Map.Map T.Text (Maybe Int) -> Maybe (Lvalue, Lvalue)
       get_sub term mrrs_map = case term of
         Call opfunc opargs (Just (dest_lv,dest_bbi)) cleanup ->
             case Map.lookup (funcNameofOp opfunc) mrrs_map of
               Just (Just i) -> Just ((dest_lv, lValueofOp $ opargs !! i))
               _ -> Nothing
         _ -> Nothing
