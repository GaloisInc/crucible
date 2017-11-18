{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass (
    Pass,
    passId,
    isMutRefTy
) where

import Mir.Mir
import Control.Monad.State.Lazy
import Data.List
import Control.Lens hiding (op)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
--import System.IO.Unsafe

import GHC.Stack

import qualified Debug.Trace as Debug


type Pass = Collection -> Collection

passId :: Pass
passId fns = fns




isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) ||  isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = foldl (\acc t -> acc || isMutRefTy t) False ts
isMutRefTy (TyCustom (BoxTy t)) = isMutRefTy t
isMutRefTy _ = False


-- mir utitiles
--
--
--

--isMutRefVar :: Var -> Bool
--isMutRefVar (Var _ _ t _) = isMutRefTy t

-- class IsMutTagged a where
--     isMutTagged :: a -> Bool

-- instance IsMutTagged Operand where
--     isMutTagged (Consume (Tagged _ "mutchange")) = True
--     isMutTagged _ = False

-- instance IsMutTagged Lvalue where
--     isMutTagged (Tagged _ "mutchange") = True
--     isMutTagged _ = False

-- removeTags :: [Operand] -> [Operand]
-- removeTags = map (\(Consume ( Tagged lv _)) -> Consume lv)
-- --
-- --

-- removeReturnVar :: [Var] -> [Var]
-- removeReturnVar [] = []
-- removeReturnVar (v:vs) = case v of
--                            (Var "_0" _ _ _) -> vs
--                            _ -> v : (removeReturnVar vs)

-- findReturnVar :: [Var] -> Var
-- findReturnVar [] = error "return var not found!"
-- findReturnVar (v:vs) = case v of
--                          (Var "_0" _ _ _) -> v
--                          _ -> findReturnVar vs
