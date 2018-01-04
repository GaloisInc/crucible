{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass (
    Pass,
    passId,
    passCollapseRefs,
    passMutRefReturnStatic,
    passRemoveBoxNullary,
    passRemoveStorage,
    passMutRefArgs
) where

import Mir.Mir
import Control.Monad.State.Lazy
import Data.List
import Control.Lens hiding (op)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map

import GHC.Stack

import Mir.Pass.CollapseRefs( passCollapseRefs )
import Mir.Pass.MutRefReturnStatic( passMutRefReturnStatic )
import Mir.Pass.RemoveBoxNullary( passRemoveBoxNullary )
import Mir.Pass.RemoveStorage( passRemoveStorage )
import Mir.Pass.RewriteMutRef( passRewriteMutRefArg )

type Pass = [Fn] -> [Fn]

passId :: Pass
passId fns = fns

passMutRefArgs :: HasCallStack => Pass
passMutRefArgs = passRewriteMutRefArg . passCollapseRefs



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
