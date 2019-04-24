{-| Operations over related to the Mir Ty AST -}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}
module Mir.MirTy where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List

import Text.PrettyPrint.ANSI.Leijen(Pretty(..))
import Control.Lens

import GHC.Stack(HasCallStack)
import Debug.Trace

import Mir.Mir
import Mir.DefId
import Mir.PP(fmt)
import Mir.GenericOps

-- | Is this type mutable?
isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) || isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = any isMutRefTy ts
isMutRefTy (TyAdt _ (Substs ts)) = any isMutRefTy ts
isMutRefTy (TyCustom (BoxTy t)) = isMutRefTy t
isMutRefTy _ = False


-- | Does this type contain any type parameters
isPoly :: Ty -> Bool
isPoly (TyParam _) = True
isPoly (TyTuple ts) = any isPoly ts
isPoly (TySlice ty) = isPoly ty
isPoly (TyArray ty _i) = isPoly ty
isPoly (TyRef ty _mut) = isPoly ty
isPoly (TyRawPtr ty _mut) = isPoly ty
isPoly (TyAdt _ (Substs params)) = any isPoly params
isPoly (TyFnDef _ (Substs params)) = any isPoly params
isPoly (TyClosure _ (Substs params)) = any isPoly params
isPoly (TyCustom (BoxTy ty)) = isPoly ty
isPoly (TyCustom (VecTy ty)) = isPoly ty
isPoly (TyCustom (IterTy ty)) = isPoly ty
isPoly _x = False           

isNever :: Ty -> Bool
isNever (TyAdt defId _) = fst (did_name defId) == "Never"
isNever _ = False

-- | Convert field to type. Perform the corresponding substitution if field is a type param.
fieldToTy :: HasCallStack => Field -> Ty
fieldToTy (Field _ t substs) = tySubst substs t

-- | Replace the subst on the Field 
substField :: Substs -> Field -> Field
substField subst (Field a t _subst)  = Field a t subst

---------------------------------------------------------------------------------------------

-- Specialize a polymorphic type signature by the provided type arguments
-- Note: Ty may have free type variables & FnSig may have free type variables
-- We increment these inside 
specialize :: HasCallStack => FnSig -> [Ty] -> FnSig
specialize sig@(FnSig args ret ps preds _atys) ts
  | k <= length ps
  = FnSig (tySubst ss args) (tySubst ss ret) ps' (tySubst ss preds) []
  | otherwise
  = error $ "BUG: specialize -- too many type arguments" ++ "\n\r sig = " ++ fmt sig ++ "\n\r ts = " ++ fmt ts
     where
       k   = length ts
       ps' = drop k ps
       l   = length ps'
       ts' = tySubst (incN l) ts
       ss  = Substs ts' <> incN 0


  
-- | GetProjections

tyProjections :: Ty -> [(DefId, Substs)]
tyProjections (TyProjection did ss) = [(did,ss)]
tyProjections (TyTuple ts) = foldMap tyProjections ts
tyProjections (TySlice ty) = tyProjections ty
tyProjections (TyArray ty _i) = tyProjections ty
tyProjections (TyRef ty _mut) = tyProjections ty
tyProjections (TyRawPtr ty _mut) = tyProjections ty
tyProjections (TyAdt _ (Substs params)) = foldMap tyProjections params
tyProjections (TyFnDef _ (Substs params)) = foldMap tyProjections params
tyProjections (TyClosure _ (Substs params)) = foldMap tyProjections params
tyProjections (TyCustom (BoxTy ty)) = tyProjections ty
tyProjections (TyCustom (VecTy ty)) = tyProjections ty
tyProjections (TyCustom (IterTy ty)) = tyProjections ty
tyProjections _ = []