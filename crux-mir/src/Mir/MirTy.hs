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

isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) || isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = foldl (\acc t -> acc || isMutRefTy t) False ts
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
specialize :: FnSig -> [Ty] -> FnSig
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


---------------------------------------------------------------------------------------------
-- "Unification"
-- Actually this is just "matching" as we only produce a substitution in one direction

combineMaps :: Map Integer Ty -> Map Integer Ty -> Maybe (Map Integer Ty)
combineMaps m1 m2 = Map.foldrWithKey go (Just m2) m1 where
  go :: Integer -> Ty -> Maybe (Map Integer Ty) -> Maybe (Map Integer Ty)
  go _k _ty Nothing = Nothing
  go k ty (Just res) =
    case Map.lookup k res of
      Just ty' -> if ty == ty' then Just res else Nothing
      Nothing ->  Just (Map.insert k ty res)

-- | Try to match an implementation type against a trait type
-- | TODO: do we also need to match the params/ats?
-- TODO: allow re-ordering of preds??
matchSig :: FnSig -> FnSig -> Maybe (Map Integer Ty)
matchSig (FnSig instArgs instRet _instParams _instPreds _instATs)
         (FnSig genArgs  genRet  _genParams  _genPreds  _genATs) = do
  m1 <- matchTys instArgs genArgs
  m2 <- matchTy  instRet  genRet
  combineMaps m1 m2

matchPred :: Predicate -> Predicate -> Maybe (Map Integer Ty)
matchPred (TraitPredicate d1 ss1) (TraitPredicate d2 ss2)
  | d1 == d2
  = matchSubsts ss1 ss2
matchPred (TraitProjection d1 ss1 ty1) (TraitProjection d2 ss2 ty2)
  | d1 == d2
  = do m1 <- matchSubsts ss1 ss2
       m2 <- matchTy ty1 ty2
       combineMaps m1 m2
matchPred _ _ = Nothing
       
-- | Try to match an implementation type (first argument) against a trait type (second argument)
-- If they succeed, produce a substitution -- a mapping from type params to types
-- Neither type should include TyProjections. They should have already been abstracted out
-- using [abstractAssociatedTypes]
matchTy :: Ty -> Ty -> Maybe (Map Integer Ty)
matchTy inst arg
  | inst == arg
  = return Map.empty
matchTy ty (TyParam i) 
  = return (Map.insert i ty Map.empty)
matchTy (TyTuple instTys) (TyTuple genTys) =
  matchTys instTys genTys
matchTy (TySlice t1) (TySlice t2) = matchTy t1 t2
matchTy (TyArray t1 i1) (TyArray t2 i2) | i1 == i2 = matchTy t1 t2
matchTy (TyRef t1 m1) (TyRef t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyAdt d1 s1) (TyAdt d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyFnDef d1 s1) (TyFnDef d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyClosure d1 s1) (TyClosure d2 s2) | d1 == d2 =  matchSubsts s1 s2
matchTy (TyFnPtr sig1) (TyFnPtr sig2) = matchSig sig1 sig2
matchTy (TyRawPtr t1 m1)(TyRawPtr t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyDowncast t1 i1) (TyDowncast t2 i2) | i1 == i2 = matchTy t1 t2
matchTy ty1 ty2@(TyProjection d2 s2) = error $
  "BUG: found " ++ fmt ty2 ++ " when trying to match " ++ fmt ty1
matchTy _ _ = Nothing

matchSubsts :: Substs -> Substs -> Maybe (Map Integer Ty)
matchSubsts (Substs tys1) (Substs tys2) = matchTys tys1 tys2

matchTys :: [Ty] -> [Ty] -> Maybe (Map Integer Ty)
matchTys = matchList matchTy

matchList :: (a -> a -> Maybe (Map Integer Ty)) -> [a] -> [a] -> Maybe (Map Integer Ty)
matchList f [] [] = return Map.empty
matchList f (t1:instTys) (t2:genTys) = do
  m1 <- f t1 t2
  m2 <- matchList f instTys genTys
  combineMaps m1 m2
matchList f _ _ = Nothing  


mkSubsts :: Map Integer Ty -> Substs
mkSubsts m = Substs (map g [0 ..]) where
  g i = case Map.lookup i m of
          Just ty -> ty
          Nothing -> TyParam i
  
