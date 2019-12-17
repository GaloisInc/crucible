{-| Operations over related to the Mir Ty AST -}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}
module Mir.MirTy where

import GHC.Stack(HasCallStack)

import Mir.Mir
import Mir.PP(fmt)
import Mir.GenericOps

---------------------------------------------------------------------------------------------

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
specialize sig@(FnSig args ret ps preds _atys abi spread) ts
  | k <= length ps
  = FnSig (tySubst ss args) (tySubst ss ret) ps' (tySubst ss preds) [] abi spread
  | otherwise
  = error $ "BUG: specialize -- too many type arguments" ++ "\n\r sig = " ++ fmt sig ++ "\n\r ts = " ++ fmt ts
     where
       k   = length ts
       ps' = drop k ps
       l   = length ps'
       ts' = tySubst (incN l) ts
       ss  = Substs ts' <> incN 0
