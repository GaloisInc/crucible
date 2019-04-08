-- Pass to remove associated types from the collection
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Mir.Pass.AssociatedTypes(passAbstractAssociated,mkAssocTyMap) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List

import Control.Lens((^.),(%~),(&),(.~))

import Mir.DefId
import Mir.Mir
import Mir.GenericOps
import Mir.PP
import Text.PrettyPrint.ANSI.Leijen(Pretty(..))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Debug.Trace
import GHC.Stack

--
-- Debugging aid
--
traceMap :: (Pretty k, Pretty v) => Map.Map k v -> a -> a
traceMap ad x =
   Map.foldrWithKey (\k v a -> trace (fmt (pretty k PP.<+> pretty v)) a) x ad


mkDictWith :: (Foldable t, Ord k) => (a -> Map k v) -> t a -> Map k v
mkDictWith f = foldr (\t m -> f t `Map.union` m) Map.empty 

--------------------------------------------------------------------------------------
-- This pass turns "associated types" into additional type arguments to polymorphic
-- functions
--
-- An associated type is defined as
-- @
-- type AssocTy = (DefId, Substs)
-- @
--   and is isomorphic to a `Ty` of the form `(TyProjection DefId Substs)`
--
-- we remember the associations via the ATDict data structure
-- @
-- type ATDict  = Map AssocTy Ty
-- @
-- and use this data structure to translate the collection to eliminate all uses
-- of TyProjection from the MIR AST
--
--
-- This translation happens in stages
--
-- 1. We need to *identify* the associated types in all traits
--    and fn definitions and mark them in the appropriate component of
--    the FnSig. (addTraitAssocTys, addFnAssocTys)
--
-- 2. We need to construct adict from the impls
-- 
-- 3. We translate the entire collection to eliminate uses of
--    `TyProjection` and add extra type arguments 

passAbstractAssociated :: Collection -> Collection
passAbstractAssociated col =
   let col1  = col  & traits    %~ fmap addTraitAssocTys
       col2  = col1 & functions %~ fmap (addFnAssocTys col1)

       implADict = (mkImplADict col2) `Map.union` (mkClosureADict col2)

       -- TODO: look at impls to find associated types for concrete implementations
       --   currently not supported
       -- "global" maps for associated types and predicates
       -- probably only pdict makes sense globally
       adict =  -- traceMap implADict $
             implADict

       mc = buildMethodContext col2

   in

     
   col2 & traits    %~ Map.map (translateTrait col2 adict mc) 
        & functions %~ Map.map (translateFn    col2 adict mc)

----------------------------------------------------------------------------------------

-- | Update the trait with information about the associated types of the trait
-- | For traits, the arguments to associated types are always the generic types of the trait
addTraitAssocTys :: Trait -> Trait
addTraitAssocTys trait = trait & traitAssocTys .~ map (,subst) anames
   where
     anames      = [ did | (TraitType did) <- trait^.traitItems ]
     subst       = Substs [ TyParam (toInteger i)
                          | i <- [0 .. (length (trait^.traitParams) - 1)] ]

-- | Update the function with information about associated types for this Fn 
addFnAssocTys :: Collection -> Fn -> Fn
addFnAssocTys col fn = fn & fsig %~ (& fsassoc_tys .~ atys) where
  
    replaceSubsts ss (nm, _) = (nm,ss)  -- length of new substs should be same as old subst, but we don't check
    
    predToAT :: Predicate -> [AssocTy]
    predToAT (TraitPredicate tn ss)
          | Just trait <- Map.lookup tn (col^.traits)
          = (map (replaceSubsts ss) (trait^.traitAssocTys))
    predToAT p = []

    atys = concat (map predToAT (fn^.fsig.fspredicates))

                          
----------------------------------------------------------------------------------------

mkImplADict :: Collection -> ATDict
mkImplADict col = foldr go Map.empty (col^.impls) where
  go :: TraitImpl -> ATDict -> ATDict
  go ti m = foldr go2 m (ti^.tiItems) where
    TraitRef tn ss = ti^.tiTraitRef
    go2 :: TraitImplItem -> ATDict -> ATDict
    go2 (TraitImplType _ ii _ _ ty) m =
      Map.insert (ii,ss) ty m
    go2 _ m = m


-- Add entries to ATDict for the "FnOnce::Output" associated type
-- for closures and other functions in the collection
--
-- NOTE: this is a hack. We need a more general treatment of
-- associated types with constraints on them. Maybe by updating
-- ATDict to be a HOF instead of a Map?
mkClosureADict :: Collection -> ATDict
mkClosureADict col = foldr go Map.empty (col^.functions) where
  go :: Fn -> ATDict -> ATDict
  go fn m 
   | (TyRef ty@(TyClosure did (Substs [_,TyFnPtr fs,_])) _ : _) <- (fn^.fsig.fsarg_tys)
   = Map.insert (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]",
                 Substs [ty, List.head (fs^.fsarg_tys)])
                 (fs^.fsreturn_ty)
                 m
     
  go fn m 
   | (ty@(TyClosure did (Substs [_,TyFnPtr fs])) : _) <- (fn^.fsig.fsarg_tys)
   = Map.insert (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]",
                 Substs [ty, List.head (fs^.fsarg_tys)])
                 (fs^.fsreturn_ty)
                 m
     
  go fn m
   = Map.insert (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]",
                 Substs [TyFnDef (fn^.fname) (Substs []),TyTuple (fn^.fsig.fsarg_tys)])
                 (fn^.fsig.fsreturn_ty)
                 m

----------------------------------------------------------------------------------------

-- | Pre-allocate the trait info so that we can find it more easily
buildMethodContext :: Collection -> Map MethName (FnSig, Trait)
buildMethodContext col = foldMap go (col^.traits) where
   go tr = foldMap go2 (tr^.traitItems) where
     go2 (TraitMethod nm sig) = Map.singleton nm (sig, tr)
     go2 _ = Map.empty
     
-----------------------------------------------------------------------------------
-- Translation for traits and Functions

-- | Convert an associated type into a Mir type parameter
toParam :: AssocTy -> Param
toParam (did,_substs) = Param (idText did)  -- do we need to include substs?

-- | Create a mapping for associated types to type parameters, starting at index k
-- For traits, k should be == length traitParams
mkAssocTyMap :: Integer -> [AssocTy] -> ATDict
mkAssocTyMap k assocs = Map.fromList (zip assocs tys) where
   tys = map TyParam [k ..]


-- | Update trait declarations with additional generic types instead of
-- associated types
translateTrait :: Collection -> ATDict -> Map MethName (FnSig, Trait) -> Trait -> Trait
translateTrait col adict mc trait =
    trait & traitItems      %~ map updateMethod
          & traitPredicates %~ abstractATs info
          & traitParams     %~ (++ (map toParam) atys)

     where
       atys = trait^.traitAssocTys 
       j = toInteger $ length (trait^.traitParams)
       k = toInteger $ length (trait^.traitAssocTys)

       ladict =  mkAssocTyMap j atys  `Map.union` adict
       
       info = ATInfo j k ladict col mc
  
       -- Translate types of methods.
       updateMethod (TraitMethod name sig) =
             let sig' = abstractATs info sig
                      & fsgenerics %~ insertAt (map toParam atys) (fromInteger j)
             in 
             TraitMethod name sig'
       updateMethod item = item



-- Fn translation for associated types
--
-- 1. find <atys>, this fn's ATs by looking at preds (predToAT)
-- 2. these atys will be new params at the end of the fn params (addATParams)
-- 3. create <info> by extending ATdict with new ATs
-- 4. translate all other components of the Fn 

-- update preds if they mention traits with associated types
-- update args and retty from the types to refer to trait params instead of assoc types
-- add assocTys if we abstract a type bounded by a trait w/ an associated type
translateFn :: Collection -> ATDict -> Map MethName (FnSig, Trait) -> Fn -> Fn
translateFn col adict mc fn =
   fn & fargs       %~ fmap (\v -> v & varty %~ abstractATs info)
      & fsig        %~ (\fs -> fs & fsarg_tys    %~ abstractATs info
                                  & fsreturn_ty  %~ abstractATs info
                                  & fspredicates %~ abstractATs info
                                  & fsgenerics   %~ (++ (map toParam atys))
                                  )
      & fbody       %~ abstractATs info 
      where
        atys = (fn^.fsig.fsassoc_tys)

        j = toInteger $ length (fn^.fsig.fsgenerics)
        k = toInteger $ length atys

        ladict = mkAssocTyMap j atys `Map.union` adict 

        info = ATInfo j k ladict col mc 




