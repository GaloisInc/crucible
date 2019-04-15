-- Pass to remove associated types from the collection
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
module Mir.Pass.AssociatedTypes(passAbstractAssociated,mkAssocTyMap) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Control.Lens((^.),(%~),(&),(.~))

import Mir.DefId
import Mir.Mir
import Mir.MirTy
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
   let doc = Map.foldrWithKey (\k v a -> (pretty k PP.<+> pretty v) PP.<$> a) PP.empty ad
   in trace (fmt doc) $ x


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
-- 1. *identify* the associated types in all traits
--     (addTraitAssocTys, addFnAssocTys)
--
-- 2. construct adict from the impls
--
-- 3. identify associated types in Fns
--
-- 4. create a datastructure for easily finding the trait that a method belongs to
--
-- 5. translate the entire collection to eliminate uses of `TyProjection`
--    and add extra type arguments 
--
-- (NOTE: some of the implementation of this pass is "abstractATs" in Mir.GenericOps)
--
passAbstractAssociated :: HasCallStack => Collection -> Collection
passAbstractAssociated col =
   let
       -- all traits have their associated types
       col1  = (col  & traits    %~ fmap addTraitAssocTys)

       adict = mkImplADict col1 `Map.union` mkClosureADict col1

       -- translate the RHS of the adict to expand ATs in AT definitions
       -- TODO: we should do this until we reach a fixpoint?
       adict1 = fmap (\f ss -> abstractATs info <$> (f ss)) adict where
           info  = ATInfo 0 0 adict col1 (error "passAbstractAssociated: No term translation yet")

       col2  =
         col1 & functions %~ fmap (addFnAssocTys col1 adict1)
              & traits    %~ fmap (\tr -> tr & traitItems %~ fmap (addTraitFnAssocTys col1 adict1 tr))
       
       mc    = buildMethodContext col2

       
   in
   
   col2 & traits    %~ Map.map (translateTrait col2 adict1 mc) 
        & functions %~ Map.map (translateFn    col2 adict1 mc)
        & impls     %~ fmap    (translateImpl  col2 adict1 mc)

----------------------------------------------------------------------------------------

-- | Update the trait with information about the associated types of the trait
-- | For traits, the arguments to associated types are always the generic types of the trait

addTraitAssocTys :: HasCallStack => Trait -> Trait
addTraitAssocTys trait =

  trait & traitAssocTys .~ map (,subst) anames
   where
     anames      = [ did | (TraitType did) <- trait^.traitItems ]
     subst       = Substs [ TyParam (toInteger i)
                          | i <- [0 .. (length (trait^.traitParams) - 1)] ]

addFnSigAssocTys :: HasCallStack => Collection -> ATDict -> FnSig -> FnSig
addFnSigAssocTys col adict sig = sig & fsassoc_tys .~ atys where
  
    replaceSubsts ss (nm, _) = (nm,ss)  -- length of new substs should be same as old subst, but we don't check
    
    predToAT :: Predicate -> [AssocTy]
    predToAT (TraitPredicate tn ss)
          | Just trait <- Map.lookup tn (col^.traits)
          = map (replaceSubsts ss) (trait^.traitAssocTys)
    predToAT p = []

    raw_atys = (concat (map predToAT (sig^.fspredicates))) 

    atys = filter (\x -> Maybe.isNothing (lookupATDict adict x)) raw_atys
  

-- | Update the function with information about associated types
-- NOTE: don't add associated types (i.e. new params) for ATs that we
-- already have definitions for in adict.
addFnAssocTys :: HasCallStack => Collection -> ATDict -> Fn -> Fn
addFnAssocTys col adict fn =
  fn & fsig %~ (addFnSigAssocTys col adict) 
  
addTraitFnAssocTys :: HasCallStack => Collection -> ATDict -> Trait -> TraitItem -> TraitItem
addTraitFnAssocTys col adict tr (TraitMethod did sig) = TraitMethod did (addFnSigAssocTys col adict' sig)
  where
    adict' :: ATDict
    adict' = mkAssocTyMap (toInteger (length (tr^.traitParams))) (tr^.traitAssocTys)
addTraitFnAssocTys col adict tr it = it

----------------------------------------------------------------------------------------

    
-- type ATDict = Map DefId (Substs -> Maybe Ty)

-- | Create a mapping from associated types (DefId,Substs) to their definitions
--   based on impls.
-- NOTE: because ATs can be defined in terms of other ATs, this map is *not*
-- idempotent---we still need to translate the range of the map
mkImplADict :: HasCallStack => Collection -> ATDict
mkImplADict col = adict where
  adict = foldr go Map.empty (col^.impls)
  
  go :: TraitImpl -> ATDict -> ATDict
  go ti m = foldr go2 m (ti^.tiItems) where
    TraitRef tn ss = ti^.tiTraitRef
    go2 :: TraitImplItem -> ATDict -> ATDict
    go2 (TraitImplType _ ii _ _ ty) m =
      extendATDict ii
        (\ss' -> case matchSubsts ss' ss of
                   Just m  -> Just $ tySubst (mkSubsts m) ty
                   Nothing -> Nothing) m
    go2 _ m = m


-- Add entries to ATDict for the "FnOnce::Output" associated type
-- For various concrete function types
mkClosureADict :: HasCallStack => Collection -> ATDict
mkClosureADict col =
  Map.singleton (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]")
     (\ substs -> case substs of
         Substs [TyClosure fname _ss, cty] ->
           case (col^.functions) Map.!? fname of
             Nothing -> Nothing
             Just fn -> Just (fn^.fsig^.fsreturn_ty)
         Substs [TyFnPtr sig] ->
             Just (sig^.fsreturn_ty)
         Substs [TyFnDef fname args,_] ->
           case (col^.functions) Map.!? fname of
             Nothing -> Nothing
             Just fn -> Just (fn^.fsig^.fsreturn_ty)
         Substs [TyDynamic _, TyTuple [ret]] ->
           Just ret
         _ -> Nothing)

----------------------------------------------------------------------------------------

-- | Pre-allocate the trait info so that we can find it more easily
buildMethodContext :: HasCallStack => Collection -> Map MethName (FnSig, Trait)
buildMethodContext col = foldMap go (col^.traits) where
   go tr = foldMap go2 (tr^.traitItems) where
     go2 (TraitMethod nm sig) = Map.singleton nm (sig, tr)
     go2 _ = Map.empty
     
-----------------------------------------------------------------------------------
-- Translation for traits and Functions



-- | Update trait declarations with additional generic types instead of
-- associated types
translateTrait :: HasCallStack => Collection -> ATDict -> Map MethName (FnSig, Trait) -> Trait -> Trait
translateTrait col adict mc trait = trait1

     where
       trait1 = trait & traitItems      %~ map updateMethod
                      & traitPredicates %~ abstractATs info
                      & traitParams     %~ (++ (map toParam) atys)

       
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

-- Update the TraitRef component 
translateImpl :: HasCallStack => Collection -> ATDict -> Map MethName (FnSig, Trait) -> TraitImpl -> TraitImpl
translateImpl col adict mc impl =
   impl & tiTraitRef .~ newTraitRef

     where
       TraitRef tn ss = impl^.tiTraitRef
       trait = case (col^.traits) Map.!? tn of
                       Just trait -> trait
                       Nothing    -> error $ "BUG: cannot find trait info for impl " ++ fmt tn
       trATs = tySubst ss (trait^.traitAssocTys)
       ss'   = lookupATs info trATs
       newTraitRef = TraitRef tn (ss <> ss')
       info  = ATInfo j k adict col mc
       j = toInteger $ length (trait^.traitParams)
       k = toInteger $ length (trait^.traitAssocTys)
       



-- Fn translation for associated types
--
-- 1. find <atys>, this fn's ATs by looking at preds (predToAT)
-- 2. these atys will be new params at the end of the fn params (addATParams)
-- 3. create <info> by extending ATdict with new ATs
-- 4. translate all other components of the Fn 

-- update preds if they mention traits with associated types
-- update args and retty from the types to refer to trait params instead of assoc types
-- add assocTys if we abstract a type bounded by a trait w/ an associated type
translateFn :: HasCallStack => Collection -> ATDict -> Map MethName (FnSig, Trait) -> Fn -> Fn
translateFn col adict mc fn =
   fn & fargs       %~ fmap (\v -> v & varty %~ abstractATs info)
      & fsig        %~ (\fs -> fs & fsarg_tys    %~ abstractATs info
                                  & fsreturn_ty  %~ abstractATs info
                                  & fspredicates %~ abstractATs info
                                  & fsgenerics   %~ (++ (map toParam atys))
                                  )
      & fbody       %~ abstractATs info 
      where
        atys = fn^.fsig.fsassoc_tys

        j = toInteger $ length (fn^.fsig.fsgenerics)
        k = toInteger $ length atys

        ladict = mkAssocTyMap j atys `Map.union` adict 

        info = ATInfo j k ladict col mc 




