-- Pass to remove associated types from the collection
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Mir.Pass.AssociatedTypes(passAssociatedTypes,mkAssocTyMap) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Control.Monad.Except(MonadError(..))

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
-- we record the associations via the ATDict data structure
-- @
-- type ATDict  = Map DefId (Substs -> Maybe Ty)
-- @
-- and use this data structure to translate the collection to eliminate all uses
-- of TyProjection from the MIR AST.  
--
--
-- This translation happens in stages
--
-- 1. *identify* the associated types in all traits, and record them
--     (addTraitAssocTys)
--
-- 2. construct the global adict from the impls and add "custom" associations
--      because ATs can be defined in terms of other ATs, we need to process the 
--      impls topologically to make sure that the result is AT-free.
--
-- 3. identify associated types in Fns, *ignoring* those that can be satisfied by
--    the global adict (addFnAssocTys)
--
-- 4. create a data structure for easily finding the trait that a method belongs to
--    (buildMethodContext). Potentially, this could be reused by other parts of the
--    translation.
--
-- 5. translate the entire collection to eliminate uses of `TyProjection`
--    and add extra type arguments 
--
-- (NOTE: some of the implementation of this pass is "abstractATs" in Mir.GenericOps)
--
passAssociatedTypes :: (?debug::Int, ?mirLib::Collection, HasCallStack) => Collection -> Collection
passAssociatedTypes col =
   let
       -- add associated types to traits
       col1  = col  & traits    %~ calcTraitAssocTys 
         
       full1 = ?mirLib <> col1

       -- make mapping from ATs to their definitions, based on impls
       -- as well as some custom ATs (closureATDict, indexATDict)
       adict1 = implATDict full1 <> closureATDict full1 <> indexATDict

       -- ati
       info1 = ATInfo 0 0 adict1 full1 (error "ONLY types here")

       -- add ATs to functions & traitItems based on trait ATs
       col2  =
         col1 & functions %~ fmap (addFnAssocTys info1)
              & traits    %~ fmap (\tr -> tr & traitItems %~ fmap (addTraitFnAssocTys info1 tr))
              & impls     %~ fmap (addImplAssocTys info1)
         
       full2 = ?mirLib <> col2
       
       mc    = buildMethodContext full2

       info  = ATInfo 0 0 adict1 full2 mc

       col3  = col2 & traits    %~ Map.map (translateTrait info) 
                    & functions %~ Map.map (translateFn    info)
                    & impls     %~ fmap    (translateImpl  info)
   in
     --trace ("adict1 is " ++ show (ppATDict adict1)) $
     col3



----------------------------------------------------------------------------------------

-- All traits that are referred to in a predicate
predRef :: Predicate -> [TraitName]
predRef (TraitPredicate did _ss)  = [did]
predRef (TraitProjection lhs rhs) = (map projectionTrait (tyProjections lhs) ++ map projectionTrait (tyProjections rhs))
  where projectionTrait :: (DefId, Substs) -> TraitName
        projectionTrait (did, _ss) =
          getTraitName did
predRef UnknownPredicate = []          

replaceSubsts :: Substs -> AssocTy -> AssocTy
replaceSubsts ss (nm, _) = (nm,ss)  -- length of new substs should be same as old subst, but we don't check


-- | Calculate associated types from predicates
--
-- NOTE: don't add associated types (i.e. new params) for ATs that we
-- already have definitions for in adict and make sure to remove duplicates
-- 
atsFromPreds :: ATInfo -> [Predicate] -> [AssocTy]
atsFromPreds ati preds = atys where    
    raw_atys = concat (map (predATs (ati^.atCol.traits)) preds)
    tr_atys  = case abstractATs ati (map (\(s,dd)-> TyProjection s dd) raw_atys) of
                   Right ats -> (map (\x -> case x of
                                          TyProjection dd ss -> Just (dd,ss)
                                          _ -> Nothing) ats)
                   Left _ -> map Just raw_atys
    adict = ati^.atDict
    atys = List.nub (Maybe.catMaybes tr_atys)

-- Traits that we should never add associated types for
noAssoc :: [DefId]
noAssoc = [textId "::ops[0]::function[0]::FnOnce[0]",
           textId "::ops[0]::function[0]::Fn[0]",
           textId "::ops[0]::function[0]::FnMut[0]" ]


-- | Extract Raw ATs from the predicates
predATs :: Map TraitName Trait -> Predicate -> [AssocTy]
predATs d (TraitPredicate did ss)
  | did `elem` noAssoc
  = []
  | Just tr <- Map.lookup did d
  = tySubst ss (tr^.traitAssocTys)
  | otherwise
  = []
predATs _d (TraitProjection lhs rhs) =
  filter (\(did,ss) -> not (getTraitName did `elem` noAssoc)) (tyProjections lhs ++ tyProjections rhs)
predATs _d UnknownPredicate = []          


----------------------------------------------------------------------------------------
-- ** Calculating associated types and adding this info to the AST
--
-- TODO: it is convenient here to stash this info in the AST, but
-- pollutes all other parts of the translation. We should only record
-- it locally and remove it from the Mir datatypes.


-- Trait ATs come from two sources:
--   1. The type items (where the arguments to the ATs are the original params of the trait)
--   2. Predicates for this trait that mention other traits with ATs
--
-- NOTE: because of (2) we have to process traits in dependency order, calculating their ATs
-- only after all of the traits that they mention in their predicates have been processed.
calcTraitAssocTys :: HasCallStack => Map TraitName Trait -> Map TraitName Trait
calcTraitAssocTys trs = go (Map.elems trs) Map.empty where
  go :: [Trait] -> Map TraitName Trait -> Map TraitName Trait
  addTraitATs :: Trait -> Map TraitName Trait -> Maybe (Map TraitName Trait)
  addTraitATs tr done = if all (`Map.member` done) refs then
                          Just (Map.insert (tr^.traitName) trait' done)
                        else
                          Nothing
      where
        -- trait names mentioned in this trait's predicates
        refs    = filter (not . (== tr^.traitName)) (concat (map predRef (tr^.traitPredicates)))
        -- 1. ATs from type items
        atItems = map (,subst) [ did | (TraitType did) <- tr^.traitItems, did /= textId "::ops[0]::function[0]::FnOnce[0]::Output[0]" ]
        subst   = Substs [ TyParam (toInteger i)
                          | i <- [0 .. (length (tr^.traitParams) - 1)] ]
        -- 2. ATs from predicate mentions
        atRefs  = concat (map (predATs done) (tr^.traitPredicates))
        trait'  = tr & traitAssocTys .~  List.nub (atItems ++ atRefs)

  go trs done =
    if null next
       then step
       else if length next == length trs then
              error $ "BUG in calcTraitAssocTys: not making progress on " ++ fmt trs
              else go next step where
      
      (step, next) = foldMaybe addTraitATs trs done


-- | Update a fnSig with ATs for the function
addFnSigAssocTys :: HasCallStack => ATInfo -> FnSig -> FnSig
addFnSigAssocTys ati sig =
  sig & fsassoc_tys .~ (atsFromPreds ati (sig^.fspredicates)) where
  
-- | Update the function with information about associated types
addFnAssocTys :: HasCallStack => ATInfo -> Fn -> Fn
addFnAssocTys ati fn =
  fn & fsig %~ addFnSigAssocTys ati 
  
addTraitFnAssocTys :: HasCallStack => ATInfo -> Trait -> TraitItem -> TraitItem
addTraitFnAssocTys ati tr (TraitMethod did sig) = TraitMethod did (addFnSigAssocTys ati' sig)
  where
    -- extend the dictionary with associated type definitions from the trait
    adict' = (<> mkAssocTyMap (toInteger (length (tr^.traitParams))) (tr^.traitAssocTys))
    ati'   = ati & atDict %~ adict'
addTraitFnAssocTys ati tr it = it


addImplAssocTys :: HasCallStack => ATInfo -> TraitImpl -> TraitImpl
addImplAssocTys ati ti =
  let atys = (atsFromPreds ati (ti^.tiPredicates)) in
  ti & tiAssocTys .~ atys


----------------------------------------------------------------------------------------
foldMaybe :: (a -> b -> Maybe b) -> [a] -> b -> (b, [a])
foldMaybe f [] b = (b,[])
foldMaybe f (x:xs) b =
  let (b',as) = foldMaybe f xs b in
  case f x b' of
    Just b'' -> (b'',as)
    Nothing -> (b',x:as)
  
      
-- | Create a mapping from associated types (DefId,Substs) to their definitions
--   based on impls.
--
-- NOTE: because ATs can be defined in terms of other TyProjections, we need to
-- create this dictionary incrementally, only adding the ATs from an impl if
-- we can already translate its RHS
--
-- NOTE: we stash away the old TraitRef for this implementation so that we
-- can do the AT translation incrementally. We need the old version to create
-- the global adict.
implATDict :: HasCallStack => Collection -> ATDict
implATDict col = go (col^.impls) mempty where
  addImpl :: TraitImpl -> ATDict -> Maybe ATDict
  addImpl ti done = case result of
       Just m -> do
         --traceM $ "implATDict for " ++ fmt (TraitRef tn ss)
         --traceM $ fmt (ti^.tiItems)
         --traceM $ "where trait is " ++ fmt tr
         Just m
       Nothing -> Nothing
    where 
    result = foldr addImplItem (Just done) (ti^.tiItems)
    TraitRef tn ss = ti^.tiPreTraitRef
    
    addImplItem :: TraitImplItem -> Maybe ATDict -> Maybe ATDict
    addImplItem tii@(TraitImplType _ ii _  _ ty) (Just m) = do
      ty' <- case abstractATs atinfo ty of
                   Left s -> do 
                     Nothing
                   Right v -> do
                     Just v
      Just $ insertATDict (ii,ss) ty' m where
        -- locally extend the dictionary with associated type definitions from the impl
        -- when we translate the RHS of the AT
        m'     = mkAssocTyMap (toInteger (length (ti^.tiGenerics))) atys
        adict' = m <> m'
        atinfo = ATInfo start num adict' col (error "Only type components")
        start  = toInteger (length (ti^.tiGenerics))
        num    = toInteger (length (ti^.tiAssocTys))
        atys   = atsFromPreds (ATInfo 0 0 m col (error "Only type components"))
                              (ti^.tiPredicates)
    addImplItem _ Nothing = Nothing
    addImplItem _ m = m
  
  go :: [TraitImpl] -> ATDict -> ATDict  
  go tis done =
    if null next
       then this
       else if length next == length tis then
            error $ "BUG in mkImplADict: not making progress on " ++ fmt tis
            else go next step where

    (this, next) = foldMaybe addImpl tis done

    step = this
  

-- Add entries to ATDict for the "FnOnce::Output" associated type
-- For various *concrete* function types
closureATDict :: HasCallStack => Collection -> ATDict
closureATDict col =
  singletonATDict (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]")
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

-- Working around limitations in translating the stdlib
--
-- Custom ATs for:
--   type Index::Output<[T],I> == SliceIndex<I,[T]>
--   type ::iter::iterator::Iterator::Item<::slice::IterMut<lifetime,T>> == &mut T
indexATDict :: HasCallStack => ATDict
indexATDict =
  (mconcat
   [singletonATDict (textId "::ops[0]::index[0]::Index[0]::Output[0]")
    (\ substs -> case substs of
        Substs [TySlice elt, ii]
          -> Just (TyProjection (textId "::slice[0]::SliceIndex[0]::Output[0]") (Substs [ii, TySlice elt]))
        Substs _ ->
          Nothing)
    
  , singletonATDict (textId "::iter[0]::iterator[0]::Iterator[0]::Item[0]")
    (\ substs ->
       case substs of 
        Substs [TyAdt did (Substs [lifetime,param])]
          | did == textId "::slice[0]::::IterMut[0]"
          -> Just (TyRef param Mut)
          
        Substs _ ->
          Nothing)
  ])

   
----------------------------------------------------------------------------------------

-- | Pre-allocate the trait info so that we can find it more easily
buildMethodContext :: HasCallStack => Collection -> Map MethName (FnSig, Trait)
buildMethodContext col = foldMap go (col^.traits) where
   go tr = foldMap go2 (tr^.traitItems) where
     go2 (TraitMethod nm sig) = Map.singleton nm (sig, tr)
     go2 _ = Map.empty
     
-----------------------------------------------------------------------------------
-- ** Actual translation for traits, impls and Functions

-- | In this part, we need to be able to translate everything. It's a bug if we don't
-- have a definition for a TyProjection here.
abstractATsE :: (GenericOps a, Pretty a, HasCallStack) => ATInfo -> a -> a
abstractATsE ati x = case abstractATs ati x of
                       Left s  -> error $ "BUG:** " ++ s ++ "\n**when abstractATs on " ++ fmt x
                       Right v -> v


-- | trait declarations 
-- add associated types to the end of the current params, translate items and predicates
translateTrait :: HasCallStack => ATInfo -> Trait -> Trait
translateTrait ati trait =                                
  trait1
     where
       trait1 = trait & traitItems      %~ map updateMethod
                      & traitPredicates %~ map (abstractATsE info)
                      & traitParams     %~ (++ (map toParam) atys)
                      
       ladict = mkAssocTyMap j atys

       info   = ati & atStart .~ j
                    & atNum   .~ toInteger (length atys)
                    & atDict  %~ (<> ladict)
                    
       atys = trait^.traitAssocTys
       j = toInteger $ length (trait^.traitParams)
       
       -- Translate types of methods and add new type parameters for the trait's ATs.
       -- Todo: remove type items?
       updateMethod (TraitMethod name sig) =
             let sig' = abstractATsE info sig
                      & fsgenerics %~ insertAt (map toParam atys) (fromInteger j)
             in 
             TraitMethod name sig'
       updateMethod item = item

-- | Update trait implementations with additional generic types instead of
-- associated types

-- This involves:
--    calculating the associated types for the impl itself (based on the impl predicates)
--    adding those ATs to the generics
--    updating the local adict with new ATs, as well as any ATs defined in this impl
translateImpl :: HasCallStack => ATInfo -> TraitImpl -> TraitImpl
translateImpl ati impl = newImpl
     where
       newImpl = impl & tiTraitRef    .~ newTraitRef
                      & tiPreTraitRef .~ (TraitRef tn ss)
                      & tiGenerics    %~ (++ (map toParam atys))
                      & tiPredicates  %~ map (abstractATsE info)
                      & tiItems       %~ map translateImplItem
                      
       ladict = mkAssocTyMap j atys
       
       info   = ati & atStart .~ j
                    & atNum   .~ toInteger (length atys)
                    & atDict  %~ (<> ladict)

       col    = ati^.atCol
       atys   = impl^.tiAssocTys
       j      = toInteger $ length (impl^.tiGenerics)       

       -- Update the TraitRef to include ATs
       -- If we don't have info about the trait, assume it has no ATs
       TraitRef tn ss = impl^.tiTraitRef       
       trATs = case (col^.traits) Map.!? tn of
                       Just trait -> tySubst ss (trait^.traitAssocTys)
                       Nothing    -> []
                       
       ss'  = case lookupATs info trATs of
                Left s -> error $ s ++ "\n when looking up atys " ++ fmt trATs
                                    ++ "\n in impl " ++ fmt (impl^.tiTraitRef)
                Right v -> v

       newTraitRef = TraitRef tn (ss <> ss')
       

       translateImplItem ti@(TraitImplMethod {}) =
         ti & tiiGenerics   %~ insertAt (map toParam atys) (fromInteger j)
            & tiiPredicates %~ abstractATsE info 
            & tiiSignature  %~ newsig
           where newsig sig = abstractATsE info sig
                                & fsgenerics %~ insertAt (map toParam atys) (fromInteger j)
       -- TODO: remove?                                
       translateImplItem ti@(TraitImplType {})  = ti

       



-- Fn translation for associated types
--
-- 1. find <atys>, which were previously calculates
-- 2. these atys will be new params at the end of the fn params
-- 3. update <info> by extending ATdict with new ATs & recording location of new ATs
-- 4. translate all other components of the Fn 

-- update preds if they mention traits with associated types
-- update args and retty from the types to refer to trait params instead of assoc types
-- add assocTys if we abstract a type bounded by a trait w/ an associated type
translateFn :: HasCallStack => ATInfo -> Fn -> Fn
translateFn ati fn = newFn
  where 
     newFn = fn & fargs       %~ fmap (\v -> v & varty %~ abstractATsE info)
                & fsig        %~ (\fs -> fs & fsarg_tys    %~ map (abstractATsE info)
                                  & fsreturn_ty  %~ abstractATsE info
                                  & fspredicates %~ map (abstractATsE info)
                                  & fsgenerics   %~ (++ (map toParam atys))
                                  )
                & fbody       %~ abstractATsE info 
     ladict = mkAssocTyMap j atys
     atys = fn^.fsig.fsassoc_tys

     info   = ati & atStart .~ j
                  & atNum   .~ toInteger (length atys)
                  & atDict  %~ (<> ladict)

     j = toInteger $ length (fn^.fsig.fsgenerics)





