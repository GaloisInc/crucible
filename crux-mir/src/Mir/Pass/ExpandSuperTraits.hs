{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}

-----------------------------------------------------------------------
-- | Explicitly inherit all supertrait items
--
-- This pass transforms the collection so that
--    1. all traits contain all *items* declared in their supertraits
--    2. all impls are for all subtraits as well as the declared traits
--
-- NOTE: all traits mentioned in supers *must* be declared
-- (i.e. in the traits part of the collection)
--    In other words, this pass must be preceeded by passRemoveUnknownPreds
--    if not, the trait will be eliminated from the collection
-- 
-----------------------------------------------------------------------
module Mir.Pass.ExpandSuperTraits where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.List as List

import Control.Lens((&),(%~),(^.))

import Mir.Mir
import Mir.GenericOps
import Mir.PP

import GHC.Stack
import Debug.Trace

{-
spanMaybe :: (a -> Maybe b) -> [a] -> ([b],[a])
spanMaybe _ xs@[] =  ([], xs)
spanMaybe p xs@(x:xs') = case p x of
    Just y  -> let (ys, zs) = spanMaybe p xs' in (y : ys, zs)
    Nothing -> ([], xs)
-}

firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust f (x:xs)
  | Just y <- f x = Just y
  | otherwise     = firstJust f xs
firstJust f []    = Nothing

passExpandSuperTraits :: Collection -> Collection
passExpandSuperTraits col = col & traits %~ inheritSuperItems
                                & impls  %~ inheritSuperImpls col

inheritSuperImpls :: Collection -> [TraitImpl] -> [TraitImpl]
inheritSuperImpls col tis = Map.elems (go tis Map.empty) where

  go :: [TraitImpl] -> Map TraitRef TraitImpl -> Map TraitRef TraitImpl
  go trs done = if null this then done else go next step where

     -- divide impls into those we can process now (all supers are done)
     -- and those we need to do later
     (this, next) = List.partition process trs

     -- we can process a traitimpl this step as long as we've already done its supertrait impls
     process :: TraitImpl -> Bool
     process ti = all (\n -> Map.member n done) (supers (ti^.tiTraitRef)) where

     -- find all of the traitrefs for supertraits
     -- this is tricky because we need to get the correct set of type arguments to the trait.
     -- we get these from the predicates associated with the trait that correspond to the
     -- names in the superclass
     supers :: TraitRef -> [TraitRef]
     supers tr@(TraitRef tn tys)
       | Nothing <- (col^.traits) Map.!? tn = []
            -- ignore supers we can't process error
            -- "BUG: supers: cannot find " ++ fmt tn
     supers tr@(TraitRef tn tys) = supRefs where

        trait     = (col^.traits) Map.! tn
        supNames  = tail (trait^.traitSupers)
        supRefs   = Maybe.mapMaybe isSupPred (trait^.traitPredicates)

        isSupPred (TraitPredicate did ss) 
          | did `elem` supNames = Just (TraitRef did (tySubst tys ss)) 
        isSupPred _ = Nothing


     addSupers :: TraitImpl -> (TraitRef, TraitImpl)
     addSupers ti = (tr, ti & tiItems %~ (++ (concat superItems))) where
       tr         = ti^.tiTraitRef
       ss         = supers tr
       superItems = map ((^.tiItems).(done Map.!)) ss

     step = Map.union done (Map.fromList (map addSupers this))

inheritSuperItems :: HasCallStack => Map TraitName Trait -> Map TraitName Trait
inheritSuperItems traits =  Map.map nubTrait (go (Map.elems traits) Map.empty) where

   -- remove duplicates
   nubTrait tr = tr & traitItems %~ List.nub

   -- go over all known traits, processing them in topological order
   go :: [Trait] -> Map TraitName Trait -> Map TraitName Trait
   go trs done = if null this then done else go next step where

      -- divide traits into those we can process now and those for later
      (this, next) = List.partition process trs

      -- we can process a trait as long as we've already done its supers
      process :: Trait -> Bool
      process tr = all (\n -> Map.member n done) (tail (tr^.traitSupers))

      addSupers :: Trait -> (TraitName, Trait)
      addSupers tr = (tr^.traitName, tr & traitItems %~ (++ newItems)) where

        
        newItems = concat (map superItems superNames)

        superNames :: [TraitName]
        superNames = tail (tr^.traitSupers)

        -- NOTE: we only add items from supertraits that we have a
        -- predicate for in the trait because we need to substitute
        -- 
        -- As a side benefit, I *think* this means that we only add
        -- items from direct super traits, which is actually what we want
        -- (Indirect supertraits will already have their items
        -- incorporated into the direct supertraits).
        -- However, this could cause an issue if a direct supertrait
        -- doesn't include a predicate.
        superItems :: TraitName -> [TraitItem]
        superItems superName =
          case findSuperPredSubsts superName (tr^.traitPredicates) of
            Nothing -> []
            Just ss ->
              map (specializeTraitItem ss) rawItems
                where
                  rawItems = (done Map.! superName)^.traitItems


        findSuperPredSubsts :: TraitName -> [Predicate] -> Maybe Substs
        findSuperPredSubsts nm [] = Nothing
        findSuperPredSubsts nm (p@(TraitPredicate did ss):_) | nm == did = Just ss
        findSuperPredSubsts nm (_:ps) = findSuperPredSubsts nm ps

        specializeTraitItem :: Substs -> TraitItem -> TraitItem
        specializeTraitItem ss (TraitMethod did sig) = TraitMethod did (tySubst ss sig)
        specializeTraitItem ss (TraitConst did ty)   = TraitConst did (tySubst ss ty)
        specializeTraitItem ss item = item

      step :: Map TraitName Trait
      step = Map.union done (Map.fromList (map addSupers this))
