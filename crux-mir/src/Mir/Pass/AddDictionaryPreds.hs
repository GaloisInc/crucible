module Mir.Pass.AddDictionaryPreds where

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map

import Control.Lens
import GHC.Stack

import Mir.Mir
import Mir.DefId
import Mir.MirTy
import Mir.GenericOps



--------------------------------------------------------------------------------------
-- Some functions need additional predicates because they are trait implementations
-- This pass adds those predicates to trait declarations and then uses those to add them
-- to function implementations
-- 
passAddDictionaryPreds :: Collection -> Collection
passAddDictionaryPreds col = col1 & functions %~ fmap addTraitPreds  where

  col1 = col & traits  %~ fmap addThisPred

  mkPred :: Trait -> Predicate
  mkPred tn = TraitPredicate (tn^.traitName)
                (Substs [TyParam (toInteger i) | i <- [0 .. ((length (tn^.traitParams)) - 1)] ])

  addThisPred :: Trait -> Trait
  addThisPred trait = trait & traitItems %~ map (addThis (mkPred trait))

  -- add predicates to trait methods
  addThis :: Predicate -> TraitItem -> TraitItem
  addThis pred (TraitMethod did sig) = TraitMethod did (sig & fspredicates %~ (addPred [pred]))
  addThis pred ti = ti

  -- add predicates to fn's that are implementation methods
  addTraitPreds :: Fn -> Fn
  addTraitPreds fn = fn & fsig %~ fspredicates %~ (addPred (newPreds fn))

  -- don't add redundant predicates
  addPred :: [Predicate] -> [Predicate] -> [Predicate]
  addPred pred preds = List.nub (pred++preds)

  -- determine the methods that are implementation methods
  -- and the new predicates they should satisfy (== preds for the traits that they impl)
  impls :: Map MethName [Predicate]
  impls = implMethods' col1

  newPreds :: Fn -> [Predicate]
  newPreds fn = Map.findWithDefault [] (fn^.fname) impls 


findMethodItem :: HasCallStack => MethName -> [TraitItem] -> Maybe TraitItem
findMethodItem mn (item@(TraitMethod did fsig):rest) =
  if (mn == did) then Just item else findMethodItem mn rest
findMethodItem mn (_:rest) = findMethodItem mn rest
findMethodItem mn [] = Nothing -- error $ "BUG: cannot find method " ++ fmt mn

implMethods' :: HasCallStack => Collection -> Map MethName [Predicate]
implMethods' col = foldMap g (col^.impls) where
  g :: TraitImpl -> Map MethName [Predicate]
  g impl = foldMap g2 (impl^.tiItems) where
     TraitRef tn ss = impl^.tiTraitRef
     items = case (col^.traits) Map.!? tn of
                 Just tr -> tr^.traitItems
                 -- Ignore impls that we know nothing about
                 Nothing -> []

     g2 :: TraitImplItem -> Map MethName [Predicate]
     g2 (TraitImplMethod mn ii _ preds _) =
        case findMethodItem ii items of
          Just (TraitMethod _ sig) ->
             Map.singleton mn (tySubst (ss <> (Substs $ TyParam <$> [0 .. ])) (sig^.fspredicates))
          _ ->
             Map.empty
             -- ignore unknown methods
             -- error $ "BUG: addDictionaryPreds: Cannot find method " ++ fmt ii ++ " in trait " ++ fmt tn
     g2 _ = Map.empty

implMethods :: Collection -> Map MethName [(TraitName,Substs)]
implMethods col = foldr g Map.empty (col^.functions) where
  g fn m = foldr g2 m (getTraitImplementation col (fn^.fname)) where
     g2 (TraitRef traitName substs, _tii) m 
         = Map.insertWith (++) (fn^.fname) [(traitName, substs)] m


defaultMethods :: Collection -> Map MethName TraitName
defaultMethods col = foldr g Map.empty (col^.traits) where
  g trait m = foldr g2 m (trait^.traitItems) where
    g2 (TraitMethod methName _sig) m
       | Just _fn <- Map.lookup methName (col^.functions)
       = Map.insert (methName) (trait^.traitName) m
    g2 _ m = m
