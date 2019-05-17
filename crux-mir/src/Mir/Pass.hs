{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Mir.Pass (
    Pass,
    rewriteCollection
) where


import Control.Monad.State.Lazy
import Data.List
import Control.Lens hiding (op,(|>))
import qualified Data.Text as T
import Data.Map(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe

import GHC.Stack

import Mir.Mir
import Mir.DefId
import Mir.MirTy
import Mir.PP(fmt)
import Mir.GenericOps

import Mir.Pass.CollapseRefs( passCollapseRefs )
import Mir.Pass.MutRefReturnStatic( passMutRefReturnStatic )
import Mir.Pass.RemoveBoxNullary( passRemoveBoxNullary )
import Mir.Pass.RemoveStorage( passRemoveStorage )
import Mir.Pass.AllocateEnum ( passAllocateEnum )
import Mir.Pass.NoMutParams ( passNoMutParams )
import Mir.Pass.AddDictionaryPreds ( passAddDictionaryPreds )
import Mir.Pass.ExpandSuperTraits ( passExpandSuperTraits )
import Mir.Pass.AssociatedTypes ( passAssociatedTypes )

import Debug.Trace
import GHC.Stack

type Pass = (?debug::Int, ?mirLib::Collection, HasCallStack) => Collection -> Collection

--------------------------------------------------------------------------------------
infixl 0 |>
(|>) :: a -> (a -> b) -> b
x |> f = f x
--------------------------------------------------------------------------------------

rewriteCollection :: Pass
rewriteCollection col =
  col
    |> toCollectionPass passNoMutParams
    |> passAllocateEnum 
    |> passRemoveUnknownPreds  -- remove predicates that we don't know anything about
    |> passTrace "initial"
    |> passAddDictionaryPreds  -- add predicates to trait member functions
    |> passExpandSuperTraits   -- add supertrait items    
    |> passTrace "after dict preds/expand super"    
    |> passAssociatedTypes     -- replace associated types with additional type parameters
    |> passTrace "after associated types translated"
    |> passMarkCStyle          -- figure out which ADTs are enums and mark them
    |> passAddTraitAdts        -- add adts for declared traits

--------------------------------------------------------------------------------------

passId :: Pass
passId = id

--------------------------------------------------------------------------------------

passTrace :: String -> Pass
passTrace str col =
  if (?debug > 5) then 
      ((trace $ "*********MIR collection " ++ str ++ "*******\n"
                ++ fmt col ++ "\n****************************")
       col)
  else col

--------------------------------------------------------------------------------------

passMarkCStyle :: Pass
passMarkCStyle col   = markCStyle (cstyleAdts, ?mirLib <> col) col where
          cstyleAdts = Map.filter isCStyle (?mirLib^.adts <> col^.adts)

--------------------------------------------------------------------------------------

passAddTraitAdts :: Pass
passAddTraitAdts col = col & adts %~ Map.union (defineTraitAdts (?mirLib^.traits <> col^.traits))

-- Create the dictionary adt type for a trait
-- The dictionary is a record (i.e. an ADT with a single variant) with
-- a field for each method in the trait.
-- Ignore non-method components of the trait
defineTraitAdts :: Map TraitName Trait -> Map TraitName Adt
defineTraitAdts traits = fmap traitToAdt traits where
   traitToAdt :: Trait -> Adt
   traitToAdt tr = do

     let itemToField :: TraitItem -> Maybe Field
         itemToField (TraitMethod did fnsig) = do
           let fnsig' = specialize fnsig ntys 
           return $ Field did (TyFnPtr fnsig') (Substs [])
         itemToField _ = Nothing

         n    = length (tr^.traitParams)
         ntys = take n (TyParam <$> [0 .. ])

     let fields = Maybe.mapMaybe itemToField (tr^.traitItems)
     Adt (tr^.traitName) [Variant (tr^.traitName) (Relative 0) fields FnKind]


--------------------------------------------------------------------------------------
--
-- Most of the implementation of this pass is in GenericOps

passRemoveUnknownPreds :: Pass
passRemoveUnknownPreds col = modifyPreds ff col 
  where
     allTraits = ?mirLib^.traits <> col^.traits
     ff did = Map.member did allTraits

--------------------------------------------------------------------------------------

toCollectionPass :: ([Fn] -> [Fn]) -> Pass
toCollectionPass f col = col { _functions = (fromList (f (Map.elems (col^.functions)))) } where
    fromList :: [Fn] -> Map.Map DefId Fn
    fromList = foldr (\fn m -> Map.insert (fn^.fname) fn m) Map.empty

--------------------------------------------------------------------------------------  


