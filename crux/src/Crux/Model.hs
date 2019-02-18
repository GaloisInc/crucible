-- | This file is almost exactly the same as crucible-c/src/Model.hs

{-# Language DataKinds #-}
{-# Language TemplateHaskell #-}
{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language PolyKinds #-}
{-# Language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Crux.Model where

import Data.Binary.IEEE754 as IEEE754
import Data.List(intercalate)
import Data.Parameterized.NatRepr(knownNat,natValue)
import Data.Parameterized.TraversableF(traverseF)
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Pair(Pair(..))
import qualified Data.Parameterized.Map as MapF
import Data.Semigroup
--import Control.Exception(throw)

import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType,FloatPrecisionRepr(..))
import Lang.Crucible.Simulator.RegMap(RegValue)
import What4.Expr (GroundEvalFn(..),ExprBuilder)
import What4.ProgramLoc

import Crux.Types
import Crux.Error

import Prelude


emptyModel :: Model sym
emptyModel = Model $ MapF.fromList
  [ noVars (BaseBVRepr (knownNat @8))
  , noVars (BaseBVRepr (knownNat @16))
  , noVars (BaseBVRepr (knownNat @32))
  , noVars (BaseBVRepr (knownNat @64))
  , noVars (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)))
  , noVars (BaseFloatRepr (FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)))
  ]

noVars :: BaseTypeRepr ty -> Pair BaseTypeRepr (Vars sym)
noVars ty = Pair ty (Vars [])

addVar ::
  ProgramLoc ->
  String ->
  BaseTypeRepr ty ->
  RegValue sym (BaseToType ty) ->
  Model sym ->
  Model sym
addVar l nm k v (Model mp) = Model (MapF.insertWith jn k (Vars [ ent ]) mp)
  where jn (Vars new) (Vars old) = Vars (new ++ old)
        ent = Entry { entryName = nm, entryLoc = l, entryValue = v }

evalVars :: GroundEvalFn s -> Vars (ExprBuilder s t fs) ty -> IO (Vals ty)
evalVars ev (Vars xs) = Vals . reverse <$> mapM evEntry xs
  where evEntry e = do v <- groundEval ev (entryValue e)
                       return e { entryValue = v }

evalModel ::
  GroundEvalFn s ->
  Model (ExprBuilder s t fs) ->
  IO (MapF BaseTypeRepr Vals)
evalModel ev (Model mp) = traverseF (evalVars ev) mp


--------------------------------------------------------------------------------

ppModel :: GroundEvalFn s -> Model (ExprBuilder s t fs) -> IO ModelViews
ppModel ev m =
  do c_code <- ppModelC ev m
     js_code <- ppModelJS ev m
     return ModelViews { modelInC  = c_code
                       , modelInJS = js_code
                       }

ppValsC :: BaseTypeRepr ty -> Vals ty -> String
ppValsC ty (Vals xs) =
  let (cty, ppRawVal) = case ty of
        BaseBVRepr n -> ("int" ++ show n ++ "_t", show)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 8, natValue sb == 24
          -> ("float", show . IEEE754.wordToFloat . fromInteger)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 11, natValue sb == 53
          -> ("double", show . IEEE754.wordToDouble . fromInteger)
        _ -> throwBug ("Type not implemented: " ++ show ty)
  in unlines
      [ "size_t const crucible_values_number_" ++ cty ++
                " = " ++ show (length xs) ++ ";"

      , "const char* crucible_names_" ++ cty ++ "[] = { " ++
            intercalate "," (map (show . entryName) xs) ++ " };"

      , cty ++ " const crucible_values_" ++ cty ++ "[] = { " ++
            intercalate "," (map (ppRawVal . entryValue) xs) ++ " };"
      ]

ppModelC ::
  GroundEvalFn s -> Model (ExprBuilder s t fs) -> IO String
ppModelC ev m =
  do vals <- evalModel ev m
     return $ unlines
            $ "#include <stdint.h>"
            : "#include <stddef.h>"
            : ""
            : MapF.foldrWithKey (\k v rest -> ppValsC k v : rest) [] vals

ppValsJS :: BaseTypeRepr ty -> Vals ty -> [String]
ppValsJS ty (Vals xs) =
  let showEnt = case ty of
        BaseBVRepr n -> showEnt' show n
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 8, natValue sb == 24 -> showEnt'
            (IEEE754.wordToFloat . fromInteger)
            (knownNat @32)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 11, natValue sb == 53 -> showEnt'
            (IEEE754.wordToDouble . fromInteger)
            (knownNat @64)
        _ -> throwBug ("Type not implemented: " ++ show ty)
  in map showEnt xs
  where
  showL l = case plSourceLoc l of
              SourcePos _ x _ -> show x
              _               -> "null"
  showEnt' repr n e =
    unlines [ "{ \"name\": " ++ show (entryName e)
            , ", \"line\": " ++ showL (entryLoc e)
            , ", \"val\": " ++ (show . repr . entryValue) e
            , ", \"bits\": " ++ show n
            , "}" ]
    

ppModelJS ::
  GroundEvalFn s -> Model (ExprBuilder s t fs) -> IO String
ppModelJS ev m =
  do vals <- evalModel ev m
     let ents = MapF.foldrWithKey (\k v rest -> ppValsJS k v ++ rest) [] vals
         pre  = "[ " : repeat ", "
     return $ case ents of
                [] -> "[]"
                _  -> unlines $ zipWith (++) pre ents ++ ["]"]



instance Semigroup (Model sym) where
  (Model m1) <> m2        = MapF.foldrWithKey f m2 m1 where
    f :: forall s. BaseTypeRepr s -> Vars sym s -> Model sym -> Model sym
    f k vs (Model m) = Model (MapF.insertWith jn k vs m) 
    jn (Vars new) (Vars old) = Vars (new ++ old)

instance Monoid (Model sym) where
  mempty               = emptyModel
  mappend m1 m2        = m1 <> m2
