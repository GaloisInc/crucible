-- | This file is almost exactly the same as crucible-c/src/Model.hs

{-# Language DataKinds #-}
{-# Language TemplateHaskell #-}
{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language PolyKinds #-}
{-# Language ScopedTypeVariables #-}

module Model where

import Data.List(intercalate)
import Data.Parameterized.NatRepr(knownNat)
import Data.Parameterized.TraversableF(traverseF)
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Pair(Pair(..))
import qualified Data.Parameterized.Map as MapF
import Data.Semigroup
import Control.Exception(throw)

import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType)
import Lang.Crucible.Simulator.RegMap(RegValue)
import What4.Expr
        (GroundValue,GroundEvalFn(..),ExprBuilder)
import What4.ProgramLoc

import Error

newtype Model sym   = Model (MapF BaseTypeRepr (Vars sym))
data Entry ty       = Entry { entryName :: String
                            , entryLoc :: ProgramLoc
                            , entryValue :: ty
                            }
newtype Vars sym ty = Vars [ Entry (RegValue sym (BaseToType ty)) ]
newtype Vals ty     = Vals [ Entry (GroundValue ty) ]

emptyModel :: Model sym
emptyModel = Model $ MapF.fromList [ noVars (BaseBVRepr (knownNat @8))
                                   , noVars (BaseBVRepr (knownNat @16))
                                   , noVars (BaseBVRepr (knownNat @32))
                                   , noVars (BaseBVRepr (knownNat @64))
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

data ModelViews = ModelViews
  { modelInC :: String
  , modelInJS :: String
  }

ppModel :: GroundEvalFn s -> Model (ExprBuilder s t fs) -> IO ModelViews
ppModel ev m =
  do c_code <- ppModelC ev m
     js_code <- ppModelJS ev m
     return ModelViews { modelInC  = c_code
                       , modelInJS = js_code
                       }

ppValsC :: BaseTypeRepr ty -> Vals ty -> String
ppValsC ty (Vals xs) =
  case ty of
    BaseBVRepr n ->
      let cty = "int" ++ show n ++ "_t"
      in unlines
          [ "size_t const crucible_values_number_" ++ cty ++
                   " = " ++ show (length xs) ++ ";"

          , "const char* crucible_names_" ++ cty ++ "[] = { " ++
                intercalate "," (map (show . entryName) xs) ++ " };"

          , cty ++ " const crucible_values_" ++ cty ++ "[] = { " ++
                intercalate "," (map (show . entryValue) xs) ++ " };"
          ]
    _ -> throw (Bug ("Type not implemented: " ++ show ty))

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
  case ty of
    BaseBVRepr n ->
      let showEnt e = unlines [ "{ \"name\": " ++ show (entryName e)
                              , ", \"line\": " ++ showL (entryLoc e)
                              , ", \"val\": " ++ show (show (entryValue e))
                              , ", \"bits\": " ++ show n
                              , "}" ]
      in map showEnt xs

    _ -> throw (Bug ("Type not implemented: " ++ show ty))
  where
  showL l = case plSourceLoc l of
              SourcePos _ x _ -> show x
              _               -> "null"

ppModelJS ::
  GroundEvalFn s -> Model (ExprBuilder s t fs) -> IO String
ppModelJS ev m =
  do vals <- evalModel ev m
     let ents = MapF.foldrWithKey (\k v rest -> ppValsJS k v ++ rest) [] vals
         pre  = "[ " : repeat ", "
     return $ case ents of
                [] -> "[]"
                _  -> unlines $ zipWith (++) pre ents ++ ["]"]

----------------------------------------------------------------------------
-- New addition: monoid instance

instance Semigroup (Model sym) where
  (Model m1) <> m2        = MapF.foldrWithKey f m2 m1 where
    f :: forall s. BaseTypeRepr s -> Vars sym s -> Model sym -> Model sym
    f k vs (Model m) = Model (MapF.insertWith jn k vs m) 
    jn (Vars new) (Vars old) = Vars (new ++ old)

instance Monoid (Model sym) where
  mempty               = emptyModel
  mappend m1 m2        = m1 <> m2
