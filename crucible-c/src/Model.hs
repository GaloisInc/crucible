{-# Language DataKinds #-}
{-# Language TemplateHaskell #-}
{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
module Model where

import Data.List(intercalate)
import Data.Parameterized.TraversableF(traverseF)
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import Control.Exception(throw)

import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType)
import Lang.Crucible.Simulator.RegMap(RegValue)
import Lang.Crucible.Solver.SimpleBackend.GroundEval
        (GroundValue,GroundEvalFn(..))
import Lang.Crucible.Solver.SimpleBuilder(SimpleBuilder)

import Error

newtype Model sym   = Model (MapF BaseTypeRepr (Vars sym))
newtype Vars sym ty = Vars [ RegValue sym (BaseToType ty) ]
newtype Vals ty     = Vals [ GroundValue ty ]

emptyModel :: Model sym
emptyModel = Model MapF.empty

addVar ::
  BaseTypeRepr ty -> RegValue sym (BaseToType ty) -> Model sym -> Model sym
addVar k v (Model mp) = Model (MapF.insertWith jn k (Vars [ v ]) mp)
  where jn (Vars new) (Vars old) = Vars (new ++ old)

evalVars :: GroundEvalFn s -> Vars (SimpleBuilder s t) ty -> IO (Vals ty)
evalVars ev (Vars xs) = Vals . reverse <$> mapM (groundEval ev) xs

evalModel ::
  GroundEvalFn s ->
  Model (SimpleBuilder s t) ->
  IO (MapF BaseTypeRepr Vals)
evalModel ev (Model mp) = traverseF (evalVars ev) mp


--------------------------------------------------------------------------------


ppVals :: BaseTypeRepr ty -> Vals ty -> String
ppVals ty (Vals xs) =
  case ty of
    BaseBVRepr n ->
      let cty = "int" ++ show n ++ "_t"
      in unlines
          [ "size_t crucible_values_number_" ++ cty ++
                   " = " ++ show (length xs) ++ ";"
          , cty ++ " crucible_values_" ++ cty ++ "[] = { " ++
                intercalate "," (map show xs) ++ " };"
          ]
    _ -> throw (Bug ("Type not implemented: " ++ show ty))

ppModel ::
  GroundEvalFn s -> Model (SimpleBuilder s t) -> IO String
ppModel ev m =
  do vals <- evalModel ev m
     return $ unlines
            $ MapF.foldrWithKey (\k v rest -> ppVals k v : rest) [] vals





