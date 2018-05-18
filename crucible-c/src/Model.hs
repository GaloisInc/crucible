{-# Language DataKinds #-}
{-# Language TemplateHaskell #-}
{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
module Model where

import Data.List(intercalate)
import Data.Parameterized.NatRepr(knownNat)
import Data.Parameterized.TraversableF(traverseF)
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Pair(Pair(..))
import qualified Data.Parameterized.Map as MapF
import Control.Exception(throw)

import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType)
import Lang.Crucible.Simulator.RegMap(RegValue)
import What4.Expr
        (GroundValue,GroundEvalFn(..),ExprBuilder)

import Error

newtype Model sym   = Model (MapF BaseTypeRepr (Vars sym))
data Entry ty       = Entry { entryName :: String, entryValue :: ty }
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
  String ->
  BaseTypeRepr ty ->
  RegValue sym (BaseToType ty) ->
  Model sym ->
  Model sym
addVar nm k v (Model mp) = Model (MapF.insertWith jn k (Vars [ ent ]) mp)
  where jn (Vars new) (Vars old) = Vars (new ++ old)
        ent = Entry { entryName = nm, entryValue = v }

evalVars :: GroundEvalFn s -> Vars (ExprBuilder s t) ty -> IO (Vals ty)
evalVars ev (Vars xs) = Vals . reverse <$> mapM evEntry xs
  where evEntry e = do v <- groundEval ev (entryValue e)
                       return e { entryValue = v }

evalModel ::
  GroundEvalFn s ->
  Model (ExprBuilder s t) ->
  IO (MapF BaseTypeRepr Vals)
evalModel ev (Model mp) = traverseF (evalVars ev) mp


--------------------------------------------------------------------------------


ppVals :: BaseTypeRepr ty -> Vals ty -> String
ppVals ty (Vals xs) =
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

ppModel ::
  GroundEvalFn s -> Model (ExprBuilder s t) -> IO String
ppModel ev m =
  do vals <- evalModel ev m
     return $ unlines
            $ "#include <stdint.h>"
            : "#include <stddef.h>"
            : ""
            : MapF.foldrWithKey (\k v rest -> ppVals k v : rest) [] vals





