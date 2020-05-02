-- | This file is almost exactly the same as crucible-c/src/Model.hs

{-# Language DataKinds #-}

{-# Language Rank2Types #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language PolyKinds #-}
{-# Language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Crux.Model where

import Data.Binary.IEEE754 as IEEE754
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr(knownNat,natValue)
import Data.Parameterized.TraversableF(traverseF)
import Data.Parameterized.Map (MapF)
import Data.Parameterized.Pair(Pair(..))
import qualified Data.Parameterized.Map as MapF

import Lang.Crucible.Types(BaseTypeRepr(..),BaseToType,FloatPrecisionRepr(..))
import Lang.Crucible.Simulator.RegMap(RegValue)
import What4.Expr (GroundEvalFn(..),ExprBuilder)
import What4.ProgramLoc

import Crux.UI.JS
import Crux.Types


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

toDouble :: Rational -> Double
toDouble = fromRational

ppValsJS :: FilePath -> BaseTypeRepr ty -> Vals ty -> [String]
ppValsJS cwd ty (Vals xs) =
  let showEnt = case ty of
        BaseBVRepr n -> showEnt' show n
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 8, natValue sb == 24 -> showEnt'
            (show . IEEE754.wordToFloat . fromInteger . BV.asUnsigned)
            (knownNat @32)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 11, natValue sb == 53 -> showEnt'
            (show . IEEE754.wordToDouble . fromInteger . BV.asUnsigned)
            (knownNat @64)
        BaseRealRepr -> showEnt' (show . toDouble) (knownNat @64)
        _ -> error ("Type not implemented: " ++ show ty)
  in map showEnt xs

  where
  showEnt' :: Show b => (a -> String) -> b -> Entry a -> String
  showEnt' repr n e =
    renderJS $ jsObj
      [ "name" ~> jsStr (entryName e)
      , "loc"  ~> jsLoc cwd (entryLoc e)
      , "val"  ~> jsStr (repr (entryValue e))
      , "bits" ~> jsStr (show n)
      ]


ppModelJS :: FilePath -> ModelView -> String
ppModelJS cwd m = case ents of
                [] -> "[]"
                _  -> unlines $ zipWith (++) pre ents ++ ["]"]
  where vals = modelVals m
        ents = MapF.foldrWithKey (\k v rest -> ppValsJS cwd k v ++ rest) [] vals
        pre  = "[ " : repeat ", "



instance Semigroup (Model sym) where
  (Model m1) <> m2        = MapF.foldrWithKey f m2 m1 where
    f :: forall s. BaseTypeRepr s -> Vars sym s -> Model sym -> Model sym
    f k vs (Model m) = Model (MapF.insertWith jn k vs m)
    jn (Vars new) (Vars old) = Vars (new ++ old)

instance Monoid (Model sym) where
  mempty               = emptyModel
  mappend m1 m2        = m1 <> m2
