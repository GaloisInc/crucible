{-|
Module     : Lang.Crucible.Utils.Structural
Copyright  : (c) Galois, Inc 2013-2016
License    : BSD3
Maintainer : Joe Hendrix <jhendrix@galois.com>

This module declares template Haskell primitives so that it is easier
to work with GADTs that have many constructors.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Utils.Structural
  ( structuralPretty
  ) where

import Control.Monad
import Data.Char (toLower)
import Language.Haskell.TH
import Text.PrettyPrint.ANSI.Leijen (brackets, text)

import Data.Parameterized.TH.GADT
import Data.Parameterized.TraversableFC


import Lang.MATLAB.Utils.PrettyPrint (ppFn, commas)

------------------------------------------------------------------------
-- Contructor cases

-- | @structuralPretty tp@ generates a function with the type
-- @Int -> tp -> Int@ that hashes type.
structuralPretty :: TypeQ -> [(TypePat, ExpQ)] -> ExpQ
structuralPretty tpq pats0 = do
  d <- lookupDataType' =<< asTypeCon "structuralPretty" =<< tpq
  pp <- newName "pp"
  a <- newName "a"

  let pats = assocTypePats (dataParamTypes d) pats0
  lamE [varP pp, varP a] $
      caseE (varE a) (matchPretty pats (varE pp) <$> dataCtors d)

matchPretty :: (Type -> Q (Maybe ExpQ))  -- ^ Pattern match functions
            -> ExpQ
            -> NormalizedCon
            -> MatchQ
matchPretty matchPat pp (NC nm tps) = do
  let n = length tps
  nms <- replicateM n (newName "x")
  let pat = conP nm (varP <$> nms)
  let vars = varE <$> nms
  let nm' = case nameBase nm of
              c:r -> toLower c : r
              [] -> error "matchPretty given constructor with empty name."
  let mkPP0 v tp = do
        me <- matchPat tp
        case me of
          Nothing -> mkPP v tp
          Just f -> [| $(f) $(pp) $(v)|]
      mkPP v ConT{} = [| text (show $(v)) |]
      mkPP v (AppT VarT{} _) = appE pp v
      mkPP v (AppT (ConT cnm) _)
       | nameBase cnm `elem` [ "Vector" ]
       = [| brackets (commas (fmap $(pp) $(v))) |]
      mkPP v (AppT (AppT (ConT cnm) _) _)
       | nameBase cnm `elem` [ "Assignment" ]
       = [| brackets (commas (toListFC $(pp) $(v))) |]
      mkPP v _ = [| text (show $(v)) |]
      --mkPP _ tp = error $ "Unsupported type " ++ show tp ++ " with " ++ nameBase nm
  let rhs = [| ppFn $(litE (stringL nm')) $(listE (zipWith mkPP0 vars tps)) |]
  match pat (normalB rhs) []
