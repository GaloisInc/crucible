{-# LANGUAGE TemplateHaskell #-}
module StructuralShowsPrec (structuralShowsPrec) where

import Data.Parameterized.TH.GADT (TypePat(..), assocTypePats, asTypeCon)
import Language.Haskell.TH
import Language.Haskell.TH.Datatype

-- | @structuralShow tp@ generates a function with the type
-- @tp -> ShowS@ that shows the constructor.
structuralShowsPrec :: TypeQ -> [(TypePat, ExpQ)] -> ExpQ
structuralShowsPrec tpq pats = do
  d <- reifyDatatype =<< asTypeCon "structuralShowPrec" =<< tpq
  p <- newName "_p"
  a <- newName "a"
  lamE [varP p, varP a] $
    caseE (varE a) (matchShowCtor d pats (varE p) <$> datatypeCons d)

showCon :: DatatypeInfo -> [(TypePat, ExpQ)] -> ExpQ -> Name -> [Type] -> MatchQ
showCon d pats p nm fieldTps = do
  let n = length fieldTps
  vars <- newNames "x" n
  let pat = ConP nm (VarP <$> vars)
  let go s (e, tp) = do
        mr <- assocTypePats (datatypeInstTypes d) pats tp
        case mr of
          Just f ->
            [| $(s) . showChar ' ' . $(f) 11 $(varE e) |]
          Nothing ->
            [| $(s) . showChar ' ' . showsPrec 11 $(varE e) |]
  let ctor = [| showString $(return (LitE (StringL (nameBase nm)))) |]
  let rhs | null vars = ctor
          | otherwise = [| showParen ($(p) >= 11) $(foldl go ctor (zip vars fieldTps)) |]
  match (pure pat) (normalB rhs) []

matchShowCtor :: DatatypeInfo -> [(TypePat, ExpQ)] -> ExpQ -> ConstructorInfo -> MatchQ
matchShowCtor d pats p con = showCon d pats p (constructorName con) (constructorFields con)

-- | Generate a list of fresh names using the base name
-- and numbered 1 to @n@ to make them useful in conjunction with
-- @-dsuppress-uniques@.
newNames ::
  String   {- ^ base name                     -} ->
  Int      {- ^ quantity                      -} ->
  Q [Name] {- ^ list of names: @base1@, @base2@, ... -}
newNames base n = traverse (\i -> newName (base ++ show i)) [1..n]
