{-
Module           : What4.Protocol.LIMP
Copyright        : (c) Galois, Inc 2019
License          : BSD3
Maintainer       : Aaron Tomb <atomb@galois.com>

Provides an interface for constructing linear programs from What4
expressions (focusing on @WeightedSum@ values).
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module What4.Solver.LIMP
  ( TranslationError(..)
  , exprToConstraint
  , exprToLinear
  , makeLinearProgram
  , ppTranslationError
  ) where

import Control.Monad
import Data.Foldable (fold)
import Numeric.Limp.Program hiding (eval)
import Numeric.Limp.Rep (Rep)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import What4.BaseTypes
import What4.Expr.BoolMap (viewBoolMap, BoolMapView(..))
import What4.Expr.Builder
import What4.Expr.WeightedSum
import What4.SemiRing
import What4.Symbol (SolverSymbol)

type family LIMPSemiRingKind (sr :: SemiRing) :: K where
  LIMPSemiRingKind SemiRingNat = 'KZ
  LIMPSemiRingKind SemiRingInteger = 'KZ
  LIMPSemiRingKind SemiRingReal = 'KR

type family LIMPBaseTypeKind (tp :: BaseType) :: K where
  LIMPBaseTypeKind BaseNatType = 'KZ
  LIMPBaseTypeKind BaseBoolType = 'KZ
  LIMPBaseTypeKind BaseIntegerType = 'KZ
  LIMPBaseTypeKind BaseRealType = 'KR

type ZVar = SolverSymbol
type RVar = SolverSymbol

data Range where
  Range ::
    SemiRingRepr sr ->
    Maybe (Coefficient sr) ->
    SolverSymbol ->
    Maybe (Coefficient sr) ->
    Range

data TranslationError where
  BitVectorsNotSupported :: TranslationError
  InvalidVariableType :: BaseTypeRepr tp -> TranslationError
  FalseInConstraint :: TranslationError
  NegativeConstraint :: TranslationError
  LinearAppNotSupported :: App (Expr t) tp -> TranslationError
  LinearExprNotSupported :: Expr t tp -> TranslationError
  ConstraintAppNotSupported :: App (Expr t) tp -> TranslationError
  ConstraintExprNotSupported :: Expr t tp -> TranslationError

ppTranslationError :: TranslationError -> Doc
ppTranslationError BitVectorsNotSupported =
  text "Bit vectors cannot currently be translated into linear functions."
ppTranslationError (InvalidVariableType tp) =
  text "Cannot construct a linear function with a variable of type" <+>
    text (show tp)
ppTranslationError FalseInConstraint =
  text "Constraint included conjunct equivalent to False."
ppTranslationError NegativeConstraint =
  text "Constraint included negative conjunct."
ppTranslationError (LinearAppNotSupported a) =
  text "Unsupported application type in linear function:" <+>
    text (show a)
ppTranslationError (LinearExprNotSupported e) =
  text "Unsupported expression type in linear function:" <+>
    text (show e)
ppTranslationError (ConstraintAppNotSupported a) =
  text "Unsupported application type in linear constraint:" <+>
    text (show a)
ppTranslationError (ConstraintExprNotSupported e) =
  text "Unsupported expression type in linear constraint:" <+>
    text (show e)

type TransM = Either TranslationError

tFail :: TranslationError -> TransM a
tFail = Left

wsToLinear ::
  (Rep c) =>
  WeightedSum (Expr t) sr ->
  TransM (Linear ZVar RVar c (LIMPSemiRingKind sr))
wsToLinear ws =
  case sumRepr ws of
    SemiRingIntegerRepr -> convert fromIntegral conZ ws
    SemiRingNatRepr -> convert fromIntegral conZ ws
    SemiRingRealRepr -> convert fromRational conR ws
    SemiRingBVRepr _ _ -> tFail BitVectorsNotSupported
  where
    convert kConst kLin =
      evalM (\a b -> return (a .+. b))
            (\k -> exprToLinear >=> return . (kConst k *.))
            (return . kLin . kConst)

appToLinear ::
  (Rep c) =>
  App (Expr t) tp ->
  TransM (Linear ZVar RVar c (LIMPBaseTypeKind tp))
appToLinear (SemiRingSum ws) =
  case sumRepr ws of
    SemiRingIntegerRepr -> wsToLinear ws
    SemiRingNatRepr -> wsToLinear ws
    SemiRingRealRepr -> wsToLinear ws
    SemiRingBVRepr _ _ -> tFail BitVectorsNotSupported
appToLinear (NatToInteger e) = exprToLinear e
appToLinear (IntegerToNat e) = exprToLinear e
appToLinear a = tFail (LinearAppNotSupported a)

exprToLinear ::
  (Rep c) =>
  Expr t tp ->
  TransM (Linear ZVar RVar c (LIMPBaseTypeKind tp))
exprToLinear (SemiRingLiteral sr k _) =
  case sr of
    SemiRingIntegerRepr -> return (conZ (fromIntegral k))
    SemiRingNatRepr -> return (conZ (fromIntegral k))
    SemiRingRealRepr -> return (conR (fromRational k))
    SemiRingBVRepr _ _ -> tFail BitVectorsNotSupported
exprToLinear (BoundVarExpr x) =
  case bvarType x of
    BaseNatRepr -> return (z1 (bvarName x))
    BaseIntegerRepr -> return (z1 (bvarName x))
    BaseRealRepr -> return (r1 (bvarName x))
    tr -> tFail (InvalidVariableType tr)
exprToLinear (AppExpr ae) = appToLinear (appExprApp ae)
exprToLinear e = tFail (LinearExprNotSupported e)

appToConstraint ::
  (Rep c) =>
  App (Expr t) BaseBoolType ->
  TransM (Constraint ZVar RVar c)
appToConstraint (BaseEq _ e1 e2) =
  (:==) <$> exprToLinear e1 <*> exprToLinear e2
appToConstraint (SemiRingLe _ e1 e2) =
  (:<=) <$> exprToLinear e1 <*> exprToLinear e2
appToConstraint (ConjPred m) =
  case viewBoolMap m of
    BoolMapUnit -> tFail FalseInConstraint
    BoolMapDualUnit -> return CTrue
    BoolMapTerms es -> fold <$> traverse termToConstraint es
      where
        termToConstraint (e, Positive) = exprToConstraint e
        termToConstraint (_, Negative) = tFail NegativeConstraint
appToConstraint a = tFail (ConstraintAppNotSupported a)

exprToConstraint ::
  (Rep c) =>
  Expr t BaseBoolType ->
  TransM (Constraint ZVar RVar c)
exprToConstraint nae@(NonceAppExpr ne) =
  case nonceExprApp ne of
    Exists _ e -> exprToConstraint e
    _ -> tFail (ConstraintExprNotSupported nae)
exprToConstraint (AppExpr ae) = appToConstraint (appExprApp ae)
exprToConstraint (BoolExpr True _) = return CTrue
exprToConstraint e = tFail (ConstraintExprNotSupported e)

rangeToBounds :: (Rep c) => Range -> TransM [Bounds ZVar RVar c]
rangeToBounds (Range SemiRingIntegerRepr ml x mh) =
  return [BoundZ (fromIntegral <$> ml, x, fromIntegral <$> mh)]
rangeToBounds (Range SemiRingNatRepr ml x mh) =
  return [BoundZ (fromIntegral <$> ml, x, fromIntegral <$> mh), lowerZ 0 x]
rangeToBounds (Range SemiRingRealRepr ml x mh) =
  return [BoundR (fromRational <$> ml, x, fromRational <$> mh)]
rangeToBounds (Range (SemiRingBVRepr _ _) _ _ _) =
  tFail BitVectorsNotSupported

makeLinearProgram ::
  (Rep c) =>
  Direction ->
  Expr t tp ->
  Expr t (BaseBoolType) ->
  [Range] ->
  TransM (Program ZVar RVar c)
makeLinearProgram d obj cs bs = do
  lobj <- exprToLinear obj
  lcs <- exprToConstraint cs
  lbs <- mapM rangeToBounds bs
  return (program d lobj lcs (concat lbs))
