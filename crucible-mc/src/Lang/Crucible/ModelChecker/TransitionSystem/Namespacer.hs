{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.Namespacer
-- Description      : Abstraction for adding namespaces to variables in What4 expressions
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.Namespacer
  ( Namespacer,
    runNamespacer,
    sallyNamespacer,
  )
where

import Control.Monad.Identity
import Data.Functor.Const
import Data.Functor.Product (Product (..))
import qualified Data.Parameterized.Context as Ctx
import Data.Semigroup (First (..))
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.Types
import What4.Expr.Builder
import qualified What4.Interface as What4
import What4.Symbol

data Namespacer sym stateFields = Namespacer
  { runNamespacer ::
      forall tp.
      What4.SymStruct sym stateFields ->
      SymExpr sym tp ->
      IO (SymExpr sym tp)
  }

sallyNamespacer ::
  Backend.IsBoolSolver (ExprBuilder t st (Flags FloatIEEE)) =>
  ExprBuilder t st (Flags FloatIEEE) ->
  Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  Namespacer (ExprBuilder t st (Flags FloatIEEE)) stateFields
sallyNamespacer sym stateSymbols stateReprs =
  Namespacer (addNamespaceToVariables sym stateSymbols stateReprs)

checkMatch ::
  -- we're not using the monad layer, but it matches the type for
  -- @traverseAndCollect@ better
  Monad m =>
  What4.SolverSymbol ->
  BaseTypeRepr expectedType ->
  Ctx.Index stateFields actualType ->
  Product (Const What4.SolverSymbol) BaseTypeRepr actualType ->
  m
    ( Maybe
        ( Data.Semigroup.First
            (Ctx.Index stateFields expectedType)
        )
    )
checkMatch fieldSymbol fieldType candidateIndex (Pair (Const candidateSymbol) candidateType) =
  pure $
    if fieldSymbol == candidateSymbol
      then case testEquality fieldType candidateType of
        Just Refl -> Just (First candidateIndex)
        Nothing -> Nothing
      else Nothing

fieldIndex ::
  Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SolverSymbol ->
  BaseTypeRepr tp ->
  Ctx.Index stateFields tp
fieldIndex fieldSymbols fieldTypes fieldSymbol fieldType = do
  let symbolsAndTypes = Ctx.zipWith Pair fieldSymbols fieldTypes
  case runIdentity
    ( Ctx.traverseAndCollect
        (checkMatch fieldSymbol fieldType)
        symbolsAndTypes
    ) of
    Just (First match) -> match
    _ ->
      error $
        "fieldIndex could not find a field named "
          ++ show fieldSymbol
          ++ " with type "
          ++ show fieldType

addNamespaceToVariables ::
  forall t st stateFields tp.
  Backend.IsBoolSolver (ExprBuilder t st (Flags FloatIEEE)) =>
  ExprBuilder t st (Flags FloatIEEE) ->
  Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SymStruct
    (ExprBuilder t st (Flags FloatIEEE))
    stateFields ->
  Expr t tp ->
  IO (Expr t tp)
addNamespaceToVariables sym stateSymbols stateReprs state = goExpr
  where
    -- @Expr@
    goExpr :: forall tp'. Expr t tp' -> IO (Expr t tp')
    goExpr sr@(SemiRingLiteral {}) = pure sr
    goExpr sr@(BoolExpr {}) = pure sr
    goExpr sr@(StringExpr {}) = pure sr
    goExpr (asApp -> Just a) = sbMakeExpr sym =<< goApp a
    -- FIXME: check that we don't need to add namespace to NonceAppExpr
    goExpr (NonceAppExpr e) =
      error $ "addNamespaceToVariables: encountered NonceAppExpr, please report to maintainers.\n" ++ show (NonceAppExpr e)
    goExpr (BoundVarExpr e) = do
      if solverSymbolAsText (bvarName e) == "state"
        then pure (BoundVarExpr e)
        else do
          let expectedType = bvarType e
          What4.structField
            sym
            state
            (fieldIndex stateSymbols stateReprs (bvarName e) expectedType)
    goExpr e = error $ show e
    -- @App@
    goApp :: forall tp'. App (Expr t) tp' -> IO (App (Expr t) tp')
    goApp = traverseApp goExpr
