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

import Control.Monad.Identity (Identity (runIdentity))
import Data.Functor.Const (Const (Const))
import Data.Functor.Product (Product (..))
import qualified Data.Parameterized.Context as Ctx
import Data.Semigroup (First (..))
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.Types
  ( BaseTypeRepr,
    TestEquality (testEquality),
    type (:~:) (Refl),
  )
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as What4
import What4.Symbol (SolverSymbol (solverSymbolAsText))

data Namespacer sym stateFields = Namespacer
  { runNamespacer ::
      forall tp.
      What4.SymStruct sym stateFields ->
      WEB.SymExpr sym tp ->
      IO (WEB.SymExpr sym tp)
  }

sallyNamespacer ::
  Backend.IsBoolSolver (WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE)) =>
  WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE) ->
  Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  Namespacer (WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE)) stateFields
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
  Backend.IsBoolSolver (WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE)) =>
  WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE) ->
  Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SymStruct
    (WEB.ExprBuilder t st (WEB.Flags WEB.FloatIEEE))
    stateFields ->
  WEB.Expr t tp ->
  IO (WEB.Expr t tp)
addNamespaceToVariables sym stateSymbols stateReprs state = goExpr
  where
    -- @Expr@
    goExpr :: forall tp'. WEB.Expr t tp' -> IO (WEB.Expr t tp')
    goExpr sr@(WEB.SemiRingLiteral {}) = pure sr
    goExpr sr@(WEB.BoolExpr {}) = pure sr
    goExpr sr@(WEB.StringExpr {}) = pure sr
    goExpr (WEB.asApp -> Just a) = WEB.sbMakeExpr sym =<< goApp a
    goExpr (WEB.NonceAppExpr e) = pure (WEB.NonceAppExpr e) -- FIXME: is this correct?
    goExpr (WEB.BoundVarExpr e) = do
      if solverSymbolAsText (WEB.bvarName e) == "state"
        then pure (WEB.BoundVarExpr e)
        else do
          let expectedType = WEB.bvarType e
          What4.structField
            sym
            state
            (fieldIndex stateSymbols stateReprs (WEB.bvarName e) expectedType)
    goExpr e = error $ show e
    -- @App@
    goApp :: forall tp'. WEB.App (WEB.Expr t) tp' -> IO (WEB.App (WEB.Expr t) tp')
    goApp = WEB.traverseApp goExpr
