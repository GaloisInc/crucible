{-# LANGUAGE FlexibleContexts #-}
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

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.ModelChecker.SallyWhat4
import Lang.Crucible.Types
import What4.Expr.Builder
import qualified What4.Interface as What4

data Namespacer sym stateFields
  = Namespacer
      { runNamespacer ::
          forall tp.
          What4.SymStruct sym stateFields ->
          SymExpr sym tp ->
          IO (SymExpr sym tp)
      }

sallyNamespacer ::
  Backend.IsBoolSolver (ExprBuilder t st (Flags FloatIEEE)) =>
  ExprBuilder t st (Flags FloatIEEE) ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  Namespacer (ExprBuilder t st (Flags FloatIEEE)) stateFields
sallyNamespacer sym st = Namespacer (addNamespaceToVariables sym st)

addNamespaceToVariables ::
  forall t st stateFields tp.
  Backend.IsBoolSolver (ExprBuilder t st (Flags FloatIEEE)) =>
  ExprBuilder t st (Flags FloatIEEE) ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SymStruct (ExprBuilder t st (Flags FloatIEEE)) stateFields ->
  Expr t tp ->
  IO (Expr t tp)
addNamespaceToVariables sym stateFieldsRepr state = goExpr
  where
    -- @Expr@
    goExpr :: forall tp'. Expr t tp' -> IO (Expr t tp')
    goExpr sr@(SemiRingLiteral {}) = pure sr
    goExpr sr@(BoolExpr {}) = pure sr
    goExpr sr@(StringExpr {}) = pure sr
    goExpr (asApp -> Just a) = sbMakeExpr sym =<< goApp a
    -- FIXME: check that we don't need to add namespace to NonceAppExpr
    goExpr (NonceAppExpr e) = pure (NonceAppExpr e)
    goExpr (BoundVarExpr e) =
      do
        let expectedType = bvarType e
        fieldAccess sym stateFieldsRepr (show $ bvarName e) expectedType state
    goExpr e = error $ show e
    -- @App@
    goApp :: forall tp'. App (Expr t) tp' -> IO (App (Expr t) tp')
    goApp = traverseApp goExpr
