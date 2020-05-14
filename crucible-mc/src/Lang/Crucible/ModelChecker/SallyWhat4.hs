{-# LANGUAGE TypeOperators #-}

-- |
-- Module           : SallyWhat4
-- Description      : Utilities to bridge the gap between Sally and What4
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SallyWhat4
  ( fieldAccess,
    userSymbol',
  )
where

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.Types (BaseTypeRepr (..))
import qualified What4.Interface as What4

-- | @userSymbol'@ is really @What4.userSymbol@, but expecting that it won't
-- fail
userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

-- | @fieldAccessor@ creates an uninterpreted function that stands for a field
-- selector within a compound structure type.  We need this because we represent
-- the state of our transition system as a large structure of all the fields we
-- want, and want to have a way of building expressions for each field.  In the
-- Sally translation, the function application `fieldAccessor state` will be
-- turned into an actual field access-looking `state.fieldAccessor` (in
-- practice, on the Sally side, this is more of a namespaced variable access).
fieldAccessor ::
  Backend.IsSymInterface sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr ctx ->
  String ->
  BaseTypeRepr fieldType ->
  IO (What4.SymFn sym (Ctx.EmptyCtx Ctx.::> What4.BaseStructType ctx) fieldType)
fieldAccessor sym stateType fieldName fieldType =
  What4.freshTotalUninterpFn
    sym
    (userSymbol' fieldName)
    (Ctx.Empty Ctx.:> BaseStructRepr stateType)
    fieldType

-- | @fieldAccess@ implements an actual field access using @fieldAccessor@.
-- Often times we will only need this, as Sally does not let us manipulate field
-- accessors as first-class values.  As such, this module does **not** export
-- @fieldAccessor@.
fieldAccess ::
  Backend.IsSymInterface sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr ctx ->
  String ->
  BaseTypeRepr fieldType ->
  What4.SymStruct sym ctx ->
  IO (What4.SymExpr sym fieldType)
fieldAccess sym stateType fieldName fieldType state =
  do
    accessor <- fieldAccessor sym stateType fieldName fieldType
    What4.applySymFn sym accessor (Ctx.Empty Ctx.:> state)
