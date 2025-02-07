{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Pretty
  ( IntrinsicPrettyFn(..)
  , IntrinsicPrinters(..)
  , ppRegVal
  ) where

import qualified Data.List as List
import           Data.Kind (Type)
import qualified Data.Text as Text

import qualified Prettyprinter as PP

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.SymbolRepr (Symbol)
import           Data.Parameterized.TraversableFC (toListFC)

-- what4
import qualified What4.Interface as W4

-- crucible
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.Intrinsics as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Simulator.SymSequence as C
import qualified Lang.Crucible.Types as C

-- | Function for pretty-printing an intrinsic type
--
-- TODO: Upstream to Crucible
type IntrinsicPrettyFn :: Type -> Symbol -> Type
newtype IntrinsicPrettyFn sym nm
  = IntrinsicPrettyFn
    (forall ctx ann.
      Ctx.Assignment C.TypeRepr ctx ->
      C.Intrinsic sym nm ctx ->
      PP.Doc ann)

newtype IntrinsicPrinters sym
  = IntrinsicPrinters
    { getIntrinsicPrinters :: MapF C.SymbolRepr (IntrinsicPrettyFn sym) }

-- TODO: Complete all the cases, upstream to Crucible
-- | Pretty-print a 'C.RegValue'.
ppRegVal ::
  forall sym tp ann.
  W4.IsExpr (W4.SymExpr sym) =>
  IntrinsicPrinters sym ->
  C.TypeRepr tp ->
  C.RegValue' sym tp ->
  PP.Doc ann
ppRegVal iFns tp (C.RV v) =
  case tp of
    -- Base types
    C.BoolRepr -> W4.printSymExpr v
    C.BVRepr _width -> W4.printSymExpr v
    C.ComplexRealRepr -> W4.printSymExpr v
    C.FloatRepr _fi -> W4.printSymExpr v
    C.IEEEFloatRepr _fpp -> W4.printSymExpr v
    C.IntegerRepr -> W4.printSymExpr v
    C.NatRepr -> W4.printSymExpr (W4.natToIntegerPure v)
    C.RealValRepr -> W4.printSymExpr v
    C.StringRepr _si -> W4.printSymExpr v
    C.SymbolicArrayRepr _idxs _tp' -> W4.printSymExpr v
    C.SymbolicStructRepr _tys -> W4.printSymExpr v

    -- Trivial cases
    C.UnitRepr -> "()"
    C.CharRepr -> PP.pretty v

    -- Simple recursive cases
    C.RecursiveRepr symb tyCtx ->
      ppRegVal iFns (C.unrollType symb tyCtx) (C.RV @sym (C.unroll v))
    C.SequenceRepr tp' ->
      C.prettySymSequence (ppRegVal iFns tp' . C.RV @sym) v
    C.StructRepr fields ->
      let struct = PP.encloseSep PP.lbrace PP.rbrace (PP.comma PP.<> PP.space) in
      let entries = Ctx.zipWith (\t (C.RV fv) -> C.RegEntry @sym t fv) fields v in
      struct (toListFC (\(C.RegEntry tp' val) -> ppRegVal iFns tp' (C.RV @sym val)) entries)
    C.IntrinsicRepr nm tyCtx ->
      case MapF.lookup nm (getIntrinsicPrinters iFns) of
        Nothing ->
          let strNm = Text.unpack (C.symbolRepr nm) in
          -- TODO: Replace with `panic`, exception, or `Maybe`
          error ("ppRegVal: Missing pretty-printing function for intrinsic: " List.++ strNm)
        Just (IntrinsicPrettyFn f) -> f tyCtx v

    -- More complex cases
    C.FunctionHandleRepr args ret -> ppFnVal args ret v
    _ -> "<unsupported>"

ppFnVal ::
  C.CtxRepr ctx ->
  C.TypeRepr ret ->
  C.FnVal sym ctx ret ->
  PP.Doc ann
ppFnVal args ret =
  \case
    C.HandleFnVal hdl ->
      PP.hsep
      [ PP.pretty (C.handleName hdl)
      , ":"
      , PP.hsep (PP.punctuate " ->" (toListFC PP.pretty args))
      , "->"
      , PP.pretty ret
      ]
    _ -> "<unsupported>"
