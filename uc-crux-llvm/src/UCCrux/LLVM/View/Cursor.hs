{-
Module           : UCCrux.LLVM.View.Cursor
Description      : See "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.View.Cursor
  ( ViewCursorError,
    ppViewCursorError,
    CursorView(..),
    cursorView,
    viewCursor,
  )
where

import           Control.Lens ((^.))
import           Control.Monad (when)
import qualified Data.Aeson.TH as Aeson.TH
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF'(ixF'))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))

import           UCCrux.LLVM.Cursor (Cursor(..))
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), SomeFullTypeRepr(..), ModuleTypes, asFullType)
import           UCCrux.LLVM.FullType.PP (ppFullTypeRepr)
import qualified UCCrux.LLVM.View.Options.Cursor as Opts

data ViewCursorError
  = StructBadIndex !Int
  | TypeMismatch SomeFullTypeRepr CursorView
  | VectorLengthMismatch !Natural !Natural
  | VectorBadIndex !Natural !Natural

ppViewCursorError :: ViewCursorError -> Doc ann
ppViewCursorError =
  \case
    StructBadIndex i -> "Bad struct index: " <> PP.viaShow i
    TypeMismatch (SomeFullTypeRepr t) vcur ->
      PP.hsep
        [ "Type mismatch:",
          ppFullTypeRepr t,
          PP.viaShow vcur
        ]
    VectorLengthMismatch typeLen len ->
      PP.hsep
        [ "Vector length mismatch. Expected length",
          PP.viaShow typeLen,
          "but got length",
          PP.viaShow len
        ]
    VectorBadIndex idx len ->
      PP.hsep
        [ "Bad vector index. Found index",
          PP.viaShow idx,
          "but vector was of length",
          PP.viaShow len
        ]

data CursorView
  = HereView
  | DereferenceView Int CursorView
  | IndexView Natural Natural CursorView
  | FieldView Int CursorView
  deriving (Eq, Ord, Generic, Show)

cursorView ::
  Cursor m inTy atTy ->
  CursorView
cursorView =
  \case
    Here{} -> HereView
    Dereference idx sub -> DereferenceView idx (cursorView sub)
    Index idx len sub ->
      IndexView (NatRepr.natValue idx) (NatRepr.natValue len) (cursorView sub)
    Field _fields idx sub ->
      FieldView (Ctx.indexVal idx) (cursorView sub)

viewCursor ::
  ModuleTypes m ->
  FullTypeRepr m inTy ->
  CursorView ->
  Either ViewCursorError (Some (Cursor m inTy))
viewCursor mts ft vcur =
  case (ft, vcur) of
    (_, HereView) -> Right (Some (Here ft))
    (FTPtrRepr pt, DereferenceView idx vsub) ->
      do Some sub <- viewCursor mts (asFullType mts pt) vsub
         return (Some (Dereference idx sub))
    (FTArrayRepr n elems, IndexView idx len vsub) ->
      do let typeLen = NatRepr.natValue n
         check
           (typeLen /= len)
           (VectorLengthMismatch typeLen len)
         Some sub <- viewCursor mts elems vsub
         Some idxRep <- return (NatRepr.mkNatRepr idx)
         NatRepr.LeqProof <-
           liftMaybe (VectorBadIndex idx len) (NatRepr.testLeq idxRep n)
         case NatRepr.testStrictLeq idxRep n of
           Right _ -> Left (VectorBadIndex idx len)
           Left NatRepr.LeqProof ->
             return (Some (Index idxRep n sub))
    (FTStructRepr _sp fields, FieldView vidx vsub) ->
      do Some idx <-
           liftMaybe (StructBadIndex vidx) (Ctx.intIndex vidx (Ctx.size fields))
         Some sub <- viewCursor mts (fields ^. ixF' idx) vsub
         return (Some (Field fields idx sub))
    _ -> Left (TypeMismatch (SomeFullTypeRepr ft) vcur)
  where
    check cond err = when cond (Left err)
    liftMaybe err =
      \case
        Nothing -> Left err
        Just v -> Right v

$(Aeson.TH.deriveJSON Opts.cursor ''CursorView)
