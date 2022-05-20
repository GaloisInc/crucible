{-
Module           : UCCrux.LLVM.View.Postcond
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

module UCCrux.LLVM.View.Postcond
  ( ViewClobberValueError,
    ppViewClobberValueError,
    ClobberValueView(..),
    clobberValueView,
    viewClobberValue,
  )
where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)

import           Data.Parameterized.Some (Some(Some))

import           UCCrux.LLVM.Cursor (findBottom)
import           UCCrux.LLVM.Postcondition.Type (ClobberValue(..))
import           UCCrux.LLVM.FullType.CrucibleType (testSameCrucibleType)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ModuleTypes, asFullType)
import           UCCrux.LLVM.View.Constraint (ViewConstrainedShapeError, ConstrainedShapeView, constrainedShapeView, viewConstrainedShape, ppViewConstrainedShapeError)
import           UCCrux.LLVM.View.Cursor (ViewCursorError, CursorView, cursorView, viewCursor, ppViewCursorError)
import           UCCrux.LLVM.View.Shape (ViewShapeError, ppViewShapeError)
import           UCCrux.LLVM.View.FullType (FullTypeReprView, FullTypeReprViewError, fullTypeReprView, viewFullTypeRepr, ppFullTypeReprViewError)

data ViewClobberValueError
  = FullTypeReprViewError FullTypeReprViewError
  | NonPointerCursorError
  | ViewCursorError ViewCursorError
  | ViewShapeError (ViewShapeError ViewConstrainedShapeError)
  | IncompatibleType
  deriving (Eq, Ord, Show)

ppViewClobberValueError :: ViewClobberValueError -> Doc ann
ppViewClobberValueError =
  \case
    FullTypeReprViewError err -> ppFullTypeReprViewError err
    NonPointerCursorError -> "Clobber of non-pointer value"
    ViewCursorError err -> ppViewCursorError err
    ViewShapeError err -> ppViewShapeError ppViewConstrainedShapeError err
    IncompatibleType -> "Incompatible clobber type"

data ClobberValueView =
  ClobberValueView
    { vClobberValueCursor :: CursorView,
      vClobberValue :: ConstrainedShapeView,
      vClobberValueType :: FullTypeReprView
    }
  deriving (Eq, Ord, Generic, Show)

clobberValueView :: ClobberValue m ft -> ClobberValueView
clobberValueView (ClobberValue cur val ty _compat) =
  ClobberValueView
    { vClobberValueCursor = cursorView cur,
      vClobberValue = constrainedShapeView val,
      vClobberValueType = fullTypeReprView ty
    }

viewClobberValue ::
  ModuleTypes m ->
  FullTypeRepr m ft ->
  ClobberValueView ->
  Either ViewClobberValueError (ClobberValue m ft)
viewClobberValue mts ft vcv =
  do Some ft' <-
       liftErr
         FullTypeReprViewError
         (viewFullTypeRepr mts (vClobberValueType vcv))
     compatPrf <-
       liftMaybe
         IncompatibleType
         (testSameCrucibleType ft' ft)
     Some cur <-
       liftErr ViewCursorError (viewCursor mts ft' (vClobberValueCursor vcv))
     let atTy = findBottom cur
     case atTy of
       FTPtrRepr pt ->
         do let ptdTo = asFullType mts pt
            shape <-
              liftErr
                ViewShapeError
                (viewConstrainedShape mts ptdTo (vClobberValue vcv))
            return $
              ClobberValue
                { clobberValueCursor = cur,
                  clobberValue = shape,
                  clobberValueType = ft',
                  clobberValueCompat = compatPrf
                }
       _ -> Left NonPointerCursorError
  where
    liftErr l =
      \case
        Left e -> Left (l e)
        Right v -> Right v

    liftMaybe err =
      \case
        Nothing -> Left err
        Just v -> Right v

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''ClobberValueView)
