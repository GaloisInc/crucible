{-
Module           : UCCrux.LLVM.View.Postcond
Description      : See "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.View.Postcond
  ( -- * ClobberValue
    ViewClobberValueError,
    ppViewClobberValueError,
    ClobberValueView(..),
    clobberValueView,
    viewClobberValue,
    -- * ClobberArg
    ClobberArgView(..),
    viewClobberArg,
    clobberArgView,
    -- * UPostcond
    UPostcondView(..),
    ViewUPostcondError,
    ppViewUPostcondError,
    viewUPostcond,
    uPostcondView
  )
where

import           Control.Lens ((^.), itraverse)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF'(ixF'))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

import           UCCrux.LLVM.Constraints (ConstrainedTypedValue)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTypes, globalTypes)
import           UCCrux.LLVM.Cursor (findBottom)
import           UCCrux.LLVM.Postcondition.Type (ClobberValue(..), SomeClobberValue(..), ClobberArg(..), SomeClobberArg(..), UPostcond(..), uArgClobbers, uGlobalClobbers, uReturnValue)
import           UCCrux.LLVM.FullType.CrucibleType (testSameCrucibleType)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.PP (ppFullTypeRepr)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), SomeFullTypeRepr(..), ModuleTypes, asFullType)
import           UCCrux.LLVM.Module (globalSymbolToString, makeGlobalSymbol, moduleGlobalMap, globalSymbol)
import           UCCrux.LLVM.View.Constraint (ViewConstrainedShapeError, ConstrainedShapeView, ConstrainedTypedValueViewError, ConstrainedTypedValueView, constrainedShapeView, viewConstrainedShape, ppViewConstrainedShapeError, viewConstrainedTypedValue, constrainedTypedValueView, ppConstrainedTypedValueViewError)
import           UCCrux.LLVM.View.Cursor (ViewCursorError, CursorView, cursorView, viewCursor, ppViewCursorError)
import           UCCrux.LLVM.View.Shape (ViewShapeError, ppViewShapeError)
import           UCCrux.LLVM.View.FullType (FullTypeReprView, FullTypeReprViewError, fullTypeReprView, viewFullTypeRepr, ppFullTypeReprViewError)
import           UCCrux.LLVM.View.Util (GlobalVarName(..))

-- Helper, not exported. Equivalent to Data.Bifunctor.first.
liftError :: (e -> i) -> Either e a -> Either i a
liftError l =
  \case
    Left e -> Left (l e)
    Right v -> Right v

-- Helper, not exported
liftMaybe :: e -> Maybe a -> Either e a
liftMaybe err =
  \case
    Nothing -> Left err
    Just v -> Right v

--------------------------------------------------------------------------------
-- * ClobberValue

data ViewClobberValueError
  = FullTypeReprViewError FullTypeReprViewError
  | NonPointerCursorError SomeFullTypeRepr
  | ViewCursorError ViewCursorError
  | ViewShapeError (ViewShapeError ViewConstrainedShapeError)
  | IncompatibleType SomeFullTypeRepr SomeFullTypeRepr

ppViewClobberValueError :: ViewClobberValueError -> Doc ann
ppViewClobberValueError =
  \case
    FullTypeReprViewError err -> ppFullTypeReprViewError err
    NonPointerCursorError (SomeFullTypeRepr ft) ->
      "Clobber of non-pointer value of type " PP.<+> ppFullTypeRepr ft
    ViewCursorError err -> ppViewCursorError err
    ViewShapeError err -> ppViewShapeError ppViewConstrainedShapeError err
    IncompatibleType (SomeFullTypeRepr ft) (SomeFullTypeRepr ft') ->
      PP.vsep
        [ "Incompatible clobber type. Expected"
        , ppFullTypeRepr ft
        , "but found"
        , ppFullTypeRepr ft'
        ]

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
       liftError
         FullTypeReprViewError
         (viewFullTypeRepr mts (vClobberValueType vcv))
     compatPrf <-
       liftMaybe
         (IncompatibleType (SomeFullTypeRepr ft) (SomeFullTypeRepr ft'))
         (testSameCrucibleType ft' ft)
     Some cur <-
       liftError ViewCursorError (viewCursor mts ft' (vClobberValueCursor vcv))
     let atTy = findBottom cur
     case atTy of
       FTPtrRepr pt ->
         do let ptdTo = asFullType mts pt
            shape <-
              liftError
                ViewShapeError
                (viewConstrainedShape mts ptdTo (vClobberValue vcv))
            return $
              ClobberValue
                { clobberValueCursor = cur,
                  clobberValue = shape,
                  clobberValueType = ft',
                  clobberValueCompat = compatPrf
                }
       _ -> Left (NonPointerCursorError (SomeFullTypeRepr atTy))

--------------------------------------------------------------------------------
-- * ClobberArg

data ClobberArgView
  = DontClobberArgView
  | DoClobberArgView ClobberValueView
  deriving (Eq, Ord, Generic, Show)

clobberArgView :: ClobberArg m inTy -> ClobberArgView
clobberArgView =
  \case
    DontClobberArg -> DontClobberArgView
    DoClobberArg cv -> DoClobberArgView (clobberValueView cv)

viewClobberArg ::
  ModuleTypes m ->
  FullTypeRepr m ft ->
  ClobberArgView ->
  Either ViewClobberValueError (ClobberArg m ft)
viewClobberArg mts ft =
  \case
    DontClobberArgView -> Right DontClobberArg
    DoClobberArgView vcv -> DoClobberArg <$> viewClobberValue mts ft vcv

--------------------------------------------------------------------------------
-- * UPostcond

data ReturnTypeExpectation
  = ExpectedVoid ConstrainedTypedValueView
  | ExpectedNonVoid SomeFullTypeRepr

data ViewUPostcondError
  = ViewClobberValueError ViewClobberValueError
  | ConstrainedTypedValueViewError ConstrainedTypedValueViewError
  | ReturnTypeMismatch ReturnTypeExpectation
  | NonExistentGlobal GlobalVarName
  | BadFunctionArgument Int

ppViewUPostcondError :: ViewUPostcondError -> Doc ann
ppViewUPostcondError =
  \case
    ViewClobberValueError err -> ppViewClobberValueError err
    ConstrainedTypedValueViewError err -> ppConstrainedTypedValueViewError err
    ReturnTypeMismatch (ExpectedVoid val) ->
      "Mismatched return types, expected void but found " PP.<+> PP.viaShow val
    ReturnTypeMismatch (ExpectedNonVoid (SomeFullTypeRepr ft)) ->
      "Mismatched return types, expected value of type " PP.<+> ppFullTypeRepr ft
    NonExistentGlobal (GlobalVarName nm) ->
      "Non-existent global: " <> PP.pretty nm
    BadFunctionArgument arg ->
      "Invalid function argument: " <> PP.viaShow arg

data UPostcondView
  = UPostcondView
      { vUArgClobbers :: IntMap ClobberArgView,
        vUGlobalClobbers :: Map GlobalVarName ClobberValueView,
        vUReturnValue :: Maybe ConstrainedTypedValueView
      }
  deriving (Eq, Ord, Generic, Show)

uPostcondView :: UPostcond m -> UPostcondView
uPostcondView up =
  UPostcondView
    { vUArgClobbers = IntMap.map viewArg (up ^. uArgClobbers),
      vUGlobalClobbers =
        Map.map viewCv (Map.mapKeys viewSymb (up ^. uGlobalClobbers)),
      vUReturnValue = constrainedTypedValueView <$> up ^. uReturnValue
    }
  where
    viewArg (SomeClobberArg ca) = clobberArgView ca
    viewSymb = GlobalVarName . Text.pack . globalSymbolToString
    viewCv (SomeClobberValue cv) = clobberValueView cv

viewUPostcond ::
  forall m arch fs va ret args.
  (fs ~ 'FS.FuncSig va ret args) =>
  ModuleContext m arch ->
  FuncSigRepr m fs ->
  UPostcondView ->
  Either ViewUPostcondError (UPostcond m)
viewUPostcond modCtx fs vup =
  do args <- itraverse viewArg (vUArgClobbers vup)
     globs <- traverse (uncurry viewGlob) (Map.toList (vUGlobalClobbers vup))
     ret :: Maybe (ConstrainedTypedValue m) <-
       case (FS.fsRetType fs, vUReturnValue vup) of
         (FS.NonVoidRepr {}, Just val) ->
           do v <-
                liftError
                  ConstrainedTypedValueViewError
                  (viewConstrainedTypedValue mts val)
              return (Just v)
         (FS.VoidRepr, Nothing) -> return Nothing
         (FS.VoidRepr, Just val) ->
           Left (ReturnTypeMismatch (ExpectedVoid val))
         (FS.NonVoidRepr ft, Nothing) ->
           Left (ReturnTypeMismatch (ExpectedNonVoid (SomeFullTypeRepr ft)))
     return $
       UPostcond
         { _uArgClobbers = args,
           _uGlobalClobbers = Map.fromList globs,
           _uReturnValue = ret
         }
  where
    m = modCtx ^. llvmModule
    mts = modCtx ^. moduleTypes
    argTys = FS.fsArgTypes fs

    viewArg i a =
      case Ctx.intIndex i (Ctx.size argTys) of
        Just (Some idx) ->
          case viewClobberArg mts (argTys ^. ixF' idx) a of
            Left err -> Left (ViewClobberValueError err)
            Right v -> Right (SomeClobberArg v)
        Nothing -> Left (BadFunctionArgument i)

    viewGlob gn@(GlobalVarName nm) vcv =
      do gSymb <-
           liftMaybe
             (NonExistentGlobal gn)
             (makeGlobalSymbol (moduleGlobalMap m) (L.Symbol (Text.unpack nm)))
         Some gTy <- return (modCtx ^. globalTypes . globalSymbol gSymb)
         cv <- liftError ViewClobberValueError (viewClobberValue mts gTy vcv)
         return (gSymb, SomeClobberValue cv)

-- See Note [JSON instance tweaks].
$(Aeson.TH.deriveJSON
  Aeson.defaultOptions
    { Aeson.fieldLabelModifier = drop (length ("vClobber" :: String)) }
  ''ClobberValueView)
$(Aeson.TH.deriveJSON
  Aeson.defaultOptions
    { Aeson.constructorTagModifier =
        reverse . drop (length ("View" :: String)) . reverse
    }
  ''ClobberArgView)
$(Aeson.TH.deriveJSON
  Aeson.defaultOptions
    { Aeson.fieldLabelModifier = drop (length ("vU" :: String)) }
  ''UPostcondView)
