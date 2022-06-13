{-
Module           : UCCrux.LLVM.View.Precond
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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.View.Precond
  ( PrecondsView(..),
    ViewPrecondsError,
    ppViewPrecondsError,
    viewPreconds,
    precondsView,
  )
where

import           Control.Lens ((^.))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import           Data.Vector (Vector)
import qualified Data.Vector as Vec
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (toListFC)
import           Data.Parameterized.TraversableFC.WithIndex (itraverseFC)
import           Data.Parameterized.Some (Some(Some))

import           UCCrux.LLVM.Constraints (ConstrainedShape)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleTypes, funcTypes)
import           UCCrux.LLVM.Precondition (Preconds(..), argPreconds, globalPreconds, postconds)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..))
import           UCCrux.LLVM.Module (funcSymbolToString, globalSymbolToString, makeFuncSymbol, makeGlobalSymbol, moduleGlobalMap, funcSymbol)
import           UCCrux.LLVM.View.Constraint (ViewConstrainedShapeError, ConstrainedShapeView, ConstrainedTypedValueViewError, ConstrainedTypedValueView, constrainedShapeView, viewConstrainedShape, ppViewConstrainedShapeError, viewConstrainedTypedValue, constrainedTypedValueView, ppConstrainedTypedValueViewError)
import           UCCrux.LLVM.View.Shape (ViewShapeError, ppViewShapeError)
import           UCCrux.LLVM.View.Postcond (UPostcondView(..), uPostcondView, viewUPostcond, ViewUPostcondError, ppViewUPostcondError)
import           UCCrux.LLVM.View.Util (FuncName(..), GlobalVarName(..))

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

data ViewPrecondsError
  = PrecondArgError ArgError
  | NonExistentGlobal GlobalVarName
  | NonExistentFunc FuncName
  | GlobalError GlobalVarName ConstrainedTypedValueViewError
  | PostcondError FuncName ViewUPostcondError

ppViewPrecondsError :: ViewPrecondsError -> Doc ann
ppViewPrecondsError =
  \case
    PrecondArgError ae -> ppArgError ae
    NonExistentGlobal glob ->
      "Non-existent global: " <> PP.pretty (getGlobalVarName glob)
    NonExistentFunc func ->
      "Non-existent function: " <> PP.pretty (getFuncName func)
    GlobalError glob err ->
      PP.hsep
        [ "Error in spec for global"
        , "`" <> PP.pretty (getGlobalVarName glob) <> "`:"
        , ppConstrainedTypedValueViewError err
        ]
    PostcondError func err ->
      PP.hsep
        [ "Error in postcondition for function"
        , "`" <> PP.pretty (getFuncName func) <> "`:"
        , ppViewUPostcondError err
        ]

data PrecondsView =
  PrecondsView
    { vArgPreconds :: Vector ConstrainedShapeView,
      vGlobalPreconds :: Map GlobalVarName ConstrainedTypedValueView,
      vPostconds :: Map FuncName UPostcondView
    }
  deriving (Eq, Ord, Generic, Show)

precondsView :: Preconds m argTypes -> PrecondsView
precondsView pres =
  PrecondsView
    { vArgPreconds =
        Vec.fromList (toListFC constrainedShapeView (pres ^. argPreconds)),
      vGlobalPreconds =
        mapKV viewGSymb constrainedTypedValueView (pres ^. globalPreconds),
      vPostconds =
        mapKV viewFSymb uPostcondView (pres ^. postconds)
    }
  where
    viewFSymb = FuncName . Text.pack . funcSymbolToString
    viewGSymb = GlobalVarName . Text.pack . globalSymbolToString
    mapKV k v m = Map.mapKeys k (Map.map v m)

data ArgError
  = NotEnoughArgs Int
  | BadArg (ViewShapeError ViewConstrainedShapeError)

ppArgError :: ArgError -> Doc ann
ppArgError =
  \case
    NotEnoughArgs i ->
      PP.hsep
        [ "Not enough argument specs provided for in precondition for function"
        , "found:"
        , "(" <> PP.viaShow i <> ")"
        ]
    BadArg err ->
      PP.hsep
        [ "Problem with specification for argument in precondition:"
        , ppViewShapeError ppViewConstrainedShapeError err
        ]

viewPreconds ::
  forall m arch fs va ret args.
  (fs ~ 'FS.FuncSig va ret args) =>
  ModuleContext m arch ->
  FuncSigRepr m fs ->
  PrecondsView ->
  Either ViewPrecondsError (Preconds m args)
viewPreconds modCtx fs vpres =
  do let genArg ::
           forall ft.
           Ctx.Index args ft ->
           FullTypeRepr m ft ->
           Either ArgError (ConstrainedShape m ft)
         genArg i ft =
           case vArgPreconds vpres Vec.!? Ctx.indexVal i of
             Nothing -> Left (NotEnoughArgs (Ctx.indexVal i))
             Just val ->
               liftError BadArg (viewConstrainedShape mts ft val)
     args <- liftError PrecondArgError (itraverseFC genArg (FS.fsArgTypes fs))

     globs <- traverse (uncurry viewGlob) (Map.toList (vGlobalPreconds vpres))
     posts <- traverse (uncurry viewPost) (Map.toList (vPostconds vpres))
     return $
       Preconds
         { _argPreconds = args,
           _globalPreconds = Map.fromList globs,
           _postconds = Map.fromList posts,
           _relationalPreconds = []
         }
  where
    m = modCtx ^. llvmModule
    mts = modCtx ^. moduleTypes
    mkSymbol = L.Symbol . Text.unpack

    viewGlob gn@(GlobalVarName nm) vglob =
      do gSymb <-
           liftMaybe
             (NonExistentGlobal gn)
             (makeGlobalSymbol (moduleGlobalMap m) (mkSymbol nm))
         glob <-
           liftError (GlobalError gn) (viewConstrainedTypedValue mts vglob)
         return (gSymb, glob)

    viewPost fn@(FuncName nm) vpost =
      do let funcTys = modCtx ^. funcTypes
         fSymb <-
           liftMaybe
             (NonExistentFunc fn)
             (makeFuncSymbol (mkSymbol nm) funcTys)
         Some fsRep@FS.FuncSigRepr{} <- return (funcTys ^. funcSymbol fSymb)
         post <-
           liftError
             (PostcondError fn)
             (viewUPostcond modCtx fsRep vpost)
         return (fSymb, post)

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''PrecondsView)
