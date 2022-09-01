{-
Module           : UCCrux.LLVM.View.Specs
Description      : See "UCCrux.LLVM.View" and "UCCrux.LLVM.Specs".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.View.Specs
  ( -- * SpecPreconds
    SpecPrecondsView(..),
    specPrecondsView,
    viewSpecPreconds,
    -- * Soundness
    SoundnessView(..),
    specSoundnessView,
    viewSoundness,
    -- * Spec
    SpecViewError,
    ppSpecViewError,
    SpecView(..),
    specView,
    viewSpec,
    -- * Specs
    SpecsView(..),
    specsView,
    viewSpecs,
    -- * Map of specs
    parseSpecs,
  )
where

import           Control.Lens ((^.))
import           Control.Monad (foldM)
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Data (Data)
import           Data.List.NonEmpty (NonEmpty)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Vector (Vector)
import qualified Data.Vector as Vec
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.TraversableFC (toListFC)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes, funcTypes)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ModuleTypes)
import           UCCrux.LLVM.Module (FuncSymbol, makeFuncSymbol, funcSymbol)
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameToString)
import           UCCrux.LLVM.Postcondition.Type (toUPostcond, typecheckPostcond, PostcondTypeError, ppPostcondTypeError)
import           UCCrux.LLVM.Soundness (Soundness)
import qualified UCCrux.LLVM.Soundness as Sound
import qualified UCCrux.LLVM.Specs.Type as Spec
import           UCCrux.LLVM.Specs.Type (SpecPreconds, Spec (Spec), Specs (Specs), SomeSpecs (SomeSpecs))
import           UCCrux.LLVM.View.Constraint (ConstrainedShapeView, constrainedShapeView)
import qualified UCCrux.LLVM.View.Options.Specs as Opts
import           UCCrux.LLVM.View.Postcond (UPostcondView, uPostcondView, viewUPostcond, ViewUPostcondError, ppViewUPostcondError)
import           UCCrux.LLVM.View.Precond (ArgError, viewArgPreconds, ppArgError)

-- Helper, not exported. Equivalent to Data.Bifunctor.first.
liftError :: (e -> i) -> Either e a -> Either i a
liftError l =
  \case
    Left e -> Left (l e)
    Right v -> Right v

--------------------------------------------------------------------------------
-- * SpecPreconds

newtype SpecPrecondsView
  = SpecPrecondsView
      { vSpecArgPreconds :: Vector ConstrainedShapeView }
  deriving (Eq, Ord, Generic, Show)

specPrecondsView :: SpecPreconds m args -> SpecPrecondsView
specPrecondsView pres =
  SpecPrecondsView $
    Vec.fromList (toListFC constrainedShapeView (Spec.specArgPreconds pres))

viewSpecPreconds ::
  ModuleTypes m ->
  Ctx.Assignment (FullTypeRepr m) args ->
  SpecPrecondsView ->
  Either ArgError (SpecPreconds m args)
viewSpecPreconds mts argTys =
  fmap Spec.SpecPreconds . viewArgPreconds mts argTys . vSpecArgPreconds

--------------------------------------------------------------------------------
-- * Soundness

data SoundnessView
  = PreciseView
  | OverapproxView
  | UnderapproxView
  | IndefiniteView
  deriving (Bounded, Data, Enum, Eq, Generic, Ord, Show)

specSoundnessView :: Soundness -> SoundnessView
specSoundnessView =
  \case
    Sound.Precise -> PreciseView
    Sound.Overapprox -> OverapproxView
    Sound.Underapprox -> UnderapproxView
    Sound.Indefinite -> IndefiniteView

viewSoundness :: SoundnessView -> Soundness
viewSoundness =
  \case
    OverapproxView -> Sound.Overapprox
    UnderapproxView -> Sound.Underapprox
    PreciseView -> Sound.Precise
    IndefiniteView -> Sound.Indefinite

--------------------------------------------------------------------------------
-- * Spec

data SpecViewError
  = SpecViewArgError ArgError
  | SpecViewUPostcondError ViewUPostcondError
  | SpecViewPostcondError PostcondTypeError

ppSpecViewError :: SpecViewError -> Doc ann
ppSpecViewError =
  \case
    SpecViewArgError argError -> ppArgError argError
    SpecViewUPostcondError uPostError -> ppViewUPostcondError uPostError
    SpecViewPostcondError postError -> ppPostcondTypeError postError

data SpecView
  = SpecView
      { vSpecPre :: SpecPrecondsView
      , vSpecPreSound :: SoundnessView
      , vSpecPost :: Maybe UPostcondView
      , vSpecPostSound :: SoundnessView
      }
  deriving (Eq, Generic, Ord, Show)

specView :: FuncSigRepr m fs -> Spec m fs -> SpecView
specView fsRep (Spec specPre specPreSound specPost specPostSound) =
  SpecView
   { vSpecPre = specPrecondsView specPre
   , vSpecPreSound = specSoundnessView specPreSound
   , vSpecPost = uPostcondView . toUPostcond fsRep <$> specPost
   , vSpecPostSound = specSoundnessView specPostSound
   }

viewSpec ::
  (fs ~ 'FS.FuncSig va ret args) =>
  ModuleContext m arch ->
  FuncSigRepr m fs ->
  SpecView ->
  Either SpecViewError (Spec m fs)
viewSpec modCtx fsRep@(FS.FuncSigRepr _ args _) vspec =
  do pre <-
       liftError SpecViewArgError (viewSpecPreconds mts args (vSpecPre vspec))

     -- Deserialize the postcondition
     uPost <-
       liftError
         SpecViewUPostcondError
         (commuteMaybe $ viewUPostcond modCtx fsRep <$> vSpecPost vspec)
     -- Typecheck the postcondition
     let typeCk p = typecheckPostcond p fsRep
     post <- liftError SpecViewPostcondError (commuteMaybe (typeCk <$> uPost))

     return $
       Spec
         { Spec.specPre = pre
         , Spec.specPreSound = viewSoundness (vSpecPreSound vspec)
         , Spec.specPost = post
         , Spec.specPostSound = viewSoundness (vSpecPostSound vspec)
         }
  where
    mts = modCtx ^. moduleTypes

    -- | Commute an applicative with Maybe. Equivalent to 'sequenceA'.
    commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
    commuteMaybe (Just val) = Just <$> val
    commuteMaybe Nothing    = pure Nothing

--------------------------------------------------------------------------------
-- * Specs

newtype SpecsView = SpecsView { getSpecsView :: NonEmpty SpecView }
  deriving (Eq, Generic, Ord, Show)

specsView :: FuncSigRepr m fs -> Specs m fs -> SpecsView
specsView funcSigRep =
  SpecsView . fmap (specView funcSigRep) . Spec.getSpecs

viewSpecs ::
  (fs ~ 'FS.FuncSig va ret args) =>
  ModuleContext m arch ->
  FuncSigRepr m fs ->
  SpecsView ->
  Either SpecViewError (Specs m fs)
viewSpecs modCtx funcSigRep (SpecsView vspecs) =
  Specs <$> traverse (viewSpec modCtx funcSigRep) vspecs

--------------------------------------------------------------------------------
-- * Map of specs

-- | Returns map of functions to specs, along with a list of functions that
-- weren't in the module. The list is guaranteed to be duplicate-free.
parseSpecs ::
  ModuleContext m arch ->
  Map FunctionName SpecsView ->
  Either SpecViewError (Map (FuncSymbol m) (SomeSpecs m), [FunctionName])
parseSpecs modCtx =
  foldM go (Map.empty, []) . Map.toList
  where
    go (mp, missingFuns) (fnName, vspecs) =
      case makeFuncSymbol (L.Symbol (functionNameToString fnName)) (modCtx ^. funcTypes) of
        Nothing -> Right (mp, fnName : missingFuns)
        Just funcSymb ->
          do Some fsRepr@FS.FuncSigRepr{} <-
               return (modCtx ^. funcTypes . funcSymbol funcSymb)
             specs <- viewSpecs modCtx fsRepr vspecs
             return (Map.insert funcSymb (SomeSpecs fsRepr specs) mp, missingFuns)

$(Aeson.TH.deriveJSON Opts.specPreconds ''SpecPrecondsView)
$(Aeson.TH.deriveJSON Opts.specSoundness ''SoundnessView)
$(Aeson.TH.deriveJSON Opts.spec ''SpecView)
$(Aeson.TH.deriveJSON Opts.specs ''SpecsView)
