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
    -- * SpecSoundness
    SpecSoundnessView(..),
    specSoundnessView,
    viewSpecSoundness,
    -- * Specs
    SpecViewError,
    ppSpecViewError,
    SpecView(..),
    specView,
    viewSpec,
  )
where

import           Control.Lens ((^.))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Data (Data)
import           Data.Vector (Vector)
import qualified Data.Vector as Vec
import           GHC.Generics (Generic)

import           Prettyprinter (Doc)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC (toListFC)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.FullType.FuncSig (FuncSigRepr)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), ModuleTypes)
import           UCCrux.LLVM.Postcondition.Type (toUPostcond, typecheckPostcond, PostcondTypeError, ppPostcondTypeError)
import           UCCrux.LLVM.Specs.Type (SpecPreconds, SpecSoundness(..), Spec (Spec))
import           UCCrux.LLVM.View.Constraint (ConstrainedShapeView, constrainedShapeView)
import           UCCrux.LLVM.View.Postcond (UPostcondView, uPostcondView, viewUPostcond, ViewUPostcondError, ppViewUPostcondError)
import           UCCrux.LLVM.View.Precond (ArgError, viewArgPreconds, ppArgError)
import qualified UCCrux.LLVM.Specs.Type as Spec

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
-- * SpecSoundness

data SpecSoundnessView
  = OverapproxView
  | UnderapproxView
  | PreciseView
  | ImpreciseView
  deriving (Bounded, Data, Enum, Eq, Generic, Ord, Show)

specSoundnessView :: SpecSoundness -> SpecSoundnessView
specSoundnessView =
  \case
    Overapprox -> OverapproxView
    Underapprox -> UnderapproxView
    Precise -> PreciseView
    Imprecise -> ImpreciseView

viewSpecSoundness :: SpecSoundnessView -> SpecSoundness
viewSpecSoundness =
  \case
    OverapproxView -> Overapprox
    UnderapproxView -> Underapprox
    PreciseView -> Precise
    ImpreciseView -> Imprecise

--------------------------------------------------------------------------------
-- * Specs

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
      , vSpecPreSound :: SpecSoundnessView
      , vSpecPost :: Maybe UPostcondView
      , vSpecPostSound :: SpecSoundnessView
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
         , Spec.specPreSound = viewSpecSoundness (vSpecPreSound vspec)
         , Spec.specPost = post
         , Spec.specPostSound = viewSpecSoundness (vSpecPostSound vspec)
         }
  where
    mts = modCtx ^. moduleTypes

    -- | Commute an applicative with Maybe
    commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
    commuteMaybe (Just val) = Just <$> val
    commuteMaybe Nothing    = pure Nothing

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''SpecPrecondsView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''SpecSoundnessView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''SpecView)
