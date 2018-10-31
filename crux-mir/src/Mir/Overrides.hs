{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language PatternSynonyms #-}
{-# Language OverloadedStrings #-}
{-# Language RankNTypes #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language ViewPatterns #-}
{-# Language TypeApplications #-}

module Mir.Overrides (bindFn) where

import Control.Monad.IO.Class

import Data.Map (Map, fromList)
import qualified Data.Map as Map

import Data.Parameterized.Context (pattern Empty)

import Data.Text (Text)
import qualified Data.Text as Text

import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.CFG.Core (CFG, cfgArgTypes, cfgHandle, cfgReturnType)
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.OverrideSim

import Lang.Crucible.Types

import What4.FunctionName (FunctionName, functionNameFromText)
import What4.Interface

import Mir.Intrinsics (MIR)


data SomeOverride p sym where
  SomeOverride :: CtxRepr args -> TypeRepr ret -> Override p sym MIR args ret -> SomeOverride p sym


bindFn ::
  forall args ret blocks p sym rtp a r .
  IsExprBuilder sym =>
  Text -> CFG MIR blocks args ret ->
  OverrideSim p sym MIR rtp a r ()
bindFn fn cfg =
  getSymInterface >>= \s ->
  case Map.lookup fn (overrides s) of
    Nothing ->
      bindFnHandle (cfgHandle cfg) $ UseCFG cfg (postdomInfo cfg)
    Just (($ functionNameFromText fn) -> o) ->
      case o of
        SomeOverride argTys retTy f ->
          case (,) <$> testEquality (cfgReturnType cfg) retTy <*> testEquality (cfgArgTypes cfg) argTys of
            Nothing -> error $ "Mismatching override type for " ++ Text.unpack fn ++
                               ".\n\tExpected (" ++ show (cfgArgTypes cfg) ++ ") → " ++ show (cfgReturnType cfg) ++
                               "\n\tbut got (" ++ show argTys ++ ") → (" ++ show retTy ++ ")."
            Just (Refl, Refl) ->
              bindFnHandle (cfgHandle cfg) $ UseOverride f

  where
    overrides :: sym -> Map Text (FunctionName -> SomeOverride p sym)
    overrides s = fromList [( "::one[0]"
                          , \funName ->
                              SomeOverride Empty (BVRepr (knownNat @ 8))
                              (mkOverride' funName (BVRepr (knownNat @ 8))
                                (Sim $ do liftIO (putStrLn "Hello, I'm an override")
                                          v <- liftIO $ bvLit (s :: sym) knownNat 1
                                          return v))
                          )]
