{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module View (viewTests) where

import           Control.Lens ((^.))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Numeric.Natural (Natural)

import           Data.Parameterized.Some (Some(Some))

import qualified Text.LLVM.AST as L

import qualified Test.Tasty as TT
import qualified Test.Tasty.QuickCheck as TQ
import           Test.QuickCheck.Arbitrary.Generic (Arbitrary(arbitrary, shrink), genericArbitrary, genericShrink)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import qualified UCCrux.LLVM.View as View

import qualified Utils

instance Arbitrary Natural where
  arbitrary = fromIntegral . abs <$> (arbitrary :: TQ.Gen Int)

instance Arbitrary View.Width where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.TypeName where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Text where
  arbitrary = Text.pack <$> (arbitrary :: TQ.Gen String)

instance Arbitrary View.VarArgsReprView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.StructPackedReprView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.FloatInfoReprView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.FullTypeReprView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.PartTypeReprView where
  arbitrary = genericArbitrary
  shrink = genericShrink

withEmptyModCtx :: (forall m arch. ModuleContext m arch -> IO a) -> IO a
withEmptyModCtx act =
  Utils.withOptions (Just L.emptyModule) "View.hs" $
    \_appCtx modCtx _halloc _cruxOpts _llOpts -> act modCtx

viewTests :: TT.TestTree
viewTests =
  TT.testGroup
    "view tests"
    [ TQ.testProperty "view" $
        \(ftv :: View.FullTypeReprView) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \modCtx ->
                return $
                  case View.viewFullTypeRepr (modCtx ^. moduleTypes) ftv of
                    Left _ -> () TQ.=== ()
                    Right (Some ft) ->
                      ftv TQ.=== View.fullTypeReprView ft
    ]
