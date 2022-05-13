{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Arbitrary instances

module View (viewTests) where

import           Control.Lens ((^.))
import           Data.Functor.Const (Const(Const, getConst))
import           Data.List.NonEmpty (NonEmpty)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Vector (Vector)
import qualified Data.Vector as Vec
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

instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary a => Arbitrary (Vector a) where
  arbitrary = Vec.fromList <$> arbitrary

instance Arbitrary a => Arbitrary (View.PtrShapeView a) where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary a => Arbitrary (View.ShapeView a) where
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
        \(vft :: View.FullTypeReprView) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \modCtx ->
                return $
                  case View.viewFullTypeRepr (modCtx ^. moduleTypes) vft of
                    Left _ -> () TQ.=== ()
                    Right (Some ft) ->
                      vft TQ.=== View.fullTypeReprView ft
    , TQ.testProperty "view" $
        -- Could get more coverage by adding another test that generates
        -- matching pairs of these.
        \((vs, vft) :: (View.ShapeView Ordering, View.FullTypeReprView)) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \modCtx ->
                return $
                  case View.viewFullTypeRepr (modCtx ^. moduleTypes) vft of
                    Left _ -> () TQ.=== ()
                    Right (Some ft) ->
                      case View.viewShape (modCtx ^. moduleTypes) (\_ _ o -> Right (Const o)) ft vs of
                        Left _ -> () TQ.=== ()
                        Right shape ->
                          vs TQ.=== View.shapeView getConst shape
    ]
