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

import           Lang.Crucible.LLVM.DataLayout (Alignment, exponentToAlignment)

import qualified Test.Tasty as TT
import qualified Test.Tasty.QuickCheck as TQ
import           Test.QuickCheck.Arbitrary.Generic (Arbitrary(arbitrary, shrink), genericArbitrary, genericShrink)

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.FullType.Type (ModuleTypes)
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

instance Arbitrary View.CursorView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary Alignment where
  arbitrary = exponentToAlignment <$> arbitrary

instance Arbitrary L.ICmpOp where
  arbitrary = genericArbitrary

instance Arbitrary View.ConstraintView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.ConstrainedShapeView where
  arbitrary = genericArbitrary
  shrink = genericShrink

instance Arbitrary View.ClobberValueView where
  arbitrary = genericArbitrary
  shrink = genericShrink

withEmptyModCtx ::
  (forall m arch. ModuleContext m arch -> ModuleTypes m -> IO a) ->
  IO a
withEmptyModCtx act =
  Utils.withOptions (Just L.emptyModule) "View.hs" $
    \_appCtx modCtx _halloc _cruxOpts _llOpts -> act modCtx (modCtx ^. moduleTypes)

viewTests :: TT.TestTree
viewTests =
  TT.testGroup
    "view tests"
    [ TQ.testProperty "view-constraint" $
        \(vc :: View.ConstraintView) ->
          ignoreError (View.viewConstraint vc) $
            \(Some c) ->
              vc TQ.=== View.constraintView c
    , TQ.testProperty "view-ft" $
        \(vft :: View.FullTypeReprView) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \_modCtx mts ->
                return $
                  ignoreError (View.viewFullTypeRepr mts vft) $
                    \(Some ft) ->
                      vft TQ.=== View.fullTypeReprView ft
    , TQ.testProperty "view-shape" $
        -- Could get more coverage by adding another test that generates
        -- matching pairs of these.
        \((vs, vft) :: (View.ShapeView Ordering, View.FullTypeReprView)) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \_modCtx mts ->
                return $
                  ignoreError (View.viewFullTypeRepr mts vft) $
                    \(Some ft) ->
                      ignoreError (View.viewShape mts (\_ o -> Right (Const o)) ft vs) $
                        \shape ->
                          vs TQ.=== View.shapeView getConst shape
    , TQ.testProperty "view-cursor" $
        -- Could get more coverage by adding another test that generates
        -- matching pairs of these.
        \((vc, vft) :: (View.CursorView, View.FullTypeReprView)) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \_modCtx mts ->
                return $
                  ignoreError (View.viewFullTypeRepr mts vft) $
                    \(Some ft) ->
                      ignoreError (View.viewCursor mts ft vc) $
                        \(Some cursor) ->
                          vc TQ.=== View.cursorView cursor
    , TQ.testProperty "view-clobber-value" $
        \((vcv, vft) :: (View.ClobberValueView, View.FullTypeReprView)) ->
          TQ.ioProperty $
            withEmptyModCtx $
              \_modCtx mts ->
                return $
                  ignoreError (View.viewFullTypeRepr mts vft) $
                    \(Some ft) ->
                      ignoreError (View.viewClobberValue mts ft vcv) $
                        \cv ->
                          vcv TQ.=== View.clobberValueView cv
    ]
  where ignoreError x k =
          case x of
            Left _ -> () TQ.=== ()
            Right v -> k v
