{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Arbitrary instances

module View (viewTests) where

import           Control.Lens ((^.))
import qualified Data.Aeson as Aeson
import           Data.Functor.Const (Const(Const, getConst))
import           Data.List.NonEmpty (NonEmpty)
import           Data.String (fromString)
import           Data.Text (Text)
import           Data.Sequence (Seq)
import           Data.Vector (Vector)
import qualified Data.Vector as Vec
import           Numeric.Natural (Natural)

import           Data.Parameterized.Some (Some(Some))

import qualified Text.LLVM.AST as L

import           Lang.Crucible.LLVM.DataLayout (Alignment, exponentToAlignment)

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH
import qualified Test.Tasty.Hedgehog as THG
import qualified Hedgehog as HG
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           UCCrux.LLVM.Context.Module (ModuleContext, moduleTypes)
import           UCCrux.LLVM.FullType.Type (ModuleTypes)
import qualified UCCrux.LLVM.View as View

import qualified Utils

--------------------------------------------------------------------------------
-- * base

genInt32 :: HG.Gen Int
genInt32 = Gen.integral (Range.linear 0 32)

genList32 :: HG.Gen a -> HG.Gen [a]
genList32 = Gen.list (Range.linear 0 32)

genNonEmpty32 :: HG.Gen a -> HG.Gen (NonEmpty a)
genNonEmpty32 = Gen.nonEmpty (Range.linear 0 32)

genSeq32 :: HG.Gen a -> HG.Gen (Seq a)
genSeq32 = Gen.seq (Range.linear 0 32)

genVector32 :: HG.Gen a -> HG.Gen (Vector a)
genVector32 g = Vec.fromList <$> genList32 g

genNat64 :: HG.Gen Natural
genNat64 = Gen.integral (Range.linear 0 64)

genText16 :: HG.Gen Text
genText16 = Gen.text (Range.linear 0 16) Gen.unicode

genNat :: HG.Gen Natural
genNat = Gen.integral (Range.linear 0 aBillion)
  where aBillion = 1000000000

genInteger :: HG.Gen Integer
genInteger = Gen.integral (Range.linear 0 aBillion)
  where aBillion = 1000000000

--------------------------------------------------------------------------------
-- * Third party

genAlign :: HG.Gen Alignment
genAlign = exponentToAlignment <$> genNat64

genICmpOp :: HG.Gen L.ICmpOp
genICmpOp =
  Gen.element [L.Ieq, L.Ine, L.Iugt, L.Iuge, L.Iult, L.Iule, L.Isgt, L.Isge, L.Islt, L.Isle]

--------------------------------------------------------------------------------
-- * UC-Crux

genTypeName :: HG.Gen View.TypeName
genTypeName = View.TypeName <$> genText16

genConstraintView :: HG.Gen View.ConstraintView
genConstraintView =
  Gen.choice
    [ View.AlignedView <$> genAlign
    , View.BVCmpView <$> genICmpOp <*> genNat <*> genInteger
    ]

genVarArgsReprView :: HG.Gen View.VarArgsReprView
genVarArgsReprView = Gen.enumBounded

genStructPackedReprView :: HG.Gen View.StructPackedReprView
genStructPackedReprView = Gen.enumBounded

genFloatInfoReprView :: HG.Gen View.FloatInfoReprView
genFloatInfoReprView = Gen.enumBounded

genFullTypeReprView :: HG.Gen View.FullTypeReprView
genFullTypeReprView =
  -- Choice shrinks towards the first item, so "simpler" constructors go first
  Gen.recursive
    Gen.choice
    [ View.FTIntReprView . View.Width <$> genNat
    , View.FTFloatReprView <$> genFloatInfoReprView
    ]
    [ Gen.subterm genFullTypeReprView View.FTUnboundedArrayReprView
    , do nat <- genNat
         Gen.subterm genFullTypeReprView (View.FTArrayReprView nat)
    , do vsp <- genStructPackedReprView
         vfields <- genList32 genFullTypeReprView
         return (View.FTStructReprView vsp vfields)
    , do vva <- genVarArgsReprView
         vargs <- genList32 genFullTypeReprView
         return (View.FTVoidFuncPtrReprView vva vargs)
    , do vva <- genVarArgsReprView
         vargs <- genList32 genFullTypeReprView
         vret <- genFullTypeReprView
         return (View.FTNonVoidFuncPtrReprView vva vret vargs)
    , View.FTPtrReprView <$> genPartTypeReprView
    ]

genPartTypeReprView :: HG.Gen View.PartTypeReprView
genPartTypeReprView =
  Gen.choice
    [ View.PTAliasReprView <$> genTypeName
    , View.PTFullReprView <$> genFullTypeReprView
    ]

genPtrShapeView :: HG.Gen vtag -> HG.Gen (View.PtrShapeView vtag)
genPtrShapeView genTag =
  Gen.recursive
    Gen.choice
    [ return View.ShapeUnallocatedView
    , View.ShapeAllocatedView <$> genInt32
    ]
    [ View.ShapeInitializedView <$> genSeq32 (genShapeView genTag)
    ]

genShapeView :: HG.Gen vtag -> HG.Gen (View.ShapeView vtag)
genShapeView genTag =
  Gen.recursive
    Gen.choice
    [ View.ShapeIntView <$> genTag
    , View.ShapeFloatView <$> genTag
    , View.ShapeOpaquePtrView <$> genTag
    ]
    [ do vtag <- genTag
         velems <- genSeq32 (genShapeView genTag)
         return (View.ShapeUnboundedArrayView vtag velems)
    , do vtag <- genTag
         velems <- genNonEmpty32 (genShapeView genTag)
         return (View.ShapeArrayView vtag velems)
    , do vtag <- genTag
         vfields <- genVector32 (genShapeView genTag)
         return (View.ShapeStructView vtag vfields)
    , View.ShapeFuncPtrView <$> genTag
    , do vtag <- genTag
         vsub <- genPtrShapeView genTag
         return (View.ShapePtrView vtag vsub)
    ]

genCursorView :: HG.Gen View.CursorView
genCursorView =
  Gen.recursive
    Gen.choice
    [return View.HereView]
    [ do idx <- genInt32
         Gen.subterm genCursorView (View.DereferenceView idx)
    , do len <- genNat64
         idx <- genNat64
         Gen.subterm genCursorView (View.IndexView len idx)
    , do fld <- genInt32
         Gen.subterm genCursorView (View.FieldView fld)
    ]

genConstrainedShapeView :: HG.Gen View.ConstrainedShapeView
genConstrainedShapeView =
  View.ConstrainedShapeView <$> genShapeView (genList32 genConstraintView)

genClobberValueView :: HG.Gen View.ClobberValueView
genClobberValueView =
  View.ClobberValueView
  <$> genCursorView
  <*> genConstrainedShapeView
  <*> genFullTypeReprView

--------------------------------------------------------------------------------
-- * Tests

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
    [ TH.testCase "view-encode-FTIntReprView" $
        TH.assertEqual
          "view-encode-FTIntReprView"
          "{\"tag\":\"FTIntReprView\",\"contents\":{\"getWidth\":1}}"
          (Aeson.encode (View.FTIntReprView (View.Width 1)))
    , prop "view-constraint" $
        do vc <- HG.forAll genConstraintView
           ignoreError (View.viewConstraint vc) $
             \(Some c) ->
               vc HG.=== View.constraintView c
    , prop "view-ft" $
        do vft <- HG.forAll genFullTypeReprView
           res <-
            HG.evalIO $
              withEmptyModCtx $
                \_modCtx mts ->
                  return $
                    case eitherToMaybe (View.viewFullTypeRepr mts vft) of
                      Nothing -> Nothing
                      Just (Some ft) -> Just (View.fullTypeReprView ft)
           vft ==? res
    , prop "view-shape" $
        do -- Could get more coverage by adding another test that generates
           -- matching pairs of these.
           vft <- HG.forAll genFullTypeReprView
           vs <- HG.forAll (genShapeView Gen.bool)
           res <-
            HG.evalIO $
              withEmptyModCtx $
                \_modCtx mts ->
                  return $
                    case eitherToMaybe (View.viewFullTypeRepr mts vft) of
                      Nothing -> Nothing
                      Just (Some ft) ->
                        case eitherToMaybe (View.viewShape mts (\_ b -> Right (Const b)) ft vs) of
                          Just s -> Just (View.shapeView getConst s)
                          Nothing -> Nothing
           vs ==? res
    , prop "view-cursor" $
        do -- Could get more coverage by adding another test that generates
           -- matching pairs of these.
           vft <- HG.forAll genFullTypeReprView
           vc <- HG.forAll genCursorView
           res <-
            HG.evalIO $
              withEmptyModCtx $
                \_modCtx mts ->
                  return $
                    case eitherToMaybe (View.viewFullTypeRepr mts vft) of
                      Nothing -> Nothing
                      Just (Some ft) ->
                        case eitherToMaybe (View.viewCursor mts ft vc) of
                          Just (Some c) -> Just (View.cursorView c)
                          Nothing -> Nothing
           vc ==? res
    , prop "view-clobber-value" $
        do -- Could get more coverage by adding another test that generates
           -- matching pairs of these.
           vft <- HG.forAll genFullTypeReprView
           vcv <- HG.forAll genClobberValueView
           res <-
            HG.evalIO $
              withEmptyModCtx $
                \_modCtx mts ->
                  return $
                    case eitherToMaybe (View.viewFullTypeRepr mts vft) of
                      Nothing -> Nothing
                      Just (Some ft) ->
                        case eitherToMaybe (View.viewClobberValue mts ft vcv) of
                          Just cv -> Just (View.clobberValueView cv)
                          Nothing -> Nothing
           vcv ==? res
    ]
  where
    prop nm p = THG.testPropertyNamed nm (fromString nm) (HG.property p)

    eitherToMaybe =
      \case
        Left {} -> Nothing
        Right v -> Just v

    a ==? b =
      case b of
        Just v -> a HG.=== v
        Nothing -> () HG.=== ()

    ignoreError x k =
      case x of
        Left _ -> () HG.=== ()
        Right v -> k v
