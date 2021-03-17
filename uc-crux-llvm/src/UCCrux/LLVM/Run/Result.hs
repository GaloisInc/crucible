{-
Module       : UCCrux.LLVM.Run.Result
Description  : The result
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
-- Needed for GHC 8.6
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Run.Result
  ( BugfindingResult (..),
    SomeBugfindingResult (..),
    FunctionSummary (..),
    FunctionSummaryTag (..),
    DidHitBounds (..),
    functionSummaryTag,
    ppFunctionSummaryTag,
    makeFunctionSummary,
    ppFunctionSummary,
    printFunctionSummary,
  )
where

{- ORMOLU_DISABLE -}
import           Data.List.NonEmpty (NonEmpty((:|)), toList)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import           Data.Parameterized.Ctx (Ctx)

import UCCrux.LLVM.Classify.Types (TruePositive, ppTruePositive, Uncertainty, ppUncertainty, MissingPreconditionTag)
import UCCrux.LLVM.Constraints (isEmpty, ppConstraints, Constraints(..))
import UCCrux.LLVM.FullType.Type (FullType)
{- ORMOLU_ENABLE -}

data FunctionSummaryTag
  = TagUnclear
  | TagFoundBugs
  | TagSafeWithPreconditions
  | TagSafeUpToBounds
  | TagAlwaysSafe
  deriving (Bounded, Enum, Eq, Ord)

functionSummaryTag :: FunctionSummary m argTypes -> FunctionSummaryTag
functionSummaryTag =
  \case
    Unclear {} -> TagUnclear
    FoundBugs {} -> TagFoundBugs
    SafeWithPreconditions {} -> TagSafeWithPreconditions
    SafeUpToBounds {} -> TagSafeUpToBounds
    AlwaysSafe {} -> TagAlwaysSafe

ppFunctionSummaryTag :: FunctionSummaryTag -> Text
ppFunctionSummaryTag =
  \case
    TagUnclear -> "Unclear result, errors are either false or true positives"
    TagFoundBugs -> "Found likely bugs"
    TagSafeWithPreconditions -> "Function is safe if deduced preconditions are met"
    TagSafeUpToBounds -> "Function is safe up to the specified bounds on loops/recursion"
    TagAlwaysSafe -> "Function is always safe"

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data FunctionSummary m (argTypes :: Ctx (FullType m))
  = Unclear (NonEmpty Uncertainty)
  | FoundBugs (NonEmpty TruePositive)
  | SafeWithPreconditions DidHitBounds (Constraints m argTypes)
  | SafeUpToBounds
  | AlwaysSafe

data SomeBugfindingResult
  = forall m arch argTypes. SomeBugfindingResult (BugfindingResult m arch argTypes)

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8/8.6
-- compatibility.
data BugfindingResult m arch (argTypes :: Ctx (FullType m)) = BugfindingResult
  { uncertainResults :: [Uncertainty],
    deducedPreconditions :: [MissingPreconditionTag],
    summary :: FunctionSummary m argTypes
  }

ppFunctionSummary :: FunctionSummary m argTypes -> Doc Void
ppFunctionSummary fs =
  PP.pretty (ppFunctionSummaryTag (functionSummaryTag fs))
    <> case fs of
      Unclear uncertainties ->
        PP.pretty $
          ":\n" <> Text.intercalate "\n----------\n" (toList (fmap ppUncertainty uncertainties))
      FoundBugs bugs ->
        PP.pretty $
          ":\n" <> Text.intercalate "\n----------\n" (toList (fmap ppTruePositive bugs))
      SafeWithPreconditions b preconditions ->
        PP.pretty (ppFunctionSummaryTag (functionSummaryTag fs) <> ":\n")
          <> if didHit b
            then PP.pretty ("The loop/recursion bound is not exceeded, and:\n" :: Text)
            else ppConstraints preconditions
      AlwaysSafe -> "."
      SafeUpToBounds -> "."

printFunctionSummary :: FunctionSummary m argTypes -> Text
printFunctionSummary fs =
  PP.renderStrict (PP.layoutPretty PP.defaultLayoutOptions (ppFunctionSummary fs))

-- | Did symbolic execution run into loop/recursion bounds?
data DidHitBounds
  = -- | Yes, it did.
    DidHitBounds
  | -- | No, it didn\'t.
    DidntHitBounds
  deriving (Bounded, Enum, Eq, Ord, Show)

didHit :: DidHitBounds -> Bool
didHit =
  \case
    DidHitBounds -> True
    DidntHitBounds -> False

makeFunctionSummary ::
  Constraints m argTypes ->
  [Uncertainty] ->
  [TruePositive] ->
  DidHitBounds ->
  FunctionSummary m argTypes
makeFunctionSummary preconditions uncertainties truePositives bounds =
  case (isEmpty preconditions, uncertainties, truePositives, bounds) of
    (True, [], [], DidntHitBounds) -> AlwaysSafe
    (True, [], [], DidHitBounds) -> SafeUpToBounds
    (False, [], [], b) -> SafeWithPreconditions b preconditions
    (_, [], t : ts, _) -> FoundBugs (t :| ts)
    (_, u : us, _, _) -> Unclear (u :| us)
