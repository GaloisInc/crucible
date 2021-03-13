{-
Module       : UCCrux.LLVM.Run.Result
Description  : The result
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Run.Result
  ( BugfindingResult (..),
    SomeBugfindingResult (..),
    FunctionSummary (..),
    FunctionSummaryTag (..),
    functionSummaryTag,
    ppFunctionSummaryTag,
    makeFunctionSummary,
    printFunctionSummary,
  )
where

{- ORMOLU_DISABLE -}
import           Data.List.NonEmpty (NonEmpty((:|)), toList)
import           Data.Text (Text)
import qualified Data.Text as Text

import UCCrux.LLVM.Classify (TruePositive, ppTruePositive, Uncertainty, ppUncertainty, MissingPreconditionTag)
import UCCrux.LLVM.Constraints (isEmpty, ppConstraints, Constraints(..))
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

data FunctionSummary m argTypes
  = Unclear (NonEmpty Uncertainty)
  | FoundBugs (NonEmpty TruePositive)
  | SafeWithPreconditions Bool (Constraints m argTypes)
  | SafeUpToBounds
  | AlwaysSafe

data SomeBugfindingResult
  = forall m arch argTypes. SomeBugfindingResult (BugfindingResult m arch argTypes)

data BugfindingResult m arch argTypes = BugfindingResult
  { uncertainResults :: [Uncertainty],
    deducedPreconditions :: [MissingPreconditionTag],
    summary :: FunctionSummary m argTypes
  }

printFunctionSummary :: FunctionSummary m argTypes -> Text
printFunctionSummary =
  \case
    fs@(Unclear uncertainties) ->
      ppFunctionSummaryTag (functionSummaryTag fs) <> ":\n"
        <> Text.intercalate "\n----------\n" (toList (fmap ppUncertainty uncertainties))
    fs@(FoundBugs bugs) ->
      ppFunctionSummaryTag (functionSummaryTag fs) <> ":\n"
        <> Text.intercalate "\n----------\n" (toList (fmap ppTruePositive bugs))
    fs@(SafeWithPreconditions b preconditions) ->
      ppFunctionSummaryTag (functionSummaryTag fs) <> ":\n"
        <> if b
          then "The loop/recursion bound is not exceeded, and:\n"
          else
            ""
              <> Text.pack (show (ppConstraints preconditions))
    fs@AlwaysSafe -> ppFunctionSummaryTag (functionSummaryTag fs) <> "."
    fs@SafeUpToBounds -> ppFunctionSummaryTag (functionSummaryTag fs) <> "."

makeFunctionSummary ::
  Constraints m argTypes ->
  [Uncertainty] ->
  [TruePositive] ->
  -- | Did we hit the bounds?
  Bool ->
  FunctionSummary m argTypes
makeFunctionSummary preconditions uncertainties truePositives bounds =
  case (isEmpty preconditions, uncertainties, truePositives, bounds) of
    (True, [], [], False) -> AlwaysSafe
    (True, [], [], True) -> SafeUpToBounds
    (False, [], [], b) -> SafeWithPreconditions b preconditions
    (_, [], t : ts, _) -> FoundBugs (t :| ts)
    (_, u : us, _, _) -> Unclear (u :| us)
