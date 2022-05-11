{-
Module       : UCCrux.LLVM.Run.Result
Description  : The result
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Run.Result
  ( BugfindingResult (..),
    SomeBugfindingResult (..),
    SomeBugfindingResult' (..),
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
import           Data.Sequence (Seq)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import           Data.Parameterized.Ctx (Ctx)
import           Data.Parameterized.Context (Assignment)

import           UCCrux.LLVM.Classify.Types (Located, ppLocated, TruePositive, ppTruePositive, Uncertainty, ppUncertainty, Diagnosis)
import           UCCrux.LLVM.FullType.Type (FullType, FullTypeRepr)
import           UCCrux.LLVM.Precondition (isEmpty, ppConstraints, Constraints(..))
import           UCCrux.LLVM.Run.Simulate (UCCruxSimulationResult)
import           UCCrux.LLVM.Run.Unsoundness (Unsoundness, ppUnsoundness)
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
    TagUnclear ->
      "Unclear result, errors are either false or true positives (or timeouts were hit)"
    TagFoundBugs -> "Found likely bugs"
    TagSafeWithPreconditions -> "Function is safe if deduced preconditions are met"
    TagSafeUpToBounds -> "Function is safe up to the specified bounds on loops/recursion"
    TagAlwaysSafe -> "Function is always safe"

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
--
-- TODO: It would be great to have more provenance information for the
-- 'Constraints'. What bug does a given constraint help avoid? On what line?
data FunctionSummary m (argTypes :: Ctx (FullType m))
  = Unclear (NonEmpty (Located Uncertainty))
  | FoundBugs (NonEmpty (Located TruePositive))
  | SafeWithPreconditions DidHitBounds Unsoundness (Constraints m argTypes)
  | SafeUpToBounds Unsoundness
  | AlwaysSafe Unsoundness

-- | The result of running the bugfinding/contract inference main loop. Contains
-- both the final, summary result ('BugfindingResult'), as well as the sequence
-- of simulation results that led to it ('UCCruxSimulationResult'), which is
-- consumed in particular during crash-equivalence checking.
data SomeBugfindingResult m arch
  = forall argTypes.
    SomeBugfindingResult
      (Assignment (FullTypeRepr m) argTypes)
      (BugfindingResult m arch argTypes)
      (Seq (UCCruxSimulationResult m arch argTypes))

data SomeBugfindingResult'
  = forall m arch. SomeBugfindingResult' (SomeBugfindingResult m arch)

-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data BugfindingResult m arch (argTypes :: Ctx (FullType m)) = BugfindingResult
  { uncertainResults :: [Located Uncertainty],
    deducedPreconditions :: [Diagnosis],
    summary :: FunctionSummary m argTypes
  }

ppFunctionSummary :: FunctionSummary m argTypes -> Doc Void
ppFunctionSummary fs =
  PP.pretty (ppFunctionSummaryTag (functionSummaryTag fs))
    <> case fs of
      Unclear uncertainties ->
        PP.pretty $
          ":\n"
            <> Text.intercalate
              "\n----------\n"
              (toList (fmap (ppLocated ppUncertainty) uncertainties))
      FoundBugs bugs ->
        PP.pretty $
          ":\n"
            <> Text.intercalate
              "\n----------\n"
              (toList (fmap (ppLocated ppTruePositive) bugs))
      SafeWithPreconditions b u preconditions ->
        PP.pretty
          (":\n" :: Text)
          <> if didHit b
            then PP.pretty ("The loop/recursion bound is not exceeded, and:\n" :: Text)
            else
              ppConstraints preconditions
                <> ppUnsoundness' u
      AlwaysSafe u -> "." <> ppUnsoundness' u
      SafeUpToBounds u -> "." <> ppUnsoundness' u
  where
    ppUnsoundness' u =
      if mempty == u
        then mempty
        else
          PP.pretty
            ( Text.unwords
                [ "\nIn addition to any assumptions listed above, the",
                  "following sources of unsoundness may invalidate this",
                  "safety claim:\n"
                ]
            )
            <> ppUnsoundness u

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

-- NOTE(lb): Unsoundness is not reported to the user when the result is
-- uncertain, because no claim is being made that unsoundness could make false.
makeFunctionSummary ::
  Constraints m argTypes ->
  [Located Uncertainty] ->
  [Located TruePositive] ->
  DidHitBounds ->
  Unsoundness ->
  FunctionSummary m argTypes
makeFunctionSummary preconditions uncertainties truePositives bounds unsoundness =
  case (isEmpty preconditions, uncertainties, truePositives, bounds) of
    (True, [], [], DidntHitBounds) -> AlwaysSafe unsoundness
    (True, [], [], DidHitBounds) -> SafeUpToBounds unsoundness
    (False, [], [], b) -> SafeWithPreconditions b unsoundness preconditions
    (_, [], t : ts, _) -> FoundBugs (t :| ts)
    (_, u : us, _, _) -> Unclear (u :| us)
