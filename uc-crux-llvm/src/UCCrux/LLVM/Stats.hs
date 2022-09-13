{-
Module       : UCCrux.LLVM.Stats
Description  : Statistics
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Stats
  ( Stats (unimplementedFreq),
    getStats,
    ppStats,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Foldable (toList)
import           Data.Text (Text)
import           Data.Void (Void)
import           Panic (panicComponent)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           UCCrux.LLVM.Bug (BugBehavior, bugBehavior)
import           UCCrux.LLVM.Classify.Types (Located(..), ppLocated, DiagnosisTag, partitionUncertainty, diagnoseTag, TruePositive, ppTruePositive, Unfixable, ppUnfixable, Unfixed, ppUnfixed, diagnosisTag)
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, ppUnimplemented)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), FunctionSummaryTag)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Stats.Count (Count)
import qualified UCCrux.LLVM.Stats.Count as Count
import           UCCrux.LLVM.Stats.Freq (Freq)
import qualified UCCrux.LLVM.Stats.Freq as Freq
{- ORMOLU_ENABLE -}

data Stats = Stats
  { missingAnnotation :: !Count,
    symbolicallyFailedAssert :: !Count,
    timeouts :: !Count,
    truePositiveFreq :: Freq (Located TruePositive),
    unclassifiedFreq :: Freq BugBehavior,
    diagnosisFreq :: Freq DiagnosisTag,
    unimplementedFreq :: Freq Unimplemented,
    unfixableFreq :: Freq Unfixable,
    unfixedFreq :: Freq Unfixed,
    summaries :: Freq FunctionSummaryTag
  }
  deriving (Eq, Ord)

getStats :: BugfindingResult m arch argTypes -> Stats
getStats result =
  let (missingAnns, failedAsserts, unimplementeds, unclass, unfixed, unfixable, timeouts') = partitionUncertainty (uncertainResults result)
   in Stats
        { missingAnnotation = toEnum $ length missingAnns,
          symbolicallyFailedAssert = toEnum $ length failedAsserts,
          timeouts = toEnum $ length timeouts',
          truePositiveFreq =
            case Result.summary result of
              Result.FoundBugs bugs -> Freq.count (toList bugs)
              _ -> Freq.empty,
          unclassifiedFreq = Freq.count (map (bugBehavior . locatedValue) unclass),
          diagnosisFreq =
            Freq.count (map diagnosisTag (deducedPreconditions result)),
          unimplementedFreq = Freq.count (map (panicComponent . locatedValue) unimplementeds),
          unfixedFreq = Freq.count (map locatedValue unfixed),
          unfixableFreq = Freq.count (map locatedValue unfixable),
          summaries = Freq.singleton (Result.functionSummaryTag (Result.summary result))
        }

ppStats :: Stats -> Doc Void
ppStats stats =
  PP.vsep
    [ ppFreq "Overall results:" (PP.pretty . Result.ppFunctionSummaryTag) (summaries stats),
      ppFreq
        "True positives:"
        (PP.pretty . ppLocated ppTruePositive)
        (truePositiveFreq stats),
      ppFreq
        "Missing preconditions:"
        (PP.pretty . diagnoseTag)
        (diagnosisFreq stats),
      ppFreq
        "Unimplemented features:"
        (PP.pretty . ppUnimplemented)
        (unimplementedFreq stats),
      PP.nest
        2
        $ PP.vsep
          [ PP.pretty ("Uncertain results:" :: Text),
            PP.pretty ("Timeouts:" :: Text) PP.<+> PP.viaShow (timeouts stats),
            ppFreq "Unfixable errors:" (PP.pretty . ppUnfixable) (unfixableFreq stats),
            ppFreq "Unfixed errors:" (PP.pretty . ppUnfixed) (unfixedFreq stats),
            ppFreq
              "Unclassified errors:"
              PP.pretty
              (unclassifiedFreq stats),
            PP.pretty
              ("Missing annotations: " :: Text)
              <> PP.viaShow (missingAnnotation stats),
            PP.pretty ("Symbolically failing assertions: " :: Text)
              <> PP.viaShow (symbolicallyFailedAssert stats)
          ]
    ]
  where
    ppFreq headline ppTag fq =
      PP.nest 2 $
        PP.vsep
          ( PP.pretty (headline :: Text) :
            map
              (\(tag, freq) -> ppTag tag <> PP.pretty (": " :: Text) <> PP.viaShow freq)
              (Freq.toList fq)
          )

instance Semigroup Stats where
  stats1 <> stats2 =
    Stats
      { unclassifiedFreq = unclassifiedFreq stats1 <> unclassifiedFreq stats2,
        missingAnnotation = missingAnnotation stats1 `Count.plus` missingAnnotation stats2,
        symbolicallyFailedAssert = symbolicallyFailedAssert stats1 `Count.plus` symbolicallyFailedAssert stats2,
        timeouts = timeouts stats1 `Count.plus` timeouts stats2,
        truePositiveFreq = truePositiveFreq stats1 <> truePositiveFreq stats2,
        diagnosisFreq = diagnosisFreq stats1 <> diagnosisFreq stats2,
        unimplementedFreq = unimplementedFreq stats1 <> unimplementedFreq stats2,
        unfixedFreq = unfixedFreq stats1 <> unfixedFreq stats2,
        unfixableFreq = unfixableFreq stats1 <> unfixableFreq stats2,
        summaries = summaries stats1 <> summaries stats2
      }

instance Monoid Stats where
  mempty =
    Stats
      { unclassifiedFreq = Freq.empty,
        missingAnnotation = Count.zero,
        symbolicallyFailedAssert = Count.zero,
        timeouts = Count.zero,
        truePositiveFreq = Freq.empty,
        diagnosisFreq = Freq.empty,
        unimplementedFreq = Freq.empty,
        unfixedFreq = Freq.empty,
        unfixableFreq = Freq.empty,
        summaries = Freq.empty
      }
