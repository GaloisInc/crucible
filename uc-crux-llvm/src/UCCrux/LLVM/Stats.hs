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
import           Control.Lens ((^.), to)
import           Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)
import           Panic (panicComponent)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import           UCCrux.LLVM.Classify.Types (Located(..), ppLocated, DiagnosisTag, partitionUncertainty, diagnoseTag, TruePositive, ppTruePositive, Unfixable, ppUnfixable, Unfixed, ppUnfixed, doc, diagnosisTag)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), FunctionSummaryTag)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, ppUnimplemented)
{- ORMOLU_ENABLE -}

data Stats = Stats
  { missingAnnotation :: !Word,
    symbolicallyFailedAssert :: !Word,
    timeouts :: !Word,
    truePositiveFreq :: Map (Located TruePositive) Word,
    unclassifiedFreq :: Map Text Word,
    diagnosisFreq :: Map DiagnosisTag Word,
    unimplementedFreq :: Map Unimplemented Word,
    unfixableFreq :: Map Unfixable Word,
    unfixedFreq :: Map Unfixed Word,
    summaries :: Map FunctionSummaryTag Word
  }
  deriving (Eq, Ord)

frequencies :: Ord a => [a] -> Map a Word
frequencies = foldr (\tag mp -> Map.insertWith (+) tag 1 mp) Map.empty

getStats :: BugfindingResult m arch argTypes -> Stats
getStats result =
  let (missingAnns, failedAsserts, unimplementeds, unclass, unfixed, unfixable, timeouts') = partitionUncertainty (uncertainResults result)
   in Stats
        { missingAnnotation = toEnum $ length missingAnns,
          symbolicallyFailedAssert = toEnum $ length failedAsserts,
          timeouts = toEnum $ length timeouts',
          truePositiveFreq =
            case Result.summary result of
              Result.FoundBugs bugs -> frequencies (toList bugs)
              _ -> Map.empty,
          unclassifiedFreq =
            frequencies (map (^. to locatedValue . doc . to render . to trunc) unclass),
          diagnosisFreq =
            frequencies (map diagnosisTag (deducedPreconditions result)),
          unimplementedFreq = frequencies (map (panicComponent . locatedValue) unimplementeds),
          unfixedFreq = frequencies (map locatedValue unfixed),
          unfixableFreq = frequencies (map locatedValue unfixable),
          summaries = Map.singleton (Result.functionSummaryTag (Result.summary result)) 1
        }
  where
    render = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
    -- Truncation is necessary because some error messages include full symbolic
    -- terms in them.
    truncLen = 80 -- Arbitrary
    trunc txt =
      Text.replace "\n" "; " $
        if Text.length txt > truncLen
          then Text.take truncLen txt <> "..."
          else txt

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
    ppFreq headline ppTag mp =
      PP.nest 2 $
        PP.vsep
          ( PP.pretty (headline :: Text) :
            map
              (\(tag, freq) -> ppTag tag <> PP.pretty (": " :: Text) <> PP.viaShow freq)
              (Map.toList mp)
          )

instance Semigroup Stats where
  stats1 <> stats2 =
    let unionWithPlus field = Map.unionWith (+) (field stats1) (field stats2)
     in Stats
          { unclassifiedFreq = unionWithPlus unclassifiedFreq,
            missingAnnotation = missingAnnotation stats1 + missingAnnotation stats2,
            symbolicallyFailedAssert = symbolicallyFailedAssert stats1 + symbolicallyFailedAssert stats2,
            timeouts = timeouts stats1 + timeouts stats2,
            truePositiveFreq = unionWithPlus truePositiveFreq,
            diagnosisFreq = unionWithPlus diagnosisFreq,
            unimplementedFreq = unionWithPlus unimplementedFreq,
            unfixedFreq = unionWithPlus unfixedFreq,
            unfixableFreq = unionWithPlus unfixableFreq,
            summaries = Map.unionWith (+) (summaries stats1) (summaries stats2)
          }

instance Monoid Stats where
  mempty =
    Stats
      { unclassifiedFreq = Map.empty,
        missingAnnotation = 0,
        symbolicallyFailedAssert = 0,
        timeouts = 0,
        truePositiveFreq = Map.empty,
        diagnosisFreq = Map.empty,
        unimplementedFreq = Map.empty,
        unfixedFreq = Map.empty,
        unfixableFreq = Map.empty,
        summaries = Map.empty
      }
