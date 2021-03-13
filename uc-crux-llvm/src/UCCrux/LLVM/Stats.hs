{-
Module       : UCCrux.LLVM.Stats
Description  : Statistics
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.Stats
  ( Stats (unimplementedFreq),
    getStats,
    ppStats,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Void (Void)
import           Panic (panicComponent)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import           UCCrux.LLVM.Classify (TruePositiveTag, MissingPreconditionTag, partitionUncertainty, diagnose, ppTruePositiveTag, truePositiveTag, Unfixable, ppUnfixable, Unfixed, ppUnfixed)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), FunctionSummaryTag)
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Errors.Unimplemented (Unimplemented, ppUnimplemented)
{- ORMOLU_ENABLE -}

data Stats = Stats
  { unclassified :: !Word,
    missingAnnotation :: !Word,
    symbolicallyFailedAssert :: !Word,
    truePositiveFreq :: Map TruePositiveTag Word,
    missingPreconditionFreq :: Map MissingPreconditionTag Word,
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
  let (missingAnns, failedAsserts, unimplementeds, unclass, unfixed, unfixable) = partitionUncertainty (uncertainResults result)
   in Stats
        { unclassified = fromIntegral $ length unclass,
          missingAnnotation = fromIntegral $ length missingAnns,
          symbolicallyFailedAssert = fromIntegral $ length failedAsserts,
          truePositiveFreq =
            case Result.summary result of
              Result.FoundBugs bugs -> frequencies (map truePositiveTag (toList bugs))
              _ -> Map.empty,
          missingPreconditionFreq =
            frequencies (deducedPreconditions result),
          unimplementedFreq = frequencies (map panicComponent unimplementeds),
          unfixedFreq = frequencies unfixed,
          unfixableFreq = frequencies unfixable,
          summaries = Map.singleton (Result.functionSummaryTag (Result.summary result)) 1
        }

ppStats :: Stats -> Doc Void
ppStats stats =
  PP.vsep
    [ ppFreq "Overall results:" (PP.pretty . Result.ppFunctionSummaryTag) (summaries stats),
      ppFreq
        "True positives:"
        (PP.pretty . ppTruePositiveTag)
        (truePositiveFreq stats),
      ppFreq
        "Missing preconditions:"
        (PP.pretty . diagnose)
        (missingPreconditionFreq stats),
      ppFreq
        "Unimplemented features:"
        (PP.pretty . ppUnimplemented)
        (unimplementedFreq stats),
      PP.nest
        2
        $ PP.vsep
          [ PP.pretty "Uncertain results:",
            PP.nest
              2
              $ PP.vsep
                [ PP.pretty "Unclassified errors: " <> PP.viaShow (unclassified stats),
                  ppFreq "Unfixable errors:" (PP.pretty . ppUnfixable) (unfixableFreq stats),
                  ppFreq "Unfixed errors:" (PP.pretty . ppUnfixed) (unfixedFreq stats)
                ],
            PP.pretty
              "Missing annotations: "
              <> PP.viaShow (missingAnnotation stats),
            PP.pretty "Symbolically failing assertions: " <> PP.viaShow (missingAnnotation stats)
          ]
    ]
  where
    ppFreq headline ppTag mp =
      PP.nest 2 $
        PP.vsep
          ( PP.pretty headline :
            map
              (\(tag, freq) -> ppTag tag <> PP.pretty ": " <> PP.viaShow freq)
              (Map.toList mp)
          )

instance Semigroup Stats where
  stats1 <> stats2 =
    let unionWithPlus field = Map.unionWith (+) (field stats1) (field stats2)
     in Stats
          { unclassified = unclassified stats1 + unclassified stats2,
            missingAnnotation = missingAnnotation stats1 + missingAnnotation stats2,
            symbolicallyFailedAssert = symbolicallyFailedAssert stats1 + symbolicallyFailedAssert stats2,
            truePositiveFreq = unionWithPlus truePositiveFreq,
            missingPreconditionFreq = unionWithPlus missingPreconditionFreq,
            unimplementedFreq = unionWithPlus unimplementedFreq,
            unfixedFreq = unionWithPlus unfixedFreq,
            unfixableFreq = unionWithPlus unfixableFreq,
            summaries = Map.unionWith (+) (summaries stats1) (summaries stats2)
          }

instance Monoid Stats where
  mempty =
    Stats
      { unclassified = 0,
        missingAnnotation = 0,
        symbolicallyFailedAssert = 0,
        truePositiveFreq = Map.empty,
        missingPreconditionFreq = Map.empty,
        unimplementedFreq = Map.empty,
        unfixedFreq = Map.empty,
        unfixableFreq = Map.empty,
        summaries = Map.empty
      }
