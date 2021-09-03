{-
Module       : UCCrux.LLVM.Equivalence
Description  : Check traces for crash equivalence or crash ordering.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.Equivalence
  ( CrashDiff,
    NonEmptyCrashDiff,
    crashDiffNonEmpty,
    crashDiffIsEmpty,
    ppCrashDiff,
    renderCrashDiff,
    getCrashDiffs,
    reportDiffs,
    checkEquiv,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.))
import           Control.Monad (when, unless, void)
import           Data.Foldable (for_, toList)
import qualified Data.Map.Strict as Map
import           Data.Maybe (catMaybes, isNothing, maybeToList)
import           Data.Sequence (Seq)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Void (Void)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified What4.ProgramLoc as What4

-- crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm

-- crux
import Crux.Config.Common
import Crux.Log as Crux

-- crux-llvm
import Crux.LLVM.Config (LLVMOptions)

 -- local
import           UCCrux.LLVM.Classify.Types (Located(location, locatedValue), Explanation, partitionExplanations, TruePositive, Unfixed, Unfixable, partitionUncertainty)
import           UCCrux.LLVM.Equivalence.Config (OrderOrEquivalence(..))
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext)
import           UCCrux.LLVM.Logging (Verbosity(Low))
import           UCCrux.LLVM.Run.Simulate (UCCruxSimulationResult, explanations)
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult(..))
import           UCCrux.LLVM.Run.Loop (zipResults)
{- ORMOLU_ENABLE -}

data CrashDiff = CrashDiff
  { _bugDiff :: Set (Located TruePositive),
    -- | Failed assertions
    _assertionDiff :: Set (Located ()),
    -- | Unclassified errors
    _unclassifiedDiff :: Set (Located ()),
    _unfixedDiff :: Set (Located Unfixed),
    _unfixableDiff :: Set (Located Unfixable)
  }
  deriving (Eq, Ord)

instance Semigroup CrashDiff where
  CrashDiff s1 s2 s3 s4 s5 <> CrashDiff t1 t2 t3 t4 t5 =
    CrashDiff (s1 <> t1) (s2 <> t2) (s3 <> t3) (s4 <> t4) (s5 <> t5)

instance Monoid CrashDiff where
  mempty = CrashDiff Set.empty Set.empty Set.empty Set.empty Set.empty

newtype NonEmptyCrashDiff = NonEmptyCrashDiff CrashDiff
  deriving (Eq, Ord, Monoid, Semigroup)

crashDiffNonEmpty :: CrashDiff -> Maybe NonEmptyCrashDiff
crashDiffNonEmpty diff =
  if diff == mempty
    then Nothing
    else Just (NonEmptyCrashDiff diff)

crashDiffIsEmpty :: CrashDiff -> Bool
crashDiffIsEmpty = isNothing . crashDiffNonEmpty

ppCrashDiff :: CrashDiff -> Doc Void
ppCrashDiff (CrashDiff posDiff assertDiff unclassDiff unfixedDiff unfixableDiff) =
  PP.vcat $
    catMaybes
      [ printDiff posDiff "Likely bugs at",
        printDiff assertDiff "Assertion failures at",
        printDiff unclassDiff "Unclassified errors at",
        printDiff unfixedDiff "Unfixed errors at",
        printDiff unfixableDiff "Unfixable errors at"
      ]
  where
    headerWithBullets header lst =
      PP.nest 2 (PP.vcat (header : map ((PP.pretty ("-" :: Text) PP.<+>) . PP.pretty) lst))
    printDiff :: Set (Located a) -> Text -> Maybe (Doc Void)
    printDiff diff header =
      if Set.null diff
        then Nothing
        else
          Just $
            headerWithBullets
              (PP.pretty header)
              (map (show . What4.plSourceLoc . location) (toList diff))

renderCrashDiff :: CrashDiff -> Text
renderCrashDiff =
  PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions . ppCrashDiff

-- | Compute the \"crash difference\" between two sets of results.
--
-- This ignores:
--
-- * timeouts,
-- * errors that are missing annotations, and
-- * executions that encountered unimplemented features of UC-Crux-LLVM.
--
-- The behavior of this function is documented in the README, updates should be
-- reflected there.
--
-- Recall that a total function @f : (A, A) -> Bool@ can be considered a
-- description of a binary relation on @A@:
-- @{ (x, y) | x, y : A, f(x, y) is True }@. The function
-- @\expls1 expls2 -> crashDiffIsEmpty (crashDiff expls1 expls2)@, which has type
-- @[Located (Explanation ...)] -> [Located (Explanation ...)] -> Bool@, is a
-- partial order when considered in this way as a binary relation on
-- @Located (Explanation ...)@ (ignoring type indices). The first set of results
-- is considered \"less\" than the second when its possible crashes are a subset
-- of the second\'s.
crashDiff ::
  [Located (Explanation m1 arch1 argTypes1)] ->
  [Located (Explanation m2 arch2 argTypes2)] ->
  CrashDiff
crashDiff expls1 expls2 =
  let (truePositives1, _, uncertain1, _) =
        partitionExplanations locatedValue (toList expls1)
      (_, failedAssert1, _, unclass1, unfixed1, unfixable1, _) =
        partitionUncertainty uncertain1
      (truePositives2, _, uncertain2, _) =
        partitionExplanations locatedValue (toList expls2)
      (_, failedAssert2, _, unclass2, unfixed2, unfixable2, _) =
        partitionUncertainty uncertain2
      setDiff a b = Set.fromList a `Set.difference` Set.fromList b
   in CrashDiff
        (setDiff truePositives2 truePositives1)
        (setDiff failedAssert2 failedAssert1)
        -- NB: 'Unclassified' errors contain 'UndefinedBehavior' and other stuff
        -- that can't be compared for equality/ordered, so we just order by
        -- program location.
        (setDiff (map void unclass2) (map void unclass1))
        (setDiff unfixed2 unfixed1)
        (setDiff unfixable2 unfixable1)

computeDiffs ::
  Seq (UCCruxSimulationResult m1 arch1 argTypes1) ->
  Seq (UCCruxSimulationResult m2 arch2 argTypes2) ->
  (CrashDiff, CrashDiff)
computeDiffs trace1 trace2 =
  let expls ::
        forall m arch argTypes.
        Seq (UCCruxSimulationResult m arch argTypes) ->
        [Located (Explanation m arch argTypes)]

      expls = concatMap explanations . toList
      diff12 = crashDiff (expls trace1) (expls trace2)
      diff21 = crashDiff (expls trace2) (expls trace1)
   in ( diff12,
        diff21
      )

-- | Analyze the functions in the two modules, and return the non-empty diffs where
-- the modules differed
getCrashDiffs ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m1 arch1 ->
  ModuleContext m2 arch2 ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | Entry points. If empty, check functions that are in both modules.
  [FunctionName] ->
  IO ([(String, NonEmptyCrashDiff)], [(String, NonEmptyCrashDiff)])
getCrashDiffs appCtx modCtx1 modCtx2 halloc cruxOpts llOpts entries =
  do
    results <-
      zipResults
        appCtx
        modCtx1
        modCtx2
        halloc
        cruxOpts
        llOpts
        entries
    when (Map.null results) $
      (appCtx ^. log)
        Low
        "Modules have no functions in common! Nothing was compared."

    pure $
      foldMap
        ( \(funcName, (SomeBugfindingResult _ trace1, SomeBugfindingResult _ trace2)) ->
            let (diff12, diff21) = computeDiffs trace1 trace2
             in ( map (funcName,) (maybeToList (crashDiffNonEmpty diff12)),
                  map (funcName,) (maybeToList (crashDiffNonEmpty diff21))
                )
        )
        (Map.toList results)

reportDiffs ::
  AppContext ->
  [(String, NonEmptyCrashDiff)] ->
  [(String, NonEmptyCrashDiff)] ->
  IO ()
reportDiffs appCtx diffs12 diffs21 =
  do
    for_
      diffs12
      ( \(funcName, NonEmptyCrashDiff diff12) ->
          unless (crashDiffIsEmpty diff12) $
            (appCtx ^. log)
              Low
              ( Text.unlines
                  [ "Version 2 had more/different crashes than version 1 on "
                      <> Text.pack funcName,
                    renderCrashDiff diff12
                  ]
              )
      )
    for_
      diffs21
      ( \(funcName, NonEmptyCrashDiff diff21) ->
          (appCtx ^. log)
            Low
            ( Text.unlines
                [ "Version 1 had more/different crashes than version 2 on "
                    <> Text.pack funcName,
                  renderCrashDiff diff21
                ]
            )
      )

checkEquiv ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m1 arch1 ->
  ModuleContext m2 arch2 ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  LLVMOptions ->
  -- | See comment on 'OrderOrEquivalence'
  OrderOrEquivalence ->
  -- | Entry points. If empty, check functions that are in both modules.
  [FunctionName] ->
  IO ()
checkEquiv appCtx modCtx1 modCtx2 halloc cruxOpts llOpts orderOrEquiv entries =
  do
    (diffs12, diffs21) <- getCrashDiffs appCtx modCtx1 modCtx2 halloc cruxOpts llOpts entries
    reportDiffs
      appCtx
      diffs12
      (case orderOrEquiv of
         Equivalence -> diffs21
         Order -> [])
