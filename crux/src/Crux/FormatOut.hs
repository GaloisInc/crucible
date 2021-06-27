{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
-- | This module provides various default formatters for outputting
-- information in human readable form.  Alternative versions should be
-- used where appropriate.

module Crux.FormatOut
  (
    sayWhatResultStatus
  , sayWhatFailedGoals
  )
where

import           Data.Foldable ( toList )
import           Data.Sequence (Seq)
import           Data.Text ( Text )
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPR

import qualified Lang.Crucible.Simulator.SimError as CSE

import           Crux.Types


sayWhatResultStatus :: CruxSimulationResult -> SayWhat
sayWhatResultStatus (CruxSimulationResult cmpl gls) =
  let tot        = sum (totalProcessedGoals . fst <$> gls)
      proved     = sum (provedGoals . fst <$> gls)
      disproved  = sum (disprovedGoals . fst <$> gls)
      incomplete = sum (incompleteGoals . fst <$> gls)
      unknown    = tot - (proved + disproved + incomplete)
      goalSummary = if tot == 0 then
                      "All goals discharged through internal simplification."
                    else
                      PP.nest 2 $
                      PP.vcat [ "Goal status:"
                              , "Total:" <+> PP.pretty tot
                              , "Proved:" <+> PP.pretty proved
                              , "Disproved:" <+> PP.pretty disproved
                              , "Incomplete:" <+> PP.pretty incomplete
                              , "Unknown:" <+> PP.pretty unknown
                              ]
  in SayMore
     (SayWhat Simply "Crux" $ ppToText goalSummary)
     $ if | disproved > 0 ->
              SayWhat Fail "Crux" "Overall status: Invalid."
          | incomplete > 0 || cmpl == ProgramIncomplete ->
              SayWhat Warn "Crux" "Overall status: Unknown (incomplete)."
          | unknown > 0 -> SayWhat Warn "Crux" "Overall status: Unknown."
          | proved == tot -> SayWhat OK "Crux" "Overall status: Valid."
          | otherwise ->
              SayWhat Fail "Crux" "Internal error computing overall status."

sayWhatFailedGoals :: Bool -> Seq ProvedGoals -> SayWhat
sayWhatFailedGoals skipIncompl allGls =
  let failedDoc = \case
        Branch gls1 gls2 -> failedDoc gls1 <> failedDoc gls2
        ProvedGoal{} -> []
        NotProvedGoal _asmps err ex _locs mdl ->
          if | skipIncompl, CSE.SimError _ (CSE.ResourceExhausted _) <- err -> []
             | Just _ <- mdl ->
                 [ PP.nest 2 $ PP.vcat
                   [ "Found counterexample for verification goal"
                   -- n.b. prefer the prepared pretty explanation, but
                   -- if not available, use the NotProved information.
                   -- Don't show both: they tend to be duplications.
                   , if null (show ex) then PP.viaShow err else ex
                   -- TODO the msg is typically the string
                   -- representation of the crucible term that failed.
                   -- It might be nice to have a debug or noisy flag
                   -- that would enable emitting this, since it tends
                   -- to be rather lengthy.
                   -- , PP.pretty msg
                   ] ]
             | otherwise ->
               [ PP.nest 2 $ PP.vcat [ "Failed to prove verification goal", ex ] ]
      allDocs = mconcat (failedDoc <$> toList allGls)
  in if null allDocs
     then SayNothing
     else SayWhat Fail "Crux" $ ppToText $ PP.vsep allDocs


ppToText :: PP.Doc ann -> Text
ppToText = PPR.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
