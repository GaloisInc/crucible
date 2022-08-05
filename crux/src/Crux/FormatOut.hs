{-# LANGUAGE GADTs #-}
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

import qualified Data.BitVector.Sized as BV
import           Data.Foldable ( toList )
import           Data.Sequence (Seq)
import           Data.Text ( Text )
import           Data.List ( length )
import           Prettyprinter ( (<+>) )
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPR

import           What4.Expr (GroundValueWrapper(..), GroundValue)
import           What4.BaseTypes
import           What4.ProgramLoc

import           Lang.Crucible.Backend (CrucibleEvent(..))
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

sayWhatFailedGoals :: Bool -> Bool -> Seq ProvedGoals -> SayWhat
sayWhatFailedGoals skipIncompl showVars allGls =
  if null allDocs
     then SayNothing
     else SayWhat Fail "Crux" $ ppToText $ PP.vsep allDocs
 where
  failedDoc = \case
    Branch gls1 gls2 -> failedDoc gls1 <> failedDoc gls2
    ProvedGoal{} -> []
    NotProvedGoal _asmps err ex _locs mdl s ->
      if | skipIncompl, CSE.SimError _ (CSE.ResourceExhausted _) <- err -> []
         | Just (_m,evs) <- mdl ->
             [ PP.nest 2 $ PP.vcat (
               [ "Found counterexample for verification goal"
               -- n.b. prefer the prepared pretty explanation, but
               -- if not available, use the NotProved information.
               -- Don't show both: they tend to be duplications.
               , if null (show ex) then PP.viaShow err else ex
               ] -- if `showVars` is set, print the sequence of symbolic
                 -- variable events that led to this failure
                 ++ if showVars then
                      ["Symbolic variables:", PP.indent 2 (PP.vcat (ppVars evs))]
                    else [] 
                 -- print abducts, if any
                 ++ if s /= [] then
                      PP.pretty ("One of the following " ++ show (length s) ++ " fact(s) would entail the goal")
                      : (map (\x -> PP.pretty ('*' : ' ' : x)) s)
                    else [])]
         | otherwise ->
           [ PP.nest 2 $ PP.vcat [ "Failed to prove verification goal", ex ] ]

  ppVars evs =
    do CreateVariableEvent loc nm tpr (GVW v) <- evs
       pure (ppVarEvent loc nm tpr v)

  ppVarEvent loc nm tpr v =
    PP.pretty nm PP.<+> "=" PP.<+> ppVal tpr v PP.<+> "at" PP.<+> PP.pretty (plSourceLoc loc)

  ppVal :: BaseTypeRepr tp -> GroundValue tp -> PP.Doc ann
  ppVal tpr v = case tpr of
    BaseBVRepr _w -> PP.viaShow (BV.asUnsigned v)
    BaseFloatRepr _fpp -> PP.viaShow v
    BaseRealRepr -> PP.viaShow v
    _ -> "<unknown>" PP.<+> PP.viaShow tpr

  allDocs = mconcat (failedDoc <$> toList allGls)



ppToText :: PP.Doc ann -> Text
ppToText = PPR.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
