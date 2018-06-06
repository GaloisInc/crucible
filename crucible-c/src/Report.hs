module Report where

import System.FilePath
import Data.List(intercalate)

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend
import What4.ProgramLoc

import Options
import Model
import Goal

type SideCond = ([AssumptionReason], SimError, ProofResult)

generateReport :: Options -> [SideCond] -> IO ()
generateReport opts xs =
  do writeFile (outDir opts </> "report.js")
        $ "var goals = " ++ jsList (map jsSideCond xs)

jsList :: [String] -> String
jsList xs = "[" ++ intercalate "," xs ++ "]"

jsSideCond :: SideCond -> String
jsSideCond (asmps,conc,status) =
  unlines [ "{ \"proved\": " ++ proved
          , ", \"counter-example\": " ++ example
          , ", \"goal\": "      ++ name
          , ", \"location\": "  ++ loc
          , ", \"assumptions\": " ++ jsList asmpList
          , "}"
          ]
  where
  proved = case status of
             Proved -> "true"
             _      -> "false"

  example = case status of
             NotProved (Just m) -> modelInJS m
             _  -> "null"

  name = show (simErrorReasonMsg (simErrorReason conc))

  loc  = src (simErrorLoc conc)

  asmpList = map (src . assumptionLoc) asmps

  src x = case plSourceLoc x of
            SourcePos _ l _ -> show (show l)
            _               -> "null"


