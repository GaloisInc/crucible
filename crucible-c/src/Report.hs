{-# Language OverloadedStrings #-}
module Report where

import System.FilePath
import Data.List(intercalate,sortBy)
import Data.Maybe(fromMaybe)
import Control.Exception(catch,SomeException(..))
import Control.Monad(when)

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend
import What4.ProgramLoc


import Options
import Model
import Goal

type SideCond = ([JS],[(AsmpLab,String)], (SimError,String), Bool, ProofResult)

generateReport :: Options -> ProvedGoals -> IO ()
generateReport opts xs =
  do when (takeExtension (inputFile opts) == ".c") (generateSource opts)
     writeFile (outDir opts </> "report.js")
        $ "var goals = " ++ renderJS (jsList (renderSindConds xs))



generateSource :: Options -> IO ()
generateSource opts =
  do src <- readFile (inputFile opts)
     writeFile (outDir opts </> "source.js")
        $ "var lines = " ++ show (lines src)
  `catch` \(SomeException {}) -> return ()


renderSindConds :: ProvedGoals -> [ JS ]
renderSindConds = map snd
                . sortBy smallerDepth
                . go (0::Integer) []
  where
  smallerDepth (x,_) (y,_) = compare x y

  go depth path gs =
    case gs of
      AtLoc pl to gs1 -> go (depth + 1) (jsObj (jsPLoc pl to) : path) gs1
      Branch gss      -> concatMap (go depth path) gss
      Goal asmps conc triv proved ->
        [ (depth, jsSideCond (reverse path,asmps,conc,triv,proved)) ]

jsPLoc :: PredLoc -> Maybe ProgramLoc -> [(String,JS)]
jsPLoc (PL l lp) to =
    [ "line" ~> jsLoc l
    , "loop" ~> (case lp of
                    NotLoop -> jsNull
                    LoopIter n -> jsStr (show n))
    , "tgt" ~> jsMaybe (fmap jsLoc to)
    ]

jsLoc :: ProgramLoc -> JS
jsLoc x = case plSourceLoc x of
            SourcePos _ l _ -> jsStr (show l)
            _               -> jsNull

jsSideCond :: SideCond -> JS
jsSideCond (path,asmps,(conc,clab),triv,status) =
  jsObj
  [ "proved"          ~> proved
  , "counter-example" ~> example
  , "goal"            ~> name
  , "lab"             ~> jsStr clab
  , "location"        ~> jsLoc (simErrorLoc conc)
  , "assumptions"     ~> jsList (map mkAsmp asmps)
  , "trivial"         ~> jsBool triv
  , "path"            ~> jsList path
  ]
  where
  proved = case status of
             Proved -> jsBool True
             _      -> jsBool False

  example = case status of
             NotProved (Just m) -> JS (modelInJS m)
             _                  -> jsNull

  name = jsStr (simErrorReasonMsg (simErrorReason conc))

  mkAsmp (a,lab) = jsObj (("lab" ~> jsStr lab) : loc)
    where
    loc =
      case a of
        Exploring pl d -> jsPLoc pl d
        OtherAsmp a'   -> [ "line" ~> jsLoc (assumptionLoc a') ]

--------------------------------------------------------------------------------
newtype JS = JS { renderJS :: String }

jsList :: [JS] -> JS
jsList xs = JS $ "[" ++ intercalate "," [ x | JS x <- xs ] ++ "]"

infix 1 ~>

(~>) :: a -> b -> (a,b)
(~>) = (,)

jsObj :: [(String,JS)] -> JS
jsObj xs =
  JS $ "{" ++ intercalate "," [ show x ++ ": " ++ v | (x,JS v) <- xs ] ++ "}"

jsBool :: Bool -> JS
jsBool b = JS (if b then "true" else "false")

jsStr :: String -> JS
jsStr = JS . show

jsNull :: JS
jsNull = JS "null"

jsMaybe :: Maybe JS -> JS
jsMaybe = fromMaybe jsNull


