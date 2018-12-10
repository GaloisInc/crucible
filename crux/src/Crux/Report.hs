-- from: crucible-c/src/Report.hs

{-# Language OverloadedStrings #-}
module Crux.Report where

import System.FilePath
import System.Directory (createDirectoryIfMissing)
import Data.List (intercalate, partition)
import Data.Maybe (fromMaybe)
import Control.Exception (catch, SomeException(..))
import Control.Monad (when)

import qualified Data.Text.IO as T

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend
import What4.ProgramLoc

import Crux.Types
import Crux.Options
import Crux.Loops

-- Note these should be data files. However, cabal-new build doesn't make it easy for the installation
-- to find data files, so they are embedded as Text constants instead.

import Crux.UI.Jquery (jquery)       -- ui/jquery.min.js
import Crux.UI.IndexHtml (indexHtml) -- ui/index.html


generateReport :: CruxOptions -> Maybe (ProvedGoals b) -> IO ()
generateReport opts xs =
  do createDirectoryIfMissing True (outDir opts)
     let exts = [".c", ".i", ".cc", ".cpp", ".cxx", ".ii"]
     when (takeExtension (inputFile opts) `elem` exts) (generateSource opts)
     writeFile (outDir opts </> "report.js")
        $ "var goals = " ++ renderJS (jsList (renderSideConds xs))
     T.writeFile (outDir opts </> "index.html") indexHtml
     T.writeFile (outDir opts </> "jquery.min.js") jquery



generateSource :: CruxOptions -> IO ()
generateSource opts =
  do src <- readFile (inputFile opts)
     writeFile (outDir opts </> "source.js") $
       "var lines = " ++ show (lines src)
  `catch` \(SomeException {}) -> return ()


renderSideConds :: Maybe (ProvedGoals b) -> [ JS ]
renderSideConds = maybe [] (go [])
  where
  flatBranch (Branch x y : more) = flatBranch (x : y : more)
  flatBranch (x : more)          = x : flatBranch more 
  flatBranch []                  = []

  isGoal x = case x of
               Goal {} -> True
               _       -> False

  go path gs =
    case gs of
      AtLoc pl _ gs1  -> go ((jsLoc pl, pl) : path) gs1
      Branch g1 g2 ->
        let (now,rest) = partition isGoal (flatBranch [g1,g2])
        in concatMap (go path) now ++ concatMap (go path) rest

      Goal asmps conc triv proved ->
        let (ls,ps) = unzip (reverse path)
            ap      = map fst (annotateLoops ps)
            mkStep a l = jsObj [ "loop" ~> jsList (map jsNum a)
                               , "loc"  ~> l ]
            apath   = zipWith mkStep ap ls
        in [ jsSideCond apath asmps conc triv proved ]

jsLoc :: ProgramLoc -> JS
jsLoc x = case plSourceLoc x of
            SourcePos _ l _ -> jsStr (show l)
            _               -> jsNull


jsSideCond ::
  [ JS ] ->
  [(AssumptionReason,String)] ->
  (SimError,String) ->
  Bool ->
  ProofResult b ->
  JS
jsSideCond path asmps (conc,_) triv status =
  jsObj
  [ "status"          ~> proved
  , "counter-example" ~> example
  , "goal"            ~> jsStr (takeFileName (head (lines (simErrorReasonMsg (simErrorReason conc)))))
  , "location"        ~> jsLoc (simErrorLoc conc)
  , "assumptions"     ~> jsList (map mkAsmp asmps)
  , "trivial"         ~> jsBool triv
  , "path"            ~> jsList path
  ]
  where
  proved = case (status, simErrorReason conc) of
             (Proved{}, _) -> jsStr "ok"
             (NotProved _, ResourceExhausted _) -> jsStr "unknown"
             (NotProved Nothing, _) -> jsStr "unknown"
             (NotProved (Just _), _) -> jsStr "fail"

  example = case status of
             NotProved (Just m) -> JS (modelInJS m)
             _                  -> jsNull

  mkAsmp (asmp,_) =
    jsObj [ "line" ~> jsLoc (assumptionLoc asmp)
          ]



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

jsNum :: Show a => a -> JS
jsNum = JS . show

---------------------------------------------------
---------------------------------------------------

