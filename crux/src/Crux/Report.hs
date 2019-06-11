-- from: crucible-c/src/Report.hs

{-# Language OverloadedStrings #-}
module Crux.Report where

import System.FilePath
import System.Directory (createDirectoryIfMissing)
import System.IO
import Data.List (intercalate, partition, isInfixOf)
import Data.Maybe (fromMaybe)
import Data.Text (unpack)
import Control.Exception (catch, SomeException(..))
import Control.Monad (when, forM_)

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
     maybeGenerateSource opts (inputFiles opts)
     writeFile (outDir opts </> "report.js")
        $ "var goals = " ++ renderJS (jsList (renderSideConds xs))
     T.writeFile (outDir opts </> "index.html") indexHtml
     T.writeFile (outDir opts </> "jquery.min.js") jquery


-- TODO: get the extensions from the Language configuration
maybeGenerateSource :: CruxOptions -> [FilePath] -> IO ()
maybeGenerateSource opts files =
  do let exts = [".c", ".i", ".cc", ".cpp", ".cxx", ".C", ".ii"]
         renderFiles = filter ((`elem` exts) . takeExtension) files
     h <- openFile (outDir opts </> "source.js") WriteMode
     hPutStrLn h "var sources = ["
     forM_ renderFiles $ \file -> do
       txt <- readFile file
       hPutStr h $ "{\"name\":" ++ show file ++ ","
       hPutStr h $ "\"lines\":" ++ show (lines txt)
       hPutStrLn h "},"
     hPutStrLn h "]"
     hClose h
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
            SourcePos f l c -> jsObj [ "file" ~> jsStr (unpack f)
                                     , "line" ~> jsStr (show l)
                                     , "col" ~> jsStr (show c)
                                     ]
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
  , "goal"            ~> jsStr goalReason
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
    jsObj [ "loc" ~> jsLoc (assumptionLoc asmp)
          ]

  goalReason = renderReason (simErrorReasonMsg (simErrorReason conc))
  renderReason rsn =
    case lines rsn of
      l1 : l2 : _ | "Undefined behavior" `isInfixOf` l1 -> l2
      l1 : _ -> takeFileName l1
      _ -> "no reason?"



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

