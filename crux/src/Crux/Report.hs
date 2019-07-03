-- from: crucible-c/src/Report.hs

{-# Language OverloadedStrings #-}
module Crux.Report where

import System.FilePath
import System.Directory (createDirectoryIfMissing, getCurrentDirectory, makeAbsolute)
import System.IO
import Data.List (partition, isInfixOf)
import Control.Exception (catch, SomeException(..))
import Control.Monad (forM_)

import qualified Data.Text.IO as T

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend

import Crux.Types
import Crux.Config.Common
import Crux.Loops

-- Note these should be data files. However, cabal-new build doesn't make it easy for the installation
-- to find data files, so they are embedded as Text constants instead.

import Crux.UI.JS
import Crux.UI.Jquery (jquery)       -- ui/jquery.min.js
import Crux.UI.IndexHtml (indexHtml) -- ui/index.html


generateReport :: CruxOptions -> Maybe (ProvedGoals b) -> IO ()
generateReport opts xs =
  do createDirectoryIfMissing True (outDir opts)
     maybeGenerateSource opts (inputFiles opts)
     cwd <- getCurrentDirectory
     writeFile (outDir opts </> "report.js")
        $ "var goals = " ++ renderJS (jsList (renderSideConds cwd xs))
     T.writeFile (outDir opts </> "index.html") indexHtml
     T.writeFile (outDir opts </> "jquery.min.js") jquery


-- TODO: get the extensions from the Language configuration
-- XXX: currently we just use the file name as a label for the file,
-- but if files come from different directores this may lead to clashes,
-- so we should do something smarter (e.g., drop only the prefix that
-- is common to all files).
maybeGenerateSource :: CruxOptions -> [FilePath] -> IO ()
maybeGenerateSource opts files =
  do let exts = [".c", ".i", ".cc", ".cpp", ".cxx", ".C", ".ii"]
         renderFiles = filter ((`elem` exts) . takeExtension) files
     h <- openFile (outDir opts </> "source.js") WriteMode
     hPutStrLn h "var sources = ["
     forM_ renderFiles $ \file -> do
       absFile <- makeAbsolute file
       txt <- readFile absFile
       hPutStr h $ "{\"label\":" ++ show (takeFileName absFile) ++ ","
       hPutStr h $ "\"name\":" ++ show absFile ++ ","
       hPutStr h $ "\"lines\":" ++ show (lines txt)
       hPutStrLn h "},"
     hPutStrLn h "]"
     hClose h
  `catch` \(SomeException {}) -> return ()


renderSideConds :: FilePath -> Maybe (ProvedGoals b) -> [ JS ]
renderSideConds cwd = maybe [] (go [])
  where
  flatBranch (Branch x y : more) = flatBranch (x : y : more)
  flatBranch (x : more)          = x : flatBranch more
  flatBranch []                  = []

  isGoal x = case x of
               Goal {} -> True
               _       -> False

  go path gs =
    case gs of
      AtLoc pl _ gs1  -> go ((jsLoc cwd pl, pl) : path) gs1
      Branch g1 g2 ->
        let (now,rest) = partition isGoal (flatBranch [g1,g2])
        in concatMap (go path) now ++ concatMap (go path) rest

      Goal asmps conc triv proved ->
        let (ls,ps) = unzip (reverse path)
            ap      = map fst (annotateLoops ps)
            mkStep a l = jsObj [ "loop" ~> jsList (map jsNum a)
                               , "loc"  ~> l ]
            apath   = zipWith mkStep ap ls
        in [ jsSideCond cwd apath asmps conc triv proved ]


jsSideCond ::
  FilePath ->
  [ JS ] ->
  [(AssumptionReason,String)] ->
  (SimError,String) ->
  Bool ->
  ProofResult b ->
  JS
jsSideCond cwd path asmps (conc,_) triv status =
  jsObj
  [ "status"          ~> proved
  , "counter-example" ~> example
  , "goal"            ~> jsStr goalReason
  , "location"        ~> jsLoc cwd (simErrorLoc conc)
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
    jsObj [ "loc" ~> jsLoc cwd (assumptionLoc asmp)
          -- , "text" ~> jsStr (show (ppAssumptionReason asmp))
          ]

  goalReason = renderReason (simErrorReasonMsg (simErrorReason conc))
  renderReason rsn =
    case lines rsn of
      l1 : l2 : _ | "Undefined behavior" `isInfixOf` l1 -> l2
      l1 : _ -> takeFileName l1
      _ -> "no reason?"



