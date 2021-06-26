-- from: crucible-c/src/Report.hs

{-# Language OverloadedStrings #-}
module Crux.Report where

import Data.Void (Void)
import System.FilePath
import System.Directory (createDirectoryIfMissing, canonicalizePath)
import System.IO
import qualified Data.Foldable as Fold
import Data.Functor.Const
import Data.List (partition)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Control.Exception (catch, SomeException(..))
import Control.Monad (forM_)
import Prettyprinter (Doc)

import qualified Data.Text.IO as T

import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend
import What4.ProgramLoc

import Crux.Types
import Crux.Config.Common
import Crux.Loops
import Crux.Model ( modelJS )

-- Note these should be data files. However, cabal-new build doesn't make it easy for the installation
-- to find data files, so they are embedded as Text constants instead.

import Crux.UI.JS
import Crux.UI.Jquery (jquery)       -- ui/jquery.min.js
import Crux.UI.IndexHtml (indexHtml) -- ui/index.html


generateReport :: CruxOptions -> CruxSimulationResult -> IO ()
generateReport opts res
  | outDir opts == "" || skipReport opts = return ()
  | otherwise =
    do let xs = cruxSimResultGoals res
           goals = map snd $ Fold.toList xs
           referencedFiles = inputFiles opts ++
                             concatMap provedGoalFiles goals
           dedup = Set.toList . Set.fromList
       createDirectoryIfMissing True (outDir opts)
       maybeGenerateSource opts (dedup referencedFiles)
       scs <- renderSideConds opts goals
       let contents = renderJS (jsList scs)
       -- Due to CORS restrictions, the only current way of statically loading local data
       -- is by including a <script> with the contents we want.
       writeFile (outDir opts </> "report.js") $ "var goals = " ++ contents
       -- However, for some purposes, having a JSON file is more practical.
       writeFile (outDir opts </> "report.json") contents
       T.writeFile (outDir opts </> "index.html") indexHtml
       T.writeFile (outDir opts </> "jquery.min.js") jquery


-- TODO: get the extensions from the Language configuration
-- XXX: currently we just use the file name as a label for the file,
-- but if files come from different directores this may lead to clashes,
-- so we should do something smarter (e.g., drop only the prefix that
-- is common to all files).
maybeGenerateSource :: CruxOptions -> [FilePath] -> IO ()
maybeGenerateSource opts files =
  do let exts = [".c", ".i", ".cc", ".cpp", ".cxx", ".C", ".ii", ".h", ".hpp", ".hxx", ".hh"]
         renderFiles = filter ((`elem` exts) . takeExtension) files
     h <- openFile (outDir opts </> "source.js") WriteMode
     hPutStrLn h "var sources = ["
     forM_ renderFiles $ \file -> do
       absFile <- canonicalizePath file
       txt <- readFile absFile
       hPutStr h $ "{\"label\":" ++ show (takeFileName absFile) ++ ","
       hPutStr h $ "\"name\":" ++ show absFile ++ ","
       hPutStr h $ "\"lines\":" ++ show (lines txt)
       hPutStrLn h "},"
     hPutStrLn h "]"
     hClose h
  `catch` \(SomeException {}) -> return ()


-- | Return a list of all program locations referenced in a set of
-- proved goals.
provedGoalLocs :: ProvedGoals -> [ProgramLoc]
-- TODO?
--provedGoalLocs (AtLoc loc _ goals) = loc : provedGoalLocs goals
provedGoalLocs (Branch goals1 goals2) = provedGoalLocs goals1 ++
                                        provedGoalLocs goals2
provedGoalLocs (ProvedGoal _ (err, _) _) = [simErrorLoc err]
provedGoalLocs (NotProvedGoal _ (err, _) _ _) = [simErrorLoc err]

-- | Return a list of all files referenced in a set of proved goals.
provedGoalFiles :: ProvedGoals -> [FilePath]
provedGoalFiles = mapMaybe posFile . map plSourceLoc . provedGoalLocs
  where
    posFile (SourcePos f _ _) = Just $ Text.unpack f
    posFile (BinaryPos f _) = Just $ Text.unpack f
    posFile _ = Nothing

renderSideConds :: CruxOptions -> [ProvedGoals] -> IO [ JS ]
renderSideConds opts = concatMapM (go ( [] :: [(JS,ProgramLoc)] ))
  where
  concatMapM f xs = concat <$> mapM f xs

  flatBranch (Branch x y : more) = flatBranch (x : y : more)
  flatBranch (x : more)          = x : flatBranch more
  flatBranch []                  = []

  isGoal x = case x of
               ProvedGoal {} -> True
               NotProvedGoal {} -> True
               _       -> False

  go path gs =
    case gs of
      Branch g1 g2 ->
        let (now,rest) = partition isGoal (flatBranch [g1,g2]) in
          (++) <$> concatMapM (go path) now <*> concatMapM (go path) rest

      ProvedGoal asmps conc triv
        | skipSuccessReports opts -> pure []
        | otherwise -> jsProvedGoal apath (map fst asmps) (fst conc) triv

      NotProvedGoal asmps conc explain cex
        | skipIncompleteReports opts
        , (SimError _ (ResourceExhausted _), _) <- conc
        -> pure []

        | otherwise -> jsNotProvedGoal apath (map fst asmps) (fst conc) explain cex

    where
      (ls,ps) = unzip (reverse path)
      ap      = map fst (annotateLoops ps)
      mkStep a l = jsObj [ "loop" ~> jsList (map jsNum a)
                         , "loc"  ~> l ]
      apath   = zipWith mkStep ap ls


jsProvedGoal ::
  [ JS ] ->
  [ CrucibleAssumption (Const ()) ] ->
  SimError ->
  Bool ->
  IO [JS]
jsProvedGoal apath asmps conc triv =
  do loc <- jsLoc (simErrorLoc conc)
     asmps' <- mapM mkAsmp asmps
     pure [jsObj
       [ "status"          ~> jsStr "ok"
       , "goal"            ~> goalReason
       , "details-short"   ~> goalDetails
       , "location"        ~> loc
       , "assumptions"     ~> jsList asmps'
       , "trivial"         ~> jsBool triv
       , "path"            ~> jsList apath
       ]]
  where
  mkAsmp asmp =
    do l <- jsLoc (assumptionLoc asmp)
       pure $ jsObj
         [ "loc" ~> l
         , "text" ~> jsStr (show (ppAssumption (\_ -> mempty) asmp))
         ]

  goalReason  = jsStr (simErrorReasonMsg (simErrorReason conc))
  goalDetails
     | null msg  = jsNull
     | otherwise = jsStr msg
    where msg = simErrorDetailsMsg (simErrorReason conc)


jsNotProvedGoal ::
  [ JS ] ->
  [ CrucibleAssumption (Const ()) ] ->
  SimError ->
  Doc Void ->
  Maybe ModelView ->
  IO [JS]
jsNotProvedGoal apath asmps conc explain cex =
  do loc <- jsLoc (simErrorLoc conc)
     asmps' <- mapM mkAsmp asmps
     ex <- case cex of
             Just m -> modelJS m
             _      -> pure jsNull
     pure [jsObj
       [ "status"          ~> status
       , "counter-example" ~> ex
       , "goal"            ~> goalReason
       , "details-short"   ~> goalDetails
       , "location"        ~> loc
       , "assumptions"     ~> jsList asmps'
       , "trivial"         ~> jsBool False
       , "path"            ~> jsList apath
       , "details-long"    ~> jsStr (show explain)
       ]]
  where
  status = case cex of
             Just _
               | ResourceExhausted _ <- simErrorReason conc -> jsStr "unknown"
               | otherwise -> jsStr "fail"
             Nothing -> jsStr "unknown"

  mkAsmp asmp =
    do l <- jsLoc (assumptionLoc asmp)
       pure $ jsObj
         [ "loc" ~> l
         , "text" ~> jsStr (show (ppAssumption (\_ -> mempty) asmp))
         ]

  goalReason  = jsStr (simErrorReasonMsg (simErrorReason conc))
  goalDetails
     | null msg  = jsNull
     | otherwise = jsStr msg
    where msg = simErrorDetailsMsg (simErrorReason conc)
