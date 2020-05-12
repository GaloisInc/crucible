-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Profiling
-- Description      : Profiling support for the simulator
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.Profiling
  ( profilingFeature
  , ProfilingOptions(..)
  , newProfilingTable
  , recordSolverEvent
  , startRecordingSolverEvents
  , enterEvent
  , exitEvent
  , inProfilingFrame
  , readMetrics
  , CrucibleProfile(..)
  , readProfilingState
  , writeProfileReport

    -- * Profiling data structures
  , CGEvent(..)
  , CGEventType(..)
  , ProfilingTable(..)
  , Lang.Crucible.Simulator.ExecutionTree.Metric(..)
  , Metrics(..)
  , symProUIJSON
  , symProUIString
  ) where

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad.Reader
import           Data.Foldable (toList)
import           Data.Hashable
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock
import           Data.Time.Clock.POSIX
import           Data.Time.Format
import           System.IO (withFile, IOMode(..), hPutStrLn)
import           Text.JSON
import           GHC.Generics (Generic)


import           What4.FunctionName
import           What4.Interface
import           What4.ProgramLoc
import           What4.SatResult

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Operations


data Metrics f =
  Metrics
  { metricSplits   :: f Integer
  , metricMerges   :: f Integer
  , metricAborts   :: f Integer
  , metricSolverStats :: f Statistics
  , metricExtraMetrics :: f (Map Text Integer)
  }

deriving instance Show (Metrics Identity)
deriving instance Generic (Metrics Identity)

traverseF_metrics :: Applicative m =>
  (forall s. e s -> m (f s)) ->
  Metrics e -> m (Metrics f)
traverseF_metrics h (Metrics x1 x2 x3 x4 x5) =
  Metrics <$> h x1 <*> h x2 <*> h x3 <*> h x4 <*> h x5

instance FunctorF Metrics where
  fmapF = fmapFDefault
instance FoldableF Metrics where
  foldMapF = foldMapFDefault
instance TraversableF Metrics where
  traverseF = traverseF_metrics

metricsToJSON :: Metrics Identity -> UTCTime -> JSValue
metricsToJSON m time = JSObject $ toJSObject $
    [ ("time", utcTimeToJSON time)
    , ("allocs", showJSON $ statAllocs $ solverStats )
    , ("paths", showJSON $ runIdentity $ metricSplits m )
    , ("merge-count", showJSON $ runIdentity $ metricMerges m )
    , ("abort-count", showJSON $ runIdentity $ metricAborts m )
    , ("non-linear-count", showJSON $ statNonLinearOps $ solverStats )
    ] ++ [ (Text.unpack k, showJSON v)
         | (k, v) <- Map.toList $ runIdentity $ metricExtraMetrics m ]
    where
      solverStats = runIdentity $ metricSolverStats m


data CGEventType = ENTER | EXIT | BLOCK | BRANCH
 deriving (Show,Eq,Ord,Generic)

data CGEvent =
  CGEvent
  { cgEvent_fnName   :: FunctionName
  , cgEvent_source   :: Maybe Position
  , cgEvent_callsite :: Maybe Position
  , cgEvent_type     :: CGEventType
  , cgEvent_blocks   :: [String]
  , cgEvent_metrics  :: Metrics Identity
  , cgEvent_time     :: UTCTime
  , cgEvent_id       :: Integer
  }
 deriving (Show, Generic)

-- FIXME... figure out why the UI seems to want this in milliseconds...
utcTimeToJSON :: UTCTime -> JSValue
utcTimeToJSON t =
  showJSON (1e3 * (fromRational $ toRational $ utcTimeToPOSIXSeconds t) :: Double)

cgEventTypeToJSON :: CGEventType -> JSValue
cgEventTypeToJSON ENTER = showJSON "ENTER"
cgEventTypeToJSON EXIT  = showJSON "EXIT"
cgEventTypeToJSON BLOCK  = showJSON "BLOCK"
cgEventTypeToJSON BRANCH  = showJSON "BRANCH"

cgEventToJSON :: CGEvent -> JSValue
cgEventToJSON ev = JSObject $ toJSObject $
    [ ("function", showJSON $ functionName $ cgEvent_fnName ev)
    , ("type", cgEventTypeToJSON (cgEvent_type ev))
    , ("metrics", metricsToJSON (cgEvent_metrics ev) (cgEvent_time ev))
    ]
    ++
    (case cgEvent_source ev of
      Nothing -> []
      Just p -> [("source", positionToJSON p)])
    ++
    (case cgEvent_callsite ev of
      Nothing -> []
      Just p -> [("callsite", positionToJSON p)])
    ++
    (case cgEvent_blocks ev of
      [] -> []
      xs -> [("blocks", showJSON xs)])

positionToJSON :: Position -> JSValue
positionToJSON p = showJSON $ show $ p

solverEventToJSON :: (UTCTime, SolverEvent) -> JSValue
solverEventToJSON (time, ev) =
   case ev of
     SolverStartSATQuery nm rsn ->
       JSObject $ toJSObject $
         [ ("type", showJSON "start")
         , ("time", utcTimeToJSON time)
         , ("part", showJSON "solver")
         , ("solver", showJSON nm)
         , ("description", showJSON rsn)
         ]
     SolverEndSATQuery res _err ->
       JSObject $ toJSObject $
         [ ("type", showJSON "finish")
         , ("time", utcTimeToJSON time)
         ] ++
         case res of
           Sat{} -> [("sat", showJSON True)]
           Unsat{} -> [("sat", showJSON False)]
           Unknown{} -> []

callGraphJSON :: UTCTime -> Metrics Identity -> Seq CGEvent -> JSValue
callGraphJSON now m evs = JSObject $ toJSObject
  [ ("type", showJSON "callgraph")
  , ("events", JSArray allEvs)
  ]

 where
 allEvs = map cgEventToJSON (toList evs ++ closingEvents now m evs)


symProUIString :: String -> String -> ProfilingTable -> IO String
symProUIString nm source tbl =
  do js <- symProUIJSON nm source tbl
     return ("data.receiveData("++ encode js ++ ");")


symProUIJSON :: String -> String -> ProfilingTable -> IO JSValue
symProUIJSON nm source tbl =
  do now <- getCurrentTime
     m <- readMetrics tbl
     evs <- readIORef (callGraphEvents tbl)
     solverEvs <- readIORef (solverEvents tbl)
     return $ JSArray $
       [ JSObject $ toJSObject $ metadata now
       , callGraphJSON now m evs
       , JSObject $ toJSObject $ solver_calls solverEvs
       ]
 where
 solver_calls evs  =
   [ ("type", showJSON "solver-calls")
   , ("events", JSArray $ map solverEventToJSON $ toList evs)
   ]

 metadata now =
   [ ("type", showJSON "metadata")
   , ("form", showJSON "")
   , ("name", showJSON nm)
   , ("source", showJSON source)
   , ("time", showJSON $ formatTime defaultTimeLocale rfc822DateFormat now)
   , ("version", showJSON "1")
   ]

data ProfilingTable =
  ProfilingTable
  { callGraphEvents :: IORef (Seq CGEvent)
  , eventDedups :: IORef (HashSet EventDedup)
  , metrics :: Metrics IORef
  , eventIDRef :: IORef Integer
  , solverEvents :: IORef (Seq (UTCTime, SolverEvent))
  }

data CrucibleProfile =
  CrucibleProfile
  { crucibleProfileTime :: UTCTime
  , crucibleProfileCGEvents :: [CGEvent]
  , crucibleProfileSolverEvents :: [SolverEvent]
  } deriving (Show, Generic)

data EventDedup =
    BlockDedup FunctionName String
  | BranchDedup FunctionName [String]
  deriving (Eq, Generic)

instance Hashable EventDedup

readProfilingState :: ProfilingTable -> IO (UTCTime, [CGEvent], [(UTCTime, SolverEvent)])
readProfilingState tbl =
  do now <- getCurrentTime
     m <- readMetrics tbl
     cgevs <- readIORef (callGraphEvents tbl)
     sevs  <- readIORef (solverEvents tbl)
     return (now, toList cgevs ++ closingEvents now m cgevs, toList sevs)

openEventFrames :: Seq CGEvent -> [CGEvent]
openEventFrames = go []
 where
 go :: [CGEvent] -> Seq CGEvent -> [CGEvent]
 go xs Seq.Empty = xs
 go xs (e Seq.:<| es) =
   case cgEvent_type e of
     ENTER -> go (e:xs) es
     EXIT  -> go (tail xs) es
     _     -> go xs es

openToCloseEvent :: UTCTime -> Metrics Identity -> CGEvent -> CGEvent
openToCloseEvent now m cge =
  cge
  { cgEvent_type = EXIT
  , cgEvent_metrics = m
  , cgEvent_time = now
  }

closingEvents :: UTCTime -> Metrics Identity -> Seq CGEvent -> [CGEvent]
closingEvents now m = map (openToCloseEvent now m) . openEventFrames

newProfilingTable :: IO ProfilingTable
newProfilingTable =
  do m <- Metrics <$> newIORef 0
                  <*> newIORef 0
                  <*> newIORef 0
                  <*> newIORef zeroStatistics
                  <*> newIORef Map.empty
                        -- TODO: Find the actual custom metrics and
                        -- initialize them to zero.  Needs a change in
                        -- the Crux API; currently 'newProfilingTable'
                        -- is called before the custom metrics are set
                        -- up.  For now, the extra metrics are missing
                        -- from the very earliest events in the log;
                        -- the JS front end works around this by
                        -- assuming that any missing value is a zero.
     evs <- newIORef mempty
     dedups <- newIORef mempty
     idref <- newIORef 0
     solverevs <- newIORef mempty
     let tbl = ProfilingTable evs dedups m idref solverevs
     return tbl

recordSolverEvent :: ProfilingTable -> SolverEvent -> IO ()
recordSolverEvent tbl ev = do
  do now <- getCurrentTime
     xs <- readIORef (solverEvents tbl)
     writeIORef (solverEvents tbl) (xs Seq.|> (now,ev))

startRecordingSolverEvents ::
  IsSymInterface sym =>
  sym ->
  ProfilingTable ->
  IO ()
startRecordingSolverEvents sym tbl =
  setSolverLogListener sym (Just (recordSolverEvent tbl))

nextEventID :: ProfilingTable -> IO Integer
nextEventID tbl =
  do i <- readIORef (eventIDRef tbl)
     writeIORef (eventIDRef tbl) $! (i+1)
     return i

dedupEvent :: ProfilingTable -> EventDedup -> IO () -> IO ()
dedupEvent tbl evt f =
  do seen <- readIORef (eventDedups tbl)
     when (not $ HashSet.member evt seen) $
       do writeIORef (eventDedups tbl) (HashSet.insert evt seen)
          f

inProfilingFrame ::
  ProfilingTable ->
  FunctionName ->
  Maybe ProgramLoc ->
  IO a ->
  IO a
inProfilingFrame tbl nm mloc action =
  Ex.bracket_
    (enterEvent tbl nm mloc)
    (exitEvent tbl nm)
    action

enterEvent ::
  ProfilingTable ->
  FunctionName ->
  Maybe ProgramLoc ->
  IO ()
enterEvent tbl nm callLoc =
  do now <- getCurrentTime
     m <- readMetrics tbl
     i <- nextEventID tbl
     let p = fmap plSourceLoc callLoc
     modifyIORef' (callGraphEvents tbl) (Seq.|> CGEvent nm Nothing p ENTER [] m now i)

readMetrics :: ProfilingTable -> IO (Metrics Identity)
readMetrics tbl = traverseF (pure . Identity <=< readIORef) (metrics tbl)

exitEvent ::
  ProfilingTable ->
  FunctionName ->
  IO ()
exitEvent tbl nm =
  do now <- getCurrentTime
     m <- traverseF (pure . Identity <=< readIORef) (metrics tbl)
     i <- nextEventID tbl
     modifyIORef' (callGraphEvents tbl) (Seq.|> CGEvent nm Nothing Nothing EXIT [] m now i)

blockEvent ::
  ProfilingTable ->
  FunctionName ->
  Maybe ProgramLoc ->
  Some (BlockID blocks) ->
  IO ()
blockEvent tbl nm callLoc blk =
  dedupEvent tbl (BlockDedup nm (show blk)) $
  do now <- getCurrentTime
     m <- readMetrics tbl
     i <- nextEventID tbl
     let p = fmap plSourceLoc callLoc
     modifyIORef' (callGraphEvents tbl)
       (Seq.|> CGEvent nm Nothing p BLOCK [show blk] m now i)

branchEvent ::
  ProfilingTable ->
  FunctionName ->
  Maybe ProgramLoc ->
  [Some (BlockID blocks)] ->
  IO ()
branchEvent tbl nm callLoc blks =
  dedupEvent tbl (BranchDedup nm (map show blks)) $
  do now <- getCurrentTime
     m <- readMetrics tbl
     i <- nextEventID tbl
     let p = fmap plSourceLoc callLoc
     modifyIORef' (callGraphEvents tbl)
       (Seq.|> CGEvent nm Nothing p BRANCH (map show blks) m now i)


updateProfilingTable ::
  IsExprBuilder sym =>
  ProfilingTable ->
  ExecState p sym ext rtp ->
  IO ()
updateProfilingTable tbl exst = do
  let sym = execStateContext exst ^. ctxSymInterface
  stats <- getStatistics sym
  writeIORef (metricSolverStats (metrics tbl)) stats

  case execStateSimState exst of
    Just (SomeSimState simst) -> do
      let extraMetrics = execStateContext exst ^. profilingMetrics
      extraMetricValues <- traverse (\m -> runMetric m simst) extraMetrics
      writeIORef (metricExtraMetrics (metrics tbl)) extraMetricValues
    Nothing ->
      -- We can't poll custom metrics at the VERY beginning or end of
      -- execution because 'ResultState' and 'InitialState' have no
      -- 'SimState' values. This is probably fine---we still get to
      -- poll them before and after the top-level function being
      -- simulated, since it gets a 'CallState' and 'ReturnState' like
      -- any other function.
      return ()

  case exst of
    InitialState _ _ _ _ _ ->
      enterEvent tbl startFunctionName Nothing
    CallState _rh call st ->
      enterEvent tbl (resolvedCallName call) (st^.stateLocation)
    ReturnState nm _ _ _ ->
      exitEvent tbl nm
    TailCallState _ call st ->
      do exitEvent tbl (st^.stateTree.actFrame.gpValue.frameFunctionName)
         enterEvent tbl (resolvedCallName call) (st^.stateLocation)
    SymbolicBranchState{} ->
      modifyIORef' (metricSplits (metrics tbl)) succ
    AbortState{} ->
      modifyIORef' (metricAborts (metrics tbl)) succ
    UnwindCallState _ _ st ->
      exitEvent tbl (st^.stateTree.actFrame.gpValue.frameFunctionName)
    BranchMergeState tgt st ->
      when (isMergeState tgt st)
           (modifyIORef' (metricMerges (metrics tbl)) succ)
    ControlTransferState res st ->
      let funcName = st^.stateTree.actFrame.gpValue.frameFunctionName in
      case res of
        ContinueResumption (ResolvedJump blk _) ->
          blockEvent tbl funcName (st^.stateLocation) (Some blk)
        CheckMergeResumption (ResolvedJump blk _) ->
          blockEvent tbl funcName (st^.stateLocation) (Some blk)
        _ -> return ()
    RunningState (RunBlockEnd _) st ->
      let funcName = st^.stateTree.actFrame.gpValue.frameFunctionName in
      case st^.stateTree.actFrame.gpValue.crucibleSimFrame.frameStmts of
        TermStmt loc term
          | Just blocks <- termStmtNextBlocks term,
            length blocks >= 2 ->
              branchEvent tbl funcName (Just loc) blocks
        _ -> return ()
    _ -> return ()

isMergeState ::
  CrucibleBranchTarget f args ->
  SimState p sym ext root f args ->
  Bool
isMergeState tgt st =
  case st^.stateTree.actContext of
    VFFBranch _ctx _assume_frame _loc _p other_branch tgt'
      | Just Refl <- testEquality tgt tgt' ->
          case other_branch of
            VFFActivePath{} -> False
            VFFCompletePath{} -> True
    VFFPartial _ctx _loc _p _ar NeedsToBeAborted -> True
    _ -> False


data ProfilingOptions =
  ProfilingOptions
  { periodicProfileInterval :: NominalDiffTime
  , periodicProfileAction   :: ProfilingTable -> IO ()
  }


-- | Write a profiling report file in the JS/JSON format expected by tye symProUI front end.
writeProfileReport ::
  FilePath {- ^ File to write -} ->
  String {- ^ "name" for the report -} ->
  String {- ^ "source" for the report -} ->
  ProfilingTable {- ^ profiling data to populate the report -} ->
  IO ()
writeProfileReport fp name source tbl =
   withFile fp WriteMode $ \h -> hPutStrLn h =<< symProUIString name source tbl

-- | This feature will pay attention to function call entry/exit events
--   and track the elapsed time and various other metrics in the given
--   profiling table.  The @ProfilingOptions@ can be used to export
--   intermediate profiling data at regular intervals, if desired.
profilingFeature ::
  ProfilingTable ->
  Maybe ProfilingOptions ->
  IO (GenericExecutionFeature sym)

profilingFeature tbl Nothing =
  return $ GenericExecutionFeature $ \exst -> updateProfilingTable tbl exst >> return ExecutionFeatureNoChange

profilingFeature tbl (Just profOpts) =
  do startTime <- getCurrentTime
     stateRef <- newIORef (computeNextState startTime)
     return (feat stateRef)

 where
 feat stateRef = GenericExecutionFeature $ \exst ->
        do updateProfilingTable tbl exst
           deadline <- readIORef stateRef
           now <- getCurrentTime
           if deadline >= now then
             return ExecutionFeatureNoChange
           else
             do periodicProfileAction profOpts tbl
                writeIORef stateRef (computeNextState now)
                return ExecutionFeatureNoChange

 computeNextState :: UTCTime -> UTCTime
 computeNextState lastOutputTime = addUTCTime (periodicProfileInterval profOpts) lastOutputTime
