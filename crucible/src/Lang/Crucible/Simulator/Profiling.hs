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
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.Profiling
  ( executeCrucibleProfiling
  , newProfilingTable

    -- * Profiling data structures
  , CGEvent(..)
  , CGEventType(..)
  , ProfilingTable(..)
  , Metrics(..)
  , symProUIJSON
  , symProUIString
  ) where

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad.Reader
import           Data.Foldable (toList)
import           Data.IORef
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Time.Clock
import           Data.Time.Clock.POSIX
import           Data.Time.Format
import           System.IO.Error as Ex
import           Text.JSON

import           What4.Config
import           What4.FunctionName
import           What4.Interface
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Operations


data Metrics f =
  Metrics
  { metricSplits   :: f Integer
  , metricMerges   :: f Integer
  , metricAborts   :: f Integer
  }

deriving instance Show (Metrics Identity)

traverseF_metrics :: Applicative m =>
  (forall s. e s -> m (f s)) ->
  Metrics e -> m (Metrics f)
traverseF_metrics h (Metrics x1 x2 x3) =
  Metrics <$> h x1 <*> h x2 <*> h x3

instance FunctorF Metrics where
  fmapF = fmapFDefault
instance FoldableF Metrics where
  foldMapF = foldMapFDefault
instance TraversableF Metrics where
  traverseF = traverseF_metrics

metricsToJSON :: Metrics Identity -> UTCTime -> JSValue
metricsToJSON m time = JSObject $ toJSObject $
    [ ("time", showJSON time)
    , ("split-count", showJSON $ metricSplits m )
    , ("merge-count", showJSON $ metricMerges m )
    , ("abort-count", showJSON $ metricAborts m )
    ]


data CGEventType = ENTER | EXIT
 deriving (Show,Eq,Ord)

data CGEvent =
  CGEvent
  { cgEvent_fnName   :: FunctionName
  , cgEvent_source   :: Maybe Position
  , cgEvent_callsite :: Maybe Position
  , cgEvent_type     :: CGEventType
  , cgEvent_metrics  :: Metrics Identity
  , cgEvent_time     :: UTCTime
  , cgEvent_id       :: Integer
  }
 deriving (Show)

instance JSON a => JSON (Identity a) where
  readJSON = fmap Identity . readJSON
  showJSON = showJSON . runIdentity

instance JSON UTCTime where
  readJSON _ = error "FIXME JSONM UTCTime"
  showJSON t = showJSON ((fromRational $ toRational $ utcTimeToPOSIXSeconds t) :: Double)

instance JSON CGEventType where
  readJSON _ = error "FIXME JSON CGEventType"
  showJSON ENTER = showJSON "ENTER"
  showJSON EXIT  = showJSON "EXIT"

instance JSON CGEvent where
  readJSON _ = error "FIXME JSON CGEvent"
  showJSON ev = JSObject $ toJSObject $
    [ ("function", showJSON $ functionName $ cgEvent_fnName ev)
    , ("type", showJSON (cgEvent_type ev))
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

positionToJSON :: Position -> JSValue
positionToJSON p = showJSON $ show $ p

callGraphJSON :: Seq CGEvent -> JSValue
callGraphJSON evs = JSObject $ toJSObject
  [ ("type", showJSON "callgraph")
  , ("events", JSArray (map showJSON $ toList evs))
  ]

symProUIString :: String -> String -> ProfilingTable -> IO String
symProUIString nm source tbl =
  do js <- symProUIJSON nm source tbl
     return ("data.receiveData("++ encode js ++ ");")

symProUIJSON :: String -> String -> ProfilingTable -> IO JSValue
symProUIJSON nm source tbl =
  do now <- getCurrentTime
     evs <- readIORef (callGraphEvents tbl)
     return $ JSArray $
       [ JSObject $ toJSObject $ metadata now
       , callGraphJSON evs
       , JSObject $ toJSObject $ solver_calls
       , JSObject $ toJSObject $ unused_terms
       ]
 where
 solver_calls =
   [ ("type", showJSON "solver-calls")
   , ("events", JSArray [])
   ]
 
 unused_terms =
   [ ("type", showJSON "unused-terms")
   , ("data", JSArray [])
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
  , metrics :: Metrics IORef
  , eventIDRef :: IORef Integer
  }

newProfilingTable :: IO ProfilingTable
newProfilingTable =
  do m <- Metrics <$> newIORef 0
                  <*> newIORef 0
                  <*> newIORef 0
     evs <- newIORef mempty
     idref <- newIORef 0
     return (ProfilingTable evs m idref)

nextEventID :: ProfilingTable -> IO Integer
nextEventID tbl =
  do i <- readIORef (eventIDRef tbl)
     writeIORef (eventIDRef tbl) $! (i+1) 
     return i

enterEvent ::
  ProfilingTable ->
  FunctionName ->
  Maybe ProgramLoc ->
  IO ()
enterEvent tbl nm callLoc =
  do now <- getCurrentTime
     m <- traverseF (pure . Identity <=< readIORef) (metrics tbl)
     i <- nextEventID tbl
     let p = fmap plSourceLoc callLoc
     modifyIORef' (callGraphEvents tbl) (Seq.|> CGEvent nm Nothing p ENTER m now i)

exitEvent ::
  ProfilingTable ->
  FunctionName ->
  IO ()
exitEvent tbl nm =
  do now <- getCurrentTime
     m <- traverseF (pure . Identity <=< readIORef) (metrics tbl)
     i <- nextEventID tbl
     modifyIORef' (callGraphEvents tbl) (Seq.|> CGEvent nm Nothing Nothing EXIT m now i)

resolvedCallName :: ResolvedCall p sym ext ret -> FunctionName
resolvedCallName (OverrideCall _o f) =
  override f
resolvedCallName (CrucibleCall _bid f) =
  case frameHandle f of SomeHandle h -> handleName h


updateProfilingTable ::
  ProfilingTable ->
  ExecState p sym ext rtp ->
  IO ()
updateProfilingTable tbl = \case
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
  ControlTransferState tgt st ->
    when (isMergeState tgt st)
         (modifyIORef' (metricMerges (metrics tbl)) succ)
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
    VFFPartial _ctx _p _ar NeedsToBeAborted -> True
    _ -> False




executeCrucibleProfiling :: forall p sym ext rtp f a.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  ProfilingTable ->
  SimState p sym ext rtp f a {- ^ Initial simulator state -} ->
  ExecCont p sym ext rtp f a {- ^ Execution continuation to run -} ->
  IO (ExecResult p sym ext rtp)
executeCrucibleProfiling tbl st0 cont =
  do let cfg = st0^.stateConfiguration
     verbOpt <- getOptionSetting verbosity cfg
     enterEvent tbl (st0^.stateTree.actFrame.gpValue.frameFunctionName) Nothing
     loop verbOpt st0 cont

 where
 loop :: forall f' a'.
   OptionSetting BaseIntegerType ->
   SimState p sym ext rtp f' a' ->
   ExecCont p sym ext rtp f' a' ->
   IO (ExecResult p sym ext rtp)
 loop verbOpt st m =
   do exst <- Ex.catches (runReaderT m st)
                [ Ex.Handler $ \(e::AbortExecReason) ->
                    runAbortHandler e st
                , Ex.Handler $ \(e::Ex.IOException) ->
                    if Ex.isUserError e then
                      runGenericErrorHandler (Ex.ioeGetErrorString e) st
                    else
                      Ex.throwIO e
                ]
      updateProfilingTable tbl exst
      case exst of
        ResultState res ->
          return res

        AbortState rsn st' ->
          let (AH handler) = st'^.abortHandler in
          loop verbOpt st' (handler rsn)

        OverrideState ovr st' ->
          loop verbOpt st' (overrideHandler ovr)

        SymbolicBranchState p a_frame o_frame tgt st' ->
          loop verbOpt st' (performIntraFrameSplit p a_frame o_frame tgt)

        ControlTransferState tgt st' ->
          loop verbOpt st' (performIntraFrameMerge tgt)

        CallState retHandler frm st' ->
          loop verbOpt st' (performFunctionCall retHandler frm)

        TailCallState vfv frm st' ->
          loop verbOpt st' (performTailCall vfv frm)

        ReturnState fnm vfv ret st' ->
          loop verbOpt st' (performReturn fnm vfv ret)

        UnwindCallState vfv ar st' ->
          loop verbOpt st' (resumeValueFromValueAbort vfv ar)

        RunningState _runTgt st' ->
          do verb <- fromInteger <$> getOpt verbOpt
             loop verbOpt st' (stepBasicBlock verb)

