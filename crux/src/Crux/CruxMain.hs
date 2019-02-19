-- | Command line interface
--
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language OverloadedStrings #-}

module Crux.CruxMain where


import Control.Monad
import Control.Monad.IO.Class
import Control.Exception (SomeException(..), displayException)
import Data.Time.Clock (NominalDiffTime)
import Numeric (readFloat)
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing)


import Data.Parameterized.Nonce(withIONonceGenerator)

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.BoundedExec
import Lang.Crucible.Simulator.Profiling
import Lang.Crucible.Simulator.PathSatisfiability

-- crucible/what4
import What4.Config (setOpt, getOptionSetting, verbosity)
import What4.Interface (getConfiguration)
import What4.FunctionName (FunctionName)
import What4.Solver.Z3 (z3Timeout)

-- crux
import Crux.Language(Language,Options)
import qualified Crux.Language as CL    --- language-specific functions start with CL.
import Crux.Types
import Crux.Error
import Crux.Goal
import Crux.Model
import Crux.Log
import Crux.Options
import Crux.Report

-- | Entry point, parse command line opions
main :: [CL.LangConf] -> IO ()
main langs =
  let ?outputConfig = defaultOutputConfig
  in processOptionsThen langs check

mainWithOutputConfig :: OutputConfig -> [CL.LangConf] -> IO ()
mainWithOutputConfig cfg langs =
  let ?outputConfig = cfg
  in processOptionsThen langs check

-- | simulate the "main" method in the given class
check :: forall a. (Language a, ?outputConfig :: OutputConfig) => Options a -> IO ()
check opts@(cruxOpts,_langOpts) =
  do let file = inputFile cruxOpts
     when (simVerbose cruxOpts > 1) $
       say "Crux" ("Checking " ++ show file)
     res <- simulate opts
     when (outDir cruxOpts /= "") $
       generateReport cruxOpts res
     when (makeCexes cruxOpts) $
       CL.makeCounterExamples opts res
  `catch` \(SomeException e) ->
      do outputLn "TOP LEVEL EXCEPTION"
         outputLn (displayException e)


parseNominalDiffTime :: String -> Maybe NominalDiffTime
parseNominalDiffTime xs =
  case readFloat xs of
    (v,""):_ -> Just (fromRational (toRational (v::Double)))
    _ -> Nothing

-- Returns only non-trivial goals
simulate :: (Language a, ?outputConfig :: OutputConfig) => Options a ->
  IO (Maybe (ProvedGoals (Either AssumptionReason SimError)))
simulate opts  =
  let (cruxOpts,_langOpts) = opts
  in
  liftIO $
  withIONonceGenerator $ \nonceGen ->

  --withCVC4OnlineBackend @(Flags FloatReal) nonceGen ProduceUnsatCores $ \sym -> do
  --withZ3OnlineBackend @(Flags FloatReal) nonceGen ProduceUnsatCores $ \sym -> do
  withZ3OnlineBackend @(Flags FloatIEEE) nonceGen ProduceUnsatCores $ \sym -> do
  --withYicesOnlineBackend @(Flags FloatReal) nonceGen ProduceUnsatCores $ \sym -> do

     -- The simulator verbosity is one less than our verbosity.
     -- In this way, we can say things, without the simulator also being verbose
     let simulatorVerb = toInteger
                       $ if simVerbose cruxOpts > 1 then simVerbose cruxOpts - 1
                                                    else 0
     void $ join (setOpt <$> getOptionSetting verbosity (getConfiguration sym)
                         <*> pure simulatorVerb)

     void $ join (setOpt <$> getOptionSetting solverInteractionFile (getConfiguration sym)
                         <*> pure ("crux-solver.out"))

     void $ join (setOpt <$> getOptionSetting z3Timeout (getConfiguration sym)
                         <*> pure (goalTimeout cruxOpts * 1000))

     frm <- pushAssumptionFrame sym

     let personality = emptyModel

     let profiling = profileCrucibleFunctions cruxOpts
                  || profileSolver cruxOpts

     createDirectoryIfMissing True (outDir cruxOpts)

     tbl <- newProfilingTable

     let inFrame :: forall b. FunctionName -> IO b -> IO b
         inFrame str = if profiling
           then inProfilingFrame tbl str Nothing
           else id

     when (profileSolver cruxOpts) $
       startRecordingSolverEvents sym tbl

     let profOutFile = outDir cruxOpts </> "report_data.js"

     glblTimeout <-
        traverse
          (\v -> case parseNominalDiffTime v of
                   Nothing -> fail $ "Invalid timeout value: " ++ v
                   Just t  -> return t)
          (globalTimeout cruxOpts)

     profOpts <-
          traverse
          (\v -> case parseNominalDiffTime v of
                    Nothing -> fail $ "Invalid profiling output interval: " ++ v
                    Just t  -> return $
                      ProfilingOptions t (writeProfileReport profOutFile (inputFile cruxOpts) (inputFile cruxOpts)))
          (profileOutputInterval cruxOpts)

     pfs <- if (profileCrucibleFunctions cruxOpts) then
              do pf <- profilingFeature tbl profOpts
                 return [pf]
            else
              return []

     tfs <- case glblTimeout of
                 Nothing -> return []
                 Just delta ->
                   do tf <- timeoutFeature delta
                      return [tf]

     bfs <-
       case loopBound cruxOpts of
         Just istr ->
           case reads istr of
             (i,""):_ ->
               do bf <- boundedExecFeature (\_ -> return (Just i)) True {-produce side conditions-}
                  return [bf]
             _ -> fail ("Invalid loop iteration count: " ++ istr)
         Nothing -> return []

     psat_fs <-
       if checkPathSat cruxOpts then
         do psatf <- pathSatisfiabilityFeature sym (considerSatisfiability sym)
            return [psatf]
       else
         return []

     let execFeatures = tfs ++ pfs ++ bfs ++ psat_fs

     gls <- inFrame "<Crux>" $
       do Result res <- CL.simulate execFeatures opts sym personality

          case res of
            TimeoutResult _ ->
              do putStrLn "Simulation timed out! Program might not be fully verified!"
            _ -> return ()

          popUntilAssumptionFrame sym frm

          let ctx' = execResultContext res

          inFrame "<Prove Goals>" $
            do pg <- proveGoals ctx' =<< (getProofObligations sym)
               provedGoalsTree ctx' pg

     when (simVerbose cruxOpts > 1) $
        say "Crux" "Simulation complete."

     when profiling $ do
       writeProfileReport profOutFile (inputFile cruxOpts) (inputFile cruxOpts) tbl

     return gls
