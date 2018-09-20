-- | Command line interface
--

{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# Language OverloadedStrings #-}

module Crux.CruxMain where


import Control.Monad
import Control.Exception(SomeException(..),displayException)
import System.IO(hPutStrLn,withFile,IOMode(..))
import System.FilePath((</>))
import System.Directory(createDirectoryIfMissing)


import Data.Parameterized.Nonce(withIONonceGenerator)

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Simulator

import Lang.Crucible.Simulator.Profiling
  ( newProfilingTable, startRecordingSolverEvents, symProUIString
  , executeCrucibleProfiling
  , inProfilingFrame
  )

-- crucible/what4
import What4.Config (setOpt, getOptionSetting, verbosity)
import What4.Interface ( getConfiguration )
import What4.FunctionName ( FunctionName )

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
main langs = processOptionsThen langs check 
        
-- | simulate the "main" method in the given class
check :: forall a. Language a => Options a -> IO ()
check opts@(cruxOpts,_langOpts) =
  do let file = inputFile cruxOpts
     when (simVerbose cruxOpts > 1) $
       say "Crux" ("Checking " ++ show file)
     res <- simulate opts
     when (outDir cruxOpts /= "") $
       generateReport cruxOpts res
     CL.makeCounterExamples opts res
  `catch` \(SomeException e) ->
      do putStrLn "TOP LEVEL EXCEPTION"
         putStrLn (displayException e) 

-- Returns only non-trivial goals 
simulate :: Language a => Options a -> 
  IO (Maybe ProvedGoals)
simulate opts  =
  let (cruxOpts,_langOpts) = opts
  in   
  
  withIONonceGenerator $ \nonceGen ->

  --withZ3OnlineBackend @_ @(Flags FloatIEEE) @_ nonceGen $ \sym -> do
  withYicesOnlineBackend nonceGen $ \(sym :: YicesOnlineBackend scope (Flags FloatReal)) -> do

     -- set the verbosity level
     void $ join (setOpt <$> getOptionSetting verbosity (getConfiguration sym)
                         <*> pure (toInteger (simVerbose cruxOpts)))
    
     void $ join (setOpt <$> getOptionSetting checkPathSatisfiability (getConfiguration sym)
                         <*> pure (checkPathSat cruxOpts))

    
     frm <- pushAssumptionFrame sym

     let personality = emptyModel

     let profiling = profileCrucibleFunctions cruxOpts
                  || profileSolver cruxOpts

     tbl <- newProfilingTable
     
     let inFrame :: forall b. FunctionName -> IO b -> IO b
         inFrame str = if profileCrucibleFunctions cruxOpts
           then inProfilingFrame tbl str Nothing
           else id

     when (profileSolver cruxOpts) $ 
       startRecordingSolverEvents sym tbl
       
     gls <- inFrame "<Crux>" $ do                   
       Result res <-
         if (profileCrucibleFunctions cruxOpts) then
           CL.simulate (executeCrucibleProfiling tbl) opts sym personality
         else
           CL.simulate executeCrucible opts sym personality
           
       _ <- popAssumptionFrame sym frm
         
       ctx' <- case res of
         FinishedResult ctx' _pr -> return ctx'
         AbortedResult ctx' _    -> return ctx'

       inFrame "<Proof Phase>" $
         do pg <- inFrame "<Prove Goals>" $
              (proveGoals ctx' =<< getProofObligations sym)
            inFrame "<SimplifyGoals>" $
              provedGoalsTree ctx' pg
                 
     when (simVerbose cruxOpts > 1) $
        say "Crux" "Simulation complete."

     when (profiling && outDir cruxOpts /= "") $ do
       createDirectoryIfMissing True (outDir cruxOpts)
       let profOutFile = outDir cruxOpts </> "report_data.js"
       withFile profOutFile WriteMode $ \h ->
         hPutStrLn h =<< symProUIString (inputFile cruxOpts) (inputFile cruxOpts) tbl            

     return gls
