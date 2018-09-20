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
import What4.Config (setOpt, getOptionSetting)
import What4.Interface ( getConfiguration )

-- crux
import Crux.Language(Language,Options)
import qualified Crux.Language as CL
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
     res <- simulate opts file
     generateReport cruxOpts res
     CL.makeCounterExamples opts res
  `catch` \(SomeException e) ->
      do putStrLn "TOP LEVEL EXCEPTION"
         putStrLn (displayException e) 


-- Returns only non-trivial goals 
simulate :: Language a => Options a -> 
  String ->
  IO (Maybe ProvedGoals)
simulate opts file  =
  let (cruxOpts,_langOpts) = opts
  in   
  
  withIONonceGenerator $ \nonceGen ->

  --withZ3OnlineBackend @_ @(Flags FloatIEEE) @_ nonceGen $ \sym -> do
  withYicesOnlineBackend nonceGen $ \(sym :: YicesOnlineBackend scope (Flags FloatReal)) -> do

     void $ join (setOpt <$> getOptionSetting checkPathSatisfiability (getConfiguration sym)
                              <*> pure (checkPathSat cruxOpts))

    
     frm <- pushAssumptionFrame sym

     let personality = emptyModel

     tbl <- newProfilingTable
     startRecordingSolverEvents sym tbl

     gls <- inProfilingFrame tbl "<Crux>" Nothing $ do

        Result res <- CL.simulate (executeCrucibleProfiling tbl)
          opts sym personality file
     
        _ <- popAssumptionFrame sym frm
     
        ctx' <- case res of
          FinishedResult ctx' _pr -> return ctx'
        -- The 'main' method returns void, so there is no need 
        -- to look at the result. However, if it does return an answer
        -- then we can look at it with this code:
        -- gp <- getGlobalPair pr
        -- putStrLn (showInt J.IntType (regValue (gp ^. gpValue)))
          AbortedResult ctx' _  -> return ctx'
        when (simVerbose cruxOpts > 1) $
          say "Crux" "Simulation complete."

        inProfilingFrame tbl "<Proof Phase>" Nothing $
          do pg <- inProfilingFrame tbl "<Prove Goals>" Nothing
                   (proveGoals ctx' =<< getProofObligations sym)
             inProfilingFrame tbl "<SimplifyGoals>" Nothing
                   (provedGoalsTree ctx' pg)

     let profOutFile = outDir cruxOpts </> "report_data.js"
     withFile profOutFile WriteMode $ \h ->
        -- TODO: in crucible-c the two arguments to symProUIString were the
        -- name of the .bc file, not the inputFile.
                                        
        hPutStrLn h =<< symProUIString (inputFile cruxOpts) (inputFile cruxOpts) tbl
                   
     return gls
                 


