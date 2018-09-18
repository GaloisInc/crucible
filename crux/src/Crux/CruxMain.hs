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

module Crux.CruxMain where


import Control.Monad
import Control.Exception(SomeException(..),displayException)
import Data.List
import System.Console.GetOpt
import System.IO
import System.Environment

import Data.Parameterized.Nonce(withIONonceGenerator)

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Simulator

-- crucible/what4
import What4.ProgramLoc

-- crux
import qualified Crux.Language as CL
import Crux.Error
import Crux.Goal
import Crux.Model
import Crux.Log
import Crux.Options
import Crux.Report

shortVersionText :: forall a. CL.Language a => String
shortVersionText = "crux-" ++ CL.name @a ++ "-0.1"

-- | Entry point, parse command line opions
main :: forall a. CL.Language a => IO ()
main = do
  hSetBuffering stdout LineBuffering
  let loptions = CL.options @a
  argv <- getArgs
  case getOpt Permute (options @a) argv of
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      case files of
        _ | showVersion opts'' -> hPutStrLn stderr (shortVersionText @a)
        _ | showHelp opts''   -> hPutStrLn stderr (usageInfo header loptions)
        [file] -> check opts'' file
                  `catch` \(SomeException e) ->
                    do putStrLn "TOP LEVEL EXCEPTION"
                       putStrLn (displayException e) 
        _ -> hPutStrLn stderr (usageInfo header loptions)
    (_, _, errs) -> do hPutStrLn stderr (concat errs ++ usageInfo header loptions)
                       return () -- exitProofUnknown
  where header = "Usage: crux" ++ CL.name @a ++ " [OPTION...] [-I | file]"

-- | simulate the "main" method in the given class
check :: forall a. CL.Language a => Options a -> String -> IO ()
check opts classname =
  do when (simVerbose opts > 1) $
       say "Crux" ("Checking " ++ show classname)
     res <- simulate @a opts classname 
     generateReport opts res
     makeCounterExamples opts res

makeCounterExamples :: Options a -> Maybe ProvedGoals -> IO ()
makeCounterExamples _opts = maybe (return ()) go
  where
  go gs =
   case gs of
     AtLoc _ _ gs1 -> go gs1
     Branch g1 g2  -> go g1 >> go g2
     Goal _ (c,_) _ res ->
       let suff = case plSourceLoc (simErrorLoc c) of
                    SourcePos _ l _ -> show l
                    _               -> "unknown"
           msg = show (simErrorReason c)
 
       in case res of
            NotProved (Just _m) ->
              do sayFail "Crux" ("Counter example for " ++ msg)
--                 (_prt,dbg) <- buildModelExes opts suff (modelInC m)
--                 say "Crux" ("*** debug executable: " ++ dbg)
                 say "Crux" ("*** break on line: " ++ suff)
            _ -> return ()

-- Returns only non-trivial goals
simulate :: forall a. CL.Language a =>
  Options a -> 
  String ->
  IO (Maybe ProvedGoals)
simulate opts cname =
  withIONonceGenerator $ \nonceGen ->
  
  withYicesOnlineBackend nonceGen $ \(sym :: YicesOnlineBackend scope (Flags FloatReal)) -> do

     frm <- pushAssumptionFrame sym

     let personality = emptyModel

     res <- CL.simulate @a (langOptions opts) sym personality (simVerbose opts) cname 
                 
     _ <- popAssumptionFrame sym frm
          
     ctx' <- case res of
               FinishedResult ctx' _pr -> return ctx'
                 -- The 'main' method returns void, so there is no need 
                 -- to look at the result. However, if it does return an answer
                 -- then we can look at it with this code:
                 -- gp <- getGlobalPair pr
                 -- putStrLn (showInt J.IntType (regValue (gp ^. gpValue)))
               AbortedResult ctx' _  -> return ctx'

     when (simVerbose opts > 1) $
       say "Crux" "Simulation complete."
      
     provedGoalsTree ctx'
       =<< proveGoals ctx'
       =<< getProofObligations sym

