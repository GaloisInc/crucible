-- | Command line interface to crucible-jvm
--
-- Currently this executable works as a simulator for Java classes.
-- It expects a static method "main" that takes no arguments and
-- returns an int result. It then executes the method and prints out
-- the result in hex.

-- TODO: set this up so we can make it run test cases

{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Main where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST
import Control.Monad
import Control.Monad.State.Strict

import Control.Exception(SomeException(..),displayException)
import Data.List

import System.Console.GetOpt
import System.IO
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle

import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.RegMap


-- crucible/what4
import What4.ProgramLoc
import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J


import qualified Lang.JVM.Codebase as JCB

import           Lang.Crucible.JVM.Translation

-- executable

import Error
import Goal
import Types
import Model
import Log
import Options
import Report

shortVersionText = "crucible-jvm-0.2"

-- | Entry point, parse command line opions
main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      case files of
        _ | showVersion opts'' -> hPutStrLn stderr shortVersionText
        _ | showHelp opts''   -> hPutStrLn stderr (usageInfo header options)
        [file] -> checkClass opts'' file
                  `catch` \(SomeException e) ->
                    do putStrLn "TOP LEVEL EXCEPTION"
                       putStrLn (displayException e)
        _ -> hPutStrLn stderr (usageInfo header options)
    (_, _, errs) -> do hPutStrLn stderr (concat errs ++ usageInfo header options)
                       return () -- exitProofUnknown
  where header = "Usage: crucible-jvm [OPTION...] [-I | file]"

-- | simulate the "main" method in the given class
checkClass :: Options -> String -> IO ()
checkClass opts classname =
  do -- say "Crux" ("Checking " ++ show classname)
     res <- simulate opts classname
     ---generateReport opts res
     makeCounterExamples opts res

makeCounterExamples :: Options -> Maybe ProvedGoals -> IO ()
makeCounterExamples opts = maybe (return ()) go
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
            NotProved (Just m) ->
              do sayFail "Crux" ("Counter example for " ++ msg)
            _ -> return ()

-- Returns only non-trivial goals
simulate ::
  Options -> 
  String ->
  IO (Maybe ProvedGoals)
simulate opts cname =
  withIONonceGenerator $ \nonceGen ->
  
  withYicesOnlineBackend nonceGen $ \(sym :: YicesOnlineBackend scope (Flags FloatReal)) -> do

     cb <- JCB.loadCodebase (jarList opts) (classPath opts)

     let mname = "main"

     frm <- pushAssumptionFrame sym

     let personality = emptyModel

     -- create a null array of strings for `args`
     -- TODO: figure out how to allocate an empty array
     let nullstr = RegEntry refRepr W4.Unassigned
     let regmap = RegMap (Ctx.Empty `Ctx.extend` nullstr)
     
     res <- executeCrucibleJVM @UnitType cb (simVerbose opts) sym
       personality cname mname regmap
           
     _ <- popAssumptionFrame sym frm
          
     ctx' <- case res of
               FinishedResult ctx' pr -> do
                 -- The 'main' method returns void, so there is no need
                 -- to look at the result. However, if it does return an answer
                 -- then we can look at it with this code:
                 -- gp <- getGlobalPair pr
                 -- putStrLn (showInt J.IntType (regValue (gp ^. gpValue)))
                 return ctx'
               AbortedResult ctx' _  -> return ctx'
      
     --say "Crux" "Simulation complete."
      
     provedGoalsTree ctx'
       =<< proveGoals ctx'
       =<<  getProofObligations sym

