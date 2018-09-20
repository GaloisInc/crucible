{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language OverloadedStrings #-}

{-# Language FlexibleContexts #-}
{-# Language TypeApplications #-}
module Main(main) where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST(RealWorld, stToIO)
import Control.Monad(unless, join, void)
import Control.Exception(SomeException(..),displayException)
import System.IO(hPutStrLn,stdout,stderr,withFile,IOMode(..))
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension, (</>))

import Control.Monad.State(evalStateT,liftIO)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(pattern Empty)

import Text.LLVM.AST(Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)


import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator.Profiling
  ( newProfilingTable, startRecordingSolverEvents, symProUIString
  , executeCrucibleProfiling, inProfilingFrame
  )
import Lang.Crucible.Simulator
  ( emptyRegMap, regValue
  , fnBindingsFromList, initSimState, runOverrideSim, callCFG
  , SimError(..), ExecResult(..)
  , initSimContext, initSimState, defaultAbortHandler
  )
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn)
import Lang.Crucible.LLVM.MemModel(withPtrWidth)
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, initializeMemory
        , transContext, cfgMap, initMemoryCFG
        , LLVMContext
        , ModuleCFGMap
        )
import Lang.Crucible.LLVM.Intrinsics
          (llvmIntrinsicTypes, llvmPtrWidth, register_llvm_overrides)

import What4.Config (setOpt, getOptionSetting)
import What4.Interface ( getConfiguration )
import What4.ProgramLoc



import Error
import Goal
import Types
import Overrides
import Model
import Clang
import Log
import Options
import Report

main :: IO ()
main =
  do args <- getArgs
     case args of
       file : _ ->
          do opts <- testOptions file
             do unless (takeExtension file == ".bc") (genBitCode opts)
                checkBC opts
           `catch` \e -> sayFail "Crux" (ppError e)
       _ -> do p <- getProgName
               hPutStrLn stderr $ unlines
                  [ "Usage:"
                  , "  " ++ p ++ " FILE.bc"
                  ]
    `catch` \(SomeException e) ->
                    do putStrLn "TOP LEVEL EXCEPTION"
                       putStrLn (displayException e)

checkBC :: Options -> IO ()
checkBC opts =
  do let file = optsBCFile opts
     say "Crux" ("Checking " ++ show file)
     res <- simulate opts (checkFun "main")
     generateReport opts res
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
                (_prt,dbg) <- buildModelExes opts suff (modelInC m)
                say "Crux" ("*** debug executable: " ++ dbg)
                say "Crux" ("*** break on line: " ++ suff)
           _ -> return ()

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (ArchOk arch, IsSymInterface sym) =>
  HandleAllocator RealWorld ->
  sym ->
  SimCtxt sym arch
setupSimCtxt halloc sym =
  initSimContext sym
                 llvmIntrinsicTypes
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 llvmExtensionImpl
                 emptyModel


-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwError (LLVMParseError err)
       Right m  -> return m

setupMem ::
  (ArchOk arch, IsSymInterface sym) =>
  LLVMContext arch ->
  ModuleTranslation arch ->
  OverM sym arch ()
setupMem ctx mtrans =
  do -- register the callable override functions
     evalStateT register_llvm_overrides ctx

     -- initialize LLVM global variables
     -- XXX: this might be wrong: only RO globals should be set
     _ <- case initMemoryCFG mtrans of
            SomeCFG initCFG -> callCFG initCFG emptyRegMap

      -- register all the functions defined in the LLVM module
     mapM_ registerModuleFn $ Map.toList $ cfgMap mtrans


-- Returns only non-trivial goals
simulate ::
  Options ->
  (forall sym arch.
      ArchOk arch => ModuleCFGMap arch -> OverM sym arch ()
  ) ->
  IO (Maybe ProvedGoals)
simulate opts k =
  do llvm_mod   <- parseLLVM (optsBCFile opts)
     halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withIONonceGenerator $ \nonceGen ->
       --withZ3OnlineBackend @_ @(Flags FloatIEEE) @_ nonceGen $ \sym ->
       withYicesOnlineBackend @_ @(Flags FloatReal) @_ nonceGen $ \sym ->
       do frm <- pushAssumptionFrame sym
          let simctx = setupSimCtxt halloc sym

          void $ join (setOpt <$> getOptionSetting checkPathSatisfiability (getConfiguration sym)
                              <*> pure (checkPathSat opts))

          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultAbortHandler

          tbl <- newProfilingTable
          startRecordingSolverEvents sym tbl

          gls <- inProfilingFrame tbl "<Crux>" Nothing $
            do res <- executeCrucibleProfiling tbl simSt $ runOverrideSim UnitRepr $
                     do setupMem llvmCtxt trans
                        setupOverrides llvmCtxt
                        k (cfgMap trans)

               _ <- popAssumptionFrame sym frm

               ctx' <- case res of
                         FinishedResult ctx' _ -> return ctx'
                         AbortedResult ctx' _  -> return ctx'

               say "Crux" "Simulation complete."

               inProfilingFrame tbl "<Proof Phase>" Nothing $
                 do pg <- inProfilingFrame tbl "<Prove Goals>" Nothing
                             (proveGoals ctx' =<< getProofObligations sym)
                    inProfilingFrame tbl "<SimplifyGoals>" Nothing
                             (provedGoalsTree ctx' pg)

          let profOutFile = outDir opts </> "report_data.js"
          withFile profOutFile WriteMode $ \h ->
            hPutStrLn h =<< symProUIString (optsBCFile opts) (optsBCFile opts) tbl

          return gls


checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> OverM sym arch ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwError BadFun
    Nothing -> throwError (MissingFun nm)
