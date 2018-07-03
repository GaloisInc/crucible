{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}

{-# Language FlexibleContexts #-}
module Main(main) where

import Data.String(fromString)
import qualified Data.Foldable as Fold
import qualified Data.Map as Map
import Data.Maybe(catMaybes)
import Control.Lens((^.))
import Control.Monad.ST(RealWorld, stToIO)
import Control.Monad(unless)
import Control.Exception(SomeException(..),displayException)
import System.IO(hPutStrLn,stdout,stderr)
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension)

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
import Lang.Crucible.Simulator.RegMap(emptyRegMap,regValue)
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.EvalStmt
        ( executeCrucible )
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Simulator.OverrideSim
        ( fnBindingsFromList, initSimState, runOverrideSim, callCFG)

import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn)
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, initializeMemory
        , transContext, cfgMap, initMemoryCFG
        , LLVMContext
        , ModuleCFGMap
        )
import Lang.Crucible.LLVM.Types(withPtrWidth)
import Lang.Crucible.LLVM.Intrinsics
          (llvmIntrinsicTypes, llvmPtrWidth, register_llvm_overrides)



import Error
import Goal
import Types
import Overrides
import Model
import Clang
import Log
import Options
import ProgressBar
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
     generateReport opts =<< simulate opts (checkFun "main")

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
  IO [ ([AssumptionReason], SimError, ProofResult) ]
simulate opts k =
  do llvm_mod   <- parseLLVM (optsBCFile opts)
     halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withIONonceGenerator $ \nonceGen ->
       -- withZ3OnlineBackend nonceGen $ \sym ->
       withYicesOnlineBackend nonceGen $ \sym ->
       do frm <- pushAssumptionFrame sym
          let simctx = setupSimCtxt halloc sym

          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultErrorHandler

          res <- executeCrucible simSt $ runOverrideSim UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)

          _ <- popAssumptionFrame sym frm

          ctx' <- case res of
                    FinishedResult ctx' _ -> return ctx'
                    AbortedResult ctx' _ ->
                      do putStrLn "Aborted result"
                         return ctx'

          say "Crux" "Simulation complete."

          gs <- Fold.toList <$> getProofObligations sym
          let n = length gs
              suff = if n == 1 then "" else "s"
          say "Crux" ("Proving " ++ show n ++ " side condition" ++ suff ++ ".")
          fmap catMaybes $
            withProgressBar 60 gs $ \g ->
               do result <- proveGoal ctx' g
                  case result of
                    NotProved {} -> return (Just (toRes result g))
                    Proved ->
                      do simp <- simpProved ctx' g
                         case simp of
                           Trivial -> return Nothing
                           NotTrivial g1 -> return (Just (toRes Proved g1))

   where toRes result g =
           ( map (^. labeledPredMsg)
                 (Fold.toList (proofAssumptions g))
           , proofGoal g ^. labeledPredMsg
           , result
           )


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



