{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
module Main(main) where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST(RealWorld, stToIO)
import System.IO(hPutStrLn,stdout,stderr)
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension,dropExtension,takeFileName)

import Control.Monad.State(evalStateT)
import Control.Monad.IO.Class(liftIO)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(pattern Empty)

import Text.LLVM.AST(Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)

import Lang.Crucible.Solver.OnlineBackend
          (withOnlineBackend,setConfig,getYicesProcess)
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))
import Lang.Crucible.Solver.SimpleBackend.Yices(push,pop,yicesConn)


import Lang.Crucible.Config(initialConfig)
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator.RegMap(emptyRegMap,regValue)
import Lang.Crucible.Simulator.ExecutionTree
        ( initSimContext, defaultErrorHandler, simConfig
        , ExecResult(..)
        )
import Lang.Crucible.Simulator.OverrideSim
        ( fnBindingsFromList, initSimState, runOverrideSim, callCFG)

import Lang.Crucible.Solver.Interface(IsSymInterface)
import Lang.Crucible.Solver.BoolInterface(getProofObligations)

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

outDir :: FilePath -> FilePath
outDir f = "output-" ++ dropExtension (takeFileName f)

main :: IO ()
main =
  do args <- getArgs
     case args of
       [file] | takeExtension file == ".bc" -> checkBC file
                                                `catch` errHandler file []
       file : incs ->
         (checkBC =<< genBitCode incs file (outDir file))
          `catch` errHandler file incs

       _ -> do p <- getProgName
               hPutStrLn stderr $ unlines
                  [ "Usage:"
                  , "  " ++ p ++ " FILE.bc"
                  , "  " ++ p ++ " FILE.c INC_DIR1 INC_DIR2 ..."
                  ]


errHandler :: FilePath -> [FilePath] -> Error -> IO ()
errHandler file incs e =
  do sayFail "Crux" (ppError e)
     case e of
       FailedToProve _ _ (Just c) ->
         do exe <- genCounterExe c incs file (outDir file)
            say "Crux" ("Counter example exe " ++ show exe)
       _ -> return ()
    `catch` \e1 -> sayFail "Crux" (ppError e1)



checkBC :: FilePath -> IO ()
checkBC file =
  do say "Crux" ("Checking " ++ show file)
     simulate file (checkFun "main")
     sayOK "Crux" "Valid."


-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (ArchOk arch, IsSymInterface sym) =>
  HandleAllocator RealWorld ->
  sym ->
  IO (SimCtxt sym arch)
setupSimCtxt halloc sym =
  withPtrWidth ?ptrWidth $
  do let verbosity = 0
     cfg <- initialConfig verbosity
               $ solver_adapter_config_options prover
                 -- ++ solver_adapter_config_options yicesOnlineAdapter
     return (initSimContext
                  sym
                  llvmIntrinsicTypes
                  cfg
                  halloc
                  stdout
                  (fnBindingsFromList [])
                  llvmExtensionImpl
                  emptyModel)


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


simulate ::
  FilePath ->
  (forall scope arch.
      ArchOk arch => ModuleCFGMap arch -> OverM scope arch ()
  ) ->
  IO ()
simulate file k =
  do llvm_mod   <- parseLLVM file
     halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withIONonceGenerator $ \nonceGen ->
       withOnlineBackend nonceGen $ \sym ->
       do -- sym <- newSimpleBackend nonceGen
          simctx <- setupSimCtxt halloc sym
          setConfig sym (simConfig simctx)
          yices <- getYicesProcess sym
          liftIO (push (yicesConn yices))

          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultErrorHandler

          res <- runOverrideSim simSt UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)
          liftIO (pop (yicesConn yices))

          case res of
            FinishedExecution ctx' _ ->
              mapM_ (proveGoal ctx' . mkGoal) =<< getProofObligations sym
            AbortedResult _ err -> throwError (SimFail err)

checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> OverM scope arch ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty -> (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _ -> throwError BadFun
    Nothing -> throwError (MissingFun nm)


