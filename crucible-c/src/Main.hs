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

import Control.Monad.State(evalStateT)

import Data.Parameterized.Nonce(NonceGenerator,withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(pattern Empty)

import Text.LLVM.AST(Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)

import Lang.Crucible.Solver.SimpleBackend (newSimpleBackend)
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))


import Lang.Crucible.Config(initialConfig)
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..)
                             , cfgArgTypes, cfgReturnType)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator.RegMap(emptyRegMap,regValue)
import Lang.Crucible.Simulator.ExecutionTree
        ( initSimContext, ctxSymInterface, defaultErrorHandler
        , ExecResult(..)
        )
import Lang.Crucible.Simulator.OverrideSim
        ( fnBindingsFromList, initSimState, runOverrideSim, callCFG)

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


main :: IO ()
main =
  do args <- getArgs
     case args of
       [file,fun] ->
         do simulate file (checkFun fun)
            putStrLn "Valid."
          `catch` \e -> hPutStrLn stderr (ppError e)

       _ -> do p <- getProgName
               hPutStrLn stderr ("Usage: " ++ p ++ " FILE FUN")



-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  ArchOk arch =>
  HandleAllocator RealWorld ->
  NonceGenerator IO scope ->
  IO (SimCtxt scope arch)
setupSimCtxt halloc nonceG =
  withPtrWidth ?ptrWidth $
  do let verbosity = 0
     cfg <- initialConfig verbosity (solver_adapter_config_options prover)
     sym <- newSimpleBackend nonceG
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
  ArchOk arch => LLVMContext arch -> ModuleTranslation arch -> Code scope arch
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
  (forall scope arch. ArchOk arch => ModuleCFGMap arch -> Code scope arch) ->
  IO ()
simulate file k =
  do llvm_mod   <- parseLLVM file
     halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withIONonceGenerator $ \nonceGen ->
       do simctx <- setupSimCtxt halloc nonceGen
          let sym = simctx ^. ctxSymInterface
          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultErrorHandler

          res <- runOverrideSim simSt UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)

          case res of
            FinishedExecution ctx' _ ->
              mapM_ (proveGoal ctx' . mkGoal) =<< getProofObligations sym
            AbortedResult _ err -> throwError (SimFail err)

checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> Code scope arch
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case (cfgArgTypes anyCfg, cfgReturnType anyCfg) of
        (Empty, UnitRepr) -> regValue <$> callCFG anyCfg emptyRegMap
        _ -> throwError BadFun
    Nothing -> throwError (MissingFun nm)


