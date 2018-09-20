{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language OverloadedStrings #-}

{-# Language FlexibleContexts #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main(main) where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST(RealWorld, stToIO)

import Control.Monad(unless,join,void)
import System.IO(stdout)
import System.FilePath(takeExtension,dropExtension,takeFileName,(</>),(<.>))
import System.Directory(createDirectoryIfMissing)

import Control.Monad.State(evalStateT,liftIO)

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
  , SimError(..)
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

import Lang.Crucible.LLVM.Extension(LLVM)
import What4.Config (setOpt, getOptionSetting)
import What4.Interface ( getConfiguration )
import What4.ProgramLoc

-- crux
import qualified Lang.Crucible.CFG.Core                as C
import qualified What4.Interface                       as W4
import qualified What4.InterpretedFloatingPoint        as W4


import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Error    as Crux

import           Crux.Types
import Crux.Model
import Crux.Log

import Types
import Error
import qualified Options as Clang
import Clang
import Overrides


main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @LangLLVM)]

-- main/checkBC implemented by Crux


{-
--- WHERE DO WE WRITEOUT THE PROFILING DATA??
let profOutFile = outDir opts </> "report_data.js"
          withFile profOutFile WriteMode $ \h ->
            hPutStrLn h =<< symProUIString (optsBCFile opts) (optsBCFile opts) tbl

-}





makeCounterExamplesLLVM :: Clang.Options -> Maybe ProvedGoals -> IO ()
makeCounterExamplesLLVM opts = maybe (return ()) go
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
  SimCtxt sym (LLVM arch)
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
       Left err -> throwCError (LLVMParseError err)
       Right m  -> return m

setupMem ::
  (ArchOk arch, IsSymInterface sym) =>
  LLVMContext arch ->
  ModuleTranslation arch ->
  OverM sym (LLVM arch) ()
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
simulateLLVM ::
  (IsBoolSolver sym, W4.IsSymExprBuilder sym, W4.IsInterpretedFloatSymExprBuilder sym,
    W4.SymInterpretedFloatType sym W4.SingleFloat ~ C.BaseRealType,
    W4.SymInterpretedFloatType sym W4.DoubleFloat ~ C.BaseRealType) =>    
  Crux.Options LangLLVM
    -> sym
    -> Model sym
    -> String
    -> IO (Result sym)
simulateLLVM (_cruxOpts,llvmOpts) sym _p _file = do

    llvm_mod   <- parseLLVM (optsBCFile llvmOpts)
    halloc     <- newHandleAllocator
    Some trans <- stToIO (translateModule halloc llvm_mod)
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW ->
      withPtrWidth ptrW $ do
          let simctx = setupSimCtxt halloc sym
          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultAbortHandler

          res <- executeCrucible simSt $ runOverrideSim UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      checkFun "main" (cfgMap trans)
          return $ Result res     

checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> Crux.throwBadFun
    Nothing -> Crux.throwMissingFun nm



-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- For now, we have an isomorphism between these two records of
-- types.
-- However, if we are willing to move the code from Clang.hs
-- to this module, we can make that code directly refer to
-- Crux.Options LangLLVM, instead of copying between the two.
toClangOptions :: Crux.Options LangLLVM -> Clang.Options
toClangOptions (cruxOpts, llvmOpts) =
  Clang.Options {
    Clang.clangBin   = clangBin llvmOpts
  , Clang.libDir     = libDir llvmOpts
  , Clang.outDir     = Crux.outDir cruxOpts
  , Clang.optsBCFile = optsBCFile llvmOpts
  , Clang.inputFile  = Crux.inputFile  cruxOpts
  }
  

-- Definitions for Crux front-end
-- This is an orphan instance because LangLLVM is declared in
-- the "Types" module so that we can refer to the instance
-- before it has been created here.

instance Crux.Language LangLLVM where
  name = "c"
  validExtensions = [".c", ".bc" ]

  type LangError LangLLVM = CError
  formatError = ppCError

  data LangOptions LangLLVM = LLVMOptions
     {
       clangBin   :: FilePath
     , libDir     :: FilePath
     , optsBCFile :: FilePath
     -- other two options are tracked by Crux
     }

  defaultOptions = LLVMOptions
    {
      clangBin   = ""
    , libDir     = "c-src"
    , optsBCFile = ""
    }

  cmdLineOptions = []
 
  envOptions = [("CLANG", \v opts -> opts { clangBin = v })]

  -- this is the replacement for "Clang.testOptions"
  ioOptions (cruxOpts,llvmOpts) = do
               
    -- keep looking for clangBin if it is unset
    clangFilePath <- if (clangBin llvmOpts == "")
             then getClang
             else return $ clangBin llvmOpts                  
    let opts2 = llvmOpts { clangBin = clangFilePath }

    -- update outDir if unset
    let inp   = Crux.inputFile cruxOpts
        name  = dropExtension (takeFileName inp)                  
        cruxOpts2 = if (Crux.outDir cruxOpts == "") then
                      cruxOpts { Crux.outDir = "results" </> name } else cruxOpts
        odir      = Crux.outDir cruxOpts2
        
    createDirectoryIfMissing True odir

    -- update optsBCFile if unset
    let opts3 = if (optsBCFile opts2 == "")
                then opts2 { optsBCFile = odir </> name <.> "bc" }
                else opts2

    unless (takeExtension inp == ".bc") (genBitCode (toClangOptions (cruxOpts2, opts3)))

    return (cruxOpts2, opts3)

  simulate = simulateLLVM
                      
  makeCounterExamples opts = makeCounterExamplesLLVM (toClangOptions opts)









=======
        _     -> throwError BadFun
    Nothing -> throwError (MissingFun nm)
>>>>>>> 2f29acd2f738770facc7164a11a06d45ba38adff
