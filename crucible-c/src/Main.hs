{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}

{-# Language FlexibleContexts #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}

module Main(main) where

import Data.String(fromString)
import qualified Data.Map as Map
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
import Lang.Crucible.Simulator
  ( emptyRegMap,regValue, executeCrucible
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
import Lang.Crucible.LLVM.Extension(LLVM)
          
import What4.ProgramLoc

-- crux
import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Options  as Crux

import Crux.Types
import Crux.Error
import Crux.Goal
import Crux.Model
import Crux.Log
import Crux.Report

import Overrides
import Types

--import Clang



import System.Process
import System.Exit
import System.FilePath
import System.Directory
import Control.Exception



-- crux
import Lang.Crucible.LLVM.Extension(X86)
import qualified Data.LLVM.BitCode as LLVM


import qualified Crux.Language as Crux
import qualified Crux.Error as Crux

import Control.Monad
import Control.Monad.IO.Class(MonadIO)
import Data.Typeable

import Data.Parameterized.Some(Some(..))

import qualified Options as Clang

main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @(LLVM (X86 32)))]

{- 
main =
-  do args <- getArgs
-     case args of
-       file : _ ->
-          do opts <- testOptions file
-             do unless (takeExtension file == ".bc") (genBitCode opts)
-                checkBC opts
-           `catch` \e -> sayFail "Crux" (ppError e)
-       _ -> do p <- getProgName
-               hPutStrLn stderr $ unlines
-                  [ "Usage:"
-                  , "  " ++ p ++ " FILE.bc"
-                  ]
-    `catch` \(SomeException e) ->
-                    do putStrLn "TOP LEVEL EXCEPTION"
-                       putStrLn (displayException e)
-}

{-
-checkBC :: Options -> IO ()
-checkBC opts =
-  do let file = optsBCFile opts
-     say "Crux" ("Checking " ++ show file)
-     res <- simulate opts (checkFun "main")
-     generateReport opts res
-     makeCounterExamples opts res
-}

makeCounterExamples0 :: Clang.Options -> Maybe ProvedGoals -> IO ()
makeCounterExamples0 opts = maybe (return ()) go
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
{-
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

          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultAbortHandler

          res <- executeCrucible simSt $ runOverrideSim UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)

          _ <- popAssumptionFrame sym frm

          ctx' <- case res of
                    FinishedResult ctx' _ -> return ctx'
                    AbortedResult ctx' _  -> return ctx'

          say "Crux" "Simulation complete."

          provedGoalsTree ctx'
            =<< proveGoals ctx'
            =<< getProofObligations sym
-}

checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwBadFun
    Nothing -> throwMissingFun nm



-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- LLVM-specific errors
--
data CError =
    ClangError Int String String
  | LLVMParseError LLVM.Error

formatCError err = case err of
    LLVMParseError e       -> LLVM.formatError e
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]

throwCError :: (MonadIO m) => CError -> m a
throwCError e = Crux.throwError @(LLVM (X86 32)) (Crux.Lang  e)

toClangOptions :: Crux.Options (LLVM arch) -> Clang.Options
toClangOptions (cruxOpts, llvmOpts) =
  Clang.Options {
    Clang.clangBin   = clangBin llvmOpts
  , Clang.libDir     = libDir llvmOpts
  , Clang.outDir     = Crux.outDir cruxOpts
  , Clang.optsBCFile = optsBCFile llvmOpts
  , Clang.inputFile  = Crux.inputFile  cruxOpts
  }
  

-- Definitions for Crux front-end
-- UGH! We don't know the pointer width until after we parse.
-- So we cannot use (LLVM arch) to index the language.


instance Typeable arch => Crux.Language (LLVM arch) where
  name = "c"
  validExtensions = [".c", ".bc" ]

  type LangError (LLVM arch) = CError
  formatError = formatCError

  data LangOptions (LLVM arch) = LLVMOptions
     {
       clangBin :: FilePath
     , libDir   :: FilePath
     , optsBCFile :: FilePath
     }

  defaultOptions = LLVMOptions
    {
      clangBin   = ""
    , libDir     = "c-src"
    , optsBCFile = ""
    }

  cmdLineOptions = []
 
  -- try to find CLANG in the environment
  envOptions = [("CLANG",
                  \v opts -> opts { clangBin = v })]

  -- 
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

    putStrLn $ "setting BCFile: " ++ optsBCFile opts3
    putStrLn $ "inputFile is: "  ++ inp
    unless (takeExtension inp == ".bc") (genBitCode (toClangOptions (cruxOpts2, opts3)))

    return (cruxOpts2, opts3)

  simulate (_cruxOpts,llvmOpts) sym _p _file = do
    putStrLn $ "crucible-c sim of" ++ optsBCFile llvmOpts
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
                      
  makeCounterExamples opts = makeCounterExamples0 (toClangOptions opts)

--------------------------------------------------
--------------------------------------------------


-- | attempt to find Clang executable by searching the file system
-- throw an error if it cannot be found this way. 
getClang :: IO FilePath
getClang = attempt (map inPath opts)
  where
  inPath x = head . lines <$> readProcess "/usr/bin/which" [x] ""
  opts     = [ "clang", "clang-4.0", "clang-3.6" ]

  attempt :: [IO FilePath] -> IO FilePath
  attempt ms =
    case ms of
      [] -> Crux.throwEnvError $
              unlines [ "Failed to find `clang`."
                      , "You may use CLANG to provide path to executable."
                      ]
      m : more -> do x <- try m
                     case x of
                       Left (SomeException {}) -> attempt more
                       Right a -> return a

runClang :: Clang.Options -> [String] -> IO ()
runClang opts params =
  do let clang = Clang.clangBin opts
     -- say "Clang" (show params)
     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)



genBitCode :: Clang.Options -> IO ()
genBitCode opts =
  do let dir  = Clang.outDir opts
     let libs = Clang.libDir opts
     createDirectoryIfMissing True dir

     let params = [ "-c", "-g", "-emit-llvm", "-O0"
                  , "-I", libs </> "includes"
                  , Clang.inputFile opts
                  , "-o", Clang.optsBCFile opts
                  ]
     runClang opts params


buildModelExes :: Clang.Options -> String -> String -> IO (FilePath,FilePath)
buildModelExes opts suff counter_src =
  do let dir  = Clang.outDir opts
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = Clang.libDir opts

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "concrete-backend.c"
                   , Clang.optsBCFile opts
                   , "-O0", "-g"
                   , "-o", debugExe
                   ]

     return (printExe, debugExe)

{-
testOptions :: FilePath -> IO Options
testOptions inp =
  do clang <- getClang
     let name = dropExtension (takeFileName inp)
         odir = "results" </> name
     createDirectoryIfMissing True odir
     return Options { clangBin  = clang
                    , libDir    = "c-src"
                    , outDir    = odir
                    , inputFile = inp
                    , optsBCFile = odir </> name <.> "bc"
                    }
-}
-----------------------------------------------------
-----------------------------------------------------




  



