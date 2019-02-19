{-# Language DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module CruxLLVMMain (main, mainWithOutputTo) where

import Data.String (fromString)
import qualified Data.Map as Map
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad.ST(RealWorld, stToIO)
import Control.Monad.State(liftIO, MonadIO)
import Control.Exception
import Data.Text (Text)

import System.Process
import System.Exit
import System.IO (Handle, stdout)
import System.FilePath
  ( takeExtension, dropExtension, takeFileName, (</>), (<.>)
  , takeDirectory)
import System.Directory (createDirectoryIfMissing, copyFile)

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context (pattern Empty)

import Text.LLVM.AST (Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)
import qualified Data.LLVM.BitCode as LLVM
import qualified Text.LLVM as LLVM

-- crucible
import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator
  ( emptyRegMap, regValue, SimError(..)
  , fnBindingsFromList, runOverrideSim, callCFG
  , initSimContext, profilingMetrics
  , ExecState( InitialState ), SimState, defaultAbortHandler
  , executeCrucible, genericToExecutionFeature, printHandle
  )
import Lang.Crucible.Simulator.ExecutionTree ( stateGlobals )
import Lang.Crucible.Simulator.GlobalState ( lookupGlobal )
import Lang.Crucible.Simulator.Profiling ( Metric(Metric) )

-- crucible-llvm
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn)
import Lang.Crucible.LLVM.Globals
        ( initializeMemory, populateAllGlobals )
import Lang.Crucible.LLVM.MemModel
        ( MemImpl, withPtrWidth, memAllocCount, memWriteCount )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap
        , LLVMContext, llvmMemVar, ModuleCFGMap
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, llvmPtrWidth, register_llvm_overrides, llvmTypeCtx)

import Lang.Crucible.LLVM.Extension(LLVM)

-- what4
import What4.ProgramLoc

-- crux
import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Error    as Crux

import Crux.Types
import Crux.Model
import Crux.Log

-- local
import Overrides

-- | Index for the crux-c "Language"
data LangLLVM


main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @LangLLVM)]

mainWithOutputTo :: Handle -> IO ()
mainWithOutputTo h =
  Crux.mainWithOutputConfig (OutputConfig False h h) [Crux.LangConf (Crux.defaultOptions @LangLLVM)]

-- main/checkBC implemented by Crux


makeCounterExamplesLLVM :: (?outputConfig :: OutputConfig) => Options -> Maybe (ProvedGoals (Either AssumptionReason SimError)) -> IO ()
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
          msg = show c

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
  LLVMContext arch ->
  SimCtxt sym (LLVM arch)
setupSimCtxt halloc sym llvmCtxt =
  initSimContext sym
                 llvmIntrinsicTypes
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 llvmExtensionImpl
                 emptyModel
    & profilingMetrics %~ Map.union (llvmMetrics llvmCtxt)


-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwCError (LLVMParseError err)
       Right m  -> return m

registerFunctions ::
  (ArchOk arch, IsSymInterface sym) =>
  LLVMContext arch ->
  LLVM.Module ->
  ModuleTranslation arch ->
  OverM sym (LLVM arch) ()
registerFunctions ctx llvm_module mtrans =
  do -- register the callable override functions
     _ctx' <- register_llvm_overrides llvm_module ctx

     -- register all the functions defined in the LLVM module
     mapM_ registerModuleFn $ Map.toList $ cfgMap mtrans



-- Returns only non-trivial goals
simulateLLVM :: (?outputConfig :: OutputConfig) => Crux.Simulate sym LangLLVM
simulateLLVM fs (_cruxOpts,llvmOpts) sym _p = do
    llvm_mod   <- parseLLVM (optsBCFile llvmOpts)
    halloc     <- newHandleAllocator
    Some trans <- stToIO (translateModule halloc llvm_mod)
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW ->
      withPtrWidth ptrW $ do
          let ?lc = llvmCtxt^.llvmTypeCtx
          let simctx = (setupSimCtxt halloc sym llvmCtxt) { printHandle = view outputHandle ?outputConfig }
          mem <- populateAllGlobals sym (globalInitMap trans)
                    =<< initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem

          res <- executeCrucible (map genericToExecutionFeature fs) $
                   InitialState simctx globSt defaultAbortHandler $
                   runOverrideSim UnitRepr $
                     do registerFunctions llvmCtxt llvm_mod trans
                        setupOverrides llvmCtxt
                        checkFun "main" (cfgMap trans)
          return $ Result res

checkFun :: (ArchOk arch, ?outputConfig :: OutputConfig) => String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
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


-- Definitions for Crux front-end
-- This is an orphan instance because LangLLVM is declared in
-- the "Types" module so that we can refer to the instance
-- before it has been created here.

instance Crux.Language LangLLVM where
  name = "llvm"
  validExtensions = [".c", ".cpp", ".cxx", ".C", ".bc" ]

  type LangError LangLLVM = CError
  formatError = ppCError

  data LangOptions LangLLVM = LLVMOptions
     {
       clangBin   :: FilePath
     , libDir     :: FilePath
     , optsBCFile :: FilePath
     -- other options are tracked by Crux
     }

  defaultOptions = LLVMOptions
    {
      clangBin   = "clang"
    , libDir     = "c-src"
    , optsBCFile = ""
    }

  envOptions = [ ("CLANG",   \v opts -> opts { clangBin = v }) ]

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

    if takeExtension inp == ".bc"
      then copyFile inp (optsBCFile opts3)
      else (genBitCode (cruxOpts2, opts3))

    return (cruxOpts2, opts3)

  simulate = simulateLLVM

  makeCounterExamples opts = makeCounterExamplesLLVM opts

---------------------------------------------------------------------
---------------------------------------------------------------------

--
-- C-specific errors
--
data CError =
    ClangError Int String String
  | LLVMParseError LLVM.Error

ppCError :: CError -> String
ppCError err = case err of
    LLVMParseError e       -> LLVM.formatError e
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]

-- Currently unused
{-
ppErr :: AbortedResult sym ext -> String
ppErr aberr =
  case aberr of
    AbortedExec abt _gp -> show (ppAbortExecReason abt)
    AbortedExit e       -> "The program exited with result " ++ show e
    AbortedBranch {}    -> "(Aborted branch?)"
-}

throwCError :: (MonadIO m) => CError -> m b
throwCError e = Crux.throwError @LangLLVM (Crux.Lang  e)

---------------------------------------------------------------------
---------------------------------------------------------------------
-- Profiling

llvmMetrics :: forall arch p sym ext
             . LLVMContext arch
            -> Map.Map Text (Metric p sym ext)
llvmMetrics llvmCtxt = Map.fromList [ ("LLVM.allocs", allocs)
                                    , ("LLVM.writes", writes)
                                    ]
  where
    allocs = Metric $ measureMemBy memAllocCount
    writes = Metric $ measureMemBy memWriteCount

    measureMemBy :: (MemImpl sym -> Int)
                 -> SimState p sym ext r f args
                 -> IO Integer
    measureMemBy f st = do
      let globals = st ^. stateGlobals
      case lookupGlobal (llvmMemVar llvmCtxt) globals of
        Just mem -> return $ toInteger (f mem)
        Nothing -> fail "Memory missing from global vars"

---------------------------------------------------------------------
---------------------------------------------------------------------
-- From Clang.hs

type Options = Crux.Options LangLLVM

data InputLanguage
  = CSource
  | CPPSource
  | Bitcode

optInputLanguage :: Options -> Maybe InputLanguage
optInputLanguage opts =
  case takeExtension (takeFileName (Crux.inputFile (fst opts))) of
    ".c" -> Just CSource
    ".cpp" -> Just CPPSource
    ".cxx" -> Just CPPSource
    ".C" -> Just CPPSource
    ".bc" -> Just Bitcode
    _ -> Nothing

-- | attempt to find Clang executable by searching the file system
-- throw an error if it cannot be found this way.
-- (NOTE: do not look for environment var "CLANG". That is assumed
--  to be tried already.)
getClang :: IO FilePath
getClang = attempt (map inPath clangs)
  where
  inPath x = head . lines <$> readProcess "/usr/bin/which" [x] ""
  clangs   = [ "clang", "clang-4.0", "clang-3.6", "clang-3.8" ]

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

runClang :: Options -> [String] -> IO ()
runClang opts params =
  do let clang = clangBin (snd opts)
     -- say "Clang" (show params)
     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

llvmLink :: [FilePath] -> FilePath -> IO ()
llvmLink ins out =
  do let params = ins ++ [ "-o", out ]
     -- TODO: make this work better for a range of clang versions
     (res, sout, serr) <- readProcessWithExitCode "llvm-link-3.6" params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

genBitCode :: Options -> IO ()
genBitCode opts =
  do let lang = optInputLanguage opts
         srcDir = takeDirectory (Crux.inputFile (fst opts))
         finalBCFile = optsBCFile (snd opts)
         curBCFile = case lang of
                       Just CPPSource -> finalBCFile ++ "-tmp"
                       _ -> finalBCFile
         params = [ "-c", "-g", "-emit-llvm", "-O0"
                  , "-I", libDir (snd opts) </> "includes"
                  , "-I", srcDir
                  , Crux.inputFile (fst opts)
                  , "-o", curBCFile
                  ]
     runClang opts params
     case lang of
       -- TODO: make this work better for a range of clang versions
       Just CPPSource ->
         llvmLink [ curBCFile, libDir (snd opts) </> "libcxx-36.bc" ] finalBCFile
       _ -> return ()


buildModelExes :: Options -> String -> String -> IO (FilePath,FilePath)
buildModelExes opts suff counter_src =
  do let dir  = Crux.outDir (fst opts)
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = libDir (snd opts)
         libcxx = case optInputLanguage opts of
                    Just CPPSource -> ["-lstdc++"]
                    _ -> []

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang opts $ [ "-I", libs </> "includes"
                     , counterFile
                     , libs </> "concrete-backend.c"
                     , Crux.inputFile (fst opts)
                     , "-O0", "-g"
                     , "-o", debugExe
                     ] ++ libcxx

     return (printExe, debugExe)
