{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language TypeFamilies #-}
{-# Language ApplicativeDo #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}

module CruxLLVMMain (main, mainWithOutputTo) where

import Data.String (fromString)
import qualified Data.Map as Map
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad(forM_)
import Control.Monad.ST(RealWorld, stToIO)
import Control.Monad.State(liftIO, MonadIO)
import Control.Exception
import Data.Text (Text)

import System.Process
import System.Exit
import System.IO (Handle, stdout)
import System.FilePath
  ( takeExtension, dropExtension, takeFileName, (</>)
  , takeDirectory, replaceExtension)
import System.Directory (createDirectoryIfMissing, removeFile)

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
  , SimErrorReason(..)
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
import qualified Crux

import Crux.Types
import Crux.Model
import Crux.Log

-- local
import Crux.LLVM.Overrides


main :: IO ()
main = mainWithOutputConfig defaultOutputConfig

mainWithOutputTo :: Handle -> IO ()
mainWithOutputTo h = mainWithOutputConfig (OutputConfig False h h)

mainWithOutputConfig :: OutputConfig -> IO ()
mainWithOutputConfig cfg =
  Crux.mainWithOutputConfig cfg cruxLLVM
  `catch` \(e :: SomeException) -> sayFail "Crux" (displayException e)
    where ?outputConfig = cfg

makeCounterExamplesLLVM ::
  Logs => Options -> ProvedGoals (Either AssumptionReason SimError) -> IO ()
makeCounterExamplesLLVM opts = go
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
          skipGoal = case simErrorReason c of
                       ResourceExhausted _ -> True
                       _ -> False

      in case (res, skipGoal) of
           (NotProved (Just m), False) ->
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
simulateLLVM :: Crux.SimulateCallback LLVMOptions
simulateLLVM fs (cruxOpts,_) sym _p = do
    llvm_mod   <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
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

checkFun :: (ArchOk arch, Logs) =>
            String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwCError BadFun
    Nothing -> throwCError (MissingFun nm)



-----------------------------------------------------------------------
-----------------------------------------------------------------------


-- Definitions for Crux front-end
-- This is an orphan instance because LangLLVM is declared in
-- the "Types" module so that we can refer to the instance
-- before it has been created here.

data LLVMOptions = LLVMOptions
  { clangBin   :: FilePath
  , linkBin    :: FilePath
  , clangOpts  :: [String]
  , libDir     :: FilePath
  , incDirs    :: [FilePath]
  }

cruxLLVM :: Crux.Language LLVMOptions
cruxLLVM = Crux.Language
  { Crux.name = "crux-llvm"
  , Crux.version = "0.1"
  , Crux.configuration = Crux.Config
      { Crux.cfgFile =
          do clangBin <- Crux.section "clang" Crux.fileSpec "clang"
                         "Binary to use for `clang`."

             linkBin  <- Crux.section "llvm-link" Crux.fileSpec "llvm-link"
                         "Binary to use for `clang`."

             clangOpts <- Crux.section "clang-opts"
                                        (Crux.oneOrList Crux.stringSpec) []
                          "Additional options for `clang`."

             libDir <- Crux.section "lib-dir" Crux.dirSpec "c-src"
                       "Locations of `crux-llvm` support library."

             incDirs <- Crux.section "include-dirs"
                            (Crux.oneOrList Crux.dirSpec) []
                        "Additional include directories."

             return LLVMOptions { .. }

      , Crux.cfgEnv  =
          [ Crux.EnvVar "CLANG"      "Binary to use for `clang`."
            $ \v opts -> Right opts { clangBin = v }

          , Crux.EnvVar "CLANG_OPTS" "Options to pass to `clang`."
            $ \v opts -> Right opts { clangOpts = words v }

          , Crux.EnvVar "LLVM_LINK" "Use this binary to link LLVM bitcode."
            $ \v opts -> Right opts { linkBin = v }
          ]

      , Crux.cfgCmdLineFlag =
          [ Crux.Option ['I'] ["include-dirs"]
            "Additional include directories."
            $ Crux.ReqArg "DIR"
            $ \d opts -> Right opts { incDirs = d : incDirs opts }
          ]
      }

  , Crux.initialize = initCruxLLVM
  , Crux.simulate   = simulateLLVM
  , Crux.makeCounterExamples = makeCounterExamplesLLVM
  }

initCruxLLVM :: Options -> IO Options
initCruxLLVM (cruxOpts,llvmOpts) =
  do -- keep looking for clangBin if it is unset
    clangFilePath <- if clangBin llvmOpts == ""
                        then getClang
                        else return (clangBin llvmOpts)

    let opts2 = llvmOpts { clangBin = clangFilePath }

    -- update outDir if unset
    name <- case Crux.inputFiles cruxOpts of
              x : _ -> pure (dropExtension (takeFileName x))
                          -- use the first file as output directory
              [] -> throwCError NoFiles

    let cruxOpts2 = if Crux.outDir cruxOpts == ""
                      then cruxOpts { Crux.outDir = "results" </> name }
                      else cruxOpts

        odir      = Crux.outDir cruxOpts2

    createDirectoryIfMissing True odir

    genBitCode (cruxOpts2, opts2)

    return (cruxOpts2, opts2)

---------------------------------------------------------------------

--
-- LLVM specific errors
--
data CError =
    ClangError Int String String
  | LLVMParseError LLVM.Error
  | MissingFun String
  | BadFun
  | EnvError String
  | NoFiles
    deriving Show

instance Exception CError where
  displayException = ppCError

ppCError :: CError -> String
ppCError err = case err of
    NoFiles                -> "crux-llvm requires at least one input file."
    EnvError msg           -> msg
    BadFun                 -> "Function should have no arguments"
    MissingFun x           -> "Cannot find code for " ++ show x
    LLVMParseError e       -> LLVM.formatError e
    ClangError n sout serr ->
      unlines $ [ "`clang` compilation failed."
                , "*** Exit code: " ++ show n
                , "*** Standard out:"
                ] ++
                [ "   " ++ l | l <- lines sout ] ++
                [ "*** Standard error:" ] ++
                [ "   " ++ l | l <- lines serr ]


throwCError :: MonadIO m => CError -> m b
throwCError e = liftIO (throwIO e)

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

type Options = Crux.Options LLVMOptions


isCPlusPlus :: FilePath -> Bool
isCPlusPlus file =
  case takeExtension file of
    ".cpp" -> True
    ".cxx" -> True
    ".C" -> True
    ".bc" -> False
    _ -> False

anyCPPFiles :: [FilePath] -> Bool
anyCPPFiles = any isCPlusPlus

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
      [] -> throwCError $ EnvError $
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
         allParams = clangOpts (snd opts) ++ params
     -- say "Clang" (show params)
     (res,sout,serr) <- readProcessWithExitCode clang allParams ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

llvmLink :: Options -> [FilePath] -> FilePath -> IO ()
llvmLink opts ins out =
  do let params = ins ++ [ "-o", out ]
     (res, sout, serr) <- readProcessWithExitCode (linkBin (snd opts)) params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)

parseLLVMLinkVersion :: String -> String
parseLLVMLinkVersion = go . map words . lines
  where
    go (("LLVM" : "version" : version : _) : _) = version
    go (_ : rest) = go rest
    go [] = ""

llvmLinkVersion :: Options -> IO String
llvmLinkVersion opts =
  do (res, sout, serr) <- readProcessWithExitCode (linkBin (snd opts)) ["--version"] ""
     case res of
       ExitSuccess   -> return (parseLLVMLinkVersion sout)
       ExitFailure n -> throwCError (ClangError n sout serr)

genBitCode :: Options -> IO ()
genBitCode opts =
  do let files = (Crux.inputFiles (fst opts))
         finalBCFile = Crux.outDir (fst opts) </> "combined.bc"
         srcBCNames = [ (src, replaceExtension src ".bc") | src <- files ]
         incs src = takeDirectory src :
                    (libDir (snd opts) </> "includes") :
                    incDirs (snd opts)
         params (src, srcBC) =
           [ "-c", "-g", "-emit-llvm", "-O0" ] ++
           concat [ [ "-I", dir ] | dir <- incs src ] ++
           [ "-o", srcBC, src ]
     forM_ srcBCNames $ \f -> runClang opts (params f)
     ver <- llvmLinkVersion opts
     let libcxxBitcode | anyCPPFiles files = [libDir (snd opts) </> "libcxx-" ++ ver ++ ".bc"]
                       | otherwise = []
     llvmLink opts (map snd srcBCNames ++ libcxxBitcode) finalBCFile
     mapM_ (removeFile . snd) srcBCNames

buildModelExes :: Options -> String -> String -> IO (FilePath,FilePath)
buildModelExes opts suff counter_src =
  do let dir  = Crux.outDir (fst opts)
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = libDir (snd opts)
         incs = (libs </> "includes") :
                (map takeDirectory files ++ incDirs (snd opts))
         files = (Crux.inputFiles (fst opts))
         libcxx | anyCPPFiles files = ["-lstdc++"]
                | otherwise = []

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang opts $ concat [ [ "-I", idir ] | idir <- incs ] ++
                     [ counterFile
                     , libs </> "concrete-backend.c"
                     , "-O0", "-g"
                     , "-o", debugExe
                     ] ++ files ++ libcxx

     return (printExe, debugExe)
