
{-# Language ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language TypeFamilies #-}
{-# Language ApplicativeDo #-}
{-# Language RecordWildCards #-}
{-# Language ScopedTypeVariables #-}

module CruxLLVMMain (main, mainWithOutputTo, mainWithOutputConfig, registerFunctions) where

import Data.String (fromString)
import qualified Data.Map as Map
import Data.IORef
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad(forM_,unless)
import Control.Monad.State(liftIO, MonadIO)
import Control.Exception
import Data.IORef
import qualified Data.Foldable as Fold
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import Data.List(intercalate, isSuffixOf)
import qualified Data.Text as Text

import Data.Binary.IEEE754 as IEEE754
import qualified Data.Parameterized.Map as MapF

import System.Process
import System.Exit
import System.IO (Handle, stdout)
import System.FilePath
  ( takeExtension, dropExtension, takeFileName, (</>)
  , takeDirectory, replaceExtension)
import System.Directory (createDirectoryIfMissing, removeFile, doesFileExist, copyFile)

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
import Lang.Crucible.Simulator.PathSplitting( executeCrucibleDFSPaths )
import Lang.Crucible.Simulator.Profiling ( Metric(Metric) )


-- crucible-llvm
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn )
import Lang.Crucible.LLVM.Globals
        ( initializeAllMemory, populateAllGlobals )
import Lang.Crucible.LLVM.MemModel
        ( MemImpl, withPtrWidth, memAllocCount, memWriteCount
        , MemOptions(..), laxPointerMemOptions, HasLLVMAnn, LLVMAnnMap
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap
        , LLVMContext, llvmMemVar, ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, register_llvm_overrides)

import Lang.Crucible.LLVM.Extension(LLVM)

-- what4
import What4.ProgramLoc

-- crux
import qualified Crux

import Crux.Goal
import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common
import Crux.SVCOMP

-- local
import Crux.LLVM.Overrides


main :: IO ()
main = mainWithOutputConfig defaultOutputConfig >>= exitWith

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig (OutputConfig False h h False)

mainWithOutputConfig :: OutputConfig -> IO ExitCode
mainWithOutputConfig cfg =
  Crux.mainWithOutputConfig cfg cruxLLVM
  `catch` \(e :: SomeException) ->
      do sayFail "Crux" (displayException e)
         return (ExitFailure 1)
    where ?outputConfig = cfg

makeCounterExamplesLLVM ::
  Logs => Options -> Seq (ProvedGoals (Either AssumptionReason SimError)) -> IO ()
makeCounterExamplesLLVM opts = mapM_ go . Fold.toList
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
           (NotProved _ (Just m), False) ->
             do sayFail "Crux" ("Counter example for " ++ msg)
                (_prt,dbg) <- buildModelExes opts suff (ppModelC m)
                say "Crux" ("*** debug executable: " ++ dbg)
                say "Crux" ("*** break on line: " ++ suff)
           _ -> return ()

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  HandleAllocator ->
  sym ->
  MemOptions ->
  LLVMContext arch ->
  SimCtxt sym (LLVM arch)
setupSimCtxt halloc sym memOpts llvmCtxt =
  initSimContext sym
                 llvmIntrinsicTypes
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 (llvmExtensionImpl memOpts)
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
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  LLVM.Module ->
  ModuleTranslation arch ->
  OverM sym (LLVM arch) ()
registerFunctions llvm_module mtrans =
  do let llvm_ctx = mtrans ^. transContext
     let ?lc = llvm_ctx ^. llvmTypeCtx

     -- register the callable override functions
     register_llvm_overrides llvm_module [] (cruxLLVMOverrides++svCompOverrides++cbmcOverrides) llvm_ctx

     -- register all the functions defined in the LLVM module
     mapM_ (registerModuleFn llvm_ctx) $ Map.elems $ cfgMap mtrans


-- Returns only non-trivial goals
simulateLLVM :: Crux.SimulateCallback LLVMOptions
simulateLLVM fs (cruxOpts,llvmOpts) (sym :: sym) _p cont = do
    llvm_mod   <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
    halloc     <- newHandleAllocator
    let ?laxArith = laxArithmetic llvmOpts
    Some trans <- translateModule halloc llvm_mod
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW -> do
      withPtrWidth ptrW $ do
        bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
        let ?lc = llvmCtxt^.llvmTypeCtx

        -- shrug... some weird interaction between do notation and implicit parameters here...
        -- not sure why I have to let/in this expression...
        let ?badBehaviorMap = bbMapRef in

           do let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt) { printHandle = view outputHandle ?outputConfig }
              mem <- populateAllGlobals sym (globalInitMap trans)
                         =<< initializeAllMemory sym llvmCtxt llvm_mod
              let globSt = llvmGlobals llvmCtxt mem

              let initSt = InitialState simctx globSt defaultAbortHandler UnitRepr $
                        runOverrideSim UnitRepr $
                          do registerFunctions llvm_mod trans
                             checkFun "main" (cfgMap trans)

              case pathStrategy cruxOpts of
                 AlwaysMergePaths ->
                   do res <- executeCrucible (map genericToExecutionFeature fs) initSt
                      cont (Result res)
                 SplitAndExploreDepthFirst ->
                   do (i,ws) <- executeCrucibleDFSPaths (map genericToExecutionFeature fs) initSt (cont . Result)
                      say "Crux" ("Total paths explored: " ++ show i)
                      unless (null ws) $
                        sayWarn "Crux" (unwords [show (Seq.length ws), "paths remaining not explored: program might not be fully verified"])

checkFun :: (ArchOk arch, Logs) =>
            String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwCError BadFun
    Nothing -> throwCError (MissingFun nm)


ppValsC :: BaseTypeRepr ty -> Vals ty -> String
ppValsC ty (Vals xs) =
  let (cty, cnm, ppRawVal) = case ty of
        BaseBVRepr n ->
          ("int" ++ show n ++ "_t", "int" ++ show n ++ "_t", show)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 8, natValue sb == 24
          -> ("float", "float", show . IEEE754.wordToFloat . fromInteger)
        BaseFloatRepr (FloatingPointPrecisionRepr eb sb)
          | natValue eb == 11, natValue sb == 53
          -> ("double", "double", show . IEEE754.wordToDouble . fromInteger)
        BaseRealRepr -> ("double", "real", (show . toDouble))
        _ -> error ("Type not implemented: " ++ show ty)
  in unlines
      [ "size_t const crucible_values_number_" ++ cnm ++
                " = " ++ show (length xs) ++ ";"

      , "const char* crucible_names_" ++ cnm ++ "[] = { " ++
            intercalate "," (map (show . entryName) xs) ++ " };"

      , cty ++ " const crucible_values_" ++ cnm ++ "[] = { " ++
            intercalate "," (map (ppRawVal . entryValue) xs) ++ " };"
      ]

ppModelC :: ModelView -> String
ppModelC m = unlines
             $ "#include <stdint.h>"
             : "#include <stddef.h>"
             : ""
             : MapF.foldrWithKey (\k v rest -> ppValsC k v : rest) [] vals
            where vals = modelVals m

propertyVerdict :: VerificationTask -> Maybe Bool
propertyVerdict task = foldl f Nothing (verificationProperties task)
 where
 comb b Nothing  = Just b
 comb b (Just x) = Just $! b && x

 f v (CheckNoError _nm, Just b)  = comb b v
 f v (CheckValidFree, Just b)    = comb b v
 f v (CheckValidDeref, Just b)   = comb b v
 f v (CheckDefBehavior, Just b)  = comb b v
 f v (CheckNoOverflow, Just b)   = comb b v
 f v _ = v

data ComputedVerdict
  = Verified
  | Falsified
  | Unknown

evaluateBenchmarkLLVM :: Logs => Options -> BenchmarkSet -> IO Integer
evaluateBenchmarkLLVM (cruxOpts,llvmOpts) bs =
   do scoreRef <- newIORef 0
      mapM_ (evaluateVerificationTask scoreRef) (zip [0::Int ..] (benchmarkTasks bs))
      readIORef scoreRef
 where
 bsRoot = Crux.outDir cruxOpts </> Text.unpack (benchmarkName bs)

 evaluateVerificationTask _ (_num,task)
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist cruxOpts ]
   = putStrLn $ unlines
        [ "Skipping:"
        , "  " ++ verificationSourceFile task
        ]

 evaluateVerificationTask scoreRef (num,task) =
   do let taskRoot = svTaskDirectory bsRoot num task
      let srcRoot  = takeDirectory (verificationSourceFile task)
      let inputs   = map (srcRoot </>) (verificationInputFiles task)
      let cruxOpts' = cruxOpts { outDir = taskRoot, inputFiles = inputs }
      putStrLn $ unlines
        [ "Evaluating:"
        , "  " ++ taskRoot
        , "  " ++ verificationSourceFile task
        ]
      (cmpl, gls) <- Crux.runSimulator cruxLLVM (cruxOpts', llvmOpts)
      Crux.generateReport cruxOpts' gls
      let verdict
            | sum (fmap countDisprovedGoals gls) > 0 = Falsified
            | Crux.ProgramComplete <- cmpl
            , sum (fmap countUnknownGoals gls) == 0 = Verified
            | otherwise                             = Unknown

      case propertyVerdict task of
        Nothing -> putStrLn $ unlines (["No verdict to evaluate!"] ++ map show (verificationProperties task))
        Just True ->
          case verdict of
            Verified  ->
               do modifyIORef' scoreRef (1+)
                  putStrLn "CORRECT"
            Falsified ->
               do modifyIORef' scoreRef (negate 16 +)
                  putStrLn $ unwords ["FAILED! benchmark should be verified"]
            Unknown   -> putStrLn "UNKNOWN"
        Just False ->
          case verdict of
            Verified  ->
               do modifyIORef' scoreRef (negate 32 +)
                  putStrLn $ unwords ["FAILED! benchmark should contain an error!"]
            Falsified ->
               do modifyIORef' scoreRef (1+)
                  putStrLn "CORRECT"
            Unknown   -> putStrLn "UNKNOWN"

-----------------------------------------------------------------------
-----------------------------------------------------------------------


-- Definitions for Crux front-end

data LLVMOptions = LLVMOptions
  { clangBin   :: FilePath
  , linkBin    :: FilePath
  , clangOpts  :: [String]
  , libDir     :: FilePath
  , incDirs    :: [FilePath]
  , memOpts    :: MemOptions
  , laxArithmetic :: Bool
  , lazyCompile :: Bool
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

             memOpts <- do laxPointerOrdering <-
                             Crux.section "lax-pointer-ordering" Crux.yesOrNoSpec False
                               "Allow order comparisons between pointers from different allocation blocks"
                           laxConstantEquality <-
                             Crux.section "lax-constant-equality" Crux.yesOrNoSpec False
                               "Allow equality comparisons between pointers to constant data"
                           return MemOptions{..}

             laxArithmetic <- Crux.section "lax-arithmetic" Crux.yesOrNoSpec False
                               "Do not produce proof obligations related to arithmetic overflow, etc."

             lazyCompile <- Crux.section "lazy-compile" Crux.yesOrNoSpec False
                               "Avoid compiling bitcode from source if intermediate files already exist"

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

          , Crux.Option [] ["lazy-compile"]
            "Avoid compiling bitcode from source if intermediate files already exist (default: off)"
            $ Crux.NoArg
            $ \opts -> Right opts{ lazyCompile = True }

          , Crux.Option [] ["lax-pointers"]
            "Turn on lax rules for pointer comparisons"
            $ Crux.NoArg
            $ \opts -> Right opts{ memOpts = laxPointerMemOptions }

          , Crux.Option [] ["lax-arithmetic"]
            "Turn on lax rules for arithemetic overflow"
            $ Crux.NoArg
            $ \opts -> Right opts { laxArithmetic = True }
          ]
      }

  , Crux.initialize = initCruxLLVM
  , Crux.simulate   = simulateLLVM
  , Crux.evaluateBenchmark = evaluateBenchmarkLLVM
  , Crux.makeCounterExamples = makeCounterExamplesLLVM
  }

initCruxLLVM :: Options -> IO Options
initCruxLLVM (cruxOpts,llvmOpts) =
  do -- keep looking for clangBin if it is unset
     clangFilePath <- if clangBin llvmOpts == ""
                        then getClang
                        else return (clangBin llvmOpts)

     let opts2 = llvmOpts { clangBin = clangFilePath }

     if svcompMode cruxOpts then
       svCompInit opts2
     else
       simpleInit opts2

 where
 svCompInit opts2 =
  do let cruxOpts2 = if Crux.outDir cruxOpts == ""
                        then cruxOpts { Crux.outDir = "results" </> "sv-comp" }
                        else cruxOpts
         odir = Crux.outDir cruxOpts2

     createDirectoryIfMissing True odir
     genSVCOMPBitCode (cruxOpts2, opts2)
     return (cruxOpts2, opts2)

 simpleInit opts2 =
  do -- update outDir if unset
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

runClang' :: Options -> [String] -> IO ()
runClang' opts params =
  do let clang = clangBin (snd opts)
         allParams = clangOpts (snd opts) ++ params
     putStrLn $ unwords ( clang : map show allParams)
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


svTaskDirectory :: FilePath -> Int -> VerificationTask -> FilePath
svTaskDirectory base num task = base </> path
 where
 files = verificationInputFiles task
 path  = padTaskNum ++ filebase files

 padWidth = 5

 filebase [] = ""
 filebase (f:_) = '_' : takeFileName f

 padTaskNum = padding ++ xs
   where
   padding = take (padWidth - length xs) (repeat '0')
   xs = show num


genSVCOMPBitCode :: Options -> IO ()
genSVCOMPBitCode opts@(cruxOpts,llvmOpts) =
    mapM_ processBenchmark (svcompBenchmarks cruxOpts)
 where
 processBenchmark bs =
   do let nm = benchmarkName bs
      putStrLn $ unwords ["Preparing", show nm]
      tgt <- getTarget bs
      mapM_ (processVerificationTask tgt (Text.unpack nm)) (zip [0::Int ..] (benchmarkTasks bs))

 processVerificationTask _tgt _benchName (_num,task)
   | or [ isSuffixOf bl (verificationSourceFile task) | bl <- svcompBlacklist cruxOpts ]
   = return ()

 processVerificationTask tgt benchName (num,task) =
   do let files = verificationInputFiles task
          inputBase = takeDirectory (verificationSourceFile task)
          outputPath  = svTaskDirectory (Crux.outDir cruxOpts </> benchName) num task
          finalBCFile = outputPath </> "combined.bc"
          srcBCNames = [ (inputBase </> src, outputPath </> replaceExtension src ".bc") | src <- files ]
          incs src = [ inputBase </> takeDirectory src
                     , libDir llvmOpts </> "includes"
                     ] ++ incDirs llvmOpts
          params (src, srcBC) =
            [ "-c", "-g", "-emit-llvm", "-O1", "-fsanitize=shift", "-fsanitize-trap=shift", "--target=" ++ tgt ] ++
            concat [ ["-I", dir] | dir <- incs src ] ++
            [ "-o", srcBC, src ]

      createDirectoryIfMissing True outputPath

      finalBcExists <- doesFileExist finalBCFile
      unless (finalBcExists && lazyCompile llvmOpts) $
        do forM_ srcBCNames $ \(src, srcBC) ->
              do copyFile src (takeDirectory srcBC </> takeFileName src)
                 copyFile (verificationSourceFile task) (takeDirectory srcBC </> takeFileName (verificationSourceFile task))
                 bcExists <- doesFileExist srcBC
                 unless (bcExists && lazyCompile llvmOpts) $
                   do runClang' opts (params (src, srcBC))
           llvmLink opts (map snd srcBCNames) finalBCFile

 getTarget bs =
   case benchmarkArchWidth bs of
     Just 32 -> return "i386-unknown-linux-elf"
     Just 64 -> return "x86_64-unknown-linux-elf"
     _ -> fail $ "Unexpected or missing architecture width"


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
     finalBCExists <- doesFileExist finalBCFile
     unless (finalBCExists && lazyCompile (snd opts)) $
      do forM_ srcBCNames $ \f -> runClang opts (params f)
         ver <- llvmLinkVersion opts
         let libcxxBitcode | anyCPPFiles files = [libDir (snd opts) </> "libcxx-" ++ ver ++ ".bc"]
                           | otherwise = []
         llvmLink opts (map snd srcBCNames ++ libcxxBitcode) finalBCFile
         mapM_ (\(src,bc) -> unless (src == bc) (removeFile bc)) srcBCNames

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
