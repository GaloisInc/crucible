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
import Control.Monad(unless)
import Control.Monad.State(evalStateT,liftIO,MonadIO)
import Control.Exception

import System.Process
import System.Exit
import System.IO(stdout)
import System.FilePath(takeExtension,dropExtension,takeFileName,(</>),(<.>))
import System.Directory(createDirectoryIfMissing)

import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(pattern Empty)

import Text.LLVM.AST(Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)
import qualified Data.LLVM.BitCode as LLVM

-- crucible
import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator
  ( emptyRegMap, regValue
  , fnBindingsFromList, initSimState, runOverrideSim, callCFG
  , SimError(..)
  , initSimContext, initSimState, defaultAbortHandler
  )

-- crucible-llvm
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn)
import Lang.Crucible.LLVM.MemModel(withPtrWidth)
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, initializeMemory, globalInitMap
        , transContext, cfgMap, populateAllGlobals
        , LLVMContext
        , ModuleCFGMap
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

-- main/checkBC implemented by Crux


makeCounterExamplesLLVM :: Options -> Maybe ProvedGoals -> IO ()
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

registerFunctions ::
  (ArchOk arch, IsSymInterface sym) =>
  LLVMContext arch ->
  ModuleTranslation arch ->
  OverM sym (LLVM arch) ()
registerFunctions ctx mtrans =
  do -- register the callable override functions
     evalStateT register_llvm_overrides ctx

     -- register all the functions defined in the LLVM module
     mapM_ registerModuleFn $ Map.toList $ cfgMap mtrans



-- Returns only non-trivial goals
simulateLLVM :: Crux.Simulate sym LangLLVM
simulateLLVM executeCrucible (_cruxOpts,llvmOpts) sym _p = do

    llvm_mod   <- parseLLVM (optsBCFile llvmOpts)
    halloc     <- newHandleAllocator
    Some trans <- stToIO (translateModule halloc llvm_mod)
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW ->
      withPtrWidth ptrW $ do
          let ?lc = llvmCtxt^.llvmTypeCtx
          let simctx = setupSimCtxt halloc sym
          mem  <- populateAllGlobals sym (globalInitMap trans)
                    =<< initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultAbortHandler

          res <- executeCrucible simSt $ runOverrideSim UnitRepr $
                   do registerFunctions llvmCtxt trans
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
     -- other options are tracked by Crux
     }

  defaultOptions = LLVMOptions
    {
      clangBin   = ""
    , libDir     = "c-src"
    , optsBCFile = ""
    }

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

    unless (takeExtension inp == ".bc") (genBitCode (cruxOpts2, opts3))

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
-- From Clang.hs

type Options = Crux.Options LangLLVM

-- | attempt to find Clang executable by searching the file system
-- throw an error if it cannot be found this way.
-- (NOTE: do not look for environment var "CLANG". That is assumed
--  to be tried already.)
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

runClang :: Options -> [String] -> IO ()
runClang opts params =
  do let clang = clangBin (snd opts)
     -- say "Clang" (show params)
     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)



genBitCode :: Options -> IO ()
genBitCode opts =
  do let dir  = Crux.outDir (fst opts)
     let libs = libDir (snd opts)
     createDirectoryIfMissing True dir

     let params = [ "-c", "-g", "-emit-llvm", "-O0"
                  , "-I", libs </> "includes"
                  , Crux.inputFile (fst opts)
                  , "-o", optsBCFile (snd opts)
                  ]
     runClang opts params


buildModelExes :: Options -> String -> String -> IO (FilePath,FilePath)
buildModelExes opts suff counter_src =
  do let dir  = Crux.outDir (fst opts)
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = libDir (snd opts)

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "concrete-backend.c"
                   , optsBCFile (snd opts)
                   , "-O0", "-g"
                   , "-o", debugExe
                   ]

     return (printExe, debugExe)
