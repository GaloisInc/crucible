{-# Language TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}

module Clang where

{-
import System.Process
import System.Exit
import System.FilePath
import System.Directory
import Control.Exception

import Options

-- crux
import Lang.Crucible.LLVM.Extension(LLVM,X86)
import qualified Data.LLVM.BitCode as LLVM


import qualified Crux.Language as Crux
import qualified Crux.Error as Crux

import Control.Monad
import Control.Monad.IO.Class(MonadIO)
import Data.Typeable

import Data.Parameterized.Some(Some(..))
-}

{-
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


-- LLVM-specific options

toOptions :: Crux.LangOptions (LLVM arch) -> Options
toOptions lopts = llvmOptions lopts



-- Definitions for Crux front-end

instance Typeable arch => Crux.Language (LLVM arch) where
  name = "c"
  validExtensions = [".c", ".bc" ]

  type LangError (LLVM arch) = CError
  formatError = formatCError

  data LangOptions (LLVM arch) = LLVMOptions
     {
       llvmOptions :: Options
     }

  defaultOptions = LLVMOptions
      {
        llvmOptions = Options {
          clangBin     = ""
          , libDir     = "c-src"
          , outDir     = ""
          , optsBCFile = ""
          , inputFile  = ""
          }
      }

  cmdLineOptions = []

  -- try to find CLANG in the environment
  envOptions = [("CLANG",
                  \v opts ->
                    opts { llvmOptions = (llvmOptions opts) { clangBin = v }})]

  -- 
  ioOptions cruxOpts lopts = do
    -- copy crux options into llvmOptions
    let opts = (llvmOptions lopts) { inputFile = Crux.inputFile cruxOpts,
                                     outDir    = Crux.outDir    cruxOpts }
               
    -- keep looking for clangBin if it is unset
    clangFilePath <- if (clangBin opts == "")
             then getClang
             else return $ clangBin opts                  
    let opts2 = opts { clangBin = clangFilePath }

    -- update outDir if unset
    let inp   = inputFile opts
        name  = dropExtension (takeFileName inp)                  
        opts3 = if (outDir opts2 == "") then opts2 { outDir = "results" </> name } else opts2
        odir  = outDir opts3
        
    createDirectoryIfMissing True odir

    -- update optsBCFile if unset
    let opts4 = if (optsBCFile opts3 == "") then opts3 { optsBCFile = odir </> name <.> "bc" }
                else opts3

    unless (takeExtension inp == ".bc") (genBitCode opts4)

    return LLVMOptions { llvmOptions = opts4 }

  simulate langOpts sym p verb file = do
    let ops = llvmOpts langOpts
    llvm_mod <- parseLLVM (optsBCFile opts)
    halloc     <- newHandleAllocator
    Some trans <- stToIO (translateModule halloc llvm_mod)
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW ->
      withPtrWidth ptrW $ do
      
          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt defaultAbortHandler

          executeCrucible simSt $ runOverrideSim UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)

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

runClang :: Options -> [String] -> IO ()
runClang opts params =
  do let clang = clangBin opts
     -- say "Clang" (show params)
     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwCError (ClangError n sout serr)



genBitCode :: Options -> IO ()
genBitCode opts =
  do let dir  = outDir opts
     let libs = libDir opts
     createDirectoryIfMissing True dir

     let params = [ "-c", "-g", "-emit-llvm", "-O0"
                  , "-I", libs </> "includes"
                  , inputFile opts
                  , "-o", optsBCFile opts
                  ]
     runClang opts params


buildModelExes :: Options -> String -> String -> IO (FilePath,FilePath)
buildModelExes opts suff counter_src =
  do let dir  = outDir opts
     createDirectoryIfMissing True dir

     let counterFile = dir </> ("counter-example-" ++ suff ++ ".c")
     let printExe    = dir </> ("print-model-" ++ suff)
     let debugExe    = dir </> ("debug-" ++ suff)
     writeFile counterFile counter_src

     let libs = libDir opts

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", printExe
                   ]

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "concrete-backend.c"
                   , optsBCFile opts
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



-}
  



