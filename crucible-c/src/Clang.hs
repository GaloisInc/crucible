{-# Language TemplateHaskell #-}
module Clang where

import System.Environment
import System.Process
import System.Exit
import System.FilePath
import System.Directory
import Control.Exception

import Error
-- import CLibSrc
-- import Log
import Options



getClang :: IO FilePath
getClang = attempt $ getEnv "CLANG"
                   : map inPath opts
  where
  inPath x = head . lines <$> readProcess "/usr/bin/which" [x] ""
  opts     = [ "clang", "clang-4.0", "clang-3.6" ]

  attempt :: [IO FilePath] -> IO FilePath
  attempt ms =
    case ms of
      [] -> throwError $ EnvError $
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
       ExitFailure n -> throwError (ClangError n sout serr)



genBitCode :: Options -> IO ()
genBitCode opts =
  do let dir = outDir opts
     let libs = libDir opts
     createDirectoryIfMissing True dir

     let params = [ "-c", "-g", "-emit-llvm", "-O0"
                  , "-I", libs </> "includes"
                  , inputFile opts
                  , "-o", optsBCFile opts
                  ]
     runClang opts params


buildModelExes :: Options -> String -> IO ()
buildModelExes opts counter_src =
  do let dir  = outDir opts
     createDirectoryIfMissing True dir

     let counterFile = dir </> "counter-example.c"
     writeFile counterFile counter_src

     let libs = libDir opts
     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "print-model.c"
                   , "-o", dir </> "print-counter-example"
                   ]

     runClang opts [ "-I", libs </> "includes"
                   , counterFile
                   , libs </> "concrete-backend.c"
                   , optsBCFile opts
                   , "-O0", "-g"
                   , "-o", dir </> "debug"
                   ]


testOptions :: FilePath -> IO Options
testOptions inp =
  do clang <- getClang
     let name = dropExtension (takeFileName inp)
         odir = "out" </> name
     createDirectoryIfMissing True odir
     return Options { clangBin  = clang
                    , libDir    = "c-src"
                    , outDir    = odir
                    , inputFile = inp
                    , optsBCFile = odir </> name <.> "bc"
                    }





