{-# Language TemplateHaskell #-}
module Clang where

import System.Environment
import System.Process
import System.Exit
import System.FilePath
import System.Directory

import Error
import CLibSrc
import Log

data CCConfig = CCConfig
  { ccPath        :: FilePath           -- ^ Path to Clang
  , ccIncludes    :: [FilePath]         -- ^ Use these dirs when compiling
  , ccDefines     :: [(String,String)]  -- ^ CPP defines
  , ccWarns       :: Bool               -- ^ Do we want to see warnings
  }


getClang :: IO FilePath
getClang = return "clang-4.0" -- XXX

getLink :: IO FilePath
getLink = return "llvm-link-4.0" -- XXX

genBitCode ::
  [FilePath]  {- ^ Include paths -} ->
  FilePath    {- ^ Source file -} ->
  FilePath    {- ^ Output directory -} ->
  IO FilePath {- ^ Location of bit-code file -}
genBitCode incs src root =
  do let dir = root -- </> takeDirectory src
         tgt = dir </> dropExtension (takeFileName src) <.> "bc"
     createDirectoryIfMissing True dir

     clang <- getClang

     let params = [ "-c", "-g", "-emit-llvm" ]
               ++ concat [ ["-I",i] | i <- incs ]
               ++ [ src, "-o", tgt ]

     -- say "Clang" (src ++ " -> " ++ tgt)

     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return tgt
       ExitFailure n -> throwError (ClangError n sout serr)

cLibSrc

genCounterExe ::
  String      {- ^ Counter source -} ->
  [FilePath]  {- ^ Include paths -} ->
  FilePath    {- ^ Source file -} ->
  FilePath    {- ^ Output directory -} ->
  IO FilePath {- ^ Location of bit-code file -}
genCounterExe counter_src incs src root =
  do -- say "Crux" "Generating counter example executable"
     let dir = root -- </> takeDirectory src
         tgt = dir </> dropExtension (takeFileName src) ++ "-counter" <.> "exe"
     createDirectoryIfMissing True dir

     clang <- getClang

     let libName = dir </> "sv-comp.c"
     writeFile libName c_src

     let counterName = dir </> "counter-example.c"
     writeFile counterName counter_src

     let params = [ "-g", "-O2" ]
               ++ concat [ ["-I",i] | i <- incs ]
               ++ [ counterName
                  , libName
                  , src
                  , "-o", tgt ]

     -- say "Clang" (src ++ " -> " ++ tgt)

     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return tgt
       ExitFailure n -> throwError (ClangError n sout serr)



