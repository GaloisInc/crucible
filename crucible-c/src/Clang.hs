module Clang where

import System.Environment
import System.Process
import System.Exit
import System.FilePath
import System.Directory

import Error

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
  do let dir = root </> takeDirectory src
         tgt = dir </> dropExtension (takeFileName src) <.> "bc"
     createDirectoryIfMissing True dir

     clang <- getClang

     let params = [ "-c", "-g", "-emit-llvm" ]
               ++ concat [ ["-I",i] | i <- incs ]
               ++ [ src, "-o", tgt ]

     putStrLn $ "[Clang] " ++ src ++ " -> " ++ tgt

     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return tgt
       ExitFailure n -> throwError (ClangError n sout serr)




