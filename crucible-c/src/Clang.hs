module Clang where

import System.Environment
import System.Process
import System.Exit

import Error

getClang :: IO FilePath
getClang = return "clang-4.0" -- XXX

genBitCode ::
  [FilePath] {- ^ Include paths -} ->
  FilePath   {- ^ Source file -} ->
  FilePath   {- ^ Output file -} ->
  IO ()
genBitCode incs src out =
  do clang <- getClang
     let params = [ "-c", "-g", "-emit-llvm" ]
               ++ concat [ ["-I",i] | i <- incs ]
               ++ [ src, "-o", show out ]
     putStrLn $ unwords params
     (res,sout,serr) <- readProcessWithExitCode clang params ""
     case res of
       ExitSuccess   -> return ()
       ExitFailure n -> throwError (ClangError n sout serr)




