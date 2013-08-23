module Main where

import Data.List

import System.IO
import System.Console.GetOpt
import System.Environment

import SAWScript.Options
import SAWScript.ProcessFile (processFile)
import qualified SAWScript.REPL as REPL

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      {- We have two modes of operation: batch processing, handled in
      'SAWScript.ProcessFile', and a REPL, defined in 'SAWScript.REPL'. -}
      case (runInteractively opts'', files) of
        (True, []) -> REPL.run opts''
        (False, file:_) -> processFile opts'' file
        (True, _:_) ->
          hPutStrLn stderr ("Unable to handle files in interactive mode"
                            ++ usageInfo header options)
        (False, []) -> putStrLn (usageInfo header options)
    (_, _, errs)      ->
      hPutStrLn stderr (concat errs ++ usageInfo header options)
  where header = "Usage: saw [OPTION...] [-I | files...]"
