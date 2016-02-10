{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module Main where

import Control.Exception
import Data.List

import System.Exit
import System.IO
import System.Console.GetOpt
import System.Environment

import SAWScript.Options
import SAWScript.Interpreter (processFile)
import qualified SAWScript.REPL as REPL
import SAWScript.Version (shortVersionText)

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      {- We have two modes of operation: batch processing, handled in
      'SAWScript.ProcessFile', and a REPL, defined in 'SAWScript.REPL'. -}
      case files of
        _ | showVersion opts'' -> hPutStrLn stderr shortVersionText
        _ | showHelp opts'' -> err (usageInfo header options)
        [] -> REPL.run opts''
        _ | runInteractively opts'' -> REPL.run opts''
        [file] -> processFile opts'' file `catch`
                  (\(ErrorCall msg) -> err msg)
        (_:_) -> err "Multiple files not yet supported."
    (_, _, errs) -> err (concat errs ++ usageInfo header options)
  where header = "Usage: saw [OPTION...] [-I | file]"
        err msg = hPutStrLn stderr msg >> exitFailure
