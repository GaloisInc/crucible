{-# LANGUAGE ImplicitParams #-}
module Main (main) where

import qualified Data.Text.IO as T
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.IO (stderr, hPutStrLn)

import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Syntax.Concrete (defaultParserHooks, ParserHooks)
import Lang.Crucible.Syntax.Prog (doParseCheck)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      prog <- getProgName
      hPutStrLn stderr $ "Usage: " ++ prog ++ " FILE [FILE ...]"
      hPutStrLn stderr "Parse crucible-syntax files and exit 0 on success or 1 on failure"
      exitFailure
    files -> do
      let ?parserHooks = defaultParserHooks
      mapM_ parseFile files

parseFile :: (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext) => FilePath -> IO ()
parseFile path = do
  contents <- T.readFile path
  doParseCheck path contents False stderr
