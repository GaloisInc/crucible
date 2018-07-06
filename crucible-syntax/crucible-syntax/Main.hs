{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.Except
import Control.Monad.ST
import System.IO
import Data.Monoid
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.CFG.SSAConversion

import qualified Options.Applicative as Opt

import System.Exit

import Text.Megaparsec as MP


newtype TheFile = TheFile FilePath
  deriving (Eq, Show, Ord)


input :: Opt.Parser (Maybe TheFile)
input = Opt.optional $ TheFile <$> Opt.strArgument (Opt.metavar "FILE" <> Opt.help "The file to process")

repl :: TheFile -> IO ()
repl fn =
  do putStr "> "
     T.getLine >>= go fn
     repl fn

go :: TheFile -> Text -> IO ()
go (TheFile fn) theInput =
  case MP.parse (many (sexp atom) <* eof) fn theInput of
    Left err ->
      do putStrLn $ parseErrorPretty' theInput err
         exitFailure
    Right v ->
      do forM_ v $ T.putStrLn . printExpr
         cfgs <- mapM (stToIO . top . cfg) v
         forM_ cfgs $
           \case
             Left err -> print err
             Right (ACFG _ _ theCfg) -> print (toSSA theCfg)


main :: IO ()
main =
  do file <- Opt.execParser options
     case file of
       Nothing -> hSetBuffering stdout NoBuffering >> repl (TheFile "stdin")
       Just f@(TheFile input) ->
         do contents <- T.readFile input
            go f contents

  where options = Opt.info input (Opt.fullDesc)
