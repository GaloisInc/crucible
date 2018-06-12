module Main where

import System.IO
import Data.Monoid
import Data.SCargot
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.Concrete

import qualified Options.Applicative as Opt

newtype TheFile = TheFile FilePath
  deriving (Eq, Show, Ord)


input :: Opt.Parser (Maybe TheFile)
input = Opt.optional $ TheFile <$> Opt.strArgument (Opt.metavar "FILE" <> Opt.help "The file to process")

repl :: IO ()
repl =
  do hSetBuffering stdout NoBuffering
     putStr "> "
     l <- T.getLine
     case decode parseExpr l of
       Left err ->
         do putStrLn err; repl
       Right v ->
         do print v; repl

main :: IO ()
main =
  do file <- Opt.execParser options
     case file of
       Nothing -> repl
       Just (TheFile input) ->
         do contents <- T.readFile input
            case decode parseExpr contents of
              Left err -> print err
              Right sexprs ->
                print sexprs

  where options = Opt.info input (Opt.fullDesc)
