module Main where

import Control.Monad.Except
import Control.Monad.ST
import System.IO
import Data.Monoid
import Data.SCargot
import Data.Text (Text)
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
  do putStr "> "
     T.getLine >>= go
     repl

go :: Text -> IO ()
go theInput =
  case decode parseExpr theInput of
    Left err -> putStrLn err
    Right v ->
      do print v
         cfgs <- mapM (\x -> cfg x >>= _alksdj . runExceptT ) v
         mapM_ print cfgs


main :: IO ()
main =
  do file <- Opt.execParser options
     case file of
       Nothing -> hSetBuffering stdout NoBuffering >> repl
       Just (TheFile input) ->
         do contents <- T.readFile input
            go contents

  where options = Opt.info input (Opt.fullDesc)
