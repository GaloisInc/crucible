{-# LANGUAGE LambdaCase #-}
module Main where

--import Control.Monad.Except
--import Control.Monad.ST
import System.IO
import Data.Monoid
--import Data.Text (Text)
--import qualified Data.Text as T
import qualified Data.Text.IO as T

--import Lang.Crucible.Syntax.Concrete
--import Lang.Crucible.Syntax.SExpr
--import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.Syntax.Prog
--import Lang.Crucible.CFG.SSAConversion

import qualified Options.Applicative as Opt

--import System.Exit

import Text.Megaparsec as MP

data Check = Check { chkInFile :: TheFile
                   , chkOutFile :: Maybe TheFile
                   , chkPrettyPrint :: Bool
                   }

data Command = CheckCommand Check
             | ReplCommand

newtype TheFile = TheFile FilePath
  deriving (Eq, Show, Ord)


file :: String -> Opt.Parser TheFile
file which = TheFile <$> Opt.strArgument (Opt.metavar "FILE" <> Opt.help ("The " <> which <> " file"))

input :: Opt.Parser TheFile
input = file "input"

output :: Opt.Parser TheFile
output = file "output"


repl :: TheFile -> IO ()
repl f@(TheFile fn) =
  do putStr "> "
     l <- T.getLine
     go fn l True stdout
     repl f



command :: Opt.Parser Command
command =
  Opt.subparser
    (Opt.command "check"
     (Opt.info (CheckCommand <$> parseCheck)
       (Opt.fullDesc <> Opt.progDesc "Check a file" <> Opt.header "crucibler")))
  <|>
  Opt.subparser
    (Opt.command "repl"
     (Opt.info (pure ReplCommand) (Opt.fullDesc <> Opt.progDesc "Open a REPL")))

parseCheck :: Opt.Parser Check
parseCheck =
  Check <$> input <*> Opt.optional output <*> Opt.switch (Opt.help "Pretty-print the source file")

main :: IO ()
main =
  do cmd <- Opt.execParser options
     case cmd of
       ReplCommand -> hSetBuffering stdout NoBuffering >> repl (TheFile "stdin")
       CheckCommand (Check (TheFile inputFile) out pp) ->
         do contents <- T.readFile inputFile
            case out of
              Nothing ->
                go inputFile contents pp stdout
              Just (TheFile outputFile) ->
                withFile outputFile WriteMode (go inputFile contents pp)

  where options = Opt.info command (Opt.fullDesc)
