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

data SimCmd = SimCmd { simInFile :: TheFile
                     , simOutFile :: Maybe TheFile
                     }

data Command = CheckCommand Check
             | SimulateCommand SimCmd
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
     doParseCheck fn l True stdout
     repl f



command :: Opt.Parser Command
command =
  Opt.subparser
    (Opt.command "check"
     (Opt.info (CheckCommand <$> parseCheck)
       (Opt.fullDesc <> Opt.progDesc "Check a file" <> Opt.header "crucibler")))
  <|>
  Opt.subparser
    (Opt.command "simulate"
     (Opt.info (SimulateCommand <$> simFile)
       (Opt.fullDesc <> Opt.progDesc "Simulate a file" <> Opt.header "crucibler")))
  <|>
  Opt.subparser
    (Opt.command "repl"
     (Opt.info (pure ReplCommand) (Opt.fullDesc <> Opt.progDesc "Open a REPL")))

simFile :: Opt.Parser SimCmd
simFile =
  SimCmd <$> input <*> Opt.optional output

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
                doParseCheck inputFile contents pp stdout
              Just (TheFile outputFile) ->
                withFile outputFile WriteMode (doParseCheck inputFile contents pp)

       SimulateCommand (SimCmd (TheFile inputFile) out) ->
         do contents <- T.readFile inputFile
            let setup _ _ = return []
            case out of
              Nothing ->
                simulateProgram inputFile contents stdout [] setup
              Just (TheFile outputFile) ->
                withFile outputFile WriteMode
                  (\outh -> simulateProgram inputFile contents outh [] setup)

  where options = Opt.info command (Opt.fullDesc)
