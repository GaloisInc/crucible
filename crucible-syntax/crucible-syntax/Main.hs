{-# LANGUAGE LambdaCase #-}
module Main where

import System.IO
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.Prog
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import What4.Config
import What4.Solver.Z3 ( z3Options )

import qualified Options.Applicative as Opt
import           Options.Applicative ( (<**>) )

data Check = Check { chkInFile :: TheFile
                   , chkOutFile :: Maybe TheFile
                   , chkPrettyPrint :: Bool
                   }

data SimCmd = SimCmd { simInFile :: TheFile
                     , simOutFile :: Maybe TheFile
                     }

data ProfCmd =
  ProfCmd { profInFile :: TheFile
          , profOutFile :: TheFile
          }

data Command = CheckCommand Check
             | SimulateCommand SimCmd
             | ProfileCommand ProfCmd
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
  Opt.subparser $
       (Opt.command "check"
        (Opt.info (CheckCommand <$> parseCheck)
         (Opt.fullDesc <> Opt.progDesc "Check a file" <> Opt.header "crucibler")))
    <> (Opt.command "simulate"
        (Opt.info (SimulateCommand <$> simFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file" <> Opt.header "crucibler")))
    <> (Opt.command "profile"
        (Opt.info (ProfileCommand <$> profFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file, with profiling" <> Opt.header "crucibler")))
    <> (Opt.command "repl"
        (Opt.info (pure ReplCommand) (Opt.fullDesc <> Opt.progDesc "Open a REPL")))

profFile :: Opt.Parser ProfCmd
profFile =
  ProfCmd <$> input <*> output

simFile :: Opt.Parser SimCmd
simFile =
  SimCmd <$> input <*> Opt.optional output

parseCheck :: Opt.Parser Check
parseCheck =
  Check <$> input <*> Opt.optional output <*> Opt.switch (Opt.help "Pretty-print the source file")

configOptions :: [ConfigDesc]
configOptions = z3Options


main :: IO ()
main =
  do cmd <- Opt.customExecParser prefs info
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
            case out of
              Nothing ->
                simulateProgram inputFile contents stdout Nothing configOptions simulationHooks
              Just (TheFile outputFile) ->
                withFile outputFile WriteMode
                  (\outh -> simulateProgram inputFile contents outh Nothing configOptions simulationHooks)

       ProfileCommand (ProfCmd (TheFile inputFile) (TheFile outputFile)) ->
         do contents <- T.readFile inputFile
            withFile outputFile WriteMode
               (\outh -> simulateProgram inputFile contents stdout (Just outh) configOptions simulationHooks)

  where info = Opt.info (command <**> Opt.helper) (Opt.fullDesc)
        prefs = Opt.prefs $ Opt.showHelpOnError <> Opt.showHelpOnEmpty

        simulationHooks =
          defaultSimulateProgramHooks
            { setupOverridesHook = setupOverrides
            }
