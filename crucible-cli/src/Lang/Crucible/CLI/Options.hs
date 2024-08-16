{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.CLI.Options (main) where

import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.Simulator.ExecutionTree (ExtensionImpl)

import Lang.Crucible.Syntax.Concrete (ParserHooks)

import qualified Options.Applicative as Opt
import           Options.Applicative ( (<**>) )

import           Lang.Crucible.CLI

file :: String -> Opt.Parser FilePath
file which = Opt.strArgument (Opt.metavar "FILE" <> Opt.help ("The " <> which <> " file"))

input :: Opt.Parser FilePath
input = file "input"

output :: Opt.Parser FilePath
output = file "output"

command :: String -> Opt.Parser Command
command name =
  Opt.subparser $
       (Opt.command "check"
        (Opt.info (CheckCommand <$> parseCheck)
         (Opt.fullDesc <> Opt.progDesc "Check a file" <> Opt.header name)))
    <> (Opt.command "simulate"
        (Opt.info (SimulateCommand <$> simFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file" <> Opt.header name)))
    <> (Opt.command "profile"
        (Opt.info (ProfileCommand <$> profFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file, with profiling" <> Opt.header name)))
    <> (Opt.command "repl"
        (Opt.info (pure ReplCommand) (Opt.fullDesc <> Opt.progDesc "Open a REPL")))

profFile :: Opt.Parser ProfCmd
profFile =
  ProfCmd <$> input <*> output

simFile :: Opt.Parser SimCmd
simFile =
  SimCmd <$> input <*> Opt.optional output

parseCheck :: Opt.Parser CheckCmd
parseCheck =
  CheckCmd <$> input <*> Opt.optional output <*> Opt.switch (Opt.help "Pretty-print the source file")

main ::
  (?parserHooks :: ParserHooks ext, IsSyntaxExtension ext) =>
  String ->
  (forall sym. IsSymInterface sym => sym -> IO (ExtensionImpl () sym ext)) ->
  SimulateProgramHooks ext ->
  IO ()
main name ext simulationHooks =
  do cmd <- Opt.customExecParser prefs info
     execCommand ext simulationHooks cmd
  where info = Opt.info (command name <**> Opt.helper) (Opt.fullDesc)
        prefs = Opt.prefs $ Opt.showHelpOnError <> Opt.showHelpOnEmpty
