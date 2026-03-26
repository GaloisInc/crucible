{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.CLI.Options (main) where

import Lang.Crucible.Backend (IsSymBackend)
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)

import Lang.Crucible.Syntax.Concrete (ParserHooks)

import qualified Options.Applicative as Opt
import           Options.Applicative ( (<**>) )

import qualified Lang.Crucible.CLI as CLI

import What4.Expr (ExprBuilder)

file :: String -> Opt.Parser FilePath
file which = Opt.strArgument (Opt.metavar "FILE" <> Opt.help ("The " <> which <> " file"))

input :: Opt.Parser FilePath
input = file "input"

output :: Opt.Parser FilePath
output = file "output"

command :: String -> Opt.Parser CLI.Command
command name =
  Opt.subparser $
       (Opt.command "check"
        (Opt.info (CLI.CheckCommand <$> parseCheck)
         (Opt.fullDesc <> Opt.progDesc "Check a file" <> Opt.header name)))
    <> (Opt.command "simulate"
        (Opt.info (CLI.SimulateCommand <$> simFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file" <> Opt.header name)))
    <> (Opt.command "profile"
        (Opt.info (CLI.ProfileCommand <$> profFile)
         (Opt.fullDesc <> Opt.progDesc "Simulate a file, with profiling" <> Opt.header name)))
    <> (Opt.command "repl"
        (Opt.info (pure CLI.ReplCommand) (Opt.fullDesc <> Opt.progDesc "Open a REPL")))

profFile :: Opt.Parser CLI.ProfCmd
profFile =
  CLI.ProfCmd <$> input <*> output

simFile :: Opt.Parser CLI.SimCmd
simFile =
  CLI.SimCmd
  <$> input
  <*> Opt.optional output
  <*> Opt.switch
        (mconcat
          [ Opt.long "debug"
          , Opt.help "Run the Crucible debugger"
          ])
  <*> Opt.many
        (Opt.strOption
          (mconcat
            [ Opt.long "debug-cmd"
            , Opt.metavar "CMD"
            , Opt.help "Command to pass to the Crucible debugger"
            ]
          ))

parseCheck :: Opt.Parser CLI.CheckCmd
parseCheck =
  CLI.CheckCmd <$> input <*> Opt.optional output <*> Opt.switch (Opt.help "Pretty-print the source file")

main ::
  (?parserHooks :: ParserHooks ext, IsSyntaxExtension ext) =>
  String ->
  (forall p sym bak t st fs. (IsSymBackend sym bak, sym ~ ExprBuilder t st fs) => bak -> IO (CLI.ExtensionSetup p sym ext)) ->
  CLI.SimulateProgramHooks ext ->
  IO ()
main name ext simulationHooks =
  do cmd <- Opt.customExecParser prefs info
     CLI.execCommand ext simulationHooks cmd
  where info = Opt.info (command name <**> Opt.helper) (Opt.fullDesc)
        prefs = Opt.prefs $ Opt.showHelpOnError <> Opt.showHelpOnEmpty
