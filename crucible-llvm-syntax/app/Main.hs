{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Monad.IO.Class (liftIO)
import System.IO
import qualified Data.Text.IO as T

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.Simulator.OverrideSim (writeGlobal)
import Lang.Crucible.FunctionHandle (newHandleAllocator)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Prog
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.MemModel (defaultMemOptions, emptyMem, mkMemVar)

import Lang.Crucible.LLVM.Syntax (emptyParserHooks, llvmParserHooks)

import What4.Config
import What4.Solver.Z3 ( z3Options )

import qualified Options.Applicative as Opt
import           Options.Applicative ( (<**>) )

data Check = Check { _chkInFile :: TheFile
                   , _chkOutFile :: Maybe TheFile
                   , _chkPrettyPrint :: Bool
                   }

data SimCmd = SimCmd { _simInFile :: TheFile
                     , _simOutFile :: Maybe TheFile
                     }

data ProfCmd =
  ProfCmd { _profInFile :: TheFile
          , _profOutFile :: TheFile
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

repl :: (?parserHooks :: ParserHooks LLVM) => TheFile -> IO ()
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
     ha <- newHandleAllocator
     mvar <- mkMemVar "llvm_memory" ha
     let ?ptrWidth = knownNat @64
     let ?parserHooks = llvmParserHooks emptyParserHooks mvar
     let simulationHooks =
           defaultSimulateProgramHooks
             { setupHook = \_sym _ha -> do
                 mem <- liftIO (emptyMem LittleEndian)
                 writeGlobal mvar mem
             , setupOverridesHook = setupOverrides
             }
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
            let sim =
                  simulateProgramWithExtension
                    (\_ -> let ?recordLLVMAnnotation = \_ _ _ -> pure ()
                           in llvmExtensionImpl defaultMemOptions)
                    inputFile
                    contents
            case out of
              Nothing ->
                 sim stdout Nothing configOptions simulationHooks
              Just (TheFile outputFile) ->
                withFile outputFile WriteMode
                  (\outh -> sim outh Nothing configOptions simulationHooks)

       ProfileCommand (ProfCmd (TheFile inputFile) (TheFile outputFile)) ->
         do contents <- T.readFile inputFile
            withFile outputFile WriteMode
               (\outh -> simulateProgram inputFile contents stdout (Just outh) configOptions simulationHooks)

  where info = Opt.info (command <**> Opt.helper) (Opt.fullDesc)
        prefs = Opt.prefs $ Opt.showHelpOnError <> Opt.showHelpOnEmpty
