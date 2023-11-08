{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Monad.IO.Class (liftIO)

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.Simulator.OverrideSim (writeGlobal)
import Lang.Crucible.FunctionHandle (newHandleAllocator)

import Lang.Crucible.Syntax.Prog
import Lang.Crucible.Syntax.Overrides (setupOverrides)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.MemModel (defaultMemOptions, emptyMem, mkMemVar)

import Lang.Crucible.LLVM.Syntax (emptyParserHooks, llvmParserHooks)

import qualified Options.Applicative as Opt
import           Options.Applicative ( (<**>) )

file :: String -> Opt.Parser FilePath
file which = Opt.strArgument (Opt.metavar "FILE" <> Opt.help ("The " <> which <> " file"))

input :: Opt.Parser FilePath
input = file "input"

output :: Opt.Parser FilePath
output = file "output"

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

parseCheck :: Opt.Parser CheckCmd
parseCheck =
  CheckCmd <$> input <*> Opt.optional output <*> Opt.switch (Opt.help "Pretty-print the source file")

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
     let ext _ = let ?recordLLVMAnnotation = \_ _ _ -> pure ()
                 in llvmExtensionImpl defaultMemOptions
     execCommand ext simulationHooks cmd
  where info = Opt.info (command <**> Opt.helper) (Opt.fullDesc)
        prefs = Opt.prefs $ Opt.showHelpOnError <> Opt.showHelpOnEmpty
