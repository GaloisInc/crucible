{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Exception as Ex
import Control.Lens ( (^.), to )
import Control.Monad.Except
import Control.Monad.ST
import System.IO
import System.Environment
import Data.Monoid
import Data.Text (Text)
--import qualified Data.Text as T
import qualified Data.Text.IO as T


import Data.Parameterized.Classes
import Data.Parameterized.Context
import Data.Parameterized.Nonce
import qualified Data.Parameterized.Map as MapF

import What4.Config
import What4.Interface

import qualified Lang.Crucible.Syntax.Concrete as Syntax
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.Atoms
-- import qualified Lang.Crucible.Syntax.Prog
import Lang.Crucible.CFG.SSAConversion
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
  ( FunctionBindings, FnState(..), initSimContext, ExtensionImpl(..), ExecResult(..)
  , partialValue, gpValue, emptyGlobals, executeCrucible, defaultAbortHandler
  , runOverrideSim, initSimState, callFnVal', regValue, FnVal(..)
  )


import qualified Options.Applicative as Opt

import System.Exit

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

go :: HandleAllocator RealWorld -> TheFile -> Text ->
   IO (FunctionBindings () (SimpleBackend s) (), Some (FnHandle EmptyCtx))
go halloc (TheFile fn) theInput =
  case MP.parse (many (sexp atom) <* eof) fn theInput of
    Left err ->
      do putStrLn $ parseErrorPretty' theInput err
         exitFailure
    Right v ->
      do forM_ v $ T.putStrLn . Syntax.printExpr
         res <- stToIO $ Syntax.top halloc $ Syntax.cfgs v
         case res of
           Left err ->
             do print err
                exitFailure
           Right cfgs ->
             do
             let f :: (FunctionBindings () (SimpleBackend n) (), Maybe (Some (FnHandle EmptyCtx))) ->
                      Syntax.ACFG ->
                      IO (FunctionBindings () (SimpleBackend n) (), Maybe (Some (FnHandle EmptyCtx)))
                 f (hdlMap, maybeMain) = \case
                    Syntax.ACFG _ _ cfg ->
                      do C.SomeCFG ssa <- return (toSSA cfg)
                         let h = C.cfgHandle ssa
                         print h
                         print ssa
                         let hdlMap' = insertHandleMap h (UseCFG ssa (postdomInfo ssa)) hdlMap
                         case maybeMain of
                           Nothing
                             | handleName h == "main"
                             , Just Refl <- testEquality (C.cfgArgTypes ssa) Empty
                             -> return (hdlMap', Just (C.Some h))
                           _ -> return (hdlMap', maybeMain)
    
             (hdlMap, maybeMain) <- foldM f (emptyHandleMap, Nothing) cfgs
             case maybeMain of
               Just hMain -> return (hdlMap, hMain)
               Nothing ->
                 do putStrLn "No 'main' function found"
                    exitFailure
   
runSimulator ::
  HandleAllocator RealWorld ->
  TheFile -> Text ->
  IO ()
runSimulator halloc fl inp =
  withIONonceGenerator $ \nonceGen ->
  do sym <- newSimpleBackend nonceGen
     (bindings, C.Some hMain) <- go halloc fl inp
     let cfg = getConfiguration sym
     vopt <- getOptionSetting verbosity cfg
     mapM_ print =<< setOpt vopt 3

     let ctx = initSimContext sym MapF.empty halloc stdout bindings
                  (ExtensionImpl (\_ _ _ _ -> \case) (\case)) ()
     let st0 = initSimState ctx emptyGlobals defaultAbortHandler

     let retTy = handleReturnType hMain

     res <- Ex.try (executeCrucible st0 $ runOverrideSim retTy $
                     callFnVal' (HandleFnVal hMain) Empty)
     case res of
       Left (ex :: SomeException) ->
         do putStrLn "Exeception escaped!"
            print ex
       Right (FinishedResult _ctx pr) ->
         do putStrLn "Finished!"
            case C.asBaseType retTy of
              C.AsBaseType _btp -> print (printSymExpr (pr^.partialValue.gpValue.to regValue))
              C.NotBaseType -> return ()

       Right (AbortedResult _ctx _ar) ->
         putStrLn "Aborted!"

main :: IO ()
main =
  do [f] <- getArgs
     contents <- T.readFile f
     ha <- newHandleAllocator
     runSimulator ha (TheFile f) contents

{-
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


repl :: TheFile -> IO ()
repl f@(TheFile fn) =
  do putStr "> "
     l <- T.getLine
     Prog.go fn l True stdout
     repl f

main :: IO ()
main =
  do cmd <- Opt.execParser options
     case cmd of
       ReplCommand -> hSetBuffering stdout NoBuffering >> repl (TheFile "stdin")
       CheckCommand (Check f@(TheFile input) out pp) ->
         do contents <- T.readFile input
            case out of
              Nothing ->
                go input contents pp stdout
              Just (TheFile output) ->
                withFile output WriteMode (go input contents pp)
  where options = Opt.info command (Opt.fullDesc)
-}
