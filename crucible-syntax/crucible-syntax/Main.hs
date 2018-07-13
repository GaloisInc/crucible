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


newtype TheFile = TheFile FilePath
  deriving (Eq, Show, Ord)


input :: Opt.Parser (Maybe TheFile)
input = Opt.optional $ TheFile <$> Opt.strArgument (Opt.metavar "FILE" <> Opt.help "The file to process")

repl :: HandleAllocator RealWorld -> TheFile -> IO ()
repl ha fn =
  do putStr "> "
     T.getLine >>= runSimulator ha fn
     repl ha fn

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
  do ha <- newHandleAllocator
     file <- Opt.execParser options
     case file of
       Nothing -> hSetBuffering stdout NoBuffering >> repl ha (TheFile "stdin")
       Just f@(TheFile inp) ->
         do contents <- T.readFile inp
            runSimulator ha f contents

  where options = Opt.info input (Opt.fullDesc)
