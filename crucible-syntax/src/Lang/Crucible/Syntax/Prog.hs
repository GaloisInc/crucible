{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Syntax.Prog
  ( assertNoExterns
  , assertNoForwardDecs
  , doParseCheck
  ) where

import Control.Lens (view)
import Control.Monad

import Data.Foldable
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import Data.String (IsString(..))
import qualified Data.Text.IO as T
import System.IO
import System.Exit
import Text.Megaparsec as MP

import Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Atoms

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.Profiling

import What4.Config
import What4.Interface (getConfiguration,notPred)
import What4.Expr (ExprBuilder, newExprBuilder, EmptyExprBuilderState(..))
import What4.FunctionName
import What4.ProgramLoc
import What4.SatResult
import What4.Solver (defaultLogData, runZ3InOverride, z3Options)

assertNoExterns :: Map GlobalName (Some GlobalVar) -> IO ()
assertNoExterns externs =
  unless (Map.null externs) $
  do putStrLn "Externs not currently supported"
     exitFailure

assertNoForwardDecs :: Map FunctionName SomeHandle -> IO ()
assertNoForwardDecs fds =
  unless (Map.null fds) $
  do putStrLn "Forward declarations not currently supported"
     exitFailure

-- | The main loop body, useful for both the program and for testing.
doParseCheck
   :: (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext)
   => FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Bool     -- ^ Whether to pretty-print the input data as well
   -> Handle   -- ^ A handle that will receive the output
   -> IO ()
doParseCheck fn theInput pprint outh =
  do Some ng <- newIONonceGenerator
     ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         do when pprint $
              forM_ v $
                \e -> T.hPutStrLn outh (printExpr e) >> hPutStrLn outh ""
            cs <- top ng ha [] $ prog v
            case cs of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right (ParsedProgram{ parsedProgCFGs = ok
                                  , parsedProgExterns = externs
                                  , parsedProgForwardDecs = fds
                                  }) -> do
                assertNoExterns externs
                assertNoForwardDecs fds
                forM_ ok $
                 \(AnyCFG theCfg) ->
                   do C.SomeCFG ssa <- return $ toSSA theCfg
                      hPutStrLn outh $ show $ cfgHandle theCfg
                      hPutStrLn outh $ show $ C.ppCFG' True (postdomInfo ssa) ssa

