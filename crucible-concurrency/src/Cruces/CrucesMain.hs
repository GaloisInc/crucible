{- |
Module           : Cruces.CrucesMain
Description      : Driver for exploring concurrent crucible-syntax
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module Cruces.CrucesMain (run, defaultCrucesOptions, cruciblesConfig) where

import Control.Lens
import Data.Foldable (toList)
import Data.List (find)
import Data.Text (pack)
import Data.String (IsString(..))
import System.Exit
import Text.Megaparsec as MP

import Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Atoms

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import What4.Interface
import What4.ProgramLoc
import What4.FunctionName

import qualified Crux
import           Crux.Types

import Data.Parameterized.Pair
import qualified SimpleGetOpt as GetOpt
import Text.Read (readMaybe)


import Crucibles.Primitives
import Crucibles.DPOR (DPOR)
import Crucibles.ExploreTypes
import Cruces.ExploreCrux

data CrucesOptions = CrucesOptions
  { noDpor :: Bool
  , debug  :: Bool
  , pedantic :: Bool
  , maxPreemptions :: Int
  , target :: FilePath
  }

defaultCrucesOptions :: CrucesOptions
defaultCrucesOptions = CrucesOptions
  { noDpor = False
  , debug  = False
  , pedantic = False
  , maxPreemptions = 0
  , target = ""
  }

cruciblesConfig :: Crux.Config CrucesOptions
cruciblesConfig = Crux.Config
  { Crux.cfgFile =  pure defaultCrucesOptions
  , Crux.cfgEnv  = []
  , Crux.cfgCmdLineFlag =
      [ GetOpt.Option [] ["no-dpor"]
        "Enumerate all paths naively"
        (GetOpt.NoArg (\opts -> Right opts { noDpor = True }))
      , GetOpt.Option [] ["pedantic"]
        "Pedantic signal behavior (spurious wakeups)"
        (GetOpt.NoArg (\opts -> Right opts { pedantic = True }))
      , GetOpt.Option [] ["max-preemptions"]
        "Maximum number of preemptive context switches"
        (GetOpt.ReqArg "NUM" (\x opts ->
                                case readMaybe x of
                                  Just i  -> Right opts { maxPreemptions = i }
                                  Nothing -> Left "--max-preemptions requires an integer"))
      ]
  }

findMain :: FunctionName -> [ACFG ()] -> FnVal sym Ctx.EmptyCtx C.UnitType
findMain mainName cs =
  case find (isFn mainName) cs of
    Just (ACFG Ctx.Empty C.UnitRepr m) ->
      HandleFnVal (cfgHandle m)
    _ ->
      undefined
  where
    isFn x (ACFG _ _ g) = handleName (cfgHandle g) == x

run :: Crux.Logs Crux.CruxLogMessage
    => (Crux.CruxOptions, CrucesOptions)
    -> IO ()
run (cruxOpts, opts) =
  Crux.withCruxLogMessage $
  do let ?dpor = not (noDpor opts)
     let ?bound = maxPreemptions opts
     let [fn] = Crux.inputFiles cruxOpts
     ha      <- newHandleAllocator
     theInput <- readFile fn
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn (pack theInput) of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         withIONonceGenerator $ \nonceGen ->
         do let mkSym :: forall s.
                  (IsSymInterface s, IsExprBuilder s) =>
                  s ->
                  IO ( FnVal s Ctx.EmptyCtx C.UnitType
                     , ExplorePrimitives (ThreadExec DPOR s () C.UnitType) s ()
                     , [Pair C.TypeRepr GlobalVar]
                     , FunctionBindings (ThreadExec DPOR s () C.UnitType) s ()
                     )
                mkSym _sym =
                  do exploreBuiltins <- mkExplorePrims ha (pedantic opts) (Some nonceGen)
                     let builtins = [ (SomeHandle h, InternalPos) | FnBinding h _ <- exploreBuiltins ]
                     let ?parserHooks = defaultParserHooks
                     parseResult <- top nonceGen ha builtins $ prog v
                     case parseResult of
                       Left (SyntaxParseError e) -> error $ show $ printSyntaxError e
                       Left err -> error $ show err
                       Right (gs, cs) ->
                         return ( findMain (fromString "main") cs
                                , crucibleSyntaxPrims
                                , toList gs
                                , fnBindingsFromList $
                                          [ case toSSA g of
                                              C.SomeCFG ssa ->
                                                FnBinding (cfgHandle g) (UseCFG ssa (postdomInfo ssa))
                                          | ACFG _ _ g <- cs
                                          ] ++ exploreBuiltins
                                )
            res <- Crux.runSimulator cruxOpts { Crux.solver = "yices"
                                              , Crux.pathSatSolver = Just "yices" } $
                     exploreCallback cruxOpts ha (view Crux.outputHandle ?outputConfig) mkSym -- fns gvs mainHdl
            case res of
              CruxSimulationResult ProgramIncomplete _ ->
                putStrLn "INCOMPLETE"
              CruxSimulationResult _ (fmap snd -> gls) ->
                mapM_ printCounterexamples gls

            return ()

printCounterexamples ::
  Crux.Logs Crux.CruxLogMessage =>
  ProvedGoals -> IO ()
printCounterexamples = Crux.logGoal
