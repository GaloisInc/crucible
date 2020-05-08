{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Syntax.Prog where

import Control.Lens (view)
import Control.Monad

import Data.Foldable (toList)
import Data.List (find)
import Data.Text (Text)
import Data.String (IsString(..))
--import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
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
import Lang.Crucible.Backend.ProofGoals
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.Profiling

import What4.Config
import What4.Interface (getConfiguration,notPred)
import What4.Expr.Builder (ExprBuilder)
import What4.SatResult
import What4.Solver (defaultLogData, runZ3InOverride)


-- | The main loop body, useful for both the program and for testing.
doParseCheck
   :: FilePath -- ^ The name of the input (appears in source locations)
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
            cs <- top ng ha [] $ cfgs v
            case cs of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right ok ->
                forM_ ok $
                 \(ACFG _ _ theCfg) ->
                   do C.SomeCFG ssa <- return $ toSSA theCfg
                      hPutStrLn outh $ show $ cfgHandle theCfg
                      hPutStrLn outh $ show $ C.ppCFG' True (postdomInfo ssa) ssa

simulateProgram
   :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> Maybe Handle -- ^ A handle to receive profiling data output
   -> [ConfigDesc] -- ^ Options to install
   -> (forall p sym ext t st. (IsSymInterface sym, sym ~ (ExprBuilder t st)) =>
         sym -> HandleAllocator -> IO [(FnBinding p sym ext,Position)]) -- ^ action to set up overrides
   -> IO ()
simulateProgram fn theInput outh profh opts setup =
  do Some ng <- newIONonceGenerator
     ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         withIONonceGenerator $ \nonceGen ->
         do sym <- newSimpleBackend nonceGen FloatIEEERepr 
            extendConfig opts (getConfiguration sym)
            ovrs <- setup @() @_ @() sym ha
            let hdls = [ (SomeHandle h, p) | (FnBinding h _,p) <- ovrs ]
            parseResult <- top ng ha hdls $ cfgs v
            case parseResult of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right cs ->
                case find isMain cs of
                  Just (ACFG Ctx.Empty retType mn) ->
                    do let mainHdl = cfgHandle mn
                       let fnBindings = fnBindingsFromList
                             [ case toSSA g of
                                 C.SomeCFG ssa ->
                                   FnBinding (cfgHandle g) (UseCFG ssa (postdomInfo ssa))
                             | ACFG _ _ g <- cs
                             ]
                       let simCtx = initSimContext sym emptyIntrinsicTypes ha outh fnBindings emptyExtensionImpl ()
                       let simSt  = InitialState simCtx emptyGlobals defaultAbortHandler retType $
                                      runOverrideSim retType $
                                        do mapM_ (registerFnBinding . fst) ovrs
                                           regValue <$> callFnVal (HandleFnVal mainHdl) emptyRegMap

                       hPutStrLn outh "==== Begin Simulation ===="

                       case profh of
                         Nothing ->
                           void $ executeCrucible FloatIEEERepr [] simSt
                         Just ph ->
                           do proftab <- newProfilingTable
                              pf <- profilingFeature proftab Nothing
                              void $ executeCrucible FloatIEEERepr [genericToExecutionFeature pf] simSt
                              hPutStrLn ph =<< symProUIString "crucibler-prof" fn proftab

                       hPutStrLn outh "\n==== Finish Simulation ===="

                       getProofObligations sym >>= \case
                         Nothing -> hPutStrLn outh "==== No proof obligations ===="
                         Just gs ->
                           do hPutStrLn outh "==== Proof obligations ===="
                              forM_ (goalsToList gs) (\g ->
                                do hPrint outh (ppProofObligation sym g)
                                   neggoal <- notPred sym (view labeledPred (proofGoal g))
                                   let bs = neggoal : map (view labeledPred) (toList (proofAssumptions g))
                                   runZ3InOverride sym defaultLogData bs (\case
                                     Sat _   -> hPutStrLn outh "COUNTEREXAMPLE"
                                     Unsat _ -> hPutStrLn outh "PROVED"
                                     Unknown -> hPutStrLn outh "UNKNOWN"
                                     )
                                )

                  _ -> hPutStrLn outh "No suitable main function found"

  where
  isMain (ACFG _ _ g) = handleName (cfgHandle g) == fromString "main"
