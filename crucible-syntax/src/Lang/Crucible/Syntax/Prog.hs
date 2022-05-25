{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Syntax.Prog
  ( doParseCheck
  , simulateProgram
  , SimulateProgramHooks(..)
  , defaultSimulateProgramHooks
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
            let ?parserHooks = defaultParserHooks
            cs <- top ng ha [] $ prog v
            case cs of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right (ParsedProgram{ parsedProgCFGs = ok
                                  , parsedProgForwardDecs = fds
                                  }) -> do
                assertNoForwardDecs fds
                forM_ ok $
                 \(ACFG _ _ theCfg) ->
                   do C.SomeCFG ssa <- return $ toSSA theCfg
                      hPutStrLn outh $ show $ cfgHandle theCfg
                      hPutStrLn outh $ show $ C.ppCFG' True (postdomInfo ssa) ssa

-- | Allows users to hook into the various stages of 'simulateProgram'.
data SimulateProgramHooks = SimulateProgramHooks
  { setupOverridesHook ::
      forall p sym ext t st fs. (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
         sym -> HandleAllocator -> IO [(FnBinding p sym ext,Position)]
    -- ^ Action to set up overrides before parsing a program.
  , resolveForwardDeclarationsHook ::
      forall p sym ext t st fs. (IsSymInterface sym, sym ~ (ExprBuilder t st fs)) =>
        Map FunctionName SomeHandle -> IO (FunctionBindings p sym ext)
    -- ^ Action to resolve forward declarations before simulating a program.
    --   If you do not intend to support forward declarations, this is an
    --   appropriate place to error if a program contains one or more forward
    --   declarations.
  }

-- | A sensible default set of hooks for 'simulateProgram' that:
--
-- * Sets up no additional overrides.
--
-- * Errors out if a program contains one or more forward declarations.
defaultSimulateProgramHooks :: SimulateProgramHooks
defaultSimulateProgramHooks = SimulateProgramHooks
  { setupOverridesHook = \_sym _ha -> pure []
  , resolveForwardDeclarationsHook = \fds ->
    do assertNoForwardDecs fds
       pure $ FnBindings emptyHandleMap
  }

assertNoForwardDecs :: Map FunctionName SomeHandle -> IO ()
assertNoForwardDecs fds =
  unless (Map.null fds) $
  do putStrLn "Forward declarations not currently supported"
     exitFailure

simulateProgram
   :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> Maybe Handle -- ^ A handle to receive profiling data output
   -> [ConfigDesc] -- ^ Options to install
   -> SimulateProgramHooks -- ^ Hooks into various parts of the function
   -> IO ()
simulateProgram fn theInput outh profh opts hooks =
  do Some ng <- newIONonceGenerator
     ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         withIONonceGenerator $ \nonceGen ->
         do sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState nonceGen
            bak <- newSimpleBackend sym
            extendConfig opts (getConfiguration sym)
            ovrs <- setupOverridesHook hooks @() @_ @() sym ha
            let hdls = [ (SomeHandle h, p) | (FnBinding h _,p) <- ovrs ]
            let ?parserHooks = defaultParserHooks
            parseResult <- top ng ha hdls $ prog v
            case parseResult of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right (ParsedProgram{ parsedProgCFGs = cs
                                  , parsedProgForwardDecs = fds
                                  }) -> do
                case find isMain cs of
                  Just (ACFG Ctx.Empty retType mn) ->
                    do fwdDecFnBindings <- resolveForwardDeclarationsHook hooks fds
                       let mainHdl = cfgHandle mn
                       let fns = foldl' (\(FnBindings m) (ACFG _ _ g) ->
                                          case toSSA g of
                                            C.SomeCFG ssa ->
                                              FnBindings $
                                                insertHandleMap
                                                  (cfgHandle g)
                                                  (UseCFG ssa (postdomInfo ssa))
                                                  m)
                                        fwdDecFnBindings cs
                       let simCtx = initSimContext bak emptyIntrinsicTypes ha outh fns emptyExtensionImpl ()
                       let simSt  = InitialState simCtx emptyGlobals defaultAbortHandler retType $
                                      runOverrideSim retType $
                                        do mapM_ (registerFnBinding . fst) ovrs
                                           regValue <$> callFnVal (HandleFnVal mainHdl) emptyRegMap

                       hPutStrLn outh "==== Begin Simulation ===="

                       case profh of
                         Nothing ->
                           void $ executeCrucible [] simSt
                         Just ph ->
                           do proftab <- newProfilingTable
                              pf <- profilingFeature proftab profilingEventFilter Nothing
                              void $ executeCrucible [genericToExecutionFeature pf] simSt
                              hPutStrLn ph =<< symProUIString "crucibler-prof" fn proftab

                       hPutStrLn outh "\n==== Finish Simulation ===="

                       getProofObligations bak >>= \case
                         Nothing -> hPutStrLn outh "==== No proof obligations ===="
                         Just gs ->
                           do hPutStrLn outh "==== Proof obligations ===="
                              forM_ (goalsToList gs) (\g ->
                                do hPrint outh =<< ppProofObligation sym g
                                   neggoal <- notPred sym (view labeledPred (proofGoal g))
                                   asms <- assumptionsPred sym (proofAssumptions g)
                                   let bs = [neggoal, asms]
                                   runZ3InOverride sym defaultLogData bs (\case
                                     Sat _   -> hPutStrLn outh "COUNTEREXAMPLE"
                                     Unsat _ -> hPutStrLn outh "PROVED"
                                     Unknown -> hPutStrLn outh "UNKNOWN"
                                     )
                                )

                  _ -> hPutStrLn outh "No suitable main function found"

  where
  isMain (ACFG _ _ g) = handleName (cfgHandle g) == fromString "main"
