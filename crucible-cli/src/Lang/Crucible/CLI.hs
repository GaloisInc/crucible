{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.CLI
  ( simulateProgramWithExtension
  , simulateProgram
  , SimulateProgramHooks(..)
  , defaultSimulateProgramHooks
  , repl
    -- * CLI helpers
  , CheckCmd(..)
  , SimCmd(..)
  , ProfCmd(..)
  , Command(..)
  , execCommand
  ) where

import Control.Monad

import Data.Foldable
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
import qualified Lang.Crucible.CFG.Reg as C.Reg
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Prog (doParseCheck, assertNoExterns, assertNoForwardDecs)
import Lang.Crucible.Syntax.SExpr

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.Backend
import qualified Lang.Crucible.Backend.Prove as Prove
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.Profiling

import What4.Config
import What4.Interface (getConfiguration)
import What4.Expr (ExprBuilder, newExprBuilder, EmptyExprBuilderState(..))
import What4.FunctionName
import What4.ProgramLoc
import What4.Solver (defaultLogData)
import What4.Solver.Z3 (z3Adapter, z3Options)

-- | Allows users to hook into the various stages of 'simulateProgram'.
data SimulateProgramHooks ext = SimulateProgramHooks
  { setupHook ::
      forall p sym bak rtp a r t st fs. (IsSymBackend sym bak, sym ~ ExprBuilder t st fs) =>
        bak ->
        HandleAllocator ->
        OverrideSim p sym ext rtp a r ()
    -- ^ Override action to execute before simulation. Used by the LLVM
    -- frontend to set up the LLVM global memory variable.
  , setupOverridesHook ::
      forall p sym t st fs. (IsSymInterface sym, sym ~ ExprBuilder t st fs) =>
         sym -> HandleAllocator -> IO [(FnBinding p sym ext,Position)]
    -- ^ Action to set up overrides before parsing a program.
  , resolveExternsHook ::
      forall sym t st fs. (IsSymInterface sym, sym ~ ExprBuilder t st fs) =>
        sym -> Map GlobalName (Some GlobalVar) -> SymGlobalState sym -> IO (SymGlobalState sym)
    -- ^ Action to resolve externs before simulating a program. If you do not
    --   intend to support externs, this is an appropriate place to error if a
    --   program contains one or more externs.
  , resolveForwardDeclarationsHook ::
      forall p sym t st fs. (IsSymInterface sym, sym ~ ExprBuilder t st fs) =>
        Map FunctionName SomeHandle -> IO (FunctionBindings p sym ext)
    -- ^ Action to resolve forward declarations before simulating a program.
    --   If you do not intend to support forward declarations, this is an
    --   appropriate place to error if a program contains one or more forward
    --   declarations.
  }

-- | A sensible default set of hooks for 'simulateProgram' that:
--
-- * Does nothing before simulation begins (has a no-op 'setupHook').
--
-- * Sets up no additional overrides.
--
-- * Errors out if a program contains one or more forward declarations.
defaultSimulateProgramHooks :: SimulateProgramHooks ext
defaultSimulateProgramHooks = SimulateProgramHooks
  { setupHook = \_sym _ha -> pure ()
  , setupOverridesHook = \_sym _ha -> pure []
  , resolveExternsHook = \_sym externs gst ->
    do assertNoExterns externs
       pure gst
  , resolveForwardDeclarationsHook = \fds ->
    do assertNoForwardDecs fds
       pure $ FnBindings emptyHandleMap
  }

simulateProgramWithExtension
   :: (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext)
   => (forall sym. IsSymInterface sym => sym -> ExtensionImpl () sym ext)
   -> FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> Maybe Handle -- ^ A handle to receive profiling data output
   -> [ConfigDesc] -- ^ Options to install
   -> SimulateProgramHooks ext -- ^ Hooks into various parts of the function
   -> IO ()
simulateProgramWithExtension mkExt fn theInput outh profh opts hooks =
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
            ovrs <- setupOverridesHook hooks @() sym ha
            let hdls = [ (SomeHandle h, p) | (FnBinding h _,p) <- ovrs ]
            parseResult <- top ng ha hdls $ prog v
            case parseResult of
              Left (SyntaxParseError e) -> T.hPutStrLn outh $ printSyntaxError e
              Left err -> hPutStrLn outh $ show err
              Right (ParsedProgram{ parsedProgCFGs = cs
                                  , parsedProgExterns = externs
                                  , parsedProgForwardDecs = fds
                                  }) -> do
                case find isMain cs of
                  Just (AnyCFG mn@(C.Reg.cfgArgTypes -> Ctx.Empty)) ->
                    do let retType = C.Reg.cfgReturnType mn
                       gst <- resolveExternsHook hooks sym externs emptyGlobals
                       fwdDecFnBindings <- resolveForwardDeclarationsHook hooks fds
                       let mainHdl = cfgHandle mn
                       let fns = foldl' (\(FnBindings m) (AnyCFG g) ->
                                          case toSSA g of
                                            C.SomeCFG ssa ->
                                              FnBindings $
                                                insertHandleMap
                                                  (cfgHandle g)
                                                  (UseCFG ssa (postdomInfo ssa))
                                                  m)
                                        fwdDecFnBindings cs
                       let ext = mkExt sym
                       let simCtx = initSimContext bak emptyIntrinsicTypes ha outh fns ext ()
                       let simSt  = InitialState simCtx gst defaultAbortHandler retType $
                                      runOverrideSim retType $
                                        do mapM_ (registerFnBinding . fst) ovrs
                                           setupHook hooks bak ha
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
                         Just {} -> hPutStrLn outh "==== Proof obligations ===="
                       let prover = Prove.offlineProver sym defaultLogData z3Adapter
                       let strat = Prove.ProofStrategy prover Prove.keepGoing
                       Prove.proveCurrentObligations bak strat $ Prove.ProofConsumer $ \goal res -> do
                         hPrint outh =<< ppProofObligation sym goal
                         case res of
                           Prove.Proved {} -> hPutStrLn outh "PROVED"
                           Prove.Disproved {} -> hPutStrLn outh "COUNTEREXAMPLE"
                           Prove.Unknown {} -> hPutStrLn outh "UNKNOWN"

                  _ -> hPutStrLn outh "No suitable main function found"

  where
  isMain (AnyCFG g) = handleName (cfgHandle g) == fromString "main"

simulateProgram
   :: FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> Maybe Handle -- ^ A handle to receive profiling data output
   -> [ConfigDesc] -- ^ Options to install
   -> SimulateProgramHooks () -- ^ Hooks into various parts of the function
   -> IO ()
simulateProgram fn theInput outh profh opts hooks = do
  let ?parserHooks = defaultParserHooks
  let ext = const emptyExtensionImpl
  simulateProgramWithExtension ext fn theInput outh profh opts hooks

repl :: 
  (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext) =>
  FilePath ->
  IO ()
repl f =
  do putStr "> "
     l <- T.getLine
     doParseCheck f l True stdout
     repl f

data CheckCmd
  = CheckCmd { chkInFile :: FilePath
             , chkOutFile :: Maybe FilePath
             , chkPrettyPrint :: Bool
             }

data SimCmd
  = SimCmd { _simInFile :: FilePath
           , _simOutFile :: Maybe FilePath
           }

data ProfCmd 
  = ProfCmd { _profInFile :: FilePath
            , _profOutFile :: FilePath
            }

-- | The 'Command' datatype represents the top-level functionalities of a
-- Crucible CLI frontend.
data Command
  = CheckCommand CheckCmd
  | SimulateCommand SimCmd
  | ProfileCommand ProfCmd
  | ReplCommand

-- | Main entry point for Crucible CLI frontends: the frontends provide
-- language-specific hooks and a 'Command' (usually parsed from the command
-- line), and this function takes care of the rest.
execCommand :: 
  (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext) =>
  (forall sym. IsSymInterface sym => sym -> ExtensionImpl () sym ext) ->
  SimulateProgramHooks ext ->
  Command ->
  IO ()
execCommand ext simulationHooks =
  \case
    ReplCommand -> hSetBuffering stdout NoBuffering >> repl "stdin"
   
    CheckCommand (CheckCmd inputFile out pp) ->
      do contents <- T.readFile inputFile
         case out of
           Nothing ->
             doParseCheck inputFile contents pp stdout
           Just outputFile ->
             withFile outputFile WriteMode (doParseCheck inputFile contents pp)
   
    SimulateCommand (SimCmd inputFile out) ->
      do contents <- T.readFile inputFile
         case out of
           Nothing -> sim inputFile contents  stdout Nothing configOptions simulationHooks
           Just outputFile ->
             withFile outputFile WriteMode
               (\outh -> sim inputFile contents outh Nothing configOptions simulationHooks)
   
    ProfileCommand (ProfCmd inputFile outputFile) ->
      do contents <- T.readFile inputFile
         withFile outputFile WriteMode
            (\outh -> sim inputFile contents stdout (Just outh) configOptions simulationHooks)
  where configOptions = z3Options
        sim = simulateProgramWithExtension ext
