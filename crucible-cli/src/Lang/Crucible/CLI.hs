{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

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

import qualified Control.Lens as Lens
import Control.Monad
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.String (IsString(..))
import Data.Void (Void)
import qualified Data.Text.IO as T
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP
import System.IO
import System.Exit
import Text.Megaparsec as MP

import Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Reg as C.Reg
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.CFG.Reg

import qualified Lang.Crucible.Debug as Debug

import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.ParsedProgram (parsedProgramFnBindings)
import Lang.Crucible.Syntax.Prog (doParseCheck, assertNoExterns, assertNoForwardDecs)
import Lang.Crucible.Syntax.SExpr

import Lang.Crucible.Backend
import qualified Lang.Crucible.Backend.Prove as Prove
import Lang.Crucible.Backend.Simple
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.Profiling
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.Seconds as Sec
import qualified Lang.Crucible.Utils.Timeout as CTO

import What4.Config
import What4.Interface (getConfiguration)
import What4.Expr (ExprBuilder, newExprBuilder, EmptyExprBuilderState(..))
import What4.FunctionName
import What4.ProgramLoc
import What4.Solver (defaultLogData)
import What4.Solver.Z3 (z3Adapter, z3Options)

-- | Personality (see
-- 'Lang.Crucible.Simulator.ExecutionTree.cruciblePersonality')
newtype Personality ext sym
  = Personality { getPersonality :: Debug.Context Void sym ext CT.UnitType }

instance Debug.HasContext (Personality ext sym) Void sym ext CT.UnitType where
  context = Lens.lens getPersonality (const Personality)
  {-# INLINE context #-}

-- | Allows users to hook into the various stages of 'simulateProgram'.
data SimulateProgramHooks ext = SimulateProgramHooks
  { setupHook ::
      forall p sym bak rtp a r t st fs. (IsSymBackend sym bak, sym ~ ExprBuilder t st fs) =>
        bak ->
        HandleAllocator ->
        Map FunctionName SomeHandle ->  -- forward declarations
        OverrideSim p sym ext rtp a r ()
    -- ^ Override action to execute before simulation.
    --
    -- Used to resolve forward declarations (i.e., register overrides for them)
    -- before simulating a program. If you do not intend to support forward
    -- declarations, this is an appropriate place to error if a program contains
    -- one or more forward declarations.
    --
    -- Used by the LLVM frontend to set up the LLVM global memory variable.
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
  { setupHook = \_sym _ha fds -> liftIO (assertNoForwardDecs fds)
  , setupOverridesHook = \_sym _ha -> pure []
  , resolveExternsHook = \_sym externs gst ->
    do assertNoExterns externs
       pure gst
  }

simulateProgramWithExtension
   :: forall ext.
      (IsSyntaxExtension ext, ?parserHooks :: ParserHooks ext)
   => (forall p sym bak t st fs. (IsSymBackend sym bak, sym ~ ExprBuilder t st fs) =>
        bak -> IO (ExtensionImpl p sym ext))
   -> FilePath -- ^ The name of the input (appears in source locations)
   -> Text     -- ^ The contents of the input
   -> Handle   -- ^ A handle that will receive the output
   -> Maybe Handle -- ^ A handle to receive profiling data output
   -> [ConfigDesc] -- ^ Options to install
   -> SimulateProgramHooks ext -- ^ Hooks into various parts of the function
   -> Bool -- ^ whether to start the debugger
   -> [Text] -- ^ extra debugger commands
   -> IO ()
simulateProgramWithExtension mkExt fn theInput outh profh opts hooks dbg dbgCmds =
  do Some ng <- newIONonceGenerator
     ha <- newHandleAllocator
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn theInput of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         withIONonceGenerator $ \nonceGen ->
         do (sym :: ExprBuilder t EmptyExprBuilderState (Flags FloatIEEE)) <- newExprBuilder FloatIEEERepr EmptyExprBuilderState nonceGen
            bak <- newSimpleBackend sym
            extendConfig opts (getConfiguration sym)

            let cExts = Debug.voidExts
            inps_ <- Debug.defaultDebuggerInputs cExts
            stmts <-
              forM dbgCmds $ \cmdTxt ->
                case Debug.parse cExts cmdTxt of
                  Left err -> do
                    putStrLn (Text.unpack (Debug.renderParseError err))
                    exitFailure
                  Right stmt -> pure stmt
            inps <- Debug.prepend stmts inps_
            dbgCtx_ <-
              Debug.initCtx
                cExts
                (Debug.IntrinsicPrinters MapF.empty)
                inps
                Debug.defaultDebuggerOutputs
                CT.UnitRepr
            let dbgCtx =
                  if dbg
                  then dbgCtx_
                  else dbgCtx_ { Debug.dbgState = Debug.Quit }
            let p = Personality @ext @(ExprBuilder t EmptyExprBuilderState (Flags FloatIEEE)) dbgCtx

            ovrs_ <- setupOverridesHook hooks @(Personality ext (ExprBuilder t EmptyExprBuilderState (Flags FloatIEEE))) sym ha
            dbgOv <-
              FnBinding
              <$> mkHandle ha "debug"
              <*> pure (UseOverride (runTypedOverride "debug" Debug.debugOverride))
            dbgRunOv <-
              FnBinding
              <$> mkHandle ha "debug-run"
              <*> pure (UseOverride (runTypedOverride "debug-run" (Debug.debugRunOverride cExts)))
            let ovrs = (dbgOv, InternalPos) : (dbgRunOv, InternalPos) : ovrs_
            let hdls = [ (SomeHandle h, o) | (FnBinding h _, o) <- ovrs ]

            parseResult <- top ng ha hdls $ prog v
            case parseResult of
              Left e ->
                T.hPutStrLn outh (PP.renderStrict (PP.layoutPretty PP.defaultLayoutOptions (PP.pretty e)))
              Right parsedProg -> do
                let ParsedProgram
                      { parsedProgCFGs = cs
                      , parsedProgExterns = externs
                      , parsedProgForwardDecs = fds
                      } = parsedProg
                case find isMain cs of
                  Just (AnyCFG mn)
                    | Ctx.Empty <- C.Reg.cfgArgTypes mn
                    , CT.UnitRepr <- C.Reg.cfgReturnType mn ->
                    do let retType = C.Reg.cfgReturnType mn
                       gst <- resolveExternsHook hooks sym externs emptyGlobals
                       let mainHdl = cfgHandle mn
                       ext <- mkExt bak

                       let fns = FnBindings emptyHandleMap
                       let simCtx = initSimContext bak emptyIntrinsicTypes ha outh fns ext p
                       let simSt  = InitialState simCtx gst defaultAbortHandler retType $
                                      runOverrideSim retType $
                                        do forM_ (parsedProgramFnBindings parsedProg) registerFnBinding
                                           mapM_ (registerFnBinding . fst) ovrs
                                           setupHook hooks bak ha fds
                                           regValue <$> callFnVal (HandleFnVal mainHdl) emptyRegMap

                       hPutStrLn outh "==== Begin Simulation ===="

                       case profh of
                         Nothing ->
                           void $ executeCrucible [Debug.debugger Debug.voidImpl] simSt
                         Just ph ->
                           do proftab <- newProfilingTable
                              pf <- profilingFeature proftab profilingEventFilter Nothing
                              void $ executeCrucible [genericToExecutionFeature pf] simSt
                              hPutStrLn ph =<< symProUIString "crucibler-prof" fn proftab

                       hPutStrLn outh "\n==== Finish Simulation ===="

                       getProofObligations bak >>= \case
                         Nothing -> hPutStrLn outh "==== No proof obligations ===="
                         Just {} -> hPutStrLn outh "==== Proof obligations ===="
                       -- TODO: Make this timeout configurable via the CLI
                       let timeout = CTO.Timeout (Sec.secondsFromInt 5)
                       let prover = Prove.offlineProver timeout sym defaultLogData z3Adapter
                       let strat = Prove.ProofStrategy prover Prove.keepGoing
                       let ppResult =
                             \case
                               Prove.Proved {} ->  "PROVED"
                               Prove.Disproved {} -> "COUNTEREXAMPLE"
                               Prove.Unknown {} -> "UNKNOWN"
                       let printer = Prove.ProofConsumer $ \goal res -> do
                             hPrint outh =<< ppProofObligation sym goal
                             hPutStrLn outh (ppResult res)
                       runExceptT (Prove.proveCurrentObligations bak strat printer) >>=
                         \case
                           Left CTO.TimedOut -> hPutStrLn outh "TIMEOUT"
                           Right () -> pure ()

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
   -> Bool -- ^ whether to start the debugger
   -> [Text] -- ^ extra debugger commands
   -> IO ()
simulateProgram fn theInput outh profh opts hooks dbg dbgCmds = do
  let ?parserHooks = defaultParserHooks
  let ext = const (pure emptyExtensionImpl)
  simulateProgramWithExtension ext fn theInput outh profh opts hooks dbg dbgCmds

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
           ,  _simDebug :: Bool
           , _simDebugCmd :: [Text]
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
  (forall p sym bak t st fs. (IsSymBackend sym bak, sym ~ ExprBuilder t st fs) =>
    bak -> IO (ExtensionImpl p sym ext)) ->
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
   
    SimulateCommand (SimCmd inputFile out dbg dbgCmds) ->
      do contents <- T.readFile inputFile
         case out of
           Nothing -> sim inputFile contents  stdout Nothing configOptions simulationHooks dbg dbgCmds
           Just outputFile ->
             withFile outputFile WriteMode
               (\outh -> sim inputFile contents outh Nothing configOptions simulationHooks dbg dbgCmds)
   
    ProfileCommand (ProfCmd inputFile outputFile) ->
      do contents <- T.readFile inputFile
         withFile outputFile WriteMode
            (\outh -> sim inputFile contents stdout (Just outh) configOptions simulationHooks False [])
  where configOptions = z3Options
        sim = simulateProgramWithExtension ext
