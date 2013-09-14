{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL.Monad ( REPLState, withInitialState
                            , REP, runREP
                            , REPResult(..), successExit, failure
                            , getModulesInScope, getNamesInScope, getSharedContext, getEnvironment
                            , putNamesInScope, putEnvironment
                            , modifyNamesInScope, modifyEnvironment
                            , io, haskeline, err) where

import Prelude hiding (maybe)

import Control.Applicative (Applicative)
import Control.Monad.Trans (lift, MonadIO, liftIO)
import Control.Monad.State (StateT, runStateT, gets, modify)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
import Data.Foldable (foldrM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (ModuleName,
                      Name,
                      ValidModule)
import SAWScript.BuildModules (buildModules)
import SAWScript.Builtins (BuiltinContext(..))
import SAWScript.Compiler (ErrT, runErrT', mapErrT, runCompiler)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Interpreter (InterpretEnv, buildInterpretEnv)
import SAWScript.Options (Options)
import SAWScript.ProcessFile (checkModuleWithDeps)
import SAWScript.REPL.GenerateModule as Generate
import SAWScript.Utils (SAWCtx)
import Verifier.SAW (SharedContext)


--------------------------------- REPL state ----------------------------------

data REPLState = REPLState { modulesInScope :: Map ModuleName ValidModule
                           , namesInScope :: Set Name
                           , sharedContext :: SharedContext SAWCtx
                           , environment :: InterpretEnv SAWCtx
                           }

withInitialState :: Options -> (REPLState -> IO ()) -> IO ()
withInitialState opts f = do
  -- Build a prototype (empty) scratchpad module.
  preludeEtc <- preludeLoadedModules
  runCompiler buildModules preludeEtc $ \built ->
    runCompiler (foldrM checkModuleWithDeps Map.empty) built $ \modulesInScope -> do
      let namesInScope = Set.empty
      let scratchpadModule = Generate.scratchpad modulesInScope
      (biContext, environment) <- buildInterpretEnv opts scratchpadModule
      let sharedContext = biSharedContext biContext
      f $ REPLState { .. }


-------------------------------- REPL results ---------------------------------

data REPResult = Success REPLState
               | SuccessExit
               | Failure


-------------------------------- The REP monad --------------------------------

{-| The 'REP' ("read-eval-print") monad encapsulates one iteration of the
read-eval-print loop. -}
newtype REP a =
  REP { extractInner :: MaybeT (StateT (REPLState)
                                       (ErrT (InputT IO))) a }
  deriving (Functor, Applicative, Monad)

runREP :: forall a.
          Haskeline.Settings IO
          -> REPLState
          -> REP a
          -> IO REPResult
runREP haskelineSettings initialState computation = do
  unwrapped :: Either String (Maybe a, REPLState)
            <- runInputT haskelineSettings .
                 runErrT' .
                   flip runStateT initialState .
                     runMaybeT .
                       extractInner $ computation
  case unwrapped of
    Right (Just _, finalState) -> return $ Success finalState
    Right (Nothing, _) -> return SuccessExit
    Left msg -> do
      runInputT haskelineSettings $ Haskeline.outputStrLn msg
      return Failure


-- Monadic primitives --

successExit :: REP a
successExit = maybe $ fail "Exiting" -- message should be ignored

failure :: String -> REP a
failure msg = REP $ lift $ lift $ fail msg

getModulesInScope :: REP (Map ModuleName ValidModule)
getModulesInScope = state $ gets modulesInScope

getNamesInScope :: REP (Set Name)
getNamesInScope = state $ gets namesInScope

getSharedContext :: REP (SharedContext SAWCtx)
getSharedContext = state $ gets sharedContext

getEnvironment :: REP (InterpretEnv SAWCtx)
getEnvironment = state $ gets environment

putNamesInScope :: Set Name -> REP ()
putNamesInScope = modifyNamesInScope . const

putEnvironment :: InterpretEnv SAWCtx -> REP ()
putEnvironment = modifyEnvironment . const

modifyNamesInScope :: (Set Name -> Set Name) -> REP ()
modifyNamesInScope f = state $ modify $ \current ->
  current { namesInScope = f (namesInScope current) }

modifyEnvironment :: (InterpretEnv SAWCtx -> InterpretEnv SAWCtx) -> REP ()
modifyEnvironment f = state $ modify $ \current ->
  current { environment = f (environment current) }


-- Lifting computations --
{- 'REP' isn't a monad transformer, but inner monads can still be lifted to
it. -}

io :: IO a -> REP a
io = REP . lift . lift . lift . liftIO

haskeline :: InputT IO a -> REP a
haskeline = REP . lift . lift . lift

err :: ErrT IO a -> REP a
err = REP . lift . lift . mapErrT liftIO

state :: StateT REPLState (ErrT (InputT IO)) a -> REP a
state = REP . lift

maybe :: MaybeT (StateT REPLState (ErrT (InputT IO))) a -> REP a
maybe = REP
