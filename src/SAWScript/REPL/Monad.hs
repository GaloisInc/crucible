-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveDataTypeable #-}

module SAWScript.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPL
  , io
  , raise
  , stop
  , catch

    -- ** Errors
  , REPLException(..)
  ,rethrowEvalError

    -- ** Environment
  , getModuleEnv, setModuleEnv
  , getTSyns, getNewtypes, getVars
  , whenDebug
  , getExprNames
  , getTypeNames
  , getPropertyNames
  , LoadedModule(..), getLoadedMod, setLoadedMod
  , builtIns
  , getPrompt
  , shouldContinue
  , unlessBatch
  , setREPLTitle

    -- ** Config Options
  , EnvVal(..)
  , OptionDescr(..)
  , setUser, getUser, tryGetUser
  , userOptions

    -- ** SAWScript stuff
  , REPLState, withInitialState
  , getModulesInScope, getNamesInScope, getSharedContext, getEnvironment
  , putNamesInScope, putEnvironment
  , modifyNamesInScope, modifyEnvironment
  , err

  ) where

import SAWScript.REPL.Trie

import Cryptol.Prims.Types(typeOf)
import Cryptol.Prims.Syntax(ECon(..),ppPrefix)
import Cryptol.Eval (EvalError)
import qualified Cryptol.ModuleSystem as M
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import qualified Cryptol.Parser.AST as P

import Control.Monad (unless,when)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef, writeIORef)
import Data.List (isPrefixOf)
import Data.Typeable (Typeable)
import System.Console.ANSI (setTitle)
import qualified Control.Exception as X
import qualified Data.Map as Map

--------------------
{-
import Prelude hiding (maybe)

import Control.Applicative (Applicative)
import Control.Monad.Trans (lift, MonadIO, liftIO)
import Control.Monad.State (StateT, runStateT, gets, modify)
import Control.Monad.Trans.Maybe (MaybeT, runMaybeT)
-}
import Data.Foldable (foldrM)
import Data.Map (Map)
{-
import qualified Data.Map as Map
-}
import Data.Set (Set)
import qualified Data.Set as Set
{-
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline
-}

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

-- FIXME! Get rid of all the continuation-passing nonsense below and
-- use ordinary monadic types. We will need to change runCompiler first.
getInitialState :: Options -> IO REPLState
getInitialState opts = do
  ref <- newIORef undefined
  withInitialState opts (writeIORef ref)
  readIORef ref

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
      f $ REPLState modulesInScope namesInScope sharedContext environment

-- Monadic primitives --

{-
successExit :: REP a
successExit = maybe $ fail "Exiting" -- message should be ignored

failure :: String -> REP a
failure msg = REP $ lift $ lift $ fail msg
-}

getREPLState :: REPL REPLState
getREPLState = fmap eREPLState getRW

modifyREPLState :: (REPLState -> REPLState) -> REPL ()
modifyREPLState f = modifyRW_ $ \rw -> rw { eREPLState = f (eREPLState rw) }

getModulesInScope :: REPL (Map ModuleName ValidModule)
getModulesInScope = fmap modulesInScope getREPLState

getNamesInScope :: REPL (Set Name)
getNamesInScope = fmap namesInScope getREPLState

getSharedContext :: REPL (SharedContext SAWCtx)
getSharedContext = fmap sharedContext getREPLState

getEnvironment :: REPL (InterpretEnv SAWCtx)
getEnvironment = fmap environment getREPLState

putNamesInScope :: Set Name -> REPL ()
putNamesInScope = modifyNamesInScope . const

putEnvironment :: InterpretEnv SAWCtx -> REPL ()
putEnvironment = modifyEnvironment . const

modifyNamesInScope :: (Set Name -> Set Name) -> REPL ()
modifyNamesInScope f = modifyREPLState $ \current ->
  current { namesInScope = f (namesInScope current) }

modifyEnvironment :: (InterpretEnv SAWCtx -> InterpretEnv SAWCtx) -> REPL ()
modifyEnvironment f = modifyREPLState $ \current ->
  current { environment = f (environment current) }

-- Lifting computations --

err :: ErrT IO a -> REPL a
err m = io $ runErrT' m >>= either fail return

-- REPL Environment ------------------------------------------------------------

data LoadedModule = LoadedModule
  { lName :: Maybe P.ModName -- ^ Focused module
  , lPath :: FilePath        -- ^ Focused file
  }

-- REPL RW Environment.
data RW = RW
  { eLoadedMod  :: Maybe LoadedModule
  , eContinue   :: Bool
  , eIsBatch    :: Bool
  , eModuleEnv  :: M.ModuleEnv
  , eUserEnv    :: UserEnv
  , eREPLState  :: REPLState -- ^ SAWScript-specific stuff
  }

-- | Initial, empty environment.
defaultRW :: Bool -> IO RW
defaultRW isBatch = do
  env <- M.initialModuleEnv
  return RW
    { eLoadedMod  = Nothing
    , eContinue   = True
    , eIsBatch    = isBatch
    , eModuleEnv  = env
    , eUserEnv    = mkUserEnv userOptions
    , eREPLState  = error "FIXME: eREPLState"
    }

-- | Build up the prompt for the REPL.
mkPrompt :: RW -> String
mkPrompt rw
  | eIsBatch rw = ""
  | otherwise   = maybe "cryptol" pretty (lName =<< eLoadedMod rw) ++ "> "

mkTitle :: RW -> String
mkTitle rw = maybe "" (\ m -> pretty m ++ " - ") (lName =<< eLoadedMod rw)
          ++ "cryptol"


-- REPL Monad ------------------------------------------------------------------

-- | REPL_ context with InputT handling.
newtype REPL a = REPL { unREPL :: IORef RW -> IO a }

-- | Run a REPL action with a fresh environment.
runREPL :: Bool -> REPL a -> IO a
runREPL isBatch m = do
  ref <- newIORef =<< defaultRW isBatch
  unREPL m ref

instance Functor REPL where
  {-# INLINE fmap #-}
  fmap f m = REPL (\ ref -> fmap f (unREPL m ref))

instance Monad REPL where
  {-# INLINE return #-}
  return x = REPL (\_ -> return x)

  {-# INLINE (>>=) #-}
  m >>= f = REPL $ \ref -> do
    x <- unREPL m ref
    unREPL (f x) ref


-- Exceptions ------------------------------------------------------------------

-- | REPL exceptions.
data REPLException
  = ParseError ParseError
  | FileNotFound FilePath
  | DirectoryNotFound FilePath
  | NoPatError [Error]
  | NoIncludeError [IncludeError]
  | EvalError EvalError
  | ModuleSystemError M.ModuleError
  | EvalPolyError T.Schema
  | TypeNotTestable T.Type
    deriving (Show,Typeable)

instance X.Exception REPLException

instance PP REPLException where
  ppPrec _ re = case re of
    ParseError e         -> ppError e
    FileNotFound path    -> sep [ text "File"
                                , text ("`" ++ path ++ "'")
                                , text"not found"
                                ]
    DirectoryNotFound path -> sep [ text "Directory"
                                  , text ("`" ++ path ++ "'")
                                  , text"not found or not a directory"
                                  ]
    NoPatError es        -> vcat (map pp es)
    NoIncludeError es    -> vcat (map ppIncludeError es)
    ModuleSystemError me -> pp me
    EvalError e          -> pp e
    EvalPolyError s      -> text "Cannot evaluate polymorphic value."
                         $$ text "Type:" <+> pp s
    TypeNotTestable t    -> text "The expression is not of a testable type."
                         $$ text "Type:" <+> pp t

-- | Raise an exception.
raise :: REPLException -> REPL a
raise exn = io (X.throwIO exn)


catch :: REPL a -> (REPLException -> REPL a) -> REPL a
catch m k = REPL (\ ref -> unREPL m ref `X.catch` \ e -> unREPL (k e) ref)

rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalError -> IO a
  rethrow exn = X.throwIO (EvalError exn)




-- Primitives ------------------------------------------------------------------

io :: IO a -> REPL a
io m = REPL (\ _ -> m)

getRW :: REPL RW
getRW  = REPL readIORef

modifyRW_ :: (RW -> RW) -> REPL ()
modifyRW_ f = REPL (\ ref -> modifyIORef ref f)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt  = mkPrompt `fmap` getRW

-- | Set the name of the currently focused file, edited by @:e@ and loaded via
-- @:r@.
setLoadedMod :: LoadedModule -> REPL ()
setLoadedMod n = do
  modifyRW_ (\ rw -> rw { eLoadedMod = Just n })
  setREPLTitle

getLoadedMod :: REPL (Maybe LoadedModule)
getLoadedMod  = eLoadedMod `fmap` getRW

shouldContinue :: REPL Bool
shouldContinue  = eContinue `fmap` getRW

stop :: REPL ()
stop  = modifyRW_ (\ rw -> rw { eContinue = False })

unlessBatch :: REPL () -> REPL ()
unlessBatch body = do
  rw <- getRW
  unless (eIsBatch rw) body

setREPLTitle :: REPL ()
setREPLTitle  = unlessBatch $ do
  rw <- getRW
  io (setTitle (mkTitle rw))

builtIns :: [(String,(ECon,T.Schema))]
builtIns = map mk [ minBound .. maxBound :: ECon ]
  where mk x = (show (ppPrefix x), (x, typeOf x))

-- | Only meant for use with one of getVars or getTSyns.
keepOne :: String -> [a] -> a
keepOne src as = case as of
  [a] -> a
  _   -> panic ("REPL: " ++ src) ["name clash in interface file"]

getVars :: REPL (Map.Map P.QName M.IfaceDecl)
getVars  = do
  me <- getModuleEnv
  let decls = M.focusedEnv me
  return (keepOne "getVars" `fmap` M.ifDecls decls)

getTSyns :: REPL (Map.Map P.QName T.TySyn)
getTSyns  = do
  me <- getModuleEnv
  let decls = M.focusedEnv me
  return (keepOne "getTSyns" `fmap` M.ifTySyns decls)

getNewtypes :: REPL (Map.Map P.QName T.Newtype)
getNewtypes = do
  me <- getModuleEnv
  let decls = M.focusedEnv me
  return (keepOne "getNewtypes" `fmap` M.ifNewtypes decls)

-- | Get visible variable names.
getExprNames :: REPL [String]
getExprNames  = do as <- (map getName . Map.keys) `fmap` getVars
                   return (map fst builtIns ++ as)

-- | Get visible type signature names.
getTypeNames :: REPL [String]
getTypeNames  =
  do tss <- getTSyns
     nts <- getNewtypes
     return $ map getName $ Map.keys tss ++ Map.keys nts

getPropertyNames :: REPL [String]
getPropertyNames =
  do xs <- getVars
     return [ getName x | (x,d) <- Map.toList xs,
                T.PragmaProperty `elem` M.ifDeclPragmas d ]

getName :: P.QName -> String
getName  = show . pp

getModuleEnv :: REPL M.ModuleEnv
getModuleEnv  = eModuleEnv `fmap` getRW

setModuleEnv :: M.ModuleEnv -> REPL ()
setModuleEnv me = modifyRW_ (\rw -> rw { eModuleEnv = me })


-- User Environment Interaction ------------------------------------------------

-- | User modifiable environment, for things like numeric base.
type UserEnv = Map.Map String EnvVal

data EnvVal
  = EnvString String
  | EnvNum    !Int
  | EnvBool   Bool
    deriving (Show)

-- | Generate a UserEnv from a description of the options map.
mkUserEnv :: OptionMap -> UserEnv
mkUserEnv opts = Map.fromList $ do
  opt <- leaves opts
  return (optName opt, optDefault opt)

-- | Set a user option.
setUser :: String -> String -> REPL ()
setUser name val = case lookupTrie name userOptions of

  [opt] -> setUserOpt opt
  []    -> io (putStrLn ("Unknown env value `" ++ name ++ "`"))
  _     -> io (putStrLn ("Ambiguous env value `" ++ name ++ "`"))

  where
  setUserOpt opt = case optDefault opt of
    EnvString _
      | Just err <- optCheck opt (EnvString val)
        -> io (putStrLn err)
      | otherwise
        -> writeEnv (EnvString val)

    EnvNum _ -> case reads val of
      [(x,_)]
        | Just err <- optCheck opt (EnvNum x)
          -> io (putStrLn err)
        | otherwise
          -> writeEnv (EnvNum x)

      _       -> io (putStrLn ("Failed to parse number for field, `" ++ name ++ "`"))

    EnvBool _
      | any (`isPrefixOf` val) ["enable","on","yes"] ->
        writeEnv (EnvBool True)
      | any (`isPrefixOf` val) ["disable","off","no"] ->
        writeEnv (EnvBool False)
      | otherwise ->
        io (putStrLn ("Failed to parse boolean for field, `" ++ name ++ "`"))

  writeEnv ev =
    modifyRW_ (\rw -> rw { eUserEnv = Map.insert name ev (eUserEnv rw) })

-- | Get a user option, using Maybe for failure.
tryGetUser :: String -> REPL (Maybe EnvVal)
tryGetUser name = do
  rw <- getRW
  return (Map.lookup name (eUserEnv rw))

-- | Get a user option, when it's known to exist.  Fail with panic when it
-- doesn't.
getUser :: String -> REPL EnvVal
getUser name = do
  mb <- tryGetUser name
  case mb of
    Just ev -> return ev
    Nothing -> panic "[REPL] getUser" ["option `" ++ name ++ "` does not exist"]

-- Environment Options ---------------------------------------------------------

type OptionMap = Trie OptionDescr

mkOptionMap :: [OptionDescr] -> OptionMap
mkOptionMap  = foldl insert emptyTrie
  where
  insert m d = insertTrie (optName d) d m

data OptionDescr = OptionDescr
  { optName    :: String
  , optDefault :: EnvVal
  , optCheck   :: EnvVal -> Maybe String
  , optHelp    :: String
  }

userOptions :: OptionMap
userOptions  = mkOptionMap
  [ OptionDescr "base" (EnvNum 10) checkBase
    "the base to display words at"
  , OptionDescr "debug" (EnvBool False) (const Nothing)
    "enable debugging output"
  , OptionDescr "ascii" (EnvBool False) (const Nothing)
    "display 7- or 8-bit words using ASCII notation."
  , OptionDescr "infLength" (EnvNum 5) checkInfLength
    "The number of elements to display for infinite sequences."
  , OptionDescr "tests" (EnvNum 100) (const Nothing)
    "The number of random tests to try."
  , OptionDescr "prover" (EnvString "cvc4") checkProver
    "The external smt solver for :prove and :sat (cvc4, yices, or z3)."
  , OptionDescr "iteSolver" (EnvBool False) (const Nothing)
    "Use smt solver to filter conditional branches in proofs."
  , OptionDescr "warnDefaulting" (EnvBool True) (const Nothing)
    "Choose if we should display warnings when defaulting."
  ]

-- | Check the value to the `base` option.
checkBase :: EnvVal -> Maybe String
checkBase val = case val of
  EnvNum n
    | n >= 2 && n <= 36 -> Nothing
    | otherwise         -> Just "base must fall between 2 and 36"
  _                     -> Just "unable to parse a value for base"

checkInfLength :: EnvVal -> Maybe String
checkInfLength val = case val of
  EnvNum n
    | n >= 0    -> Nothing
    | otherwise -> Just "the number of elements should be positive"
  _ -> Just "unable to parse a value for infLength"

checkProver :: EnvVal -> Maybe String
checkProver val = case val of
  EnvString s
    | s `elem` ["cvc4", "yices", "z3"] -> Nothing
    | otherwise                        -> Just "prover must be cvc4, yices, or z3"
  _ -> Just "unable to parse a value for prover"

-- Environment Utilities -------------------------------------------------------

whenDebug :: REPL () -> REPL ()
whenDebug m = do
  EnvBool b <- getUser "debug"
  when b m
