{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.REPL (run) where

import Prelude hiding (print, read)

import Control.Applicative ((<$>))
import Control.Monad.Trans (MonadIO)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified System.Console.Haskeline as Haskeline
import System.Directory (createDirectoryIfMissing)
import qualified System.Environment.XDG.BaseDir as XDG
import System.FilePath ((</>))

import SAWScript.AST (ModuleName, renderModuleName,
                      Module(..), ValidModule,
                      BlockStmt(Bind),
                      Name, LName, Located(..), UnresolvedName,
                      ResolvedName(..),
                      RawT, ResolvedT, Schema, rewindSchema,
                      topLevelContext)
import qualified SAWScript.AST as AST
import SAWScript.Interpreter (Value, isVUnit,
                              interpretModuleAtEntry,
                              interpretEnvValues, interpretEnvTypes)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
import SAWScript.Options (Options)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.REPL.GenerateModule (replFileName, replModuleName, wrapBStmt)
import SAWScript.REPL.Monad (REPLState, withInitialState,
                             REP, runREP,
                             REPResult(..),
                             getModulesInScope, getNamesInScope,
                               getSharedContext, getEnvironment,
                             putEnvironment,
                             modifyNamesInScope, modifyEnvironment)
import qualified SAWScript.REPL.Monad as REP
import SAWScript.ResolveSyns (resolveSyns)
import SAWScript.Utils (SAWCtx, Pos(..))

run :: Options -> IO ()
run opts = do
  settings <- replSettings
  withInitialState opts $ loop settings
  where loop :: Haskeline.Settings IO -> REPLState -> IO ()
        loop settings state = do
          result <- runREP settings state (read >>= evaluate >>= print)
          case result of
            Success state' -> loop settings state'
            SuccessExit -> return ()
            Failure -> loop settings state

replSettings :: MonadIO m => IO (Haskeline.Settings m)
replSettings = do
  dataHome <- XDG.getUserDataDir "sawscript"
  createDirectoryIfMissing True dataHome
  return $ Haskeline.setComplete Haskeline.noCompletion $
             Haskeline.defaultSettings
               { Haskeline.historyFile = Just (dataHome </> "repl_history") }


------------------------------------ Read -------------------------------------

read :: REP (BlockStmt UnresolvedName RawT)
read = do
  promptString <- buildPromptString
  line <- REP.haskeline $ Haskeline.getInputLine promptString
  case line of
    Nothing -> REP.successExit
    Just sawScriptStr -> do
      -- Lex and parse.
      tokens <- REP.err $ scan replFileName sawScriptStr
      REP.err $ parseBlockStmt tokens

buildPromptString :: REP String
buildPromptString = do
  modsInScope <- getModulesInScope
  let moduleNames = map renderModuleName $ Map.keys modsInScope
  return $ intercalate " " moduleNames ++ "> "


---------------------------------- Evaluate -----------------------------------

{- Evaluation is fairly straightforward; however, there are a few important
caveats:

  1. 'return' is type-polymorphic.  This means that 'return "foo"' will produce
     a type-polymorphic function 'm -> m String', for any monad 'm'.  It also
     means that if you type 'return "foo"' into a naively-written interpreter,
     you won't see 'foo'!  The solution is to force each statement that comes
     into the REPL to have type 'TopLevel t' ('TopLevel' is the SAWScript
     version of 'IO').  This gets done as soon as the statement is parsed.

  2. Handling binding variables to values is somewhat tricky.  When you're
     allowed to bind variables in the REPL, you're basically working in the
     context of a partially evaluated module: all the results of all the old
     computations are in scope, and you're allowed to add new computations that
     depend on them.  It's insufficient to merely hang onto the AST for the
     old computations, as that could cause them to be evaluated multiple times;
     it could also cause their type to be inferred differently several times,
     which is bad.  Instead, we hang onto the inferred types of previous
     computations and use them to seed the name resolver and the typechecker;
     we also hang onto the results and use them to seed the interpreter. -}
evaluate :: BlockStmt UnresolvedName RawT
            -> REP (Maybe Name, Value SAWCtx)
evaluate ast = do
  -- Set the context (i.e., the monad) for the statement (point 1 above).
  let ast' :: BlockStmt UnresolvedName RawT
      ast' = case ast of
        Bind maybeVar _ctx expr -> Bind maybeVar (Just topLevelContext) expr
        stmt -> stmt
  {- Remember, we're trying to present the illusion that you're working
  inside an ever-expanding 'do' block.  In actuality, though, only on
  statement is ever being evaluated at a time, and some statements we'd like to
  allow (namely, 'foo <- bar') aren't legal as single statements in 'do'
  blocks.  Hence, if we're being asked to bind 'foo <- bar', save the name
  'foo' and evaluate 'bar'.  (We'll bind it manually to 'foo' later.) -}
  let boundName :: Maybe Name
      withoutBinding :: BlockStmt UnresolvedName RawT
      (boundName, withoutBinding) =
        case ast' of
          Bind (Just (getVal -> varName, _)) ctx expr -> (Just varName,
                                                Bind Nothing ctx expr)
          _ -> (Nothing, ast')
  {- The compiler pipeline is targeted at modules, so wrap up the statement in
  a trivial module. -}
  modsInScope :: Map ModuleName ValidModule
              <- getModulesInScope
  let astModule :: Module UnresolvedName RawT RawT
      astModule = wrapBStmt modsInScope "it" withoutBinding
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: Module UnresolvedName ResolvedT ResolvedT
               <- REP.err $ resolveSyns astModule
  -- Add the types of previously evaluated and named expressions.
  synsResolved' <- injectBoundExpressionTypes synsResolved
  -- Rename references.
  renamed :: Module ResolvedName ResolvedT ResolvedT
          <- REP.err $ renameRefs synsResolved'
  -- Infer and check types.
  typechecked :: Module ResolvedName Schema ResolvedT
              <- REP.err $ checkModule renamed
  -- Interpret the statement.
  ctx <- getSharedContext
  env <- getEnvironment
  (result, env') <- REP.io $ interpretModuleAtEntry "it" ctx env typechecked
  -- Update the environment and return the result.
  putEnvironment env'
  saveResult boundName result
  return (boundName, result)

injectBoundExpressionTypes :: Module UnresolvedName ResolvedT ResolvedT
                              -> REP (Module UnresolvedName ResolvedT ResolvedT)
injectBoundExpressionTypes orig = do
  boundNames <- getNamesInScope
  boundNamesAndTypes :: Map LName ResolvedT
                     <-
    getEnvironment <&>
    interpretEnvTypes <&>
    Map.filterWithKey (\name _type ->
                        Set.member (getVal $ stripModuleName name) boundNames) <&>
    Map.mapKeysMonotonic stripModuleName <&>
    Map.map rewindSchema
  -- Inject the types.
  return $ orig { modulePrimEnv =
                    Map.union boundNamesAndTypes (modulePrimEnv orig) }
  where stripModuleName :: Located ResolvedName -> LName
        stripModuleName (getVal -> (LocalName _)) =
          error "injectBoundExpressionTypes: bound LocalName"
        stripModuleName (getVal -> (TopLevelName _modName varName)) = Located varName varName PosREPL

saveResult :: Maybe Name -> Value SAWCtx -> REP ()
saveResult Nothing _ = return ()
saveResult (Just name) result = do
  -- Record that 'name' is in scope.
  modifyNamesInScope $ Set.insert name
  -- Save the type of 'it'.
  let itsName = Located (TopLevelName replModuleName "it") "it" PosREPL
      itsName' = Located (TopLevelName replModuleName name) "it" PosREPL
  modifyEnvironment $ \env ->
    let typeEnv = interpretEnvTypes env in
    let typeEnv' =
          case Map.lookup itsName typeEnv of
            Nothing -> error "evaluate: could not find most recent expression"
            Just itsType ->
              Map.insert itsName' (extractFromBlock itsType) typeEnv
    in env { interpretEnvTypes = typeEnv' }
  -- Save the value of 'it'.
  modifyEnvironment $ \env ->
    let valueEnv = interpretEnvValues env in
    let valueEnv' =
          case Map.lookup itsName valueEnv of
            Nothing -> error "evaluate: could not find most recent expression"
            Just _itsValue ->
              Map.insert itsName' result valueEnv
    in env { interpretEnvValues = valueEnv' }

extractFromBlock :: Schema -> Schema
extractFromBlock (AST.Forall [] (AST.TyCon AST.BlockCon [ctx, inner]))
  | ctx == (AST.TyCon (AST.ContextCon AST.TopLevel) []) = AST.Forall [] inner
  | otherwise = error "extractFromBlock: not a TopLevel expression"
extractFromBlock (AST.Forall (_:_) _) =
  {- TODO: Support polymorphism.  Polymorphism in the interpreter is actually
  rather difficult, as doing stuff in the interpreter might very well cause
  other values to become more constrained. -}
  error "extractFromBlock: polymorphism not yet supported"
extractFromBlock _ = error "extractFromBlock: unknown construct"


------------------------------------ Print ------------------------------------

print :: (Maybe a, Value SAWCtx) -> REP ()
print (Just _, _) =
  -- This value's being bound.  Don't print it.
  return ()
print (Nothing, v)
  | isVUnit v = return ()
  | otherwise = REP.haskeline $ Haskeline.outputStrLn $ show v


----------------------------------- Utility -----------------------------------

-- From 'Control.Lens.Combinators'.
(<&>) :: Functor f => f a -> (a -> b) -> f b
a <&> f = f <$> a
infixl 1 <&>
{-# INLINE (<&>) #-}
