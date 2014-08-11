-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP, PatternGuards, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findNbCommand

  -- , moduleCmd, loadCmd, loadPrelude

    -- Misc utilities
  , handleCtrlC
  , sanitize

    -- To support Notebook interface (might need to refactor)
  , replParse
  --, liftModuleCmd
  --, moduleCmdResult
  ) where

import Verifier.SAW.SharedTerm (SharedContext)

import SAWScript.REPL.Monad
import SAWScript.REPL.Trie

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as M (preludeName)
import qualified Cryptol.ModuleSystem.Monad as M (ImportSource(..))

import qualified Cryptol.Eval.Value as E
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Renamer as R
import qualified Cryptol.Testing.Random  as TestR
import qualified Cryptol.Testing.Exhaust as TestX
import qualified Cryptol.Parser
import Cryptol.Parser
    (parseExprWith,ParseError(),Config(..),defaultConfig,parseModName)
import qualified Cryptol.Parser.NoPat
import Cryptol.Parser.Position (emptyRange,getLoc)
import qualified Cryptol.TypeCheck
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Subst as T
import qualified Cryptol.TypeCheck.InferTypes as T
import qualified Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.PP (dump,ppWithNames)
import Cryptol.TypeCheck.Defaulting(defaultExpr)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import qualified Cryptol.Parser.AST as P
import Cryptol.Prims.Doc(helpDoc)
import qualified Cryptol.Transform.Specialize as S
import qualified Cryptol.Symbolic

import Control.Monad (guard,unless,forM_,when)
import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate,isPrefixOf)
import Data.Maybe (fromMaybe,mapMaybe)
import System.Exit (ExitCode(ExitSuccess))
--import System.Process (shell,createProcess,waitForProcess)
--import qualified System.Process as Process(runCommand)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import System.IO(hFlush,stdout)
--import System.Random(newStdGen)
import Numeric (showFFloat)

-- SAWScript imports
import qualified SAWScript.AST as SS
    (ModuleName, {-renderModuleName,-}
     renderResolvedName, pShow,
     Module(..), ValidModule,
     BlockStmt(Bind),
     Name, LName, Located(..), UnresolvedName,
     ResolvedName(..),
     RawT, ResolvedT,
     Context(..), Schema(..), Type(..), TyCon(..), rewindSchema,
     block,
     topLevelContext,
     updateAnnotation)
import SAWScript.Interpreter
    (Value, isVUnit,
     interpretModuleAtEntry,
     InterpretEnv(..),
     interpretEnvValues, interpretEnvTypes)
import qualified SAWScript.Lexer (scan)
import qualified SAWScript.MGU (checkModule)
import qualified SAWScript.Parser (parseBlockStmt)
import qualified SAWScript.RenameRefs (renameRefs)
import qualified SAWScript.ResolveSyns (resolveSyns)
import qualified SAWScript.Value (Value(VTerm), evaluate)
import SAWScript.REPL.GenerateModule (replFileName, replModuleName, wrapBStmt)
import SAWScript.Utils (SAWCtx, Pos(..))

import qualified Verifier.SAW.Cryptol


#if __GLASGOW_HASKELL__ < 706
import Control.Monad (liftM)
import qualified Text.ParserCombinators.ReadP as P
import Text.Read hiding (step)
import System.Environment (getEnvironment)

lookupEnv :: String -> IO (Maybe String)
lookupEnv key = lookup key `liftM` getEnvironment

readEither :: Read a => String -> Either String a
readEither s =
  case [ x | (x,"") <- readPrec_to_S read' minPrec s ] of
    [x] -> Right x
    []  -> Left "Prelude.read: no parse"
    _   -> Left "Prelude.read: ambiguous parse"
 where
  read' =
    do x <- readPrec
       lift P.skipSpaces
       return x

-- | Parse a string using the 'Read' instance.
-- Succeeds if there is exactly one valid result.
readMaybe :: Read a => String -> Maybe a
readMaybe s = case readEither s of
                Left _  -> Nothing
                Right a -> Just a
#else
import System.Environment (lookupEnv)
#endif

-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (REPL ())         -- ^ Successfully parsed command
  | Ambiguous String [String] -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown String            -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cName :: String
  , cBody :: CommandBody
  , cHelp :: String
  }

instance Show CommandDescr where
  show = cName

instance Eq CommandDescr where
  (==) = (==) `on` cName

instance Ord CommandDescr where
  compare = compare `on` cName

data CommandBody
  = ExprArg     (String   -> REPL ())
  | ExprTypeArg (String   -> REPL ())
  | FilenameArg (FilePath -> REPL ())
  | OptionArg   (String   -> REPL ())
  | ShellArg    (String   -> REPL ())
  | NoArg       (REPL ())


-- | REPL command parsing.
commands :: CommandMap
commands  = foldl insert emptyTrie commandList
  where
  insert m d = insertTrie (cName d) d m

-- | Notebook command parsing.
nbCommands :: CommandMap
nbCommands  = foldl insert emptyTrie nbCommandList
  where
  insert m d = insertTrie (cName d) d m

-- | A subset of commands safe for Notebook execution
nbCommandList :: [CommandDescr]
nbCommandList  =
  [ CommandDescr ":env" (ExprTypeArg envCmd)
    "display the current sawscript environment"
  , CommandDescr ":type"   (ExprArg typeOfCmd)
    "check the type of an expression"
  , CommandDescr ":browse" (ExprTypeArg browseCmd)
    "display the current environment"
  , CommandDescr ":eval" (ExprArg evalCmd)
    "evaluate an expression and print the result"
  , CommandDescr ":?"      (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  , CommandDescr ":help"   (ExprArg helpCmd)
    "display a brief description about a built-in operator"
  {-
  , CommandDescr ":set" (OptionArg setOptionCmd)
    "set an environmental option (:set on its own displays current values)"
  -}
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr ":quit"   (NoArg quitCmd)
    "exit the REPL"
{-
  , CommandDescr ":load"   (FilenameArg loadCmd)
    "load a module"
  , CommandDescr ":reload" (NoArg reloadCmd)
    "reload the currently loaded module"
  , CommandDescr ":edit"   (FilenameArg editCmd)
    "edit the currently loaded module"
  , CommandDescr ":!" (ShellArg runShellCmd)
    "execute a command in the shell"
-}
  , CommandDescr ":cd" (FilenameArg cdCmd)
    "set the current working directory"
{-
  , CommandDescr ":module" (FilenameArg moduleCmd)
    "load a module"

  , CommandDescr ":check" (ExprArg qcCmd)
    "use random testing to check that the argument always returns true"
  , CommandDescr ":prove" (ExprArg proveCmd)
    "use an external solver to prove that the argument always returns true"
  , CommandDescr ":sat" (ExprArg satCmd)
    "use a solver to find a satisfying assignment for which the argument returns true"
  , CommandDescr ":debug_specialize" (ExprArg specializeCmd)
    "do type specialization on a closed expression"
-}
  ]

genHelp :: [CommandDescr] -> [String]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd = concat [ "  ", cName cmd, pad (cName cmd), cHelp cmd ]
  padding     = 2 + maximum (map (length . cName) cs)
  pad n       = replicate (max 0 (padding - length n)) ' '


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Command -> REPL ()
runCommand c = case c of

  Command cmd -> cmd `SAWScript.REPL.Monad.catch` handler
                     `SAWScript.REPL.Monad.catchFail` handler2
    where
    handler re = io (putStrLn "" >> print (pp re))
    handler2 s = io (putStrLn "" >> putStrLn s)

  Unknown cmd -> io (putStrLn ("Unknown command: " ++ cmd))

  Ambiguous cmd cmds -> io $ do
    putStrLn (cmd ++ " is ambiguous, it could mean one of:")
    putStrLn ("\t" ++ intercalate ", " cmds)


-- Get the setting we should use for displaying values.
getPPValOpts :: REPL E.PPOpts
getPPValOpts =
  do EnvNum base      <- getUser "base"
     EnvBool ascii    <- getUser "ascii"
     EnvNum infLength <- getUser "infLength"
     return E.PPOpts { E.useBase      = base
                     , E.useAscii     = ascii
                     , E.useInfLength = infLength
                     }

interactiveSource :: M.ImportSource
interactiveSource = M.FromModule (P.ModName ["<interactive>"])

replCheckExpr :: P.Expr -> REPL (T.Expr, T.Schema)
replCheckExpr pexpr = do

  -- Remove patterns
  let (npe, errs) = Cryptol.Parser.NoPat.removePatterns pexpr
  unless (null errs) $ raise (NoPatError errs)

  -- Rename
  nameEnv <- getNamingEnv
  let (res, _warnings) = R.runRenamer nameEnv (R.rename npe)
  re <- case res of
          Right r   -> return r
          Left errs -> raise (ModuleSystemError (M.RenamerErrors interactiveSource errs))

  -- Typecheck
  inferInput <- getInferInput
  let range = fromMaybe emptyRange (getLoc re)
  out <- io (Cryptol.TypeCheck.tcExpr re inferInput)
  case out of
    Cryptol.TypeCheck.Monad.InferOK _warns seeds o ->
      do setNameSeeds seeds
         --typeCheckWarnings warns
         return o
    Cryptol.TypeCheck.Monad.InferFailed _warns errs ->
      do raise (ModuleSystemError (M.TypeCheckingFailed interactiveSource errs))
{-
      do typeCheckWarnings warns
         typeCheckingFailed errs
-}

evalCmd :: String -> REPL ()
evalCmd str = do
  pexpr <- replParseExpr str
  (expr, schema) <- replCheckExpr pexpr

  -- Translate
  sc <- getSharedContext
  inpVars <- getInpVars
  termEnv <- getTermEnv
  let cryEnv = Verifier.SAW.Cryptol.Env
        { Verifier.SAW.Cryptol.envT = Map.empty
        , Verifier.SAW.Cryptol.envE = fmap (\t -> (t, 0)) termEnv
        , Verifier.SAW.Cryptol.envP = Map.empty
        , Verifier.SAW.Cryptol.envC = inpVars
        }
  sharedterm <- io $ Verifier.SAW.Cryptol.importExpr sc cryEnv expr

  -- Evaluate and print
  let val = SAWScript.Value.evaluate sc sharedterm
  io $ rethrowEvalError $ print val

{-
  (val,_ty) <- replEvalExpr str
  ppOpts <- getPPValOpts
  io $ rethrowEvalError $ print $ pp $ E.WithBase ppOpts val
-}

{-
qcCmd :: String -> REPL ()
qcCmd "" =
  do xs <- getPropertyNames
     if null xs
        then io $ putStrLn "There are no properties in scope."
        else forM_ xs $ \x ->
               do io $ putStr $ "property " ++ x ++ " "
                  qcCmd x

qcCmd str =
  do (val,ty) <- replEvalExpr str
     EnvNum testNum  <- getUser "tests"
     case TestX.testableType ty of
       Just (sz,vss) | sz <= toInteger testNum ->
         do io $ putStrLn "Using exhaustive testing."
            let doTest _ [] = panic "We've unexpectedly run out of test cases"
                                    []
                doTest _ (vs : vss1) =
                    if TestX.runTest val vs
                        then (Nothing, vss1)
                        else (Just vs, vss1)
            ok <- go doTest sz 0 vss
            when ok $ io $ putStrLn "QED"

       n -> case TestR.testableType ty of
              Nothing   -> raise (TypeNotTestable ty)
              Just gens ->
                do io $ putStrLn "Using random testing."
                   prt testingMsg
                   g <- io newStdGen
                   ok <- go (TestR.runTest val gens) testNum 0 g
                   when ok $
                     case n of
                       Just (valNum,_) ->
                         do let valNumD = fromIntegral valNum :: Double
                                percent = fromIntegral (testNum * 100)
                                        / valNumD
                                showValNum
                                   | valNum > 2 ^ (20::Integer) =
                                       "2^^" ++ show (round $ logBase 2 valNumD :: Integer)
                                   | otherwise = show valNum
                            io $ putStrLn $ "Coverage: "
                                     ++ showFFloat (Just 2) percent "% ("
                                     ++ show testNum ++ " of "
                                     ++ showValNum ++ " values)"
                       Nothing -> return ()

  where
  testingMsg = "testing..."

  totProgressWidth = 4    -- 100%

  prt msg   = io (putStr msg >> hFlush stdout)
  prtLn msg = io (putStrLn msg >> hFlush stdout)

  ppProgress this tot =
    let percent = show (div (100 * this) tot) ++ "%"
        width   = length percent
        pad     = replicate (totProgressWidth - width) ' '
    in prt (pad ++ percent)

  del n       = prt (replicate n '\BS')
  delTesting  = del (length testingMsg)
  delProgress = del totProgressWidth

  go _ totNum testNum _
     | testNum >= totNum =
         do delTesting
            prtLn $ "passed " ++ show totNum ++ " tests."
            return True

  go doTest totNum testNum st =
     do ppProgress testNum totNum
        case doTest (div (100 * (1 + testNum)) totNum) st of
          (Nothing, st1) -> do delProgress
                               go doTest totNum (testNum + 1) st1
          (Just vs, _g1) ->
             do opts <- getPPValOpts
                do delProgress
                   delTesting
                   prtLn "FAILED for the following inputs:"
                   io $ mapM_ (print . pp . E.WithBase opts) vs
                   return False
-}

{-
proveCmd :: String -> REPL ()
proveCmd str = do
  parseExpr <- replParseExpr str
  (expr, schema) <- replCheckExpr parseExpr
  -- spexpr <- replSpecExpr expr
  EnvString proverName <- getUser "prover"
  EnvBool iteSolver <- getUser "iteSolver"
  EnvBool verbose <- getUser "debug"
  result <- liftModuleCmd $ Cryptol.Symbolic.prove (proverName, iteSolver, verbose) (expr, schema)
  ppOpts <- getPPValOpts
  case result of
    Left msg        -> io $ putStrLn msg
    Right Nothing   -> io $ putStrLn "Q.E.D."
    Right (Just vs) -> io $ print $ hsep (doc : docs) <+> text "= False"
                         where doc = ppPrec 3 parseExpr -- function application has precedence 3
                               docs = map (pp . E.WithBase ppOpts) vs

satCmd :: String -> REPL ()
satCmd str = do
  parseExpr <- replParseExpr str
  (expr, schema) <- replCheckExpr parseExpr
  EnvString proverName <- getUser "prover"
  EnvBool iteSolver <- getUser "iteSolver"
  EnvBool verbose <- getUser "debug"
  result <- liftModuleCmd $ Cryptol.Symbolic.sat (proverName, iteSolver, verbose) (expr, schema)
  ppOpts <- getPPValOpts
  case result of
    Left msg        -> io $ putStrLn msg
    Right Nothing   -> io $ putStrLn "Unsatisfiable."
    Right (Just vs) -> io $ print $ hsep (doc : docs) <+> text "= True"
                         where doc = ppPrec 3 parseExpr -- function application has precedence 3
                               docs = map (pp . E.WithBase ppOpts) vs
-}

typeOfCmd :: String -> REPL ()
typeOfCmd str = do
  expr      <- replParseExpr str
  (def,sig) <- replCheckExpr expr

  -- XXX need more warnings from the module system
  --io (mapM_ printWarning ws)
  whenDebug (io (putStrLn (dump def)))
  io $ print $ pp expr <+> text ":" <+> pp sig

{-
reloadCmd :: REPL ()
reloadCmd  = do
  mb <- getLoadedMod
  case mb of
    Just m  -> loadCmd (lPath m)
    Nothing -> return ()
-}

{-
editCmd :: String -> REPL ()
editCmd path
  | null path = do
      mb <- getLoadedMod
      case mb of

        Just m -> do
          success <- replEdit (lPath m)
          if success
             then loadCmd (lPath m)
             else return ()

        Nothing   -> do
          io (putStrLn "No files to edit.")
          return ()

  | otherwise = do
      _  <- replEdit path
      mb <- getLoadedMod
      case mb of
        Nothing -> loadCmd path
        Just _  -> return ()
-}

{-
moduleCmd :: String -> REPL ()
moduleCmd modString
  | null modString = return ()
  | otherwise      = do
      case parseModName modString of
        Just m -> loadCmd =<< liftModuleCmd (M.findModule m)
        Nothing -> io $ putStrLn "Invalid module name."

loadPrelude :: REPL ()
loadPrelude  = moduleCmd $ show $ pp M.preludeName

loadCmd :: FilePath -> REPL ()
loadCmd path
  | null path = return ()
  | otherwise = do
      setLoadedMod LoadedModule
        { lName = Nothing
        , lPath = path
        }

      m <- moduleCmdResult =<< io (M.loadModuleByPath path)
      whenDebug (io (putStrLn (dump m)))
      setLoadedMod LoadedModule
        { lName = Just (T.mName m)
        , lPath = path
        }
-}

quitCmd :: REPL ()
quitCmd  = stop


envCmd :: String -> REPL ()
envCmd _pfx = do
  env <- getEnvironment
  let showLName = SS.renderResolvedName . SS.getVal
{-
  io $ putStrLn "\nTerms:\n"
  io $ sequence_ [ putStrLn (showLName x ++ " = " ++ show v) | (x, v) <- Map.assocs (interpretEnvShared env) ]
  io $ putStrLn "\nValues:\n"
  io $ sequence_ [ putStrLn (showLName x ++ " = " ++ show v) | (x, v) <- Map.assocs (interpretEnvValues env) ]
  io $ putStrLn "\nTypes:\n"
-}
  io $ sequence_ [ putStrLn (showLName x ++ " : " ++ SS.pShow v) | (x, v) <- Map.assocs (interpretEnvTypes env) ]

browseCmd :: String -> REPL ()
browseCmd pfx = do
  browseTSyns pfx
  browseNewtypes pfx
  browseVars pfx

browseTSyns :: String -> REPL ()
browseTSyns pfx = do
  tsyns <- getTSyns
  let tsyns' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) tsyns
  unless (Map.null tsyns') $ io $ do
    putStrLn "Type Synonyms"
    putStrLn "============="
    let ppSyn (qn,T.TySyn _ ps cs ty) = pp (T.TySyn qn ps cs ty)
    print (nest 4 (vcat (map ppSyn (Map.toList tsyns'))))
    putStrLn ""

browseNewtypes :: String -> REPL ()
browseNewtypes pfx = do
  nts <- getNewtypes
  let nts' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) nts
  unless (Map.null nts') $ io $ do
    putStrLn "Newtypes"
    putStrLn "========"
    let ppNT (qn,nt) = T.ppNewtypeShort (nt { T.ntName = qn })
    print (nest 4 (vcat (map ppNT (Map.toList nts'))))
    putStrLn ""

browseVars :: String -> REPL ()
browseVars pfx = do
  vars  <- getVars
  let allNames = vars
          {- This shows the built-ins as well:
             Map.union vars
                  (Map.fromList [ (Name x,t) | (x,(_,t)) <- builtIns ]) -}
      vars' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) allNames

      isProp p     = T.PragmaProperty `elem` (M.ifDeclPragmas p)
      (props,syms) = Map.partition isProp vars'

  ppBlock "Properties" props
  ppBlock "Symbols" syms

  where
  ppBlock name xs =
    unless (Map.null xs) $ io $ do
      putStrLn name
      putStrLn (replicate (length name) '=')
      let step k d acc =
              pp k <+> char ':' <+> pp (M.ifDeclSig d) : acc
      print (nest 4 (vcat (Map.foldrWithKey step [] xs)))
      putStrLn ""



setOptionCmd :: String -> REPL ()
setOptionCmd str
  | Just value <- mbValue = setUser key value
  | null key              = mapM_ (describe . optName) (leaves userOptions)
  | otherwise             = describe key
  where
  (before,after) = break (== '=') str
  key   = trim before
  mbValue = case after of
              _ : stuff -> Just (trim stuff)
              _         -> Nothing

  describe k = do
    ev <- tryGetUser k
    io $ case ev of
           Just (EnvString s)   -> putStrLn (k ++ " = " ++ s)
           Just (EnvNum n)      -> putStrLn (k ++ " = " ++ show n)
           Just (EnvBool True)  -> putStrLn (k ++ " = on")
           Just (EnvBool False) -> putStrLn (k ++ " = off")
           Nothing              -> do putStrLn ("Unknown user option: `" ++ k ++ "`")
                                      when (any isSpace k) $ do
                                        let (k1, k2) = break isSpace k
                                        putStrLn ("Did you mean: `:set " ++ k1 ++ " =" ++ k2 ++ "`?")


helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd = io (mapM_ putStrLn (genHelp commandList))
  | Just (ec,_) <- lookup cmd builtIns =
                io $ print $ helpDoc ec
  | otherwise = do io $ putStrLn $ "// No documentation is available."
                   typeOfCmd cmd


{-
runShellCmd :: String -> REPL ()
runShellCmd cmd
  = io $ do h <- Process.runCommand cmd
            _ <- waitForProcess h
            return ()
-}

cdCmd :: FilePath -> REPL ()
cdCmd f | null f = io $ putStrLn $ "[error] :cd requires a path argument"
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then io $ setCurrentDirectory f
    else raise $ DirectoryNotFound f

-- SAWScript commands ----------------------------------------------------------

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
sawScriptCmd :: String -> REPL ()
sawScriptCmd str = do
  tokens <- err $ SAWScript.Lexer.scan replFileName str
  ast <- err $ SAWScript.Parser.parseBlockStmt tokens
  -- Set the context (i.e., the monad) for the statement (point 1 above).
  let ast' :: SS.BlockStmt SS.UnresolvedName SS.RawT
      ast' = case ast of
        SS.Bind maybeVar _ctx expr -> SS.Bind maybeVar (Just SS.topLevelContext) expr
        stmt -> stmt
  {- Remember, we're trying to present the illusion that you're working
  inside an ever-expanding 'do' block.  In actuality, though, only on
  statement is ever being evaluated at a time, and some statements we'd like to
  allow (namely, 'foo <- bar') aren't legal as single statements in 'do'
  blocks.  Hence, if we're being asked to bind 'foo <- bar', save the name
  'foo' and evaluate 'bar'.  (We'll bind it manually to 'foo' later.) -}
  let boundName :: Maybe SS.Name
      withoutBinding :: SS.BlockStmt SS.UnresolvedName SS.RawT
      (boundName, withoutBinding) =
        case ast' of
          SS.Bind (Just (SS.getVal -> varName, ty)) ctx expr
            -> let ty' = fmap (SS.block SS.topLevelContext) ty
               in (Just varName, SS.Bind Nothing ctx (SS.updateAnnotation ty' expr))
          _ -> (Nothing, ast')
  {- The compiler pipeline is targeted at modules, so wrap up the statement in
  a trivial module. -}
  modsInScope :: Map SS.ModuleName SS.ValidModule
              <- getModulesInScope
  let astModule :: SS.Module SS.UnresolvedName SS.RawT SS.RawT
      astModule = wrapBStmt modsInScope "it" withoutBinding
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: SS.Module SS.UnresolvedName SS.ResolvedT SS.ResolvedT
               <- err $ SAWScript.ResolveSyns.resolveSyns astModule
  -- Add the types of previously evaluated and named expressions.
  synsResolved' <- injectBoundExpressionTypes synsResolved
  -- Rename references.
  renamed :: SS.Module SS.ResolvedName SS.ResolvedT SS.ResolvedT
          <- err $ SAWScript.RenameRefs.renameRefs synsResolved'
  -- Infer and check types.
  typechecked :: SS.Module SS.ResolvedName SS.Schema SS.ResolvedT
              <- err $ SAWScript.MGU.checkModule renamed
  -- Interpret the statement.
  sc <- getSharedContext
  env <- getEnvironment
  (result, env') <- io $ interpretModuleAtEntry "it" sc env typechecked
  -- Update the environment and return the result.
  putEnvironment env'
  saveResult sc boundName result
  case boundName of
    Nothing | not (isVUnit result) -> io $ print result
    _                              -> return ()


injectBoundExpressionTypes :: SS.Module SS.UnresolvedName SS.ResolvedT SS.ResolvedT
                              -> REPL (SS.Module SS.UnresolvedName SS.ResolvedT SS.ResolvedT)
injectBoundExpressionTypes orig = do
  boundNames <- getNamesInScope
  boundNamesAndTypes :: Map SS.LName SS.ResolvedT
                     <-
    getEnvironment <&>
    interpretEnvTypes <&>
    Map.filterWithKey (\name _type ->
                        Set.member (SS.getVal $ stripModuleName name) boundNames) <&>
    Map.mapKeysMonotonic stripModuleName <&>
    Map.map SS.rewindSchema
  -- Inject the types.
  return $ orig { SS.modulePrimEnv =
                    Map.union boundNamesAndTypes (SS.modulePrimEnv orig) }
  where stripModuleName :: SS.Located SS.ResolvedName -> SS.LName
        stripModuleName (SS.getVal -> (SS.LocalName _)) =
          error "injectBoundExpressionTypes: bound LocalName"
        stripModuleName (SS.getVal -> (SS.TopLevelName _modName varName)) = SS.Located varName varName PosREPL

saveResult :: SharedContext SAWCtx -> Maybe SS.Name -> Value SAWCtx -> REPL ()
saveResult _ Nothing _ = return ()
saveResult sc (Just name) result = do
  -- Record that 'name' is in scope.
  modifyNamesInScope $ Set.insert name
  -- Save the type of 'it'.
  let itsName = SS.Located (SS.TopLevelName replModuleName "it") "it" PosREPL
      itsName' = SS.Located (SS.TopLevelName replModuleName name) "it" PosREPL
  env <- getEnvironment
  let typeEnv = interpretEnvTypes env
  let valueEnv = interpretEnvValues env
  let sharedEnv = interpretEnvShared env
  let typeEnv' =
        case Map.lookup itsName typeEnv of
          Nothing -> error "evaluate: could not find most recent expression"
          Just itsType ->
            Map.insert itsName' (extractFromBlock itsType) typeEnv
  let (valueEnv', sharedEnv') =
        case result of
          SAWScript.Value.VTerm _ t ->
            (Map.insert itsName' (SAWScript.Value.evaluate sc t) valueEnv,
             Map.insert itsName' t sharedEnv)
          _ ->
            (Map.insert itsName' result valueEnv, sharedEnv)

  putEnvironment $ env
    { interpretEnvValues = valueEnv'
    , interpretEnvTypes  = typeEnv'
    , interpretEnvShared = sharedEnv' }

  case result of
    SAWScript.Value.VTerm (Just s) t
      -> do io $ putStrLn $ "Binding SAWCore term: " ++ show name
            let qname = convertName name
            let lname = P.Located emptyRange qname
            modifyNamingEnv (MN.shadowing (MN.singletonE qname (MN.EFromBind lname)))
            modifyInpVars (Map.insert qname s)
            modifyTermEnv (Map.insert qname t)
    SAWScript.Value.VTerm Nothing t
      -> do io $ putStrLn $ "SAWCore term (no type info): " ++ show name
    _ -> return ()

convertName :: SS.Name -> T.QName
convertName n = T.QName Nothing (T.Name n)

extractFromBlock :: SS.Schema -> SS.Schema
extractFromBlock (SS.Forall [] (SS.TyCon SS.BlockCon [ctx, inner]))
  | ctx == (SS.TyCon (SS.ContextCon SS.TopLevel) []) = SS.Forall [] inner
  | otherwise = error "extractFromBlock: not a TopLevel expression"
extractFromBlock (SS.Forall (_:_) _) =
  {- TODO: Support polymorphism.  Polymorphism in the interpreter is actually
  rather difficult, as doing stuff in the interpreter might very well cause
  other values to become more constrained. -}
  error "extractFromBlock: polymorphism not yet supported"
extractFromBlock _ = error "extractFromBlock: unknown construct"


-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: REPL ()
handleCtrlC  = io (putStrLn "Ctrl-C")


-- Utilities -------------------------------------------------------------------

isNamePrefix :: String -> P.QName -> Bool
isNamePrefix pfx n = case n of
  P.QName _ (P.Name _) -> pfx `isPrefixOf` pretty n
  _                    -> False

{-
printWarning :: (Range,Warning) -> IO ()
printWarning = print . ppWarning

printError :: (Range,Error) -> IO ()
printError = print . ppError
-}

-- | Lift a parsing action into the REPL monad.
replParse :: (String -> Either ParseError a) -> String -> REPL a
replParse parse str = case parse str of
  Right a -> return a
  Left e  -> raise (ParseError e)

replParseExpr :: String -> REPL P.Expr
replParseExpr = replParse $ parseExprWith interactiveConfig

interactiveConfig :: Config
interactiveConfig = defaultConfig { cfgSource = "<interactive>" }

{-
moduleCmdResult :: M.ModuleRes a -> REPL a
moduleCmdResult (res,ws0) = do
  EnvBool yes <- getUser "warnDefaulting"
  let isDefaultWarn (T.DefaultingTo _ _) = True
      isDefaultWarn _ = False

      filterDefaults (M.TypeCheckWarnings xs) =
        case filter (not . isDefaultWarn . snd) xs of
          [] -> Nothing
          ys -> Just (M.TypeCheckWarnings ys)
      filterDefaults w = Just w

  let ws = if yes then ws0
                  else mapMaybe filterDefaults ws0
  io (mapM_ (print . pp) ws)
  case res of
    Right (a,me') -> setModuleEnv me' >> return a
    Left err      -> raise (ModuleSystemError err)

replSpecExpr :: T.Expr -> REPL T.Expr
replSpecExpr e = liftModuleCmd $ S.specialize e

replEvalExpr :: String -> REPL (E.Value, T.Type)
replEvalExpr str =
  do expr      <- replParseExpr str
     (def,sig) <- replCheckExpr expr

     let range = fromMaybe emptyRange (getLoc expr)
     (def1,ty) <-
        case defaultExpr range def sig of
          Nothing -> raise (EvalPolyError sig)
          Just (tys,def1) ->
            do let nms = T.addTNames (T.sVars sig) IntMap.empty
               io $ mapM_ (warnDefault nms) tys
               let su = T.listSubst [ (T.tpVar a, t) | (a,t) <- tys ]
               return (def1, T.apSubst su (T.sType sig))

     val <- liftModuleCmd (M.evalExpr def1)
     whenDebug (io (putStrLn (dump def1)))
     return (val,ty)
  where
  warnDefault ns (x,t) =
        print $ text "Assuming" <+> ppWithNames ns x <+> text "=" <+> pp t
-}

{-
replEdit :: String -> REPL Bool
replEdit file = do
  mb <- io (lookupEnv "EDITOR")
  let editor = fromMaybe "vim" mb
  io $ do
    (_,_,_,ph) <- createProcess (shell (unwords [editor, file]))
    exit       <- waitForProcess ph
    return (exit == ExitSuccess)
-}

type CommandMap = Trie CommandDescr


-- Command Parsing -------------------------------------------------------------

-- | Strip leading space.
sanitize :: String -> String
sanitize  = dropWhile isSpace

-- | Strip trailing space.
sanitizeEnd :: String -> String
sanitizeEnd = reverse . sanitize . reverse

trim :: String -> String
trim = sanitizeEnd . sanitize

-- | Split at the first word boundary.
splitCommand :: String -> Maybe (String,String)
splitCommand txt =
  case sanitize txt of
    ':' : more
      | (as,bs) <- span (\x -> isPunctuation x || isSymbol x) more
      , not (null as) -> Just (':' : as, sanitize bs)

      | (as,bs) <- break isSpace more
      , not (null as) -> Just (':' : as, sanitize bs)

      | otherwise -> Nothing

    expr -> guard (not (null expr)) >> return (expr,[])

-- | Uncons a list.
uncons :: [a] -> Maybe (a,[a])
uncons as = case as of
  a:rest -> Just (a,rest)
  _      -> Nothing

-- | Lookup a string in the command list.
findCommand :: String -> [CommandDescr]
findCommand str = lookupTrie str commands

-- | Lookup a string in the notebook-safe command list.
findNbCommand :: String -> [CommandDescr]
findNbCommand str = lookupTrie str nbCommands

-- | Parse a line as a command.
parseCommand :: (String -> [CommandDescr]) -> String -> Maybe Command
parseCommand findCmd line = do
  (cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    [c] -> case cBody c of
      ExprArg     body -> Just (Command (body args'))
      ExprTypeArg body -> Just (Command (body args'))
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      OptionArg   body -> Just (Command (body args'))
      ShellArg    body -> Just (Command (body args'))
      NoArg       body -> Just (Command  body)

    [] -> case uncons cmd of
      Just (':',_) -> Just (Unknown cmd)
      Just _       -> Just (Command (sawScriptCmd line))
      _            -> Nothing

    cs -> Just (Ambiguous cmd (map cName cs))

  where
  expandHome path =
    case path of
      '~' : c : more | isPathSeparator c -> do dir <- io getHomeDirectory
                                               return (dir </> more)
      _ -> return path

----------------------------------- Utility -----------------------------------

-- From 'Control.Lens.Combinators'.
(<&>) :: Functor f => f a -> (a -> b) -> f b
a <&> f = fmap f a
infixl 1 <&>
{-# INLINE (<&>) #-}
