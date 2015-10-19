{-# LANGUAGE CPP, PatternGuards, FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
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

--import Verifier.SAW.SharedTerm (SharedContext)

import SAWScript.REPL.Monad
import SAWScript.REPL.Trie

import qualified Cryptol.ModuleSystem as M

import qualified Cryptol.Eval.Value as E
import Cryptol.Parser (ParseError())
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.ModuleSystem.Name as T (nameIdent)
import qualified Cryptol.Utils.Ident as T (unpackIdent)
import Cryptol.Utils.PP

import Control.Monad (guard, unless, when)
import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate,isPrefixOf)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map

-- SAWScript imports
import qualified SAWScript.AST as SS
    (pShow,
     Import(..),
     Located(..))
import qualified SAWScript.CryptolEnv as CEnv
import SAWScript.Compiler (liftParser)
import SAWScript.Interpreter
    (interpretStmt,
     primDocEnv,
     primTypeEnv)
import qualified SAWScript.Lexer (scan)
import qualified SAWScript.Parser (parseStmtSemi)
import qualified SAWScript.Value (evaluate)
import SAWScript.TopLevel (TopLevelRW(..))
import SAWScript.TypedTerm
import SAWScript.Utils (Pos(..))


{-
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
-}

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
  , CommandDescr ":load"   (FilenameArg loadCmd)
    "load a module"
  , CommandDescr ":add"    (FilenameArg addCmd)
    "load an additional module"
{-
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
_getPPValOpts :: REPL E.PPOpts
_getPPValOpts =
  do EnvNum base      <- getUser "base"
     EnvBool ascii    <- getUser "ascii"
     EnvNum infLength <- getUser "infLength"
     return E.PPOpts { E.useBase      = base
                     , E.useAscii     = ascii
                     , E.useInfLength = infLength
                     }

evalCmd :: String -> REPL ()
evalCmd str = do
  let str' = SS.Located str str PosREPL
  sc <- getSharedContext
  cenv <- getCryptolEnv
  TypedTerm _schema sharedterm <- io (CEnv.parseTypedTerm sc cenv str')

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

typeOfCmd :: String -> REPL ()
typeOfCmd str = do
  let str' = SS.Located str str PosREPL
  txt <- case Map.lookup str' primTypeEnv of
           Just ty -> return (text (SS.pShow ty))
           Nothing -> do
             sc <- getSharedContext
             cenv <- getCryptolEnv
             TypedTerm schema _ <- io (CEnv.parseTypedTerm sc cenv str')
             -- TODO: export functions to let us get the expr

             -- XXX need more warnings from the module system
             --io (mapM_ printWarning ws)
             --io $ print $ pp expr <+> text ":" <+> pp sig
             return (pp schema)
  io $ print $ text str <+> text ":" <+> txt

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
loadPrelude  = moduleCmd $ show $ pp MB.preludeName
-}

loadCmd :: FilePath -> REPL ()
loadCmd path
  | null path = return ()
  | otherwise = do
      sc <- getSharedContext
      cenv <- getCryptolEnv
      cenv' <- io (CEnv.importModule sc cenv (SS.Import (Left path) Nothing Nothing))
      setCryptolEnv cenv'
      --whenDebug (io (putStrLn (dump m)))

addCmd :: FilePath -> REPL ()
addCmd path
  | null path = return ()
  | otherwise = do
      sc <- getSharedContext
      cenv <- getCryptolEnv
      cenv' <- io (CEnv.importModule sc cenv (SS.Import (Left path) Nothing Nothing))
      setCryptolEnv cenv'
      --whenDebug (io (putStrLn (dump m)))

quitCmd :: REPL ()
quitCmd  = stop


envCmd :: String -> REPL ()
envCmd _pfx = do
  env <- getEnvironment
  let showLName = SS.getVal
{-
  io $ putStrLn "\nTerms:\n"
  io $ sequence_ [ putStrLn (showLName x ++ " = " ++ show v) | (x, v) <- Map.assocs (interpretEnvShared env) ]
  io $ putStrLn "\nValues:\n"
  io $ sequence_ [ putStrLn (showLName x ++ " = " ++ show v) | (x, v) <- Map.assocs (interpretEnvValues env) ]
  io $ putStrLn "\nTypes:\n"
-}
  io $ sequence_ [ putStrLn (showLName x ++ " : " ++ SS.pShow v) | (x, v) <- Map.assocs (rwTypes env) ]

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



_setOptionCmd :: String -> REPL ()
_setOptionCmd str
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
  | Just d <- Map.lookup cmd primDocEnv =
                io $ putStr d
-- FIXME? can we restore the ability to lookup doc strings from Cryptol?
--  | Just (ec,_) <- lookup cmd builtIns =
--                io $ print $ helpDoc ec

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
  stmt <- err $ liftParser SAWScript.Parser.parseStmtSemi tokens
  ro <- getTopLevelRO
  ie <- getEnvironment
  ie' <- io $ interpretStmt True ro ie stmt
  putEnvironment ie'

replFileName :: String
replFileName = "<stdin>"

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: REPL ()
handleCtrlC  = io (putStrLn "Ctrl-C")


-- Utilities -------------------------------------------------------------------

isNamePrefix :: String -> T.Name -> Bool
isNamePrefix pfx n = pfx `isPrefixOf` T.unpackIdent (T.nameIdent n)

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
