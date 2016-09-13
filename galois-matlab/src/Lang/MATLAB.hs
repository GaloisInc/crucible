{-# LANGUAGE CPP #-}
module Lang.MATLAB
  ( AST.Module(..)
  , parseModule
  , parseScript
    -- * Function
  , AST.Function
  , AST.fnDecl
  , AST.fnStmts
  , AST.fnNestedFunctions
  , AST.methodToFunction
    -- * Function declarations.
  , Common.FunctionDecl
  , Common.fnName
  , Common.fnOutputs
  , Common.fnInputs
    -- * Statement
  , AST.ResolvedStmt
  , Common.TermStmt(..)
  , Common.ShouldPrint(..)
  , Common.Stmt(..)
  , Common.IfStmt(..)
  , Common.SwitchCases(..)
  , Expr.Expr(..)
  , Expr.LhsExpr(..)
  , Expr.SubExpr(..)
  , Expr.ArrayIndexArgs
  , Expr.ppExpr
  , Expr.exprVars
  , Common.PrefixOp
  , Common.InfixOp
  , Common.FnArg(..)
    -- * Ident
  , Common.Ident
  , Common.identText
  , Common.identFromText
  , Common.identAppend
    -- * Position
  , Position.Position(..)
  , Position.Posd(..)
  , Position.PositionMonad(..)
  , Position.ppLineAndCol
  , Position.startOfFile
    -- * Classes
  , AST.Method(..)
  , AST.mdFirstRet
  , AST.ResolvedClassDef(..)
  , AST.classIdentToText
  , AST.extractProperties
  , AST.extractMethods
  , LiteralAST.mdToFnDecl
    -- * Low-level interface
  , ErrorWithPos(..)
  , ppErrorWithPos
  , parse
  , runAlex
  ) where

import           Control.Monad
import qualified Data.ByteString.Lazy as LazyBS
import qualified Data.Foldable as Fold
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Traversable as Tr

import           Lang.MATLAB.LiteralAST as LiteralAST
import           Lang.MATLAB.AST as AST
import           Lang.MATLAB.Common as Common
import           Lang.MATLAB.Expr as Expr
import qualified Lang.MATLAB.LiteralAST as Src
import           Lang.MATLAB.Parser
import           Lang.MATLAB.Position as Position

#if !MIN_VERSION_base(4,8,0)
import           Control.Applicative
import           Data.Traversable (traverse)
#endif

-- | This checks for duplicates in the list under a given projection.
--
-- It returns 'Nothing' if there are no duplicates and a pair otherwise.
findDuplicatesUnder :: Ord k
                    => (a -> k)
                    -> [a]
                    -> Maybe (a, a)
findDuplicatesUnder proj entries =
    case Map.minView dup_map of
      Just (x:y:_,_) -> Just (x,y)
      _ -> Nothing

  where -- Build list containing key value pairs
        pairs = fmap (\a -> (proj a, [a])) entries
        -- Create map that maps each key to list of values with that key.
        key_map = Map.fromListWith (++) pairs
        -- Include only duplicates.
        dup_map = Map.filter (\l -> length l > 1) key_map

unexpectedEnd :: String
unexpectedEnd = "Unexpected keyword \"end\" appears outside function body."

-- | If in script mode, extract the ParserStmt value from the given TopStmt.
-- If not in script mode, fail with an error message.
getScriptStmt :: PositionMonad m
        => TermStmt Src.TopStmt
        -> m (TermStmt Src.ParserStmt)
getScriptStmt (TStmt (Posd p v) pr) =
  case v of
    Src.EndStmt -> failAt p unexpectedEnd
    Src.FunctionDecl _ ->
      failAt p "Function declarations are not allowed in script mode."
    Src.ClassDecl _ ->
      failAt p "Class declarations are not allowed in script mode."
    Src.Stmt s -> return $ TStmt (Posd p s) pr

isEnd :: TermStmt Src.TopStmt -> Bool
isEnd (TStmt (Posd _ Src.EndStmt) _) = True
isEnd _ = False

processStmt :: PositionMonad m
            => ([Function] -> [ResolvedStmt] -> m a)
            -> TermStmt Src.TopStmt
            -> ([Function] -> [ResolvedStmt] -> m a)
processStmt gen (TStmt (Posd p ts) ps) fl sl =
  case ts of
    Src.Stmt s -> do
      s' <- transTermStmt (TStmt (Posd p s) ps)
      gen fl (s':sl)
    Src.FunctionDecl d -> gen (unnestedFunction d sl:fl) []
    Src.ClassDecl _ -> failAt p "MATLAB.hs@processStmt: not implemented yet (TODO)"
    Src.EndStmt -> failAt p unexpectedEnd

groupUnnestedFns :: PositionMonad m
                 => ([Function] -> [ResolvedStmt] -> m a)
                 -> [TermStmt Src.TopStmt]
                 -> m a
groupUnnestedFns gen [] = gen [] []
groupUnnestedFns gen (ts:r) = do
  groupUnnestedFns (processStmt gen ts) r

-- | A data structure for traversing statements to identify local functions.
data LocalFunctionStack
   = TopIFn (Seq Function)
      -- | This identifies a place where a local function was found.
      --
      -- The first argument contains functions  above this on the stack.
      -- The second argument is the current function declaration.
      -- The third arugment contains statements in the current function
      -- The last argument contains nested functions found beneath this one.
   | StackIFn LocalFunctionStack
              FunctionDecl
              (Seq ResolvedStmt)
              (Seq Function)

-- | Attempt to extract functions from stack.
extractNested :: Monad m => LocalFunctionStack -> m [Function]
extractNested (TopIFn f) = return (Fold.toList f)
extractNested (StackIFn _ d _ _) =
  fail $ "Input ended before " ++ show (val (fnName d)) ++ " was terminated."

-- | Append a function to the local function stack.
appendFn :: LocalFunctionStack -> Function -> LocalFunctionStack
appendFn (TopIFn f) fn = TopIFn (f Seq.|> fn)
appendFn (StackIFn stk d sfn nested_fns) fn = StackIFn stk d sfn (nested_fns Seq.|> fn)

-- | Resolve nested functions.
resolveNested :: PositionMonad m
              => LocalFunctionStack
                 -- ^ We have identified a local function.
              -> TermStmt Src.TopStmt
                 -- ^ Next statement to parse.
              -> m LocalFunctionStack
-- Fail if a class declaration is encountered
resolveNested _ (TStmt (Posd p (Src.ClassDecl _)) _) =
  failAt p "Unexpected class declaration inside function."
-- Start parsing another function when we have encountered a nested function.
resolveNested fns (TStmt (Posd _ (Src.FunctionDecl d)) _) =
  return $ StackIFn fns d Seq.empty Seq.empty
-- Append a statement to a function.
resolveNested stk' (TStmt (Posd p (Src.Stmt s)) pr) = do
  stmt <- transTermStmt (TStmt (Posd p s) pr)
  case stk' of
    TopIFn _ -> failAt p "Unexpected statement outside function."
    StackIFn stk d sfn nested_fns -> do
      return $ StackIFn stk d (sfn Seq.|> stmt) nested_fns
-- End the current statement.
resolveNested stk' (TStmt (Posd p Src.EndStmt) _) =
  case stk' of
    TopIFn _ -> failAt p unexpectedEnd
    StackIFn stk d stmt_fn nested_fns -> do
      let fn = Function d (Fold.toList stmt_fn) (Fold.toList nested_fns)
      return $ appendFn stk fn

-- | Resolve a list of functions.
--
-- Note this only does matching it does not check names are unique.
resolveFns :: PositionMonad m
           => FunctionDecl
           -> [TermStmt Src.TopStmt]
           -> m [Function]
resolveFns d tstmts
  | any isEnd tstmts = do
      let fns = StackIFn (TopIFn Seq.empty) d Seq.empty Seq.empty
      lcls <- foldM resolveNested fns tstmts
      extractNested lcls
  | otherwise = do
      let gen fl sl = pure (unnestedFunction d sl : fl)
      groupUnnestedFns gen tstmts

newtype Trans a = Trans { unTrans :: Either ErrorWithPos a }

instance Functor Trans where
  fmap = liftM

instance Applicative Trans where
  pure = return
  (<*>) = ap

instance Monad Trans where
  Trans (Left e) >>= _ = Trans (Left e)
  Trans (Right v) >>= h = h v

  return v = Trans (Right v)
  fail msg = Trans (Left (ErrorWithPos msg Nothing))

instance PositionMonad Trans where
  failAt p msg = Trans (Left (ErrorWithPos msg (Just p)))

-- | Parse a program as a list of statements.
transScript :: Src.Program -> Trans [ResolvedStmt]
transScript (Src.Program tstmts _) =
  traverse (transTermStmt <=< getScriptStmt) tstmts

-- | This translates a source program into a module.
transProgram :: Src.Program -> Trans Module
transProgram (Src.Program (TStmt (Posd _ (Src.ClassDecl c)) _ : _) _) = do
  -- Class module case:
  --
  -- multiple statements, the first one being a class definition;
  -- this file is a module that defines a class
  rc <- ResolvedClassDef
          <$> pure (Src.clIdent c)
          <*> mapM resolveAttr (Src.clAttributes c)
          <*> pure (Src.clSuperclasses c)
          <*> mapM (Tr.sequence . fmap resolveMB) (Src.clMemberBlocks c)
  return $ ClassModule rc
transProgram (Src.Program (TStmt (Posd _ (Src.FunctionDecl d)) _ : tstmts) p) = do
  -- Function module case:
  --
  -- multiple statements, the first one being a function declaration;
  -- this file is a module that defines a function
  fns <- resolveFns d tstmts
  case findDuplicatesUnder (val . fnName . fnDecl) fns of
    Nothing -> return ()
    Just (f,g) -> do
      let nm  = val (fnName (fnDecl f))
      let p_f = pos (fnName (fnDecl f))
      let p_g = pos (fnName (fnDecl g))
      failAt p_f $
        show nm ++ " is declared on both lines " ++ show (posLine p_g)
          ++ " and " ++ show (posLine p_f) ++ "."

  case fns of
    [] -> failAt p "Expected at least one function."
    (fn:internal_fns) -> return $ FunctionModule fn internal_fns
transProgram p =
  -- Script module case:
  --
  -- otherwise, this is just some file containing MATLAB statements
  ScriptModule <$> transScript p

ppErrorWithPos :: ErrorWithPos -> String
ppErrorWithPos (ErrorWithPos msg (Just p)) =
  "Error at " ++ show p ++ "\n  " ++ msg
ppErrorWithPos (ErrorWithPos msg Nothing) = "Error: " ++ msg

-- | This parses a module.
parseModule :: FilePath -> LazyBS.ByteString -> Either String Module
parseModule path contents =
  case runAlex path contents parse of
    Left (p,msg) -> Left $ "Parse error at " ++ show p ++ ":\n  " ++ msg
    Right pgm ->
      case unTrans (transProgram pgm) of
        Left e  -> Left $ ppErrorWithPos e
        Right m -> Right m

-- | This parses a file as a script.
parseScript :: FilePath -> LazyBS.ByteString -> Either ErrorWithPos [ResolvedStmt]
parseScript path contents =
  case runAlex path contents parse of
    Left (p,msg) -> Left $ ErrorWithPos msg (Just p)
    Right pgm ->
      case unTrans (transScript pgm) of
        Left e -> Left e
        Right stmts -> Right stmts
