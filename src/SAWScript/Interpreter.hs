{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if !MIN_VERSION_base(4,8,0)
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.Interpreter
  ( interpret
  , interpretDeclGroup
  , interpretStmt
  , interpretFile
  , buildTopLevelEnv
  , extendEnv
  , Value, isVUnit
  , IsValue(..)
  , primTypeEnv
  , primDocEnv
  , processFile
  )
  where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable hiding ( mapM )
#endif
import qualified Control.Exception as X
import Control.Monad (foldM, unless, (>=>))
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Map ( Map )

import qualified SAWScript.AST as SS
import SAWScript.AST (Located(..))
import SAWScript.Builtins
import SAWScript.Compiler (reportErrT)
import qualified SAWScript.CryptolEnv as CEnv
import qualified SAWScript.Import
import SAWScript.JavaBuiltins
import SAWScript.JavaExpr
import SAWScript.LLVMBuiltins
import SAWScript.Options
import SAWScript.Lexer (lexSAW)
import SAWScript.MGU (checkDecl, checkDeclGroup)
import SAWScript.Parser (parseSchema)
import SAWScript.Proof
import SAWScript.TopLevel
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value
import Verifier.SAW.Conversion
import Verifier.SAW.Prelude (preludeModule)
--import Verifier.SAW.PrettySExp
import Verifier.SAW.Prim (EvalError)
import Verifier.SAW.Rewriter ( Simpset, emptySimpset, rewritingSharedContext
                             , scSimpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.Java.Codebase as JCB
import qualified Verifier.Java.SAWBackend as JavaSAW
import qualified Verifier.LLVM.Backend.SAW as LLVMSAW

import qualified Verifier.SAW.Cryptol as Cryptol
import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import Cryptol.ModuleSystem.Env (meSolverConfig)
import Cryptol.TypeCheck (SolverConfig)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.TypeCheck.PP (ppWithNames)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listSubst)
import Cryptol.Utils.PP
import qualified Cryptol.Eval.Value as V (defaultPPOpts, ppValue, PPOpts(..))

import qualified Text.PrettyPrint.ANSI.Leijen as PP

import SAWScript.AutoMatch

-- Environment -----------------------------------------------------------------

maybeInsert :: Ord k => k -> Maybe a -> Map k a -> Map k a
maybeInsert _ Nothing m = m
maybeInsert k (Just x) m = Map.insert k x m

extendEnv :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> TopLevelRW -> TopLevelRW
extendEnv x mt md v rw =
  rw { rwValues  = Map.insert name v (rwValues rw)
     , rwTypes   = maybeInsert name mt (rwTypes rw)
     , rwDocs    = maybeInsert (getVal name) md (rwDocs rw)
     , rwCryptol = ce'
     }
  where
    name = x
    qname = T.mkUnqual (T.mkName (getOrig x))
    modname = T.mkModName [getOrig x]
    ce = rwCryptol rw
    ce' = case v of
            VTerm t
              -> CEnv.bindTypedTerm (qname, t) ce
            VType s
              -> CEnv.bindType (qname, s) ce
            VInteger n
              -> CEnv.bindInteger (qname, n) ce
            VCryptolModule m
              -> CEnv.bindCryptolModule (modname, m) ce
            _ -> ce

-- | Variation that does not force the value argument: it assumes it
-- is not a term or int.
extendEnv' :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> TopLevelRW -> TopLevelRW
extendEnv' x mt md v rw =
  rw { rwValues  = Map.insert x v (rwValues rw)
     , rwTypes   = maybeInsert x mt (rwTypes rw)
     , rwDocs    = maybeInsert (getVal x) md (rwDocs rw)
     }

-- Interpretation of SAWScript -------------------------------------------------

interpret :: TopLevelRO -> TopLevelRW -> SS.Expr -> IO Value
interpret ro rw expr =
    case expr of
      SS.Bit b               -> return $ VBool b
      SS.String s            -> return $ VString s
      SS.Z z                 -> return $ VInteger z
      SS.Code str            -> toValue `fmap` CEnv.parseTypedTerm sc (rwCryptol rw) str
      SS.CType str           -> toValue `fmap` CEnv.parseSchema (rwCryptol rw) str
      SS.Array es            -> VArray <$> traverse (interpret ro rw) es
      SS.Block stmts         -> interpretStmts ro rw stmts
      SS.Tuple es            -> VTuple <$> traverse (interpret ro rw) es
      SS.Record bs           -> VRecord <$> traverse (interpret ro rw) bs
      SS.Index e1 e2         -> do a <- interpret ro rw e1
                                   i <- interpret ro rw e2
                                   return (indexValue a i)
      SS.Lookup e n          -> do a <- interpret ro rw e
                                   return (lookupValue a n)
      SS.TLookup e i         -> do a <- interpret ro rw e
                                   return (tupleLookupValue a i)
      SS.Var x               -> case Map.lookup x (rwValues rw) of
                                  Nothing -> fail $ "unknown variable: " ++ SS.getVal x
                                  Just v -> return v

      SS.Function x t e      -> do let rw' v = extendEnv x (fmap SS.tMono t) Nothing v rw
                                       f v = interpret ro (rw' v) e
                                   return $ VLambda f
      SS.Application e1 e2   -> do v1 <- interpret ro rw e1
                                   v2 <- interpret ro rw e2
                                   case v1 of
                                     VLambda f -> f v2
                                     _ -> fail $ "interpret Application: " ++ show v1
      SS.Let dg e            -> do rw' <- interpretDeclGroup ro rw dg
                                   interpret ro rw' e
      SS.TSig e _            -> interpret ro rw e

  where sc = roSharedContext ro

interpretDecl :: TopLevelRO -> TopLevelRW -> SS.Decl -> IO TopLevelRW
interpretDecl ro rw (SS.Decl n mt expr) = do
  v <- interpret ro rw expr
  return (extendEnv n mt Nothing v rw)

interpretFunction :: TopLevelRO -> TopLevelRW -> SS.Expr -> Value
interpretFunction ro rw expr =
    case expr of
      SS.Function x t e -> VLambda f
        where f v = interpret ro (extendEnv x (fmap SS.tMono t) Nothing v rw) e
      SS.TSig e _ -> interpretFunction ro rw e
      _ -> error "interpretFunction: not a function"

interpretDeclGroup :: TopLevelRO -> TopLevelRW -> SS.DeclGroup -> IO TopLevelRW
interpretDeclGroup ro rw (SS.NonRecursive d) =
  interpretDecl ro rw d
interpretDeclGroup ro rw (SS.Recursive ds) = return rw'
  where rw' = foldr ($) rw [ extendEnv' n mty Nothing (interpretFunction ro rw' e) | SS.Decl n mty e <- ds ]

interpretStmts :: TopLevelRO -> TopLevelRW -> [SS.Stmt] -> IO Value
interpretStmts ro rw stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.StmtBind Nothing _ _ e] -> interpret ro rw e
      SS.StmtBind Nothing _ _ e : ss ->
          do v1 <- interpret ro rw e
             return $ VBind v1 $ VLambda $ const $ interpretStmts ro rw ss
      SS.StmtBind (Just x) mt _ e : ss ->
          do v1 <- interpret ro rw e
             let f v = interpretStmts ro (extendEnv x (fmap SS.tMono mt) Nothing v rw) ss
             bindValue v1 (VLambda f)
      SS.StmtLet bs : ss -> interpret ro rw (SS.Let bs (SS.Block ss))
      SS.StmtCode s : ss ->
          do ce' <- CEnv.parseDecls sc (rwCryptol rw) s
             interpretStmts ro rw{rwCryptol = ce'} ss
      SS.StmtImport _ : _ ->
          do fail "block import unimplemented"
  where sc = roSharedContext ro

processStmtBind :: Bool -> TopLevelRO -> TopLevelRW -> Maybe SS.LName
                 -> Maybe SS.Type -> Maybe SS.Type -> SS.Expr -> IO TopLevelRW
processStmtBind printBinds ro rw mx mt _mc expr = do
  let it = SS.Located "it" "it" PosREPL
  let lname = maybe it id mx
  let ctx = SS.tContext SS.TopLevel
  let expr' = case mt of
                Nothing -> expr
                Just t -> SS.TSig expr (SS.tBlock ctx t)
  let decl = SS.Decl lname Nothing expr'
  let opts = rwPPOpts rw

  SS.Decl _ (Just schema) expr'' <- reportErrT $ checkDecl (rwTypes rw) decl

  val <- interpret ro rw expr''

  -- Run the resulting TopLevel action.
  (result, ty, rw') <-
    case schema of
      SS.Forall [] t ->
        case t of
          SS.TyCon SS.BlockCon [c, t'] | c == ctx -> do
            (result, rw') <- runTopLevel (SAWScript.Value.fromValue val) ro rw
            return (result, t', rw')
          _ -> return (val, t, rw)
      _ -> fail $ "Not a monomorphic type: " ++ SS.pShow schema

  -- Print non-unit result if it was not bound to a variable
  case mx of
    Nothing | printBinds && not (isVUnit result) -> putStrLn (showsPrecValue opts 0 result "")
    _                                            -> return ()

  -- Print function type if result was a function
  case ty of
    SS.TyCon SS.FunCon _ -> putStrLn $ getVal lname ++ " : " ++ SS.pShow ty
    _ -> return ()

  let rw'' = extendEnv lname (Just (SS.tMono ty)) Nothing result rw'
  return rw''

-- | Interpret a block-level statement in the TopLevel monad.
interpretStmt :: Bool -> TopLevelRO -> TopLevelRW -> SS.Stmt -> IO TopLevelRW
interpretStmt printBinds ro rw stmt =
  case stmt of
    SS.StmtBind mx mt mc expr -> processStmtBind printBinds ro rw mx mt mc expr
    SS.StmtLet dg             -> do dg' <- reportErrT (checkDeclGroup (rwTypes rw) dg)
                                    interpretDeclGroup ro rw dg'
    SS.StmtCode lstr          -> do cenv' <- CEnv.parseDecls sc (rwCryptol rw) lstr
                                    return rw { rwCryptol = cenv' }
    SS.StmtImport imp         -> do cenv' <- CEnv.importModule sc (rwCryptol rw) imp
                                    return rw { rwCryptol = cenv' }
  where sc = roSharedContext ro

interpretFile :: TopLevelRO -> TopLevelRW -> FilePath -> IO TopLevelRW
interpretFile ro rw file = do
  stmts <- SAWScript.Import.loadFile (roOptions ro) file
  foldM (interpretStmt False ro) rw stmts

-- | Evaluate the value called 'main' from the current environment.
interpretMain :: TopLevelRO -> TopLevelRW -> IO ()
interpretMain ro rw =
  case Map.lookup mainName (rwValues rw) of
    Nothing -> return () -- fail "No 'main' defined"
    Just v -> fst <$> runTopLevel (fromValue v) ro rw
  where mainName = Located "main" "main" (PosInternal "entry")

buildTopLevelEnv :: Options -> IO (BuiltinContext, TopLevelRO, TopLevelRW)
buildTopLevelEnv opts =
    do let mn = mkModuleName ["SAWScript"]
       let scm = insImport preludeModule $
                 insImport JavaSAW.javaModule $
                 insImport LLVMSAW.llvmModule $
                 insImport CryptolSAW.cryptolModule $
                 emptyModule mn
       sc0 <- mkSharedContext scm
       let convs = natConversions
                   ++ bvConversions
                   ++ vecConversions
                   ++ [ tupleConversion
                      , recordConversion
                      , remove_ident_coerce
                      , remove_ident_unsafeCoerce
                      ]
       simps <- scSimpset sc0 [] [] convs
       let sc = rewritingSharedContext sc0 simps
       ss <- basic_ss sc
       jcb <- JCB.loadCodebase (jarList opts) (classPath opts)
       let ro0 = TopLevelRO
                   { roSharedContext = sc
                   , roJavaCodebase = jcb
                   , roOptions = opts
                   }
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biJavaCodebase = jcb
                 }
       let vm0 = Map.insert (qualify "basic_ss") (toValue ss) (valueEnv opts bic)
       let tm0 = Map.insert (qualify "basic_ss") (readSchema "Simpset") primTypeEnv
       ce0 <- CEnv.initCryptolEnv sc
       let rw0 = TopLevelRW
                   { rwValues   = vm0
                   , rwTypes    = tm0
                   , rwDocs     = primDocEnv
                   , rwCryptol  = ce0
                   , rwPPOpts   = defaultPPOpts
                   }
       return (bic, ro0, rw0)

processFile :: Options -> FilePath -> IO ()
processFile opts file = do
  (_, ro, rw) <- buildTopLevelEnv opts
  rw' <- interpretFile ro rw file
  interpretMain ro rw'

-- Primitives ------------------------------------------------------------------

include_value :: FilePath -> TopLevel ()
include_value file = do
  ro <- getTopLevelRO
  rw <- getTopLevelRW
  rw' <- io $ interpretFile ro rw file
  putTopLevelRW rw'

set_ascii :: Bool -> TopLevel ()
set_ascii b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsAscii = b } }

set_base :: Int -> TopLevel ()
set_base b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsBase = b } }

print_value :: Value -> TopLevel ()
print_value (VString s) = io $ putStrLn s
print_value (VTerm t) = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = meSolverConfig (CEnv.eModuleEnv cenv)
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  t' <- io $ defaultTypedTerm sc cfg t
  opts <- fmap rwPPOpts getTopLevelRW
  let opts' = V.defaultPPOpts { V.useAscii = ppOptsAscii opts
                              , V.useBase = ppOptsBase opts
                              }
  io $ rethrowEvalError $ print $ V.ppValue opts' (evaluateTypedTerm sc t')
print_value v = do
  opts <- fmap rwPPOpts getTopLevelRW
  io $ putStrLn (showsPrecValue opts 0 v "")

rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalError -> IO a
  rethrow exn = fail (show exn) -- X.throwIO (EvalError exn)

-- | Default the values of the type variables in a typed term.
defaultTypedTerm :: SharedContext s -> SolverConfig -> TypedTerm s -> IO (TypedTerm s)
defaultTypedTerm sc cfg (TypedTerm schema trm) = do
  mdefault <- defaultReplExpr cfg undefined schema
  let inst = do (soln, _) <- mdefault
                mapM (`lookup` soln) (T.sVars schema)
  case inst of
    Nothing -> return (TypedTerm schema trm)
    Just tys -> do
      let vars = T.sVars schema
      let nms = T.addTNames vars IntMap.empty
      mapM_ (warnDefault nms) (zip vars tys)
      xs <- mapM (Cryptol.importType sc Cryptol.emptyEnv) tys
      let tm = Map.fromList [ (T.tpUnique tp, (t, 0)) | (tp, t) <- zip (T.sVars schema) xs ]
      let env = Cryptol.emptyEnv { Cryptol.envT = tm }
      ys <- mapM (Cryptol.proveProp sc env) (T.sProps schema)
      trm' <- scApplyAll sc trm (xs ++ ys)
      let su = listSubst (zip (map T.tpVar vars) tys)
      let schema' = T.Forall [] [] (apSubst su (T.sType schema))
      return (TypedTerm schema' trm')
  where
    warnDefault ns (x,t) =
      print $ text "Assuming" <+> ppWithNames ns x <+> text "=" <+> pp t

readSchema :: String -> SS.Schema
readSchema str =
  case parseSchema (lexSAW "internal" str) of
    Left err -> error (show err)
    Right schema -> schema

data Primitive
  = Primitive
    { primName :: SS.LName
    , primType :: SS.Schema
    , primDoc  :: [String]
    , primFn   :: Options -> BuiltinContext -> Value
    }

primitives :: Map SS.LName Primitive
primitives = Map.fromList
  [ prim "return"              "{m, a} a -> m a"
    (pureVal VReturn)
    [ "Yield a value in a command context. The command"
    , "    x <- return e"
    ,"will result in the same value being bound to 'x' as the command"
    , "    let x = e"
    ]

  , prim "true"                "Bool"
    (pureVal True)
    [ "A boolean value." ]

  , prim "false"               "Bool"
    (pureVal False)
    [ "A boolean value." ]

  , prim "for"                 "{m, a, b} [a] -> (a -> m b) -> m [b]"
    (pureVal (VLambda . forValue))
    [ "Apply the given command in sequence to the given list. Return"
    , "the list containing the result returned by the command at each"
    , "iteration."
    ]

  , prim "str_concat"          "String -> String -> String"
    (pureVal ((++) :: String -> String -> String))
    [ "Concatenate two strings to yield a third." ]

  , prim "define"              "String -> Term -> TopLevel Term"
    (pureVal definePrim)
    [ "Wrap a term with a name that allows its body to be hidden or"
    , "revealed. This can allow any sub-term to be treated as an"
    , "uninterpreted function during proofs."
    ]

  , prim "include"             "String -> TopLevel ()"
    (pureVal include_value)
    [ "Execute the given SAWScript file." ]

  , prim "env"                 "TopLevel ()"
    (pureVal envCmd)
    [ "Print all sawscript values in scope." ]

  , prim "set_ascii"           "Bool -> TopLevel ()"
    (pureVal set_ascii)
    [ "Select whether to pretty-print arrays of 8-bit numbers as ascii strings." ]

  , prim "set_base"            "Int -> TopLevel ()"
    (pureVal set_base)
    [ "Set the number base for pretty-printing numeric literals."
    , "Permissible values include 2, 8, 10, and 16." ]

  , prim "print"               "{a} a -> TopLevel ()"
    (pureVal print_value)
    [ "Print the value of the given expression." ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
    [ "Pretty-print the given term in SAWCore syntax." ]

  , prim "print_term_depth"    "Int -> Term -> TopLevel ()"
    (pureVal ((\d -> print . ppTermDepth d) :: Int -> SharedTerm SAWCtx -> IO ()))
    [ "Pretty-print the given term in SAWCore syntax up to a given depth." ]

{-
  , prim "print_term_sexp"     "Term -> TopLevel ()"
    (pureVal ((print . ppSharedTermSExp) :: SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_term_sexp'"    "Int -> Term -> TopLevel ()"
    (pureVal printTermSExp')
    [ "TODO" ]
-}

  , prim "dump_file_AST"       "String -> TopLevel ()"
    (bicVal $ const $ \opts -> SAWScript.Import.loadFile opts >=> mapM_ print)
    [ "Dump a pretty representation of the SAWScript AST for a file." ]

  , prim "parser_printer_roundtrip"       "String -> TopLevel ()"
    (bicVal $ const $
      \opts -> SAWScript.Import.loadFile opts >=>
               PP.putDoc . SS.prettyWholeModule)
    [ "Parses the file as SAWScript and renders the resultant AST back to SAWScript concrete syntax." ]

  , prim "print_type"          "Term -> TopLevel ()"
    (pureVal print_type)
    [ "Print the type of the given term." ]

  , prim "type"                "Term -> Type"
    (pureVal (ttSchema :: TypedTerm SAWCtx -> T.Schema))
    [ "Return the type of the given term." ]

  , prim "show_term"           "Term -> String"
    (pureVal (scPrettyTerm :: SharedTerm SAWCtx -> String))
    [ "Pretty-print the given term in SAWCore syntax, yielding a String." ]

  , prim "check_term"          "Term -> TopLevel ()"
    (pureVal check_term)
    [ "Type-check the given term, printing an error message if ill-typed." ]

  , prim "term_size"           "Term -> Int"
    (pureVal (scSharedSize :: SharedTerm SAWCtx -> Integer))
    [ "Return the size of the given term in the number of DAG nodes." ]

  , prim "term_tree_size"      "Term -> Int"
    (pureVal (scTreeSize :: SharedTerm SAWCtx -> Integer))
    [ "Return the size of the given term in the number of nodes it would"
    , "have if treated as a tree instead of a DAG."
    ]

  , prim "abstract_symbolic"   "Term -> TopLevel Term"
    (pureVal abstractSymbolicPrim)
    [ "Take a term containing symbolic variables of the form returned"
    , "by 'fresh_symbolic' and return a new lambda term in which those"
    , "variables have been replaced by parameter references."
    ]

  , prim "fresh_symbolic"      "String -> Type -> TopLevel Term"
    (pureVal freshSymbolicPrim)
    [ "Create a fresh symbolic variable of the given type. The given name"
    , "is used only for pretty-printing."
    ]

  , prim "sbv_uninterpreted"   "String -> Term -> TopLevel Uninterp"
    (pureVal sbvUninterpreted)
    [ "Indicate that the given term should be used as the definition of the"
    , "named function when loading an SBV file. This command returns an"
    , "object that can be passed to 'read_sbv'."
    ]

  , prim "check_convertable"  "Term -> Term -> TopLevel ()"
    (pureVal checkConvertablePrim)
    [ "Check if two terms are convertable" ]

  , prim "replace"             "Term -> Term -> Term -> TopLevel Term"
    (pureVal replacePrim)
    [ "'replace x y z' rewrites occurences of term x into y inside the"
    , "term z.  x and y must be closed terms."
    ]

  , prim "hoist_ifs"            "Term -> TopLevel Term"
    (pureVal hoistIfsPrim)
    [ "Hoist all if-then-else expressions as high as possible." ]

  , prim "read_bytes"          "String -> TopLevel Term"
    (pureVal readBytes)
    [ "Read binary file as a value of type [n][8]." ]

  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term"
    (pureVal readSBV)
    [ "Read an SBV file produced by Cryptol 1, using the given set of"
    , "overrides for any uninterpreted functions that appear in the file."
    ]

  , prim "load_aig"            "String -> TopLevel AIG"
    (pureVal loadAIGPrim)
    [ "Read an AIG file in binary AIGER format, yielding an AIG value." ]
  , prim "save_aig"            "String -> AIG -> TopLevel ()"
    (pureVal saveAIGPrim)
    [ "Write an AIG to a file in binary AIGER format." ]
  , prim "save_aig_as_cnf"     "String -> AIG -> TopLevel ()"
    (pureVal saveAIGasCNFPrim)
    [ "Write an AIG representing a boolean function to a file in DIMACS"
    , "CNF format."
    ]

  , prim "dsec_print"                "Term -> Term -> TopLevel ()"
    (scVal dsecPrint)
    [ "Use ABC's 'dsec' command to compare two terms as SAIGs."
    , "The terms must have a type as described in ':help write_saig',"
    , "i.e. of the form '(i, s) -> (o, s)'. Note that nothing is returned:"
    , "you must read the output to see what happened."
    , ""
    , "You must have an 'abc' executable on your PATH to use this command."
    ]

  , prim "cec"                 "AIG -> AIG -> TopLevel ProofResult"
    (pureVal cecPrim)
    [ "Perform a Combinitorial Equivalance Check between two AIGs."
    , "The AIGs must have the same number of inputs and outputs."
    ]

  , prim "bitblast"            "Term -> TopLevel AIG"
    (scVal bitblastPrim)
    [ "Translate a term into an AIG.  The term must be representable as a"
    , "function from a finite number of bits to a finite number of bits."
    ]

  , prim "read_aig"            "String -> TopLevel Term"
    (pureVal readAIGPrim)
    [ "Read an AIG file in AIGER format and translate to a term." ]

  , prim "read_core"           "String -> TopLevel Term"
    (pureVal readCore)
    [ "Read a term from a file in the SAWCore external format." ]

  , prim "write_aig"           "String -> Term -> TopLevel ()"
    (scVal writeAIG)
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits."
    ]

  , prim "write_saig"          "String -> Term -> TopLevel ()"
    (scVal writeSAIGInferLatches)
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits. The type must be of the form"
    , "'(i, s) -> (o, s)' and is interpreted as an '[|i| + |s|] -> [|o| + |s|]'"
    , "AIG with '|s|' latches."
    , ""
    , "Arguments:"
    , "  file to translation to : String"
    , "  function to translate to sequential AIG : Term"
    ]

  , prim "write_saig'"         "String -> Term -> Term -> TopLevel ()"
    (scVal writeAIGComputedLatches)
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits, '[m] -> [n]'. The int argument,"
    , "'k', must be at most 'min {m, n}', and specifies that the *last* 'k'"
    , "input and output bits are joined as latches."
    , ""
    , "Arguments:"
    , "  file to translation to : String"
    , "  number of latches : Term"
    , "  function to translate to sequential AIG : Term"
    ]

  , prim "write_cnf"           "String -> Term -> TopLevel ()"
    (scVal writeCNF)
    [ "Write the given term to the named file in CNF format." ]

  , prim "write_smtlib1"       "String -> Term -> TopLevel ()"
    (scVal writeSMTLib1)
    [ "Write the given term to the named file in SMT-Lib version 1 format." ]

  , prim "write_smtlib2"       "String -> Term -> TopLevel ()"
    (scVal writeSMTLib2)
    [ "Write the given term to the named file in SMT-Lib version 2 format." ]

  , prim "write_core"          "String -> Term -> TopLevel ()"
    (pureVal (writeCore :: FilePath -> TypedTerm SAWCtx -> IO ()))
    [ "Write out a representation of a term in SAWCore external format." ]

  , prim "auto_match" "String -> String -> TopLevel ()"
    (pureVal (autoMatch interpretStmts :: FilePath -> FilePath -> TopLevel ()))
    [ "Interactively decides how to align two modules of potentially heterogeneous"
    , "language and prints the result."
    ]

  , prim "prove"               "ProofScript SatResult -> Term -> TopLevel ProofResult"
    (scVal provePrim)
    [ "Use the given proof script to attempt to prove that a term is valid"
    , "(true for all inputs). Returns a proof result that can be analyzed"
    , "with 'caseProofResult' to determine whether it represents a successful"
    , "proof or a counter-example."
    ]

  , prim "prove_print"         "ProofScript SatResult -> Term -> TopLevel Theorem"
    (scVal provePrintPrim)
    [ "Use the given proof script to attempt to prove that a term is valid"
    , "(true for all inputs). Returns a Theorem if successful, and aborts"
    , "if unsuccessful."
    ]

  , prim "sat"                 "ProofScript SatResult -> Term -> TopLevel SatResult"
    (scVal satPrim)
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (true for any input). Returns a proof result that can"
    , "be analyzed with 'caseSatResult' to determine whether it represents"
    , "a satisfiying assignment or an indication of unsatisfiability."
    ]

  , prim "sat_print"           "ProofScript SatResult -> Term -> TopLevel ()"
    (scVal satPrintPrim)
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (true for any input). Returns nothing if successful, and"
    , "aborts if unsuccessful."
    ]

  , prim "qc_print"            "Int -> Term -> TopLevel ()"
    (scVal quickCheckPrintPrim)
    [ "Quick Check a term by applying it to a sequence of random inputs"
    , "and print the results. The 'Int' arg specifies how many tests to run."
    ]

  , prim "codegen"             "String -> String -> Term -> TopLevel ()"
    (scVal codegenSBV)
    [ "Generate straight-line C code for the given term using SBV."
    , ""
    , "First argument is directory path (\"\" for stdout) for generating files."
    , "Second argument is C function name."
    , "Third argument is the term to generated code for. It must be a"
    , "first-order function whose arguments and result are all of type"
    , "Bit, [8], [16], [32], or [64]."
    ]

  , prim "unfolding"           "[String] -> ProofScript ()"
    (scVal unfoldGoal)
    [ "Unfold the named subterm(s) within the current goal." ]

  , prim "simplify"            "Simpset -> ProofScript ()"
    (scVal simplifyGoal)
    [ "Apply the given simplifier rule set to the current goal." ]

  , prim "beta_reduce_goal"    "ProofScript ()"
    (scVal beta_reduce_goal)
    [ "Reduce the current goal to beta-normal form." ]

  , prim "print_goal"          "ProofScript ()"
    (pureVal (printGoal :: ProofScript SAWCtx ()))
    [ "Print the current goal that a proof script is attempting to prove." ]

  , prim "print_goal_depth"    "Int -> ProofScript ()"
    (pureVal printGoalDepth)
    [ "Print the current goal that a proof script is attempting to prove,"
    , "limited to a maximum depth."
    ]
  , prim "print_goal_consts"   "ProofScript ()"
    (pureVal printGoalConsts)
    [ "Print the list of unfoldable constants in the current proof goal."
    ]
{-
  , prim "print_goal_sexp"     "ProofScript ()"
    (pureVal printGoalSExp)
    [ "TODO" ]

  , prim "print_goal_sexp'"    "Int -> ProofScript ()"
    (pureVal printGoalSExp')
    [ "TODO" ]
-}

  , prim "assume_valid"        "ProofScript ProofResult"
    (pureVal (assumeValid :: ProofScript SAWCtx ProofResult))
    [ "Assume the current goal is valid, completing the proof." ]

  , prim "assume_unsat"        "ProofScript SatResult"
    (pureVal (assumeUnsat :: ProofScript SAWCtx SatResult))
    [ "Assume the current goal is unsatisfiable, completing the proof." ]

  , prim "quickcheck"          "Int -> ProofScript SatResult"
    (scVal quickcheckGoal)
    [ "Quick Check the current goal by applying it to a sequence of random"
    , "inputs. Fail the proof script if the goal returns 'False' for any"
    , "of these inputs."
    ]

  , prim "abc"                 "ProofScript SatResult"
    (scVal satABC)
    [ "Use the ABC theorem prover to prove the current goal." ]

  , prim "boolector"           "ProofScript SatResult"
    (scVal satBoolector)
    [ "Use the Boolector theorem prover to prove the current goal." ]

  , prim "cvc4"                "ProofScript SatResult"
    (scVal satCVC4)
    [ "Use the CVC4 theorem prover to prove the current goal." ]

  , prim "z3"                  "ProofScript SatResult"
    (scVal satZ3)
    [ "Use the Z3 theorem prover to prove the current goal." ]

  , prim "mathsat"             "ProofScript SatResult"
    (scVal satMathSAT)
    [ "Use the MathSAT theorem prover to prove the current goal." ]

  , prim "yices"               "ProofScript SatResult"
    (scVal satYices)
    [ "Use the Yices theorem prover to prove the current goal." ]

  , prim "unint_z3"            "[String] -> ProofScript SatResult"
    (scVal satUnintZ3)
    [ "Use the Z3 theorem prover to prove the current goal. Leave the"
    , "given list of names, as defined with 'define', as uninterpreted."
    ]

  , prim "offline_aig"         "String -> ProofScript SatResult"
    (scVal satAIG)
    [ "Write the current goal to the given file in AIGER format." ]

  , prim "offline_cnf"         "String -> ProofScript SatResult"
    (scVal satCNF)
    [ "Write the current goal to the given file in CNF format." ]

  , prim "offline_extcore"     "String -> ProofScript SatResult"
    (scVal satExtCore)
    [ "Write the current goal to the given file in SAWCore format." ]

  , prim "offline_smtlib1"     "String -> ProofScript SatResult"
    (scVal satSMTLib1)
    [ "Write the current goal to the given file in SMT-Lib1 format." ]

  , prim "offline_smtlib2"     "String -> ProofScript SatResult"
    (scVal satSMTLib2)
    [ "Write the current goal to the given file in SMT-Lib2 format." ]

  , prim "external_cnf_solver" "String -> [String] -> ProofScript SatResult"
    (scVal (satExternal True))
    [ "Use an external SAT solver supporting CNF to prove the current goal."
    , "The first argument is the executable name of the solver, and the"
    , "second is the list of arguments to pass to the solver. The string '%f'"
    , "anywhere in the argument list will be replaced with the name of the"
    , "temporary file holding the CNF version of the formula."]

  , prim "external_aig_solver" "String -> [String] -> ProofScript SatResult"
    (scVal (satExternal False))
    [ "Use an external SAT solver supporting AIG to prove the current goal."
    , "The first argument is the executable name of the solver, and the"
    , "second is the list of arguments to pass to the solver. The string '%f'"
    , "anywhere in the argument list will be replaced with the name of the"
    , "temporary file holding the AIG version of the formula."]

  , prim "trivial"             "ProofScript SatResult"
    (pureVal trivial)
    [ "Succeed only if the proof goal is a literal 'True'." ]

  , prim "empty_ss"            "Simpset"
    (pureVal (emptySimpset :: Simpset (SharedTerm SAWCtx)))
    [ "The empty simplification rule set, containing no rules." ]

  , prim "cryptol_ss"          "TopLevel Simpset"
    (scVal cryptolSimpset)
    [ "A set of simplification rules that will expand definitions from the"
    , "Cryptol module."
    ]

  , prim "add_prelude_eqs"     "[String] -> Simpset -> TopLevel Simpset"
    (scVal addPreludeEqs)
    [ "Add the named equality rules from the Prelude module to the given"
    , "simplification rule set."
    ]

  , prim "add_cryptol_eqs"     "[String] -> Simpset -> TopLevel Simpset"
    (scVal addCryptolEqs)
    [ "Add the named equality rules from the Cryptol module to the given"
    , "simplification rule set."
    ]

  , prim "add_prelude_defs"    "[String] -> Simpset -> TopLevel Simpset"
    (scVal addPreludeDefs)
    [ "Add the named definitions from the Prelude module to the given"
    , "simplification rule set."
    ]

  --, prim "basic_ss"            "Simpset"

  , prim "addsimp"             "Theorem -> Simpset -> Simpset"
    (scVal addsimp)
    [ "Add a proved equality theorem to a given simplification rule set." ]

  , prim "addsimp'"            "Term -> Simpset -> Simpset"
    (scVal addsimp')
    [ "Add an arbitrary equality term to a given simplification rule set." ]

  , prim "addsimps"            "[Theorem] -> Simpset -> Simpset"
    (scVal addsimps)
    [ "Add proved equality theorems to a given simplification rule set." ]

  , prim "addsimps'"           "[Term] -> Simpset -> Simpset"
    (scVal addsimps')
    [ "Add arbitrary equality terms to a given simplification rule set." ]

  , prim "rewrite"             "Simpset -> Term -> TopLevel Term"
    (scVal rewritePrim)
    [ "Rewrite a term using a specific simplification rule set, returning"
    , "the rewritten term"
    ]

  , prim "unfold_term"         "[String] -> Term -> TopLevel Term"
    (scVal unfold_term)
    [ "Unfold the definitions of the specified constants in the given term." ]

  , prim "beta_reduce_term"    "Term -> TopLevel Term"
    (scVal beta_reduce_term)
    [ "Reduce the given term to beta-normal form." ]

  , prim "cryptol_load"        "String -> TopLevel CryptolModule"
    (scVal CEnv.loadCryptolModule)
    [ "Load the given file as a Cryptol module." ]

  , prim "cryptol_extract"     "CryptolModule -> String -> TopLevel Term"
    (pureVal (CEnv.lookupCryptolModule :: CryptolModule SAWCtx -> String -> IO (TypedTerm SAWCtx)))
    [ "Load a single definition from a Cryptol module and translate it into"
    , "a 'Term'."
    ]

  -- Java stuff

  , prim "java_bool"           "JavaType"
    (pureVal JavaBoolean)
    [ "The Java type of booleans." ]

  , prim "java_byte"           "JavaType"
    (pureVal JavaByte)
    [ "The Java type of bytes." ]

  , prim "java_char"           "JavaType"
    (pureVal JavaChar)
    [ "The Java type of characters." ]

  , prim "java_short"          "JavaType"
    (pureVal JavaShort)
    [ "The Java type of short integers." ]

  , prim "java_int"            "JavaType"
    (pureVal JavaInt)
    [ "The standard Java integer type." ]

  , prim "java_long"           "JavaType"
    (pureVal JavaLong)
    [ "The Java type of long integers." ]

  , prim "java_float"          "JavaType"
    (pureVal JavaFloat)
    [ "The Java type of single-precision floating point values." ]

  , prim "java_double"         "JavaType"
    (pureVal JavaDouble)
    [ "The Java type of double-precision floating point values." ]

  , prim "java_array"          "Int -> JavaType -> JavaType"
    (pureVal JavaArray)
    [ "The Java type of arrays of a fixed number of elements of the given"
    , "type."
    ]

  , prim "java_class"          "String -> JavaType"
    (pureVal JavaClass)
    [ "The Java type corresponding to the named class." ]

  --, prim "java_value"          "{a} String -> a"

  , prim "java_var"            "String -> JavaType -> JavaSetup Term"
    (bicVal javaVar)
    [ "Return a term corresponding to the initial value of the named Java"
    , "variable, which should have the given type. The returned term can be"
    , "used to construct more complex expressions. For example it can be used"
    , "with 'java_return' to describe the expected return value in terms"
    , "of the initial value of a variable. The Java variable can also be of"
    , "the form \"args[n]\" to refer to the (0-based) nth argument of a method."
    ]

  , prim "java_class_var"      "String -> JavaType -> JavaSetup ()"
    (bicVal javaClassVar)
    [ "Declare that the named Java variable should point to an object of the"
    , "given class type."
    ]

  , prim "java_may_alias"      "[String] -> JavaSetup ()"
    (bicVal javaMayAlias)
    [ "Indicate that the given set of Java variables are allowed to alias"
    , "each other."
    ]

  , prim "java_assert"         "Term -> JavaSetup ()"
    (bicVal javaAssert)
    [ "Assert that the given term should evaluate to true in the initial"
    , "state of a Java method."
    ]

  --, prim "java_assert_eq"      "{a} String -> a -> JavaSetup ()"
  --  (bicVal javaAssertEq)

  , prim "java_ensure_eq"      "String -> Term -> JavaSetup ()"
    (bicVal javaEnsureEq)
    [ "Specify that the given Java variable should have a value equal to the"
    , "given term when execution finishes."
    ]

  , prim "java_modify"         "String -> JavaSetup ()"
    (bicVal javaModify)
    [ "Indicate that a Java method may modify the named portion of the state." ]

  , prim "java_return"         "Term -> JavaSetup ()"
    (bicVal javaReturn)
    [ "Indicate the expected return value of a Java method." ]

  , prim "java_verify_tactic"  "ProofScript SatResult -> JavaSetup ()"
    (bicVal javaVerifyTactic)
    [ "Use the given proof script to prove the specified properties about"
    , "a Java method."
    ]

  , prim "java_sat_branches"   "Bool -> JavaSetup ()"
    (pureVal javaSatBranches)
    [ "Turn on or off satisfiability checking of branch conditions during"
    , "symbolic execution."
    ]

  , prim "java_no_simulate"    "JavaSetup ()"
    (pureVal javaNoSimulate)
    [ "Skip symbolic simulation for this Java method." ]

  , prim "java_allow_alloc"    "JavaSetup ()"
    (pureVal javaAllowAlloc)
    [ "Allow allocation of new objects or arrays during simulation,"
    , "as long as the behavior of the method can still be described"
    , "as a pure function."
    ]

  , prim "java_pure"           "JavaSetup ()"
    (pureVal javaPure)
    [ "The empty specification for 'java_verify'. Equivalent to 'return ()'." ]

  , prim "java_load_class"     "String -> TopLevel JavaClass"
    (bicVal (const . loadJavaClass))
    [ "Load the named Java class and return a handle to it." ]

  , prim "java_browse_class"   "JavaClass -> TopLevel ()"
    (pureVal browseJavaClass)
    [ "Print out the contents of the given Java class." ]

  --, prim "java_class_info"     "JavaClass -> TopLevel ()"

  , prim "java_extract"
    "JavaClass -> String -> JavaSetup () -> TopLevel Term"
    (bicVal extractJava)
    [ "Translate a Java method directly to a Term. The parameters of the"
    , "Term will be the parameters of the Java method, and the return"
    , "value will be the return value of the method. Only static methods"
    , "with scalar argument and return types are currently supported. For"
    , "more flexibility, see 'java_symexec' or 'java_verify'."
    ]

  , prim "java_symexec"
    "JavaClass -> String -> [(String, Term)] -> [String] -> Bool -> TopLevel Term"
    (bicVal symexecJava)
    [ "Symbolically execute a Java method and construct a Term corresponding"
    , "to its result. The first list contains pairs of variable or field"
    , "names along with Terms specifying their initial (possibly symbolic)"
    , "values. The second list contains the names of the variables or fields"
    , "to treat as outputs. The resulting Term will be of tuple type, with"
    , "as many elements as there are names in the output list."
    ]

  , prim "java_verify"
    "JavaClass -> String -> [JavaMethodSpec] -> JavaSetup () -> TopLevel JavaMethodSpec"
    (bicVal verifyJava)
    [ "Verify a Java method against a method specification. The first two"
    , "arguments are the same as for 'java_extract' and 'java_symexec'."
    , "The list of JavaMethodSpec values in the third argument makes it"
    , "possible to use the results of previous verifications to take the"
    , "place of actual execution when encountering a method call. The last"
    , "parameter is a setup block, containing a sequence of commands of type"
    , "'JavaSetup a' that configure the symbolic simulator and specify the"
    , "types of variables in scope, the expected results of execution, and"
    , "the tactics to use to verify that the method produces the expected"
    , "results."
    ]

  , prim "llvm_int"            "Int -> LLVMType"
    (pureVal llvmInt)
    [ "The type of LLVM integers, of the given bit width." ]

  , prim "llvm_float"          "LLVMType"
    (pureVal llvmFloat)
    [ "The type of single-precision floating point numbers in LLVM." ]

  , prim "llvm_double"         "LLVMType"
    (pureVal llvmDouble)
    [ "The type of double-precision floating point numbers in LLVM." ]

  , prim "llvm_array"          "Int -> LLVMType -> LLVMType"
    (pureVal llvmArray)
    [ "The type of LLVM arrays with the given number of elements of the"
    , "given type."
    ]

  , prim "llvm_var"            "String -> LLVMType -> LLVMSetup Term"
    (bicVal llvmVar)
    [ "Return a term corresponding to the initial value of the named LLVM"
    , "variable, which should have the given type. The returned term can be"
    , "used to construct more complex expressions. For example it can be used"
    , "with 'llvm_return' to describe the expected return value in terms"
    , "of the initial value of a variable."
    ]

  , prim "llvm_ptr"            "String -> LLVMType -> LLVMSetup Term"
    (bicVal llvmPtr)
    [ "Declare that the named LLVM variable should point to a value of the"
    , "given type. This command makes the given variable visible later, so"
    , "the use of 'llvm_ptr \"p\" ...' is necessary before using, for"
    , "instance, 'llvm_ensure \"*p\" ...'."
    ]

  --, prim "llvm_may_alias"      "[String] -> LLVMSetup ()"
  --  (bicVal llvmMayAlias)

  , prim "llvm_assert"         "Term -> LLVMSetup ()"
    (bicVal llvmAssert)
    [ "Assert that the given term should evaluate to true in the initial"
    , "state of an LLVM function."
    ]

  --, prim "llvm_assert_eq"      "{a} String -> a -> LLVMSetup ()"
  --  (pureVal llvmAssertEq)

  , prim "llvm_ensure_eq"      "String -> Term -> LLVMSetup ()"
    (pureVal llvmEnsureEq)
    [ "Specify that the LLVM Java variable should have a value equal to the"
    , "given term when execution finishes."
    ]

  , prim "llvm_return"         "Term -> LLVMSetup ()"
    (pureVal llvmReturn)
    [ "Indicate the expected return value of an LLVM function." ]

  , prim "llvm_verify_tactic"  "ProofScript SatResult -> LLVMSetup ()"
    (bicVal llvmVerifyTactic)
    [ "Use the given proof script to prove the specified properties about"
    , "an LLVM function."
    ]

  , prim "llvm_sat_branches"   "Bool -> LLVMSetup ()"
    (pureVal llvmSatBranches)
    [ "Turn on or off satisfiability checking of branch conditions during"
    , "symbolic execution."
    ]

  , prim "llvm_no_simulate"    "LLVMSetup ()"
    (pureVal llvmNoSimulate)
    [ "Skip symbolic simulation for this LLVM method." ]

  , prim "llvm_pure"           "LLVMSetup ()"
    (pureVal llvmPure)
    [ "The empty specification for 'llvm_verify'. Equivalent to 'return ()'." ]

  , prim "llvm_load_module"    "String -> TopLevel LLVMModule"
    (pureVal loadLLVMModule)
    [ "Load an LLVM bitcode file and return a handle to it." ]

  , prim "llvm_browse_module"  "LLVMModule -> TopLevel ()"
    (pureVal browseLLVMModule)
    [ "Print out the contents of a given LLVM module." ]

  --, prim "llvm_module_info"    "LLVMModule -> TopLevel ()"

  , prim "llvm_extract"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel Term"
    (scVal extractLLVM)
    [ "Translate an LLVM function directly to a Term. The parameters of the"
    , "Term will be the parameters of the LLVM function, and the return"
    , "value will be the return value of the functions. Only functions with"
    , "scalar argument and return types are currently supported. For more"
    , "flexibility, see 'llvm_symexec' or 'llvm_verify'."
    ]

  , prim "llvm_symexec"
    "LLVMModule -> String -> [(String, Int)] -> [(String, Term, Int)] -> [(String, Int)] -> Bool -> TopLevel Term"
    (bicVal symexecLLVM)
    [ "Symbolically execute an LLVM function and construct a Term corresponding"
    , "to its result. The first list describes what allocations should be"
    , "performed before execution. Each name given is allocated to point to"
    , "the given number of elements, of the appropriate type. The second list"
    , "contains pairs of variables or expressions along with Terms specifying"
    , "their initial (possibly symbolic) values, and the number of elements"
    , "that the term should contain. The third list contains the names of the"
    , "variables or expressions to treat as outputs, along with the number of"
    , "elements to read from those locations. Finally, the Bool argument sets"
    , "branch satisfiability checking on or off. The resulting Term will be of"
    , "tuple type, with as many elements as there are names in the output list."
    ]

  , prim "llvm_verify"
    "LLVMModule -> String -> [LLVMMethodSpec] -> LLVMSetup () -> TopLevel LLVMMethodSpec"
    (bicVal verifyLLVM)
    [ "Verify an LLVM function against a specification. The first two"
    , "arguments are the same as for 'llvm_extract' and 'llvm_symexec'."
    , "The list of LLVMMethodSpec values in the third argument makes it"
    , "possible to use the results of previous verifications to take the"
    , "place of actual execution when encountering a function call. The last"
    , "parameter is a setup block, containing a sequence of commands of type"
    , "'LLVMSetup a' that configure the symbolic simulator and specify the"
    , "types of variables in scope, the expected results of execution, and"
    , "the tactics to use to verify that the function produces the expected"
    , "results."
    ]

  , prim "caseSatResult"       "{b} SatResult -> b -> (Term -> b) -> b"
    (\_ bic -> toValueCase (biSharedContext bic) caseSatResultPrim)
    [ "Branch on the result of SAT solving."
    , ""
    , "Usage: caseSatResult <code to run if unsat> <code to run if sat>."
    , ""
    , "For example,"
    , ""
    , "  r <- sat abc <thm>"
    , "  caseSatResult r <unsat> <sat>"
    , ""
    , "will run '<unsat>' if '<thm>' is unSAT and will run '<sat> <example>'"
    , "if '<thm>' is SAT, where '<example>' is a satisfying assignment."
    , "If '<thm>' is a curried function, then '<example>' will be a tuple."
    ]

  , prim "caseProofResult"     "{b} ProofResult -> b -> (Term -> b) -> b"
    (\_ bic -> toValueCase (biSharedContext bic) caseProofResultPrim)
    [ "Branch on the result of proofing."
    , ""
    , "Usage: caseProofResult <code to run if true> <code to run if false>."
    , ""
    , "For example,"
    , ""
    , "  r <- prove abc <thm>"
    , "  caseProofResult r <true> <false>"
    , ""
    , "will run '<trie>' if '<thm>' is proved and will run '<false> <example>'"
    , "if '<thm>' is false, where '<example>' is a counter example."
    , "If '<thm>' is a curried function, then '<example>' will be a tuple."
    ]

  , prim "undefined"           "{a} a"
    (\_ _ -> error "interpret: undefined")
    [ "An undefined value of any type. Evaluating 'undefined' makes the"
    , "program crash."
    ]

  , prim "exit"                "Int -> TopLevel ()"
    (pureVal exitPrim)
    [ "Exit SAWScript, returning the supplied exit code to the parent"
    , "process."
    ]
  , prim "time"                "{a} TopLevel a -> TopLevel a"
    (\_ _ -> toValue timePrim)
    [ "Print the CPU time used by the given TopLevel command." ]
  ]
  where
    prim :: String -> String -> (Options -> BuiltinContext -> Value) -> [String]
         -> (SS.LName, Primitive)
    prim name ty fn doc = (qname, Primitive
                                  { primName = qname
                                  , primType = readSchema ty
                                  , primDoc  = doc
                                  , primFn   = fn
                                  })
      where qname = qualify name

    pureVal :: forall t. IsValue t => t -> Options -> BuiltinContext -> Value
    pureVal x _ _ = toValue x

    scVal :: forall t. IsValue t =>
             (SharedContext SAWCtx -> t) -> Options -> BuiltinContext -> Value
    scVal f _ bic = toValue (f (biSharedContext bic))

    bicVal :: forall t. IsValue t =>
              (BuiltinContext -> Options -> t) -> Options -> BuiltinContext -> Value
    bicVal f opts bic = toValue (f bic opts)

primTypeEnv :: Map SS.LName SS.Schema
primTypeEnv = fmap primType primitives

valueEnv :: Options -> BuiltinContext -> Map SS.LName Value
valueEnv opts bic = fmap f primitives
  where f p = (primFn p) opts bic

primDocEnv :: Map SS.Name String
primDocEnv =
  Map.fromList [ (getVal n, doc n p) | (n, p) <- Map.toList primitives ]
    where
      doc n p = unlines $
                [ "Description"
                , "-----------"
                , ""
                , "    " ++ getVal n ++ " : " ++ SS.pShow (primType p)
                , ""
                ] ++ primDoc p

qualify :: String -> Located SS.Name
qualify s = Located s s (PosInternal "coreEnv")
