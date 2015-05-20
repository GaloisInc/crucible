{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

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

import Control.Applicative
import qualified Control.Exception as X
import Control.Monad (foldM, unless)
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Traversable hiding ( mapM )

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
import Verifier.SAW.PrettySExp
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
import qualified Cryptol.Eval.Value as V (defaultPPOpts, ppValue)

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
    qname = T.QName Nothing (T.Name (getOrig x))
    modname = T.ModName [getOrig x]
    ce = rwCryptol rw
    ce' = case v of
            VTerm t
              -> CEnv.bindTypedTerm (qname, t) ce
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

  SS.Decl _ (Just schema) expr'' <- reportErrT $ checkDecl (rwTypes rw) decl

  val <- interpret ro rw expr''

  -- | Run the resulting TopLevel action.
  (result, ty, rw') <-
    case schema of
      SS.Forall [] t ->
        case t of
          SS.TyCon SS.BlockCon [c, t'] | c == ctx -> do
            (result, rw') <- runTopLevel (SAWScript.Value.fromValue val) ro rw
            return (result, t', rw')
          _ -> return (val, t, rw)
      _ -> fail $ "Not a monomorphic type: " ++ SS.pShow schema

  -- | Print non-unit result if it was not bound to a variable
  case mx of
    Nothing | printBinds && not (isVUnit result) -> print result
    _                                            -> return ()

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
                   ++ finConversions
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

print_value :: Value -> TopLevel ()
print_value (VString s) = io $ putStrLn s
print_value (VTerm t) = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = meSolverConfig (CEnv.eModuleEnv cenv)
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  t' <- io $ defaultTypedTerm sc cfg t
  io $ rethrowEvalError $ print $ V.ppValue V.defaultPPOpts (evaluateTypedTerm sc t')
print_value v = io $ putStrLn (showsPrecValue defaultPPOpts 0 v "")

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
    [ "TODO" ]

  , prim "for"                 "{m, a, b} [a] -> (a -> m b) -> m [b]"
    (pureVal (VLambda . forValue))
    [ "TODO" ]

  , prim "str_concat"          "String -> String -> String"
    (pureVal ((++) :: String -> String -> String))
    [ "TODO" ]

  , prim "define"              "String -> Term -> TopLevel Term"
    (pureVal definePrim)
    [ "TODO" ]

  , prim "include"             "String -> TopLevel ()"
    (pureVal include_value)
    [ "Execute the given SAWScript file" ]

  , prim "env"                 "TopLevel ()"
    (pureVal envCmd)
    [ "Print all sawscript values in scope" ]

  , prim "print"               "{a} a -> TopLevel ()"
    (pureVal print_value)
    [ "TODO" ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_term_depth"    "Int -> Term -> TopLevel ()"
    (pureVal ((\d -> print . ppTermDepth d) :: Int -> SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_term_sexp"     "Term -> TopLevel ()"
    (pureVal ((print . ppSharedTermSExp) :: SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_term_sexp'"    "Int -> Term -> TopLevel ()"
    (pureVal printTermSExp')
    [ "TODO" ]

  , prim "print_type"          "Term -> TopLevel ()"
    (pureVal print_type)
    [ "TODO" ]

  , prim "type"                "Term -> Type"
    (pureVal (ttSchema :: TypedTerm SAWCtx -> T.Schema))
    [ "TODO" ]

  , prim "show_term"           "Term -> String"
    (pureVal (scPrettyTerm :: SharedTerm SAWCtx -> String))
    [ "TODO" ]

  , prim "check_term"          "Term -> TopLevel ()"
    (pureVal check_term)
    [ "TODO" ]

  , prim "term_size"           "Term -> Int"
    (pureVal (scSharedSize :: SharedTerm SAWCtx -> Integer))
    [ "TODO" ]

  , prim "term_tree_size"      "Term -> Int"
    (pureVal (scTreeSize :: SharedTerm SAWCtx -> Integer))
    [ "TODO" ]

  , prim "abstract_symbolic"   "Term -> TopLevel Term"
    (pureVal abstractSymbolicPrim)
    [ "TODO" ]

  , prim "fresh_symbolic"      "String -> Type -> TopLevel Term"
    (pureVal freshSymbolicPrim)
    [ "TODO" ]

  , prim "sbv_uninterpreted"   "String -> Term -> TopLevel Uninterp"
    (pureVal sbvUninterpreted)
    [ "TODO" ]

  , prim "check_convertable"  "Term -> Term -> TopLevel ()"
    (pureVal checkConvertablePrim)
    [ "Check if two terms are convertable" ]

  , prim "replace"             "Term -> Term -> Term -> TopLevel Term"
    (pureVal replacePrim)
    [ "'replace x y z' rewrites occurences of term x into y inside the term z.  x and y must be closed terms." ]

  , prim "hoist_ifs"            "Term -> TopLevel Term"
    (pureVal hoistIfsPrim)
    [ "Hoist all if-then-else expressions as high as possible" ]

  , prim "read_bytes"          "String -> TopLevel Term"
    (pureVal readBytes)
    [ "Read binary file as a value of type [n][8]" ]

  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term"
    (pureVal readSBV)
    [ "TODO" ]

  , prim "load_aig"            "String -> TopLevel AIG"
    (pureVal loadAIGPrim)
    [ "Read an AIG file in binary AIGER format." ]

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
    [ "Translate a term into an AIG.  The term must be representable as a function"
    , "from a finite number of bits to a finite number of bits."
    ]

  , prim "read_aig"            "String -> TopLevel Term"
    (pureVal readAIGPrim)
    [ "Read an AIG file in AIGER format and translate to a term" ]

  , prim "read_core"           "String -> TopLevel Term"
    (pureVal readCore)
    [ "Read a term from a file in the SAWCore external format" ]

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
    [ "TODO" ]

  , prim "write_smtlib1"       "String -> Term -> TopLevel ()"
    (scVal writeSMTLib1)
    [ "TODO" ]

  , prim "write_smtlib2"       "String -> Term -> TopLevel ()"
    (scVal writeSMTLib2)
    [ "TODO" ]

  , prim "write_core"          "String -> Term -> TopLevel ()"
    (pureVal (writeCore :: FilePath -> TypedTerm SAWCtx -> IO ()))
    [ "Write out a representation of a term in SAWCore external format." ]

  , prim "prove"               "{b} ProofScript b -> Term -> TopLevel ProofResult"
    (scVal provePrim)
    [ "TODO" ]

  , prim "prove_print"         "{b} ProofScript b -> Term -> TopLevel Theorem"
    (scVal provePrintPrim)
    [ "TODO" ]

  , prim "sat"                 "{b} ProofScript b -> Term -> TopLevel SatResult"
    (scVal satPrim)
    [ "TODO" ]

  , prim "sat_print"           "{b} ProofScript b -> Term -> TopLevel ()"
    (scVal satPrintPrim)
    [ "TODO" ]

  , prim "qc_print"            "Int -> Term -> TopLevel ()"
    (scVal quickCheckPrintPrim)
    [ "Quick Check term and print the results."
    , "The 'Int' arg specifies how many tests to run."
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
    [ "TODO" ]

  , prim "simplify"            "Simpset -> ProofScript ()"
    (scVal simplifyGoal)
    [ "TODO" ]

  , prim "print_goal"          "ProofScript ()"
    (pureVal (printGoal :: ProofScript SAWCtx ()))
    [ "TODO" ]

  , prim "print_goal_depth"    "Int -> ProofScript ()"
    (pureVal printGoalDepth)
    [ "TODO" ]

  , prim "print_goal_sexp"     "ProofScript ()"
    (pureVal printGoalSExp)
    [ "TODO" ]

  , prim "print_goal_sexp'"    "Int -> ProofScript ()"
    (pureVal printGoalSExp')
    [ "TODO" ]

  , prim "assume_valid"        "ProofScript ProofResult"
    (pureVal (assumeValid :: ProofScript SAWCtx ProofResult))
    [ "TODO" ]

  , prim "assume_unsat"        "ProofScript SatResult"
    (pureVal (assumeUnsat :: ProofScript SAWCtx SatResult))
    [ "TODO" ]

  , prim "quickcheck"          "Int -> ProofScript SatResult"
    (scVal quickcheckGoal)
    [ "TODO" ]

  , prim "abc"                 "ProofScript SatResult"
    (scVal satABC)
    [ "TODO" ]

  , prim "boolector"           "ProofScript SatResult"
    (scVal satBoolector)
    [ "TODO" ]

  , prim "cvc4"                "ProofScript SatResult"
    (scVal satCVC4)
    [ "TODO" ]

  , prim "z3"                  "ProofScript SatResult"
    (scVal satZ3)
    [ "TODO" ]

  , prim "mathsat"             "ProofScript SatResult"
    (scVal satMathSAT)
    [ "TODO" ]

  , prim "yices"               "ProofScript SatResult"
    (scVal satYices)
    [ "TODO" ]

  , prim "unint_z3"            "[String] -> ProofScript SatResult"
    (scVal satUnintZ3)
    [ "TODO" ]

  , prim "offline_aig"         "String -> ProofScript SatResult"
    (scVal satAIG)
    [ "TODO" ]

  , prim "offline_cnf"         "String -> ProofScript SatResult"
    (scVal satCNF)
    [ "TODO" ]

  , prim "offline_extcore"     "String -> ProofScript SatResult"
    (scVal satExtCore)
    [ "TODO" ]

  , prim "offline_smtlib1"     "String -> ProofScript SatResult"
    (scVal satSMTLib1)
    [ "TODO" ]

  , prim "offline_smtlib2"     "String -> ProofScript SatResult"
    (scVal satSMTLib2)
    [ "TODO" ]

  , prim "external_cnf_solver" "String -> [String] -> ProofScript SatResult"
    (scVal (satExternal True))
    [ "TODO" ]

  , prim "external_aig_solver" "String -> [String] -> ProofScript SatResult"
    (scVal (satExternal False))
    [ "TODO" ]

  , prim "empty_ss"            "Simpset"
    (pureVal (emptySimpset :: Simpset (SharedTerm SAWCtx)))
    [ "TODO" ]

  , prim "cryptol_ss"          "TopLevel Simpset"
    (scVal cryptolSimpset)
    [ "TODO" ]

  , prim "add_prelude_eqs"     "[String] -> Simpset -> TopLevel Simpset"
    (scVal addPreludeEqs)
    [ "TODO" ]

  , prim "add_cryptol_eqs"     "[String] -> Simpset -> TopLevel Simpset"
    (scVal addCryptolEqs)
    [ "TODO" ]

  , prim "add_prelude_defs"    "[String] -> Simpset -> TopLevel Simpset"
    (scVal addPreludeDefs)
    [ "TODO" ]

  --, prim "basic_ss"            "Simpset"

  , prim "addsimp"             "Theorem -> Simpset -> Simpset"
    (scVal addsimp)
    [ "TODO" ]

  , prim "addsimp'"            "Term -> Simpset -> Simpset"
    (scVal addsimp')
    [ "TODO" ]

  , prim "addsimps"            "[Theorem] -> Simpset -> Simpset"
    (scVal addsimps)
    [ "TODO" ]

  , prim "addsimps'"           "[Term] -> Simpset -> Simpset"
    (scVal addsimps')
    [ "TODO" ]

  , prim "rewrite"             "Simpset -> Term -> TopLevel Term"
    (scVal rewritePrim)
    [ "TODO" ]

  , prim "cryptol_load"        "String -> TopLevel CryptolModule"
    (scVal CEnv.loadCryptolModule)
    [ "TODO" ]

  , prim "cryptol_extract"     "CryptolModule -> String -> TopLevel Term"
    (pureVal (CEnv.lookupCryptolModule :: CryptolModule SAWCtx -> String -> IO (TypedTerm SAWCtx)))
    [ "TODO" ]

  -- Java stuff

  , prim "java_bool"           "JavaType"
    (pureVal JavaBoolean)
    [ "TODO" ]

  , prim "java_byte"           "JavaType"
    (pureVal JavaByte)
    [ "TODO" ]

  , prim "java_char"           "JavaType"
    (pureVal JavaChar)
    [ "TODO" ]

  , prim "java_short"          "JavaType"
    (pureVal JavaShort)
    [ "TODO" ]

  , prim "java_int"            "JavaType"
    (pureVal JavaInt)
    [ "TODO" ]

  , prim "java_long"           "JavaType"
    (pureVal JavaLong)
    [ "TODO" ]

  , prim "java_float"          "JavaType"
    (pureVal JavaFloat)
    [ "TODO" ]

  , prim "java_double"         "JavaType"
    (pureVal JavaDouble)
    [ "TODO" ]

  , prim "java_array"          "Int -> JavaType -> JavaType"
    (pureVal JavaArray)
    [ "TODO" ]

  , prim "java_class"          "String -> JavaType"
    (pureVal JavaClass)
    [ "TODO" ]

  --, prim "java_value"          "{a} String -> a"

  , prim "java_var"            "String -> JavaType -> JavaSetup Term"
    (bicVal javaVar)
    [ "TODO" ]

  , prim "java_class_var"      "{a} String -> JavaType -> JavaSetup a"
    (bicVal javaClassVar)
    [ "TODO" ]

  , prim "java_may_alias"      "[String] -> JavaSetup ()"
    (bicVal javaMayAlias)
    [ "TODO" ]

  , prim "java_assert"         "Term -> JavaSetup ()"
    (bicVal javaAssert)
    [ "TODO" ]

  --, prim "java_assert_eq"      "{a} String -> a -> JavaSetup ()"
  --  (bicVal javaAssertEq)

  , prim "java_ensure_eq"      "String -> Term -> JavaSetup ()"
    (bicVal javaEnsureEq)
    [ "TODO" ]

  , prim "java_modify"         "String -> JavaSetup ()"
    (bicVal javaModify)
    [ "TODO" ]

  , prim "java_return"         "Term -> JavaSetup ()"
    (bicVal javaReturn)
    [ "TODO" ]

  , prim "java_verify_tactic"  "ProofScript SatResult -> JavaSetup ()"
    (bicVal javaVerifyTactic)
    [ "TODO" ]

  , prim "java_no_simulate"    "JavaSetup ()"
    (pureVal javaNoSimulate)
    [ "TODO" ]

  , prim "java_pure"           "JavaSetup ()"
    (pureVal javaPure)
    [ "TODO" ]

  , prim "java_load_class"     "String -> TopLevel JavaClass"
    (bicVal (const . loadJavaClass))
    [ "TODO" ]

  , prim "java_browse_class"   "JavaClass -> TopLevel ()"
    (pureVal browseJavaClass)
    [ "TODO" ]

  --, prim "java_class_info"     "JavaClass -> TopLevel ()"

  , prim "java_extract"
    "JavaClass -> String -> JavaSetup () -> TopLevel Term"
    (bicVal extractJava)
    [ "TODO" ]

  , prim "java_symexec"
    "JavaClass -> String -> [(String, Term)] -> [String] -> TopLevel Term"
    (bicVal symexecJava)
    [ "TODO" ]

  , prim "java_verify"
    "JavaClass -> String -> [JavaMethodSpec] -> JavaSetup () -> TopLevel JavaMethodSpec"
    (bicVal verifyJava)
    [ "TODO" ]

  , prim "llvm_int"            "Int -> LLVMType"
    (pureVal llvmInt)
    [ "TODO" ]

  , prim "llvm_float"          "LLVMType"
    (pureVal llvmFloat)
    [ "TODO" ]

  , prim "llvm_double"         "LLVMType"
    (pureVal llvmDouble)
    [ "TODO" ]

  , prim "llvm_array"          "Int -> LLVMType -> LLVMType"
    (pureVal llvmArray)
    [ "TODO" ]

  , prim "llvm_var"            "String -> LLVMType -> LLVMSetup Term"
    (bicVal llvmVar)
    [ "TODO" ]

  , prim "llvm_ptr"            "String -> LLVMType -> LLVMSetup Term"
    (bicVal llvmPtr)
    [ "TODO" ]

  --, prim "llvm_may_alias"      "[String] -> LLVMSetup ()"
  --  (bicVal llvmMayAlias)

  , prim "llvm_assert"         "Term -> LLVMSetup ()"
    (bicVal llvmAssert)
    [ "TODO" ]

  --, prim "llvm_assert_eq"      "{a} String -> a -> LLVMSetup ()"
  --  (bicVal llvmAssertEq)

  , prim "llvm_ensure_eq"      "String -> Term -> LLVMSetup ()"
    (bicVal llvmEnsureEq)
    [ "TODO" ]

  , prim "llvm_return"         "Term -> LLVMSetup ()"
    (bicVal llvmReturn)
    [ "TODO" ]

  , prim "llvm_verify_tactic"  "ProofScript SatResult -> LLVMSetup ()"
    (bicVal llvmVerifyTactic)
    [ "TODO" ]

  , prim "llvm_no_simulate"    "LLVMSetup ()"
    (pureVal llvmNoSimulate)
    [ "TODO" ]

  , prim "llvm_pure"           "LLVMSetup ()"
    (pureVal llvmPure)
    [ "TODO" ]

  , prim "llvm_load_module"    "String -> TopLevel LLVMModule"
    (pureVal loadLLVMModule)
    [ "TODO" ]

  , prim "llvm_browse_module"  "LLVMModule -> TopLevel ()"
    (pureVal browseLLVMModule)
    [ "TODO" ]

  --, prim "llvm_module_info"    "LLVMModule -> TopLevel ()"

  , prim "llvm_extract"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel Term"
    (scVal extractLLVM)
    [ "TODO" ]

  , prim "llvm_symexec"
    "LLVMModule -> String -> [(String, Int)] -> [(String, Term, Int)] -> [(String, Int)] -> TopLevel Term"
    (bicVal symexecLLVM)
    [ "TODO" ]

  , prim "llvm_verify"
    "LLVMModule -> String -> [LLVMMethodSpec] -> LLVMSetup () -> TopLevel LLVMMethodSpec"
    (bicVal verifyLLVM)
    [ "TODO" ]

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
    [ "An undefined value of any type. Evaluating 'undefined' makes the program crash." ]

  , prim "exit"                "Int -> TopLevel ()"
    (pureVal exitPrim)

    [ "Exit SAWScript, returning the supplied exit code to the parent process." ]
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
