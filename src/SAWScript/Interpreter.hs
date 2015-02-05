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
  , InterpretEnv(..)
  , buildInterpretEnv
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

import qualified Cryptol.TypeCheck.AST as T
import Cryptol.TypeCheck.Defaulting (defaultExpr)
import Cryptol.TypeCheck.PP (ppWithNames)
import Cryptol.TypeCheck.Subst (apSubst, listSubst)
import Cryptol.Parser.Position (emptyRange)
import Cryptol.Utils.PP
import qualified Cryptol.Eval.Value as V (defaultPPOpts, ppValue)

-- Environment -----------------------------------------------------------------

data InterpretEnv = InterpretEnv
  { ieValues  :: Map SS.LName Value
  , ieTypes   :: Map SS.LName SS.Schema
  , ieDocs    :: Map SS.Name String
  , ieCryptol :: CEnv.CryptolEnv SAWCtx
  , ieRO      :: RO
  , ieOptions :: Options
  }

extendEnv :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> InterpretEnv -> InterpretEnv
extendEnv x mt md v (InterpretEnv vm tm dm ce ro opts) = InterpretEnv vm' tm' dm' ce' ro opts
  where
    name = x
    qname = T.QName Nothing (T.Name (getOrig x))
    modname = T.ModName [getOrig x]
    vm' = Map.insert name v vm
    tm' = maybe tm (\t -> Map.insert name t tm) mt
    dm' = maybe dm (\d -> Map.insert (getVal name) d dm) md
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
extendEnv' :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> InterpretEnv -> InterpretEnv
extendEnv' x mt md v (InterpretEnv vm tm dm ce ro opts) = InterpretEnv vm' tm' dm' ce ro opts
  where
    dm' = maybe dm (\d -> Map.insert (getVal x) d dm) md
    vm' = Map.insert x v vm
    tm' = maybe tm (\t -> Map.insert x t tm) mt

-- Interpretation of SAWScript -------------------------------------------------

interpret :: SharedContext SAWCtx -> InterpretEnv -> SS.Expr -> IO Value
interpret sc env@(InterpretEnv vm _tm _dm ce _ro _opts) expr =
    case expr of
      SS.Bit b               -> return $ VBool b
      SS.String s            -> return $ VString s
      SS.Z z                 -> return $ VInteger z
      SS.Undefined           -> return $ error "interpret: undefined"
      SS.Code str            -> toValue `fmap` CEnv.parseTypedTerm sc ce str
      SS.CType str           -> toValue `fmap` CEnv.parseSchema ce str
      SS.Array es            -> VArray <$> traverse (interpret sc env) es
      SS.Block stmts         -> interpretStmts sc env stmts
      SS.Tuple es            -> VTuple <$> traverse (interpret sc env) es
      SS.Record bs           -> VRecord <$> traverse (interpret sc env) bs
      SS.Index e1 e2         -> do a <- interpret sc env e1
                                   i <- interpret sc env e2
                                   return (indexValue a i)
      SS.Lookup e n          -> do a <- interpret sc env e
                                   return (lookupValue a n)
      SS.TLookup e i         -> do a <- interpret sc env e
                                   return (tupleLookupValue a i)
      SS.Var x               -> case Map.lookup x vm of
                                  Nothing -> fail $ "unknown variable: " ++ SS.getVal x
                                  Just v -> return v

      SS.Function x t e      -> do let env' v = extendEnv x (fmap SS.tMono t) Nothing v env
                                       f v = interpret sc (env' v) e
                                   return $ VLambda f
      SS.Application e1 e2   -> do v1 <- interpret sc env e1
                                   v2 <- interpret sc env e2
                                   case v1 of
                                     VLambda f -> f v2
                                     _ -> fail $ "interpret Application: " ++ show v1
      SS.Let dg e            -> do env' <- interpretDeclGroup sc env dg
                                   interpret sc env' e
      SS.TSig e _            -> interpret sc env e

interpretDecl :: SharedContext SAWCtx -> InterpretEnv -> SS.Decl -> IO InterpretEnv
interpretDecl sc env (SS.Decl n mt expr) = do
  v <- interpret sc env expr
  return (extendEnv n mt Nothing v env)

interpretFunction :: SharedContext SAWCtx -> InterpretEnv -> SS.Expr -> Value
interpretFunction sc env expr =
    case expr of
      SS.Function x t e -> VLambda f
        where f v = interpret sc (extendEnv x (fmap SS.tMono t) Nothing v env) e
      SS.TSig e _ -> interpretFunction sc env e
      _ -> error "interpretFunction: not a function"

interpretDeclGroup :: SharedContext SAWCtx -> InterpretEnv -> SS.DeclGroup -> IO InterpretEnv
interpretDeclGroup sc env (SS.NonRecursive d) =
  interpretDecl sc env d
interpretDeclGroup sc env (SS.Recursive ds) = return env'
  where env' = foldr ($) env [ extendEnv' n mty Nothing (interpretFunction sc env' e) | SS.Decl n mty e <- ds ]

interpretStmts :: SharedContext SAWCtx -> InterpretEnv -> [SS.Stmt] -> IO Value
interpretStmts sc env@(InterpretEnv vm tm dm ce ro opts) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.StmtBind Nothing _ _ e] -> interpret sc env e
      SS.StmtBind Nothing _ _ e : ss ->
          do v1 <- interpret sc env e
             return $ VBind v1 $ VLambda $ const $ interpretStmts sc env ss
      SS.StmtBind (Just x) mt _ e : ss ->
          do v1 <- interpret sc env e
             let f v = interpretStmts sc (extendEnv x (fmap SS.tMono mt) Nothing v env) ss
             bindValue v1 (VLambda f)
      SS.StmtLet bs : ss -> interpret sc env (SS.Let bs (SS.Block ss))
      SS.StmtCode s : ss ->
          do ce' <- CEnv.parseDecls sc ce s
             interpretStmts sc (InterpretEnv vm tm dm ce' ro opts) ss
      SS.StmtImport _ : _ ->
          do fail "block import unimplemented"

processStmtBind :: Bool -> SharedContext SAWCtx -> InterpretEnv -> Maybe SS.LName
                 -> Maybe SS.Type -> Maybe SS.Type -> SS.Expr -> IO InterpretEnv
processStmtBind printBinds sc env mx mt _mc expr = do
  let it = SS.Located "it" "it" PosREPL
  let lname = maybe it id mx
  let ctx = SS.tContext SS.TopLevel
  let expr' = case mt of
                Nothing -> expr
                Just t -> SS.TSig expr (SS.tBlock ctx t)
  let decl = SS.Decl lname Nothing (SS.Block [SS.StmtBind Nothing Nothing (Just ctx) expr'])

  SS.Decl _ (Just schema) expr'' <- reportErrT $ checkDecl (ieTypes env) decl
  ty <- case schema of
          SS.Forall [] t ->
            case t of
              SS.TyCon SS.BlockCon [c, t'] | c == ctx -> return t'
              _ -> fail $ "Not a TopLevel monadic type: " ++ SS.pShow t
          _ -> fail $ "Not a monomorphic type: " ++ SS.pShow schema

  val <- interpret sc env expr''
  -- | Run the resulting IO action.
  result <- runTopLevel (SAWScript.Value.fromValue val) (ieRO env)

  -- | Print non-unit result if it was not bound to a variable
  case mx of
    Nothing | printBinds && not (isVUnit result) -> print result
    _                                            -> return ()

  let env' = extendEnv lname (Just (SS.tMono ty)) Nothing result env
  return env'

-- | Interpret a block-level statement in the TopLevel monad.
interpretStmt :: Bool -> SharedContext SAWCtx -> InterpretEnv -> SS.Stmt -> IO InterpretEnv
interpretStmt printBinds sc env stmt =
  case stmt of
    SS.StmtBind mx mt mc expr -> processStmtBind printBinds sc env mx mt mc expr
    SS.StmtLet dg             -> do dg' <- reportErrT (checkDeclGroup (ieTypes env) dg)
                                    interpretDeclGroup sc env dg'
    SS.StmtCode lstr          -> do cenv' <- CEnv.parseDecls sc (ieCryptol env) lstr
                                    return env { ieCryptol = cenv' }
    SS.StmtImport imp         -> do cenv' <- CEnv.importModule sc (ieCryptol env) imp
                                    return env { ieCryptol = cenv' }
    SS.StmtInclude file       -> interpretFile sc env file

interpretFile :: SharedContext SAWCtx -> InterpretEnv -> FilePath -> IO InterpretEnv
interpretFile sc env file = do
  stmts <- SAWScript.Import.loadFile (ieOptions env) file
  foldM (interpretStmt False sc) env stmts

-- | Evaluate the value called 'main' from the current environment.
interpretMain :: InterpretEnv -> IO ()
interpretMain env =
  case Map.lookup mainName (ieValues env) of
    Nothing -> return () -- fail "No 'main' defined"
    Just v -> runTopLevel (fromValue v) (ieRO env)
  where mainName = Located "main" "main" (PosInternal "entry")

buildInterpretEnv :: Options -> IO (BuiltinContext, InterpretEnv)
buildInterpretEnv opts =
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
       let ro0 = RO { roSharedContext = sc
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
       return (bic, InterpretEnv vm0 tm0 primDocEnv ce0 ro0 opts)

processFile :: Options -> FilePath -> IO ()
processFile opts file = do
  (bic, env) <- buildInterpretEnv opts
  let sc = biSharedContext bic
  env' <- interpretFile sc env file
  interpretMain env'

-- Primitives ------------------------------------------------------------------

print_value :: Value -> TopLevel ()
print_value (VString s) = io $ putStrLn s
print_value (VTerm t) = do
  sc <- getSharedContext
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  t' <- io $ defaultTypedTerm sc t
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

defaultTypedTerm :: SharedContext s -> TypedTerm s -> IO (TypedTerm s)
defaultTypedTerm sc (TypedTerm schema trm) =
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
    inst = do (soln, _) <- defaultExpr emptyRange undefined schema
              mapM (`lookup` soln) (T.sVars schema)
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

  , prim "print"               "{a} a -> TopLevel ()"
    (pureVal print_value)
    [ "TODO" ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_type"          "Term -> TopLevel ()"
    (pureVal print_type)
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

  , prim "read_bytes"          "String -> TopLevel Term"
    (pureVal readBytes)
    [ "Read binary file as a value of type [n][8]" ]

  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term"
    (pureVal readSBV)
    [ "TODO" ]

  , prim "read_aig"            "String -> TopLevel Term"
    (pureVal readAIGPrim)
    [ "TODO" ]

  , prim "read_core"           "String -> TopLevel Term"
    (pureVal readCore)
    [ "TODO" ]

  , prim "write_aig"           "String -> Term -> TopLevel ()"
    (scVal writeAIG)
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits."
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
    [ "TODO" ]


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


  , prim "unfolding"           "[String] -> ProofScript ()"
    (scVal unfoldGoal)
    [ "TODO" ]

  , prim "simplify"            "Simpset -> ProofScript ()"
    (scVal simplifyGoal)
    [ "TODO" ]

  , prim "print_goal"          "ProofScript ()"
    (pureVal (printGoal :: ProofScript SAWCtx ()))
    [ "TODO" ]

  , prim "assume_valid"        "ProofScript ProofResult"
    (pureVal (assumeValid :: ProofScript SAWCtx ProofResult))
    [ "TODO" ]

  , prim "assume_unsat"        "ProofScript SatResult"
    (pureVal (assumeUnsat :: ProofScript SAWCtx SatResult))
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

{-
  , prim "abc_old"             "ProofScript SatResult"
    (scVal satABCold)
    [ "TODO" ]
-}

  , prim "yices"               "ProofScript SatResult"
    (scVal satYices)
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

  --, prim "llvm_value"          "{a} String -> a"

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

  , prim "llvm_modify"         "String -> LLVMSetup ()"
    (bicVal llvmModify)
    [ "TODO" ]

  , prim "llvm_return"         "Term -> LLVMSetup ()"
    (bicVal llvmReturn)
    [ "TODO" ]

  , prim "llvm_verify_tactic"  "ProofScript SatResult -> LLVMSetup ()"
    (bicVal llvmVerifyTactic)
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
    "LLVMModule -> String -> [(String, Term)] -> [String] -> TopLevel Term"
    (bicVal symexecLLVM)
    [ "TODO" ]

  , prim "llvm_verify"
    "LLVMModule -> String -> [LLVMMethodSpec] -> LLVMSetup () -> TopLevel LLVMMethodSpec"
    (bicVal verifyLLVM)
    [ "TODO" ]

  , prim "caseSatResult"       "{b} SatResult -> b -> (Term -> b) -> b"
    (\_ bic -> toValueCase (biSharedContext bic) caseSatResultPrim)
    [ "TODO" ]

  , prim "caseProofResult"     "{b} ProofResult -> b -> (Term -> b) -> b"
    (\_ bic -> toValueCase (biSharedContext bic) caseProofResultPrim)
    [ "TODO" ]

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
