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
  , interpretMain
  , interpretModuleAtEntry
  , InterpretEnv(..)
  , buildInterpretEnv
  , extendEnv
  , Value, isVUnit
  , IsValue(..)
  , primTypeEnv
  , primDocEnv
  )
  where

import Control.Applicative
import Control.Monad ( foldM )
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Traversable hiding ( mapM )

import qualified SAWScript.AST as SS
import SAWScript.AST (Located(..))
import SAWScript.Builtins hiding (evaluate)
import qualified SAWScript.CryptolEnv as CEnv
import SAWScript.JavaBuiltins
import SAWScript.LLVMBuiltins
import SAWScript.Options
import SAWScript.Lexer (lexSAW)
import SAWScript.Parser (parseSchema)
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value
import Verifier.SAW.Conversion
import Verifier.SAW.Prelude (preludeModule)
import Verifier.SAW.Rewriter ( Simpset, emptySimpset, rewritingSharedContext
                             , scSimpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.Java.Codebase as JCB
import qualified Verifier.Java.SAWBackend as JavaSAW
import qualified Verifier.LLVM.Backend.SAW as LLVMSAW

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import qualified Cryptol.TypeCheck.AST as T

-- Environment -----------------------------------------------------------------

data InterpretEnv = InterpretEnv
  { ieValues  :: Map SS.LName Value
  , ieTypes   :: Map SS.LName SS.Schema
  , ieDocs    :: Map SS.Name String
  , ieCryptol :: CEnv.CryptolEnv SAWCtx
  }

extendEnv :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> InterpretEnv -> InterpretEnv
extendEnv x mt md v (InterpretEnv vm tm dm ce) = InterpretEnv vm' tm' dm' ce'
  where
    name = x
    qname = T.QName Nothing (T.Name (getOrig x))
    vm' = Map.insert name v vm
    tm' = maybe tm (\t -> Map.insert name t tm) mt
    dm' = maybe dm (\d -> Map.insert (getVal name) d dm) md
    ce' = case v of
            VTerm schema trm
              -> CEnv.bindTypedTerm (qname, TypedTerm schema trm) ce
            VInteger n
              -> CEnv.bindInteger (qname, n) ce
            _ -> ce

-- | Variation that does not force the value argument: it assumes it
-- is not a term or int.
extendEnv' :: SS.LName -> Maybe SS.Schema -> Maybe String -> Value -> InterpretEnv -> InterpretEnv
extendEnv' x mt md v (InterpretEnv vm tm dm ce) = InterpretEnv vm' tm' dm' ce
  where
    dm' = maybe dm (\d -> Map.insert (getVal x) d dm) md
    vm' = Map.insert x v vm
    tm' = maybe tm (\t -> Map.insert x t tm) mt

-- Interpretation of SAWScript -------------------------------------------------

interpret :: SharedContext SAWCtx -> InterpretEnv -> SS.Expr -> IO Value
interpret sc env@(InterpretEnv vm _tm _dm ce) expr =
    case expr of
      SS.Bit b               -> return $ VBool b
      SS.String s            -> return $ VString s
      SS.Z z                 -> return $ VInteger z
      SS.Undefined           -> return $ error "interpret: undefined"
      SS.Code str            -> toValue `fmap` CEnv.parseTypedTerm sc ce str
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

interpretStmts :: SharedContext SAWCtx -> InterpretEnv -> [SS.BlockStmt] -> IO Value
interpretStmts sc env@(InterpretEnv vm tm dm ce) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ _ e] -> interpret sc env e
      SS.Bind Nothing _ _ e : ss ->
          do v1 <- interpret sc env e
             return $ VBind v1 $ VLambda $ const $ interpretStmts sc env ss
      SS.Bind (Just x) mt _ e : ss ->
          do v1 <- interpret sc env e
             let f v = interpretStmts sc (extendEnv x (fmap SS.tMono mt) Nothing v env) ss
             bindValue v1 (VLambda f)
      SS.BlockLet bs : ss -> interpret sc env (SS.Let bs (SS.Block ss))
      SS.BlockCode s : ss ->
          do ce' <- CEnv.parseDecls sc ce s
             interpretStmts sc (InterpretEnv vm tm dm ce') ss

interpretModule
    :: SharedContext SAWCtx
    -> InterpretEnv -> SS.ValidModule -> IO InterpretEnv
interpretModule sc env m =
    do cenv' <- foldM (CEnv.importModule sc) (ieCryptol env) (SS.moduleCryDeps m)
       let env' = env { ieCryptol = cenv' }
       let decls = SS.moduleExprEnv m
       foldM (interpretDecl sc) env' decls

interpretModuleAtEntry :: SS.Name
                          -> SharedContext SAWCtx
                          -> InterpretEnv
                          -> SS.ValidModule
                          -> IO (Value, InterpretEnv)
interpretModuleAtEntry entryName sc env m =
  do interpretEnv@(InterpretEnv vm _tm _dm _ce) <- interpretModule sc env m
     let mainName = Located entryName entryName (PosInternal "entry")
     case Map.lookup mainName vm of
       Just v -> do
         --putStrLn "We've been asked to execute a 'TopLevel' action, so run it."
         -- We've been asked to execute a 'TopLevel' action, so run it.
         r <- fromValue v
         return (r, interpretEnv)
       Nothing -> fail $ "No " ++ entryName ++ " in module " ++ show (SS.moduleName m)

-- | Interpret an expression using the default value environments.
interpretEntry :: SS.Name -> Options -> SS.ValidModule -> IO Value
interpretEntry entryName opts m =
    do (bic, interpretEnv0) <- buildInterpretEnv opts m
       let sc = biSharedContext bic
       (result, _interpretEnv) <-
         interpretModuleAtEntry entryName sc interpretEnv0 m
       return result

buildInterpretEnv :: Options -> SS.ValidModule -> IO (BuiltinContext, InterpretEnv)
buildInterpretEnv opts m =
    do let mn = mkModuleName [SS.moduleName m]
       let scm = insImport preludeModule $
                 insImport JavaSAW.javaModule $
                 insImport LLVMSAW.llvmModule $
                 insImport CryptolSAW.cryptolModule $
                 emptyModule mn
       sc0 <- mkSharedContext scm
       simps <- scSimpset sc0 [] [] natConversions
       let sc = rewritingSharedContext sc0 simps
       ss <- basic_ss sc
       jcb <- JCB.loadCodebase (jarList opts) (classPath opts)
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biJavaCodebase = jcb
                 }
       let vm0 = Map.insert (qualify "basic_ss") (toValue ss) (valueEnv opts bic)
       let tm0 = Map.insert (qualify "basic_ss") (readSchema "Simpset") primTypeEnv
       ce0 <- CEnv.initCryptolEnv sc
       return (bic, InterpretEnv vm0 tm0 primDocEnv ce0)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m = fromValue <$> interpretEntry "main" opts m


-- Primitives ------------------------------------------------------------------

print_value :: SharedContext SAWCtx -> Value -> IO ()
print_value _sc (VString s) = putStrLn s
print_value  sc (VTerm _ trm) = print (evaluate sc trm)
print_value _sc v = putStrLn (showsPrecValue defaultPPOpts 0 v "")

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

  , prim "define"              "String -> Term -> TopLevel Term"
    (scVal definePrim)
    [ "TODO" ]

  , prim "print"               "{a} a -> TopLevel ()"
    (scVal print_value)
    [ "TODO" ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
    [ "TODO" ]

  , prim "print_type"          "Term -> TopLevel ()"
    (scVal print_type)
    [ "TODO" ]

  , prim "show_term"           "Term -> String"
    (pureVal (scPrettyTerm :: SharedTerm SAWCtx -> String))
    [ "TODO" ]

  , prim "check_term"          "Term -> TopLevel ()"
    (scVal check_term)
    [ "TODO" ]

  , prim "term_size"           "Term -> Int"
    (pureVal (scSharedSize :: SharedTerm SAWCtx -> Integer))
    [ "TODO" ]

  , prim "term_tree_size"      "Term -> Int"
    (pureVal (scTreeSize :: SharedTerm SAWCtx -> Integer))
    [ "TODO" ]


  , prim "sbv_uninterpreted"   "String -> Term -> TopLevel Uninterp"
    (scVal sbvUninterpreted)
    [ "TODO" ]

  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term"
    (bicVal readSBV)
    [ "TODO" ]

  , prim "read_aig"            "String -> TopLevel Term"
    (scVal readAIGPrim)
    [ "TODO" ]

  , prim "read_core"           "String -> TopLevel Term"
    (scVal readCore)
    [ "TODO" ]

  , prim "write_aig"           "String -> Term -> TopLevel ()"
    (scVal writeAIG)
    [ "TODO" ]

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
    (pureVal (writeCore :: FilePath -> SharedTerm SAWCtx -> IO ()))
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

  , prim "abc"                 "{a} ProofScript a"
    (scVal satABC)
    [ "TODO" ]

  , prim "boolector"           "{a} ProofScript a"
    (scVal satBoolector)
    [ "TODO" ]

  , prim "cvc4"                "{a} ProofScript a"
    (scVal satCVC4)
    [ "TODO" ]

  , prim "z3"                  "{a} ProofScript a"
    (scVal satZ3)
    [ "TODO" ]

  , prim "mathsat"             "{a} ProofScript a"
    (scVal satMathSAT)
    [ "TODO" ]

{-
  , prim "abc_old"             "{a} ProofScript a"
    (scVal satABCold)
    [ "TODO" ]
-}

  , prim "yices"               "{a} ProofScript a"
    (scVal satYices)
    [ "TODO" ]

  , prim "offline_aig"         "{a} String -> ProofScript a"
    (scVal satAIG)
    [ "TODO" ]

  , prim "offline_cnf"         "{a} String -> ProofScript a"
    (scVal satCNF)
    [ "TODO" ]

  , prim "offline_extcore"     "{a} String -> ProofScript a"
    (scVal satExtCore)
    [ "TODO" ]

  , prim "offline_smtlib1"     "{a} String -> ProofScript a"
    (scVal satSMTLib1)
    [ "TODO" ]

  , prim "offline_smtlib2"     "{a} String -> ProofScript a"
    (scVal satSMTLib2)
    [ "TODO" ]

  , prim "external_cnf_solver" "{a} String -> [String] -> ProofScript a"
    (scVal (satExternal True))
    [ "TODO" ]

  , prim "external_aig_solver" "{a} String -> [String] -> ProofScript a"
    (scVal (satExternal False))
    [ "TODO" ]

  , prim "empty_ss"            "Simpset"
    (pureVal (emptySimpset :: Simpset (SharedTerm SAWCtx)))
    [ "TODO" ]

  --, prim "basic_ss"            "Simpset"

  , prim "addsimp"             "Theorem -> Simpset -> Simpset"
    (scVal addsimp)
    [ "TODO" ]

  , prim "addsimp'"            "{a} a -> Simpset -> Simpset"
    (scVal addsimp')
    [ "TODO" ]

  , prim "rewrite"             "Simpset -> Term -> TopLevel Term"
    (scVal rewritePrim)
    [ "TODO" ]

  -- Java stuff

  , prim "java_bool"           "JavaType"
    (pureVal javaBool)
    [ "TODO" ]

  , prim "java_byte"           "JavaType"
    (pureVal javaByte)
    [ "TODO" ]

  , prim "java_char"           "JavaType"
    (pureVal javaChar)
    [ "TODO" ]

  , prim "java_short"          "JavaType"
    (pureVal javaShort)
    [ "TODO" ]

  , prim "java_int"            "JavaType"
    (pureVal javaInt)
    [ "TODO" ]

  , prim "java_long"           "JavaType"
    (pureVal javaLong)
    [ "TODO" ]

  , prim "java_float"          "JavaType"
    (pureVal javaFloat)
    [ "TODO" ]

  , prim "java_double"         "JavaType"
    (pureVal javaDouble)
    [ "TODO" ]

  , prim "java_array"          "Int -> JavaType -> JavaType"
    (pureVal javaArray)
    [ "TODO" ]

  , prim "java_class"          "String -> JavaType"
    (pureVal javaClass)
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

  , prim "java_verify_tactic"  "{a} ProofScript a -> JavaSetup ()"
    (bicVal javaVerifyTactic)
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

  , prim "llvm_verify_tactic"  "{a} ProofScript a -> LLVMSetup ()"
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
