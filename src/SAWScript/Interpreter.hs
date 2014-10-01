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
import Verifier.SAW.Prelude (preludeModule)
import Verifier.SAW.Rewriter ( Simpset, emptySimpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.Java.Codebase as JCB
import qualified Verifier.Java.SAWBackend as JavaSAW
import qualified Verifier.LLVM.Backend.SAW as LLVMSAW

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import qualified Cryptol.TypeCheck.AST as T

-- Environment -----------------------------------------------------------------

data InterpretEnv s = InterpretEnv
  { ieValues  :: Map SS.LName (Value s)
  , ieTypes   :: Map SS.LName SS.Schema
  , ieCryptol :: CEnv.CryptolEnv s
  }

extendEnv :: SS.LName -> Maybe SS.Schema -> Value s -> InterpretEnv s -> InterpretEnv s
extendEnv x mt v (InterpretEnv vm tm ce) = InterpretEnv vm' tm' ce'
  where
    name = x
    qname = T.QName Nothing (T.Name (getOrig x))
    vm' = Map.insert name v vm
    tm' = case mt of
            Just t -> Map.insert name t tm
            Nothing -> tm
    ce' = case v of
            VTerm schema trm
              -> CEnv.bindTypedTerm (qname, TypedTerm schema trm) ce
            VInteger n
              -> CEnv.bindInteger (qname, n) ce
            _ -> ce

-- | Variation that does not force the value argument: it assumes it
-- is not a term or int.
extendEnv' :: SS.LName -> Maybe SS.Schema -> Value s -> InterpretEnv s -> InterpretEnv s
extendEnv' x mt v (InterpretEnv vm tm ce) = InterpretEnv vm' tm' ce
  where
    vm' = Map.insert x v vm
    tm' = case mt of
            Just t -> Map.insert x t tm
            Nothing -> tm

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> InterpretEnv s -> SS.Expr -> IO (Value s)
interpret sc env@(InterpretEnv vm _tm ce) expr =
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

      SS.Function x t e      -> do let f v = interpret sc (extendEnv x (fmap SS.tMono t) v env) e
                                   return $ VLambda f
      SS.Application e1 e2   -> do v1 <- interpret sc env e1
                                   v2 <- interpret sc env e2
                                   case v1 of
                                     VLambda f -> f v2
                                     _ -> fail $ "interpret Application: " ++ show v1
      SS.Let dg e            -> do env' <- interpretDeclGroup sc env dg
                                   interpret sc env' e
      SS.TSig e _            -> interpret sc env e

interpretDecl :: SharedContext s -> InterpretEnv s -> SS.Decl -> IO (InterpretEnv s)
interpretDecl sc env (SS.Decl n mt expr) = do
  v <- interpret sc env expr
  return (extendEnv n mt v env)

interpretFunction :: SharedContext s -> InterpretEnv s -> SS.Expr -> Value s
interpretFunction sc env expr =
    case expr of
      SS.Function x t e -> VLambda f
        where f v = interpret sc (extendEnv x (fmap SS.tMono t) v env) e
      SS.TSig e _ -> interpretFunction sc env e
      _ -> error "interpretFunction: not a function"

interpretDeclGroup :: SharedContext s -> InterpretEnv s -> SS.DeclGroup -> IO (InterpretEnv s)
interpretDeclGroup sc env (SS.NonRecursive d) =
  interpretDecl sc env d
interpretDeclGroup sc env (SS.Recursive ds) = return env'
  where env' = foldr ($) env [ extendEnv' n mty (interpretFunction sc env' e) | SS.Decl n mty e <- ds ]

interpretStmts
    :: forall s. SharedContext s
    -> InterpretEnv s -> [SS.BlockStmt] -> IO (Value s)
interpretStmts sc env@(InterpretEnv vm tm ce) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ _ e] -> interpret sc env e
      SS.Bind Nothing _ _ e : ss ->
          do v1 <- interpret sc env e
             return $ VBind v1 $ VLambda $ const $ interpretStmts sc env ss
      SS.Bind (Just x) mt _ e : ss ->
          do v1 <- interpret sc env e
             let f v = interpretStmts sc (extendEnv x (fmap SS.tMono mt) v env) ss
             bindValue v1 (VLambda f)
      SS.BlockLet bs : ss -> interpret sc env (SS.Let bs (SS.Block ss))
      SS.BlockCode s : ss ->
          do ce' <- CEnv.parseDecls sc ce s
             interpretStmts sc (InterpretEnv vm tm ce') ss

interpretModule
    :: forall s. SharedContext s
    -> InterpretEnv s -> SS.ValidModule -> IO (InterpretEnv s)
interpretModule sc env m =
    do cenv' <- foldM (CEnv.importModule sc) (ieCryptol env) (SS.moduleCryDeps m)
       let env' = env { ieCryptol = cenv' }
       let decls = SS.moduleExprEnv m
       foldM (interpretDecl sc) env' decls

interpretModuleAtEntry :: SS.Name
                          -> SharedContext s
                          -> InterpretEnv s
                          -> SS.ValidModule
                          -> IO (Value s, InterpretEnv s)
interpretModuleAtEntry entryName sc env m =
  do interpretEnv@(InterpretEnv vm _tm _ce) <- interpretModule sc env m
     let mainName = Located entryName entryName (PosInternal "entry")
     case Map.lookup mainName vm of
       Just v -> do
         --putStrLn "We've been asked to execute a 'TopLevel' action, so run it."
         -- We've been asked to execute a 'TopLevel' action, so run it.
         r <- fromValue v
         return (r, interpretEnv)
       Nothing -> fail $ "No " ++ entryName ++ " in module " ++ show (SS.moduleName m)

-- | Interpret an expression using the default value environments.
interpretEntry :: SS.Name -> Options -> SS.ValidModule -> IO (Value SAWCtx)
interpretEntry entryName opts m =
    do (bic, interpretEnv0) <- buildInterpretEnv opts m
       let sc = biSharedContext bic
       (result, _interpretEnv) <-
         interpretModuleAtEntry entryName sc interpretEnv0 m
       return result

buildInterpretEnv :: Options -> SS.ValidModule
                  -> IO (BuiltinContext, InterpretEnv SAWCtx)
buildInterpretEnv opts m =
    do let mn = mkModuleName [SS.moduleName m]
       let scm = insImport preludeModule $
                 insImport JavaSAW.javaModule $
                 insImport LLVMSAW.llvmModule $
                 insImport CryptolSAW.cryptolModule $
                 emptyModule mn
       sc <- mkSharedContext scm
       ss <- basic_ss sc
       jcb <- JCB.loadCodebase (jarList opts) (classPath opts)
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biJavaCodebase = jcb
                 }
       let vm0 = Map.insert (qualify "basic_ss") (toValue ss) (valueEnv opts bic)
       let tm0 = Map.insert (qualify "basic_ss") (readSchema "Simpset") primTypeEnv
       ce0 <- CEnv.initCryptolEnv sc
       return (bic, InterpretEnv vm0 tm0 ce0)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m = fromValue <$> interpretEntry "main" opts m


-- Primitives ------------------------------------------------------------------

print_value :: SharedContext SAWCtx -> Value SAWCtx -> IO ()
print_value _sc (VString s) = putStrLn s
print_value  sc (VTerm _ trm) = print (evaluate sc trm)
print_value _sc v = putStrLn (showsPrecValue defaultPPOpts 0 v "")

readSchema :: String -> SS.Schema
readSchema str =
  case parseSchema (lexSAW "internal" str) of
    Left err -> error (show err)
    Right schema -> schema

primitives :: Map SS.LName (SS.Schema, Options -> BuiltinContext -> Value SAWCtx)
primitives = Map.fromList
  [ prim "return"              "{m, a} a -> m a"                      $ pureVal (VReturn :: Value SAWCtx -> Value SAWCtx)
  , prim "for"                 "{m, a, b} [a] -> (a -> m b) -> m [b]" $ pureVal (\xs -> VLambda (forValue xs) :: Value SAWCtx)
  , prim "define"              "String -> Term -> TopLevel Term"      $ scVal definePrim
  , prim "print"               "{a} a -> TopLevel ()"                 $ scVal print_value
  , prim "print_term"          "Term -> TopLevel ()"                  $ pureVal ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ())
  , prim "print_type"          "Term -> TopLevel ()"                  $ scVal print_type
  , prim "show_term"           "Term -> String"                       $ pureVal (scPrettyTerm :: SharedTerm SAWCtx -> String)
  , prim "check_term"          "Term -> TopLevel ()"                  $ scVal check_term
  , prim "term_size"           "Term -> Int"                          $ pureVal (scSharedSize :: SharedTerm SAWCtx -> Integer)
  , prim "term_tree_size"      "Term -> Int"                          $ pureVal (scTreeSize :: SharedTerm SAWCtx -> Integer)

  , prim "sbv_uninterpreted"   "String -> Term -> TopLevel Uninterp"   $ scVal sbvUninterpreted
  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term" $ scVal readSBV
  , prim "read_aig"            "String -> TopLevel Term"               $ scVal readAIGPrim
  , prim "read_core"           "String -> TopLevel Term"               $ scVal readCore
  , prim "write_aig"           "String -> Term -> TopLevel ()"         $ scVal writeAIG
  , prim "write_cnf"           "String -> Term -> TopLevel ()"         $ scVal writeCNF
  , prim "write_smtlib1"       "String -> Term -> TopLevel ()"         $ scVal writeSMTLib1
  , prim "write_smtlib2"       "String -> Term -> TopLevel ()"         $ scVal writeSMTLib2
  , prim "write_core"          "String -> Term -> TopLevel ()"         $ pureVal (writeCore :: FilePath -> SharedTerm SAWCtx -> IO ())

  , prim "prove"               "{b} ProofScript b -> Term -> TopLevel ProofResult" $ scVal provePrim
  , prim "prove_print"         "{b} ProofScript b -> Term -> TopLevel Theorem"     $ scVal provePrintPrim
  , prim "sat"                 "{b} ProofScript b -> Term -> TopLevel SatResult"   $ scVal satPrim
  , prim "sat_print"           "{b} ProofScript b -> Term -> TopLevel ()"          $ scVal satPrintPrim

  , prim "unfolding"           "[String] -> ProofScript ()"  $ scVal unfoldGoal
  , prim "simplify"            "Simpset -> ProofScript ()"   $ scVal simplifyGoal
  , prim "print_goal"          "ProofScript ()"              $ pureVal (printGoal :: ProofScript SAWCtx ())
  , prim "assume_valid"        "ProofScript ProofResult"     $ pureVal (assumeValid :: ProofScript SAWCtx ProofResult)
  , prim "assume_unsat"        "ProofScript SatResult"       $ pureVal (assumeUnsat :: ProofScript SAWCtx SatResult)
  , prim "abc"                 "{a} ProofScript a"           $ scVal satABC
  , prim "boolector"           "{a} ProofScript a"           $ scVal satBoolector
  , prim "cvc4"                "{a} ProofScript a"           $ scVal satCVC4
  , prim "z3"                  "{a} ProofScript a"           $ scVal satZ3
  , prim "mathsat"             "{a} ProofScript a"           $ scVal satMathSAT
  , prim "abc_old"             "{a} ProofScript a"           $ scVal satABCold
  , prim "yices"               "{a} ProofScript a"           $ scVal satYices
  , prim "offline_aig"         "{a} String -> ProofScript a" $ scVal satAIG
  , prim "offline_cnf"         "{a} String -> ProofScript a" $ scVal satCNF
  , prim "offline_extcore"     "{a} String -> ProofScript a" $ scVal satExtCore
  , prim "offline_smtlib1"     "{a} String -> ProofScript a" $ scVal satSMTLib1
  , prim "offline_smtlib2"     "{a} String -> ProofScript a" $ scVal satSMTLib2

  , prim "external_cnf_solver" "{a} String -> [String] -> ProofScript a" $ scVal (satExternal True)
  , prim "external_aig_solver" "{a} String -> [String] -> ProofScript a" $ scVal (satExternal False)

  , prim "empty_ss"            "Simpset"                          $ pureVal (emptySimpset :: Simpset (SharedTerm SAWCtx))
  --, prim "basic_ss"            "Simpset"                          $
  , prim "addsimp"             "Theorem -> Simpset -> Simpset"    $ scVal addsimp
  , prim "addsimp'"            "{a} a -> Simpset -> Simpset"      $ scVal addsimp'
  , prim "rewrite"             "Simpset -> Term -> TopLevel Term" $ scVal rewritePrim
  -- Java stuff
  , prim "java_bool"           "JavaType"                    $ pureVal javaBool
  , prim "java_byte"           "JavaType"                    $ pureVal javaByte
  , prim "java_char"           "JavaType"                    $ pureVal javaChar
  , prim "java_short"          "JavaType"                    $ pureVal javaShort
  , prim "java_int"            "JavaType"                    $ pureVal javaInt
  , prim "java_long"           "JavaType"                    $ pureVal javaLong
  , prim "java_float"          "JavaType"                    $ pureVal javaFloat
  , prim "java_double"         "JavaType"                    $ pureVal javaDouble
  , prim "java_array"          "Int -> JavaType -> JavaType" $ pureVal javaArray
  , prim "java_class"          "String -> JavaType"          $ pureVal javaClass
  --, prim "java_value"          "{a} String -> a"
  , prim "java_var"            "String -> JavaType -> JavaSetup Term"  $ bicVal javaVar
  , prim "java_class_var"      "{a} String -> JavaType -> JavaSetup a" $ bicVal javaClassVar
  , prim "java_may_alias"      "[String] -> JavaSetup ()"              $ bicVal javaMayAlias
  , prim "java_assert"         "Term -> JavaSetup ()"                  $ bicVal javaAssert
  --, prim "java_assert_eq"      "{a} String -> a -> JavaSetup ()"       $ bicVal javaAssertEq
  , prim "java_ensure_eq"      "String -> Term -> JavaSetup ()"        $ bicVal javaEnsureEq
  , prim "java_modify"         "String -> JavaSetup ()"                $ bicVal javaModify
  , prim "java_return"         "Term -> JavaSetup ()"                  $ bicVal javaReturn
  , prim "java_verify_tactic"  "{a} ProofScript a -> JavaSetup ()"     $ bicVal javaVerifyTactic
  , prim "java_pure"           "JavaSetup ()"                          $ pureVal javaPure
  , prim "java_load_class"     "String -> TopLevel JavaClass"          $ bicVal (const . loadJavaClass)
  , prim "java_browse_class"   "JavaClass -> TopLevel ()"              $ pureVal browseJavaClass
  --, prim "java_class_info"     "JavaClass -> TopLevel ()"
  , prim "java_extract"        "{a} JavaClass -> String -> JavaSetup () -> TopLevel a"
                                                                       $ bicVal extractJava
  , prim "java_verify"         "JavaClass -> String -> [JavaMethodSpec] -> JavaSetup () -> TopLevel JavaMethodSpec"
                                                                       $ bicVal verifyJava

  , prim "llvm_int"            "Int -> LLVMType"                      $ pureVal llvmInt
  , prim "llvm_float"          "LLVMType"                             $ pureVal llvmFloat
  , prim "llvm_double"         "LLVMType"                             $ pureVal llvmDouble
  , prim "llvm_array"          "Int -> LLVMType -> LLVMType"          $ pureVal llvmArray
  --, prim "llvm_value"          "{a} String -> a"                      $ 
  , prim "llvm_var"            "String -> LLVMType -> LLVMSetup Term" $ bicVal llvmVar
  , prim "llvm_ptr"            "String -> LLVMType -> LLVMSetup Term" $ bicVal llvmPtr
  --, prim "llvm_may_alias"      "[String] -> LLVMSetup ()" $ bicVal llvmMayAlias
  , prim "llvm_assert"         "Term -> LLVMSetup ()"                 $ bicVal llvmAssert
  --, prim "llvm_assert_eq"      "{a} String -> a -> LLVMSetup ()"      $ bicVal llvmAssertEq
  , prim "llvm_ensure_eq"      "String -> Term -> LLVMSetup ()"       $ bicVal llvmEnsureEq
  , prim "llvm_modify"         "String -> LLVMSetup ()"               $ bicVal llvmModify
  , prim "llvm_return"         "Term -> LLVMSetup ()"                 $ bicVal llvmReturn
  , prim "llvm_verify_tactic"  "{a} ProofScript a -> LLVMSetup ()"    $ bicVal llvmVerifyTactic
  , prim "llvm_pure"           "LLVMSetup ()"                         $ pureVal llvmPure
  , prim "llvm_load_module"    "String -> TopLevel LLVMModule"        $ pureVal loadLLVMModule
  , prim "llvm_browse_module"  "LLVMModule -> TopLevel ()"            $ pureVal browseLLVMModule
  --, prim "llvm_module_info"    "LLVMModule -> TopLevel ()"            $ 
  , prim "llvm_extract"        "LLVMModule -> String -> LLVMSetup () -> TopLevel Term" $ scVal extractLLVM
  , prim "llvm_verify"         "LLVMModule -> String -> [LLVMMethodSpec] -> LLVMSetup () -> TopLevel LLVMMethodSpec" $ bicVal verifyLLVM

  , prim "caseSatResult"       "{b} SatResult -> b -> (Term -> b) -> b"   $ \_ bic -> toValueCase (biSharedContext bic) caseSatResultPrim
  , prim "caseProofResult"     "{b} ProofResult -> b -> (Term -> b) -> b" $ \_ bic -> toValueCase (biSharedContext bic) caseProofResultPrim
  ]
  where
    prim :: forall a. String -> String -> a -> (SS.LName, (SS.Schema, a))
    prim s1 s2 v = (qualify s1, (readSchema s2, v))

    pureVal :: forall t. IsValue SAWCtx t => t -> Options -> BuiltinContext -> Value SAWCtx
    pureVal x _ _ = toValue x

    scVal :: forall t. IsValue SAWCtx t =>
             (SharedContext SAWCtx -> t) -> Options -> BuiltinContext -> Value SAWCtx
    scVal f _ bic = toValue (f (biSharedContext bic))

    bicVal :: forall t. IsValue SAWCtx t =>
              (BuiltinContext -> Options -> t) -> Options -> BuiltinContext -> Value SAWCtx
    bicVal f opts bic = toValue (f bic opts)

primTypeEnv :: Map SS.LName SS.Schema
primTypeEnv = fmap fst primitives

valueEnv :: Options -> BuiltinContext -> Map SS.LName (Value SAWCtx)
valueEnv opts bic = fmap f primitives
  where f (_, v) = v opts bic

qualify :: String -> Located SS.Name
qualify s = Located s s (PosInternal "coreEnv")
