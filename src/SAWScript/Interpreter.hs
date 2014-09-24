{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.Interpreter
  ( interpret
  , interpretMain
  , interpretModuleAtEntry
  , InterpretEnv(..)
  , buildInterpretEnv
  , Value, isVUnit
  , IsValue(..)
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
import qualified SAWScript.MGU as MGU
import SAWScript.Options
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
            VTerm (Just schema) trm
              -> CEnv.bindTypedTerm (qname, TypedTerm schema trm) ce
            VInteger n
              -> CEnv.bindInteger (qname, n) ce
            _ -> ce

-- Interpretation of SAWScript -------------------------------------------------

interpret
    :: forall s. SharedContext s
    -> InterpretEnv s -> SS.Expr -> IO (Value s)
interpret sc env@(InterpretEnv vm _tm ce) expr =
    case expr of
      SS.Bit b               -> return $ VBool b
      SS.String s            -> return $ VString s
      SS.Z z                 -> return $ VInteger z
      SS.Undefined           -> fail "interpret: undefined"
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
      SS.Let ds e            -> do env' <- foldM (interpretDecl sc) env ds
                                   interpret sc env' e
      SS.TSig e _            -> interpret sc env e

interpretDecl :: SharedContext s -> InterpretEnv s -> SS.Decl -> IO (InterpretEnv s)
interpretDecl sc env (SS.Decl n mt expr) = do
  v <- interpret sc env expr
  return (extendEnv n mt v env)

interpretStmts
    :: forall s. SharedContext s
    -> InterpretEnv s -> [SS.BlockStmt] -> IO (Value s)
interpretStmts sc env@(InterpretEnv vm tm ce) stmts =
    case stmts of
      [] -> fail "empty block"
      [SS.Bind Nothing _ _ e] -> interpret sc env e
      SS.Bind Nothing _ _ e : ss ->
          do v1 <- interpret sc env e
             v2 <- interpretStmts sc env ss
             return (v1 `thenValue` v2)
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
       Just (VIO v) -> do
         --putStrLn "We've been asked to execute a 'TopLevel' action, so run it."
         -- We've been asked to execute a 'TopLevel' action, so run it.
         r <- v
         return (r, interpretEnv)
       Just v -> do
         --putStrLn "We've been asked to evaluate a pure value, so wrap it up in IO and give it back."
         {- We've been asked to evaluate a pure value, so wrap it up in IO
         and give it back. -}
         return (v, interpretEnv)
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
    do let mn = case SS.moduleName m of SS.ModuleName x -> mkModuleName [x]
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
       let tm0 = transitivePrimEnv m
       ce0 <- CEnv.initCryptolEnv sc
       return (bic, InterpretEnv vm0 tm0 ce0)

-- | Interpret function 'main' using the default value environments.
interpretMain :: Options -> SS.ValidModule -> IO ()
interpretMain opts m = fromValue <$> interpretEntry "main" opts m

-- | Collects primitives from the module and all its transitive dependencies.
transitivePrimEnv :: SS.ValidModule -> Map SS.LName SS.Schema
transitivePrimEnv m = Map.unions (env : envs)
  where
    env = SS.modulePrimEnv m
    envs = map transitivePrimEnv (Map.elems (SS.moduleDependencies m))


-- Primitives ------------------------------------------------------------------

print_value :: SharedContext SAWCtx -> Value SAWCtx -> IO ()
print_value _sc (VString s) = putStrLn s
print_value  sc (VTerm _ trm) = print (evaluate sc trm)
print_value _sc v = putStrLn (showsPrecValue defaultPPOpts 0 v "")

valueEnv :: Options -> BuiltinContext -> Map SS.LName (Value SAWCtx)
valueEnv opts bic = Map.fromList
  [ (qualify "sbv_uninterpreted", toValue $ sbvUninterpreted sc)
  , (qualify "read_sbv"    , toValue $ readSBV sc)
  , (qualify "read_aig"    , toValue $ readAIGPrim sc)
  , (qualify "write_aig"   , toValue $ writeAIG sc)
  , (qualify "write_cnf"   , toValue $ writeCNF sc)
  -- Java stuff
  , (qualify "java_load_class", toValue $ loadJavaClass bic)
  , (qualify "java_browse_class", toValue browseJavaClass)
  , (qualify "java_extract", toValue $ extractJava bic opts)
  , (qualify "java_verify" , toValue $ verifyJava bic opts)
  , (qualify "java_pure"   , toValue $ javaPure)
  , (qualify "java_var"    , toValue $ javaVar bic opts)
  , (qualify "java_class_var", toValue $ javaClassVar bic opts)
  , (qualify "java_may_alias", toValue $ javaMayAlias bic opts)
  , (qualify "java_assert" , toValue $ javaAssert bic opts)
  --, (qualify "java_assert_eq" , toValue $ javaAssertEq bic opts)
  , (qualify "java_ensure_eq" , toValue $ javaEnsureEq bic opts)
  , (qualify "java_modify" , toValue $ javaModify bic opts)
  , (qualify "java_return" , toValue $ javaReturn bic opts)
  , (qualify "java_verify_tactic" , toValue $ javaVerifyTactic bic opts)
  , (qualify "java_bool"   , toValue javaBool)
  , (qualify "java_byte"   , toValue javaByte)
  , (qualify "java_char"   , toValue javaChar)
  , (qualify "java_short"  , toValue javaShort)
  , (qualify "java_int"    , toValue javaInt)
  , (qualify "java_long"   , toValue javaLong)
  , (qualify "java_float"  , toValue javaFloat)
  , (qualify "java_double" , toValue javaDouble)
  , (qualify "java_array"  , toValue javaArray)
  , (qualify "java_class"  , toValue javaClass)
  -- LLVM stuff
  , (qualify "llvm_load_module", toValue loadLLVMModule)
  , (qualify "llvm_browse_module", toValue browseLLVMModule)
  , (qualify "llvm_extract", toValue $ extractLLVM sc)
  , (qualify "llvm_verify" , toValue $ verifyLLVM bic opts)
  , (qualify "llvm_pure"   , toValue $ llvmPure)
  , (qualify "llvm_ptr"    , toValue $ llvmPtr bic opts)
  , (qualify "llvm_var"    , toValue $ llvmVar bic opts)
  -- , (qualify "llvm_may_alias", toValue $ llvmMayAlias bic opts)
  , (qualify "llvm_assert" , toValue $ llvmAssert bic opts)
  --, (qualify "llvm_assert_eq" , toValue $ llvmAssertEq bic opts)
  , (qualify "llvm_ensure_eq" , toValue $ llvmEnsureEq bic opts)
  , (qualify "llvm_modify" , toValue $ llvmModify bic opts)
  , (qualify "llvm_return" , toValue $ llvmReturn bic opts)
  , (qualify "llvm_verify_tactic" , toValue $ llvmVerifyTactic bic opts)
  , (qualify "llvm_int"    , toValue llvmInt)
  , (qualify "llvm_float"  , toValue llvmFloat)
  , (qualify "llvm_double" , toValue llvmDouble)
  , (qualify "llvm_array"  , toValue llvmArray)
  -- Generic stuff
  , (qualify "check_term"  , toValue $ check_term sc)
  , (qualify "prove"       , toValue $ provePrim sc)
  , (qualify "prove_print" , toValue $ provePrintPrim sc)
  , (qualify "sat"         , toValue $ satPrim sc)
  , (qualify "sat_print"   , toValue $ satPrintPrim sc)
  , (qualify "empty_ss"    , toValue (emptySimpset :: Simpset (SharedTerm SAWCtx)))
  , (qualify "addsimp"     , toValue $ addsimp sc)
  , (qualify "addsimp'"    , toValue $ addsimp' sc)
  , (qualify "rewrite"     , toValue $ rewritePrim sc)
  , (qualify "assume_valid", toValue (assumeValid :: ProofScript SAWCtx ProofResult))
  , (qualify "assume_unsat", toValue (assumeUnsat :: ProofScript SAWCtx SatResult))
  , (qualify "abc_old"     , toValue $ satABCold sc)
  , (qualify "abc"         , toValue $ satABC sc)
  , (qualify "yices"       , toValue $ satYices sc)
  , (qualify "external_cnf_solver", toValue $ satExternal True sc)
  , (qualify "external_aig_solver", toValue $ satExternal False sc)
  , (qualify "boolector"   , toValue $ satBoolector sc)
  , (qualify "cvc4"        , toValue $ satCVC4 sc)
  , (qualify "mathsat"     , toValue $ satMathSAT sc)
  , (qualify "z3"          , toValue $ satZ3 sc)
  , (qualify "offline_aig" , toValue $ satAIG sc)
  , (qualify "offline_cnf" , toValue $ satCNF sc)
  , (qualify "offline_extcore" , toValue $ satExtCore sc)
  , (qualify "offline_smtlib1" , toValue $ satSMTLib1 sc)
  , (qualify "offline_smtlib2" , toValue $ satSMTLib2 sc)
  , (qualify "unfolding"   , toValue $ unfoldGoal sc)
  , (qualify "simplify"    , toValue $ simplifyGoal sc)
  , (qualify "print_goal"  , toValue (printGoal :: ProofScript SAWCtx ()))
  , (qualify "write_smtlib1", toValue $ writeSMTLib1 sc)
  , (qualify "write_smtlib2", toValue $ writeSMTLib2 sc)
  , (qualify "write_core"   , toValue (writeCore :: FilePath -> SharedTerm SAWCtx -> IO ()))
  , (qualify "read_core"    , toValue $ readCore sc)
  , (qualify "term"         , toValue (id :: Value SAWCtx -> Value SAWCtx))
  , (qualify "term_size"    , toValue (scSharedSize :: SharedTerm SAWCtx -> Integer))
  , (qualify "term_tree_size", toValue (scTreeSize :: SharedTerm SAWCtx -> Integer))
  , (qualify "print"       , toValue $ print_value sc)
  , (qualify "print_type"  , toValue $ print_type sc)
  , (qualify "print_term"  , toValue ((putStrLn . scPrettyTerm) :: SharedTerm SAWCtx -> IO ()))
  , (qualify "show_term"   , toValue (scPrettyTerm :: SharedTerm SAWCtx -> String))
  , (qualify "return"      , toValue (VReturn :: Value SAWCtx -> Value SAWCtx))
  , (qualify "for"         , toValue $ \xs -> VLambda (forValue xs) :: Value SAWCtx)
    {-
  , (qualify "seq"        , toValue ((>>) :: ProofScript SAWCtx (Value SAWCtx)
                                          -> ProofScript SAWCtx (Value SAWCtx)
                                          -> ProofScript SAWCtx (Value SAWCtx))) -- FIXME: temporary
    -}
  , (qualify "define"      , toValue $ definePrim sc)
  , (qualify "caseSatResult", toValueCase sc caseSatResultPrim)
  , (qualify "caseProofResult", toValueCase sc caseProofResultPrim)
  ] where sc = biSharedContext bic

qualify :: String -> Located SS.Name
qualify s = Located s s (PosInternal "coreEnv")
