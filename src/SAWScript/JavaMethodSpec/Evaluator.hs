module SAWScript.JavaMethodSpec.Evaluator
  ( EvalContext(..)
  , evalContextFromPathState
  , ExprEvaluator
  , runEval
  , evalJavaExpr
  , setJavaExpr
  , evalJavaExprAsLogic
  , evalJavaRefExpr
  , evalLogicExpr
  , evalMixedExpr
  , evalMixedExprAsLogic
  , ExprEvalError(..)
    -- * Utilities
  , SpecPathState
  , SpecJavaValue
  , addAssertionPS
  , setArrayValuePS
  ) where

import Control.Lens
import Control.Monad (forM)
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.Int (Int32)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)

import qualified SAWScript.CongruenceClosure as CC (Term(..))
import qualified SAWScript.JavaExpr as TC
import SAWScript.JavaUtils
import SAWScript.Utils ( SAWCtx )

import Execution.JavaSemantics (AtomicValue(..))
import Verifier.Java.Codebase (LocalVariableIndex, FieldId)
import Verifier.Java.Common


import Verifier.SAW.Recognizer (asBoolType, asBitvectorType)
import Verifier.SAW.SharedTerm

-- SpecPathState {{{1

-- | Add assertion for predicate to path state.
addAssertionPS :: SharedContext SAWCtx -> SharedTerm SAWCtx -> SpecPathState
               -> IO SpecPathState
addAssertionPS sc x p = do
  p & pathAssertions %%~ \a -> liftIO (scAnd sc a x)

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValuePS :: Ref -> Int32 -> SharedTerm ctx
                -> Path (SharedContext ctx)
                -> Path (SharedContext ctx)
setArrayValuePS r n v =
  pathMemory . memScalarArrays %~ Map.insert r (n, v)

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext = EvalContext {
         ecContext :: SharedContext SAWCtx
       , ecLocals :: Map LocalVariableIndex SpecJavaValue
       , ecReturnValue :: Maybe SpecJavaValue
       , ecPathState :: SpecPathState
       }

evalContextFromPathState :: SharedContext SAWCtx
                         -> Maybe SpecJavaValue
                         -> SpecPathState
                         -> EvalContext
evalContextFromPathState sc rv ps =
  let Just f = currentCallFrame ps
      localMap = f ^. cfLocals
  in EvalContext {
         ecContext = sc
       , ecLocals = localMap
       , ecReturnValue = rv
       , ecPathState = ps
       }

-- ExprEvalError {{{1

data ExprEvalError
  = EvalExprUndefined TC.JavaExpr
  | EvalExprBadJavaType String TC.JavaExpr
  | EvalExprBadLogicType String String
  | EvalExprUnknownArray TC.JavaExpr
  | EvalExprUnknownLocal LocalVariableIndex TC.JavaExpr
  | EvalExprUnknownField FieldId TC.JavaExpr
  | EvalExprNoReturn
  | EvalExprOther String
  deriving Show


-- ExprEvaluator {{{1

type ExprEvaluator a = ExceptT ExprEvalError IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either ExprEvalError b)
runEval v = liftIO (runExceptT v)

-- N.B. This method assumes that the Java path state is well-formed, the the
-- JavaExpression syntactically referes to the correct type of method (static
-- versus instance), and correct well-typed arguments. It does not assume that
-- all the instanceFields in the JavaEvalContext are initialized.
evalJavaExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator SpecJavaValue
evalJavaExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.ReturnVal _ ->
              case ecReturnValue ec of
                Just rv -> return rv
                Nothing -> throwE EvalExprNoReturn
            TC.Local _ idx _ ->
              case Map.lookup idx (ecLocals ec) of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownLocal idx expr
            TC.InstanceField r f -> do
              RValue ref <- eval r
              let ifields = (ecPathState ec) ^. pathMemory . memInstanceFields
              case Map.lookup (ref, f) ifields of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownField f expr
            TC.StaticField f -> do
              let sfields = (ecPathState ec) ^. pathMemory . memStaticFields
              case Map.lookup f sfields of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownField f expr

setJavaExpr :: TC.JavaExpr -> SpecJavaValue -> EvalContext
            -> ExprEvaluator EvalContext
setJavaExpr (CC.Term app) v ec =
  case app of
    TC.ReturnVal _ ->
      return (ec { ecReturnValue = Just v })
    TC.Local _ idx _ ->
      return (ec { ecLocals = Map.insert idx v (ecLocals ec) })
    TC.InstanceField r f -> do
      RValue ref <- evalJavaExpr r ec
      return (ec { ecPathState =
                     setInstanceFieldValuePS ref f v (ecPathState ec) })
    TC.StaticField f -> do
      return (ec { ecPathState =
                     setStaticFieldValuePS f v (ecPathState ec) })

evalJavaExprAsLogic :: TC.JavaExpr -> EvalContext
                    -> ExprEvaluator (SharedTerm SAWCtx)
evalJavaExprAsLogic expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    RValue r ->
      let arrs = (ecPathState ec) ^. pathMemory . memScalarArrays in
      case Map.lookup r arrs of
        Nothing    -> throwE $ EvalExprUnknownArray expr
        Just (_,n) -> return n
    IValue n -> return n
    LValue n -> return n
    _ -> throwE $ EvalExprBadJavaType "evalJavaExprAsLogic" expr

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr -> EvalContext
              -> ExprEvaluator SpecJavaValue
evalMixedExpr (TC.LE expr) ec = do
  n <- evalLogicExpr expr ec
  let sc = ecContext ec
  ty <- liftIO $ scWhnf sc =<< scTypeOf sc n
  case (asBitvectorType ty, asBoolType ty) of
    (Just 32, _) -> return (IValue n)
    (Just 64, _) -> return (LValue n)
    (Just _, _) -> throwE (EvalExprBadLogicType "evalMixedExpr" (show ty))
    (Nothing, Just _) -> do
      b <- liftIO $ do
        boolTy <- scBoolType sc
        false <- scBool sc False
        -- TODO: fix this to work in a different way. This is endian-specific.
        scVector sc boolTy (replicate 31 false ++ [n])
      return (IValue b)
    (Nothing, Nothing) ->
      throwE (EvalExprBadLogicType "evalMixedExpr" (show ty))
evalMixedExpr (TC.JE expr) ec = evalJavaExpr expr ec

-- | Evaluates a typed expression in the context of a particular state.
evalLogicExpr :: TC.LogicExpr -> EvalContext
              -> ExprEvaluator (SharedTerm SAWCtx)
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
      exprs = TC.logicExprJavaExprs initExpr
  args <- forM exprs $ \expr -> do
    t <- evalJavaExprAsLogic expr ec
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) $
                 TC.logicExprJavaExprs initExpr
  liftIO $ TC.useLogicExpr sc initExpr argTerms

evalJavaRefExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator Ref
evalJavaRefExpr expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    RValue ref -> return ref
    _ -> throwE $ EvalExprBadJavaType "evalJavaRefExpr" expr

evalMixedExprAsLogic :: TC.MixedExpr -> EvalContext
                     -> ExprEvaluator (SharedTerm SAWCtx)
evalMixedExprAsLogic (TC.LE expr) = evalLogicExpr expr
evalMixedExprAsLogic (TC.JE expr) = evalJavaExprAsLogic expr
