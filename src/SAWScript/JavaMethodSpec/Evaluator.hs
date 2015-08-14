module SAWScript.JavaMethodSpec.Evaluator
  ( EvalContext(..)
  , evalContextFromPathState
  , ExprEvaluator
  , runEval
  , evalJavaExpr
  , evalJavaExprAsLogic
  , evalJavaRefExpr
  , evalLogicExpr
  , evalMixedExpr
  , evalMixedExprAsLogic
  , ExprEvalError(..)
    -- * Utilities
  , SpecPathState
  , SpecJavaValue
  , addAssertion
  , addAssumption
  , setArrayValue
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
import SAWScript.Utils ( SAWCtx, basic_ss)

import qualified Execution.JavaSemantics as JSS (AtomicValue(..))
import qualified Verifier.Java.Codebase as JSS (LocalVariableIndex, FieldId)
import qualified Verifier.Java.Common   as JSS


import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer (asBoolType, asBitvectorType)
import Verifier.SAW.Rewriter (rewriteSharedTerm)
import Verifier.SAW.SharedTerm

-- SpecPathState {{{1

type SpecPathState = JSS.Path (SharedContext SAWCtx)
type SpecJavaValue = JSS.Value (SharedTerm SAWCtx)

-- | Add assertion for predicate to path state.
addAssertion :: SharedContext SAWCtx -> SharedTerm SAWCtx -> SpecPathState -> IO SpecPathState
addAssertion sc x p = do
  -- TODO: p becomes an additional VC in this case
  andOp <- liftIO $ scApplyPrelude_and sc
  p & JSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- | Add assumption for predicate to path state.
addAssumption :: SharedContext SAWCtx -> SharedTerm SAWCtx -> SpecPathState -> IO SpecPathState
addAssumption sc x p = do
  andOp <- liftIO $ scApplyPrelude_and sc
  p & JSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValue :: JSS.Ref -> Int32 -> SharedTerm ctx
              -> JSS.Path (SharedContext ctx)
              -> JSS.Path (SharedContext ctx)
setArrayValue r n v =
  JSS.pathMemory . JSS.memScalarArrays %~ Map.insert r (n, v)

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext = EvalContext {
         ecContext :: SharedContext SAWCtx
       , ecLocals :: Map JSS.LocalVariableIndex SpecJavaValue
       , ecPathState :: SpecPathState
       , ecJavaExprs :: Map String TC.JavaExpr
       }

evalContextFromPathState :: SharedContext SAWCtx -> Map String TC.JavaExpr -> SpecPathState -> EvalContext
evalContextFromPathState sc m ps =
  let Just f = JSS.currentCallFrame ps
      localMap = f ^. JSS.cfLocals
  in EvalContext {
         ecContext = sc
       , ecLocals = localMap
       , ecPathState = ps
       , ecJavaExprs = m
       }

-- ExprEvalError {{{1

data ExprEvalError
  = EvalExprUndefined TC.JavaExpr
  | EvalExprBadJavaType String TC.JavaExpr
  | EvalExprBadLogicType String String
  | EvalExprUnknownArray TC.JavaExpr
  | EvalExprUnknownLocal JSS.LocalVariableIndex TC.JavaExpr
  | EvalExprUnknownField JSS.FieldId TC.JavaExpr
  | EvalExprOther String


-- ExprEvaluator {{{1

type ExprEvaluator a = ExceptT ExprEvalError IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either ExprEvalError b)
runEval v = liftIO (runExceptT v)

-- or undefined subexpression if not.
-- N.B. This method assumes that the Java path state is well-formed, the
-- the JavaExpression syntactically referes to the correct type of method
-- (static versus instance), and correct well-typed arguments.  It does
-- not assume that all the instanceFields in the JavaEvalContext are initialized.
evalJavaExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator SpecJavaValue
evalJavaExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Local _ idx _ ->
              case Map.lookup idx (ecLocals ec) of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownLocal idx expr
            TC.InstanceField r f -> do
              JSS.RValue ref <- eval r
              let ifields = (ecPathState ec) ^. JSS.pathMemory . JSS.memInstanceFields
              case Map.lookup (ref, f) ifields of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownField f expr
            TC.StaticField f -> do
              let sfields = (ecPathState ec) ^. JSS.pathMemory . JSS.memStaticFields
              case Map.lookup f sfields of
                Just v -> return v
                Nothing -> throwE $ EvalExprUnknownField f expr

evalJavaExprAsLogic :: TC.JavaExpr -> EvalContext -> ExprEvaluator (SharedTerm SAWCtx)
evalJavaExprAsLogic expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue r ->
      let arrs = (ecPathState ec) ^. JSS.pathMemory . JSS.memScalarArrays in
      case Map.lookup r arrs of
        Nothing    -> throwE $ EvalExprUnknownArray expr
        Just (_,n) -> return n
    JSS.IValue n -> return n
    JSS.LValue n -> return n
    _ -> throwE $ EvalExprBadJavaType "evalJavaExprAsLogic" expr

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr -> EvalContext
              -> ExprEvaluator SpecJavaValue
evalMixedExpr (TC.LE expr) ec = do
  n <- evalLogicExpr expr ec
  let sc = ecContext ec
  ty <- liftIO $ scTypeOf sc n
  ss <- liftIO $ basic_ss sc
  ty' <- liftIO $ rewriteSharedTerm sc ss ty
  case (asBitvectorType ty', asBoolType ty') of
    (Just 32, _) -> return (JSS.IValue n)
    (Just 64, _) -> return (JSS.LValue n)
    (Just _, _) -> throwE (EvalExprBadLogicType "evalMixedExpr" (show ty'))
    (Nothing, Just _) -> do
      b <- liftIO $ do
        boolTy <- scBoolType sc
        false <- scBool sc False
        -- TODO: fix this to work in a different way. This is endian-specific.
        scVector sc boolTy (replicate 31 false ++ [n])
      return (JSS.IValue b)
    (Nothing, Nothing) ->
      throwE (EvalExprBadLogicType "evalMixedExpr" (show ty'))
evalMixedExpr (TC.JE expr) ec = evalJavaExpr expr ec

-- | Evaluates a typed expression in the context of a particular state.
evalLogicExpr :: TC.LogicExpr -> EvalContext -> ExprEvaluator (SharedTerm SAWCtx)
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
      getExprs =
        filter (not . TC.isClassJavaExpr . snd) . Map.toList . ecJavaExprs
      exprs = getExprs ec
  args <- forM exprs $ \(_name, expr) -> do
    t <- evalJavaExprAsLogic expr ec
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) (TC.logicExprJavaExprs initExpr)
  liftIO $ TC.useLogicExpr sc initExpr argTerms

evalJavaRefExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator JSS.Ref
evalJavaRefExpr expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue ref -> return ref
    _ -> throwE $ EvalExprBadJavaType "evalJavaRefExpr" expr

evalMixedExprAsLogic :: TC.MixedExpr -> EvalContext
                     -> ExprEvaluator (SharedTerm SAWCtx)
evalMixedExprAsLogic (TC.LE expr) = evalLogicExpr expr
evalMixedExprAsLogic (TC.JE expr) = evalJavaExprAsLogic expr
