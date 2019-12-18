{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}

-- | Normalization and equivalence checking for expressions
module What4.Serialize.Normalize
  ( normSymFn
  , normExpr
  , testEquivSymFn
  , testEquivExpr
  , ExprEquivResult(..)
  ) where


import qualified Data.Parameterized.TraversableFC as FC
import qualified What4.Interface as S
import qualified What4.Expr as S
import qualified What4.Expr.Builder as B
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.WeightedSum as WSum
import           Data.Parameterized.Classes

normSymFn :: forall sym st fs t args ret. sym ~ B.ExprBuilder t st fs => sym -> B.ExprSymFn t args ret -> IO (B.ExprSymFn t args ret)
normSymFn sym symFn = case B.symFnInfo symFn of
  B.DefinedFnInfo args expr evals -> do
    expr' <- normExpr sym expr
    S.definedFn sym (B.symFnName symFn) args expr' evals
  _ -> return symFn


normExpr :: forall sym st fs t tp. sym ~ B.ExprBuilder t st fs =>
              sym

          -> B.Expr t tp -> IO (B.Expr t tp)
normExpr sym e = go e
  where go :: B.Expr t tp -> IO (B.Expr t tp)
        go (B.SemiRingLiteral S.SemiRingIntegerRepr val _) = S.intLit sym val
        go (B.AppExpr appExpr) = normAppExpr sym appExpr
        go x@(B.NonceAppExpr nae) =
          case B.nonceExprApp nae of
            B.FnApp fn args -> do
              fn' <- normSymFn sym fn
              args' <- FC.traverseFC (normExpr sym) args
              B.sbNonceExpr sym (B.FnApp fn' args')
            _ -> return x
        go x = return x

-- | Normalize an expression by passing it back through the builder
-- FIXME: incomplete
normAppExpr :: forall sym st fs t tp. sym ~ S.ExprBuilder t st fs => sym -> S.AppExpr t tp -> IO (S.Expr t tp)
normAppExpr sym ae = do
  e' <- go (S.appExprApp ae)
  B.sbMakeExpr sym e'
  where norm2 :: forall tp' tp'' tp'''
               . (S.Expr t tp' -> S.Expr t tp'' -> IO (S.Expr t tp'''))
              -> S.Expr t tp' -> S.Expr t tp'' -> IO (S.Expr t tp''')
        norm2 f e1 e2 = do
          e1' <- normExpr sym e1
          e2' <- normExpr sym e2
          f e1' e2'

        go :: forall tp'. S.App (S.Expr t) tp' -> IO (S.App (S.Expr t) tp')
        go (S.DisjPred bm) = do
          bm' <- BooM.traverseVars (normExpr sym) bm
          return (S.DisjPred bm')
        go (S.BaseIte _ _ test then_ else_) = do
          test' <- normExpr sym test
          then' <- normExpr sym then_
          else' <- normExpr sym else_
          Just sm' <- B.asApp <$> S.baseTypeIte sym test' then' else'
          return sm'
        go x@(S.SemiRingSum sm) =
          case WSum.sumRepr sm of
            S.SemiRingIntegerRepr -> do
              let
                smul si i = do
                    i' <- normExpr sym i
                    si' <- S.intLit sym si
                    S.intMul sym si' i'
              Just sm' <- B.asApp <$> WSum.evalM (norm2 $ S.intAdd sym) smul (S.intLit sym) sm
              return sm'
            _ -> return x
        go x@(S.SemiRingProd pd) =
          case WSum.prodRepr pd of
            S.SemiRingIntegerRepr -> do
                maybeS <- WSum.prodEvalM (norm2 $ S.intMul sym) return pd
                case maybeS of
                  Just s | Just sm' <- B.asApp s -> return sm'
                  _ -> return x
            _ -> return x
        go x@(S.SemiRingLe sr e1 e2) = do
          case sr of
            S.OrderedSemiRingIntegerRepr -> do
              Just sm' <- B.asApp <$> (norm2 $ S.intLe sym) e1 e2
              return sm'
            _ -> return x
        go x = return x



data ExprEquivResult = ExprEquivalent | ExprNormEquivalent | ExprUnequal

testEquivExpr :: forall sym st fs t tp tp'. sym ~ S.ExprBuilder t st fs => sym -> B.Expr t tp -> B.Expr t tp' -> IO (ExprEquivResult)
testEquivExpr sym e1 e2 = case testEquality e1 e2 of
  Just Refl -> return ExprEquivalent
  _ -> do
    e1' <- normExpr sym e1
    e2' <- normExpr sym e2
    case testEquality e1' e2' of
      Just Refl -> return ExprNormEquivalent
      _ -> return ExprUnequal

testEquivSymFn :: forall sym st fs t args ret args' ret'. sym ~ S.ExprBuilder t st fs => sym -> S.SymFn sym args ret -> S.SymFn sym args' ret' -> IO (ExprEquivResult)
testEquivSymFn sym fn1 fn2 =
  let
    argTypes1 = S.fnArgTypes fn1
    argTypes2 = S.fnArgTypes fn2
    retType1 = S.fnReturnType fn1
    retType2 = S.fnReturnType fn2
  in if | Just Refl <- testEquality argTypes1 argTypes2
        , Just Refl <- testEquality retType1 retType2
        , B.symFnName fn1 == B.symFnName fn2 ->
          case (S.symFnInfo fn1, S.symFnInfo fn2) of
           (S.DefinedFnInfo argBVs1 efn1 _, S.DefinedFnInfo argBVs2 efn2 _) -> do
             args <- FC.traverseFC (\bv -> S.freshConstant sym (S.bvarName bv) (B.bvarType bv)) argBVs1
             expr1 <- B.evalBoundVars sym efn1 argBVs1 args
             expr2 <- B.evalBoundVars sym efn2 argBVs2 args
             case testEquality expr1 expr2 of
               Just Refl -> return ExprEquivalent
               Nothing -> do
                 expr1' <- normExpr sym expr1
                 expr2' <- normExpr sym expr2
                 case testEquality expr1' expr2' of
                   Just Refl -> return ExprNormEquivalent
                   Nothing -> return ExprUnequal
           (S.UninterpFnInfo _ _, S.UninterpFnInfo _ _) -> return ExprEquivalent
           (S.MatlabSolverFnInfo _ _ _, _) -> fail "Unsupported function type for equivalence check."
           (_, S.MatlabSolverFnInfo _ _ _) -> fail "Unsupported function type for equivalence check."
           (_, _) -> return ExprUnequal
        | otherwise -> return ExprUnequal
