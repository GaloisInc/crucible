{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Some ( Some (..) )

import qualified Data.List.NonEmpty as NE

import qualified What4.Interface as S
import qualified What4.Expr as S
import qualified What4.Expr.Builder as B
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Expr.BoolMap as BooM
import qualified What4.SemiRing as SR
import           Data.Parameterized.Classes

import           Control.Monad ( zipWithM )
import           Control.Monad.Fail as MF
import           Control.Monad.Reader ( ReaderT, MonadReader )
import qualified Control.Monad.Reader as MR
import           Control.Monad.Except ( throwError, ExceptT, MonadError )
import qualified Control.Monad.Except as ME
import qualified Control.Monad.Writer as MW

normSymFn :: forall sym st fs t args ret. sym ~ B.ExprBuilder t st fs => sym -> B.ExprSymFn t args ret -> Ctx.Assignment (S.Expr t) args -> IO (S.Expr t ret)
normSymFn sym symFn argEs = case B.symFnInfo symFn of
  B.DefinedFnInfo argBVs expr _ -> do
    argEs' <- FC.traverseFC (normExpr sym) argEs
    expr' <- B.evalBoundVars sym expr argBVs argEs'
    normExpr sym expr'
  _ -> S.applySymFn sym symFn argEs


normExpr :: forall sym st fs t tp
          . sym ~ B.ExprBuilder t st fs
         => sym
         -> B.Expr t tp -> IO (B.Expr t tp)
normExpr sym e = go e
  where go :: B.Expr t tp -> IO (B.Expr t tp)
        go (B.SemiRingLiteral S.SemiRingIntegerRepr val _) = S.intLit sym val
        go (B.AppExpr appExpr) = normAppExpr sym appExpr
        go x@(B.NonceAppExpr nae) =
          case B.nonceExprApp nae of
            B.FnApp fn args -> normSymFn sym fn args
            _ -> return x
        go x = return x

-- | Normalize an expression by passing it back through the builder
-- FIXME: incomplete
normAppExpr :: forall sym st fs t tp
             . sym ~ S.ExprBuilder t st fs
            => sym
            -> S.AppExpr t tp
            -> IO (S.Expr t tp)
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
        go (S.BaseIte _ _ test then_ else_) = do
          test' <- normExpr sym test
          then' <- normExpr sym then_
          else' <- normExpr sym else_
          Just sm' <- B.asApp <$> S.baseTypeIte sym test' then' else'
          return sm'

        go (S.ConjPred bm) = do
          bm' <- BooM.traverseVars (normExpr sym) bm
          Just sm' <- B.asApp <$> B.sbMakeExpr sym (B.ConjPred bm')
          return sm'

        go (S.BVOrBits width bs) = do
          bs' <- B.traverseBVOrSet (normExpr sym) bs
          return $ B.BVOrBits width bs'

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

data ExpressionContext t = ExpressionContext [(Some (S.Expr t), Some (S.Expr t))]

data ExpressionMismatch t = forall ret ret'.
  ExpressionMismatch (S.Expr t ret) (S.Expr t ret') [(Some (S.Expr t), Some (S.Expr t))]

newtype EqCheckM t a = EqCheckM (ReaderT (ExpressionContext t) (ExceptT (ExpressionMismatch t) IO) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (ExpressionContext t)
           , MonadError (ExpressionMismatch t)
           )

instance MF.MonadFail (EqCheckM t) where
  fail _msg = throwMismatch

runSymExprEqCheck :: forall sym t st fs tp1 tp2
                   . sym ~ B.ExprBuilder t st fs
                   => sym
                   -> B.Expr t tp1
                   -> B.Expr t tp2
                   -> IO (Maybe (ExpressionMismatch t))
runSymExprEqCheck sym expr1 expr2 =
  runEqCheckM (ExpressionContext [(Some expr1, Some expr2)]) (checkExprEq' sym expr1 expr2)

runEqCheckM :: ExpressionContext t -> EqCheckM t a -> IO (Maybe (ExpressionMismatch t))
runEqCheckM ctx (EqCheckM m) = do
  ME.runExceptT (MR.runReaderT m ctx) >>= \case
    Left err -> return $ Just err
    Right _ -> return Nothing

withExprs :: S.Expr t ret1 -> S.Expr t ret2 -> EqCheckM t a -> EqCheckM t a
withExprs e1 e2 m = MR.local (\(ExpressionContext env) -> ExpressionContext ((Some e1, Some e2) : env)) m

throwMismatch :: EqCheckM t a
throwMismatch = do
  ExpressionContext ((Some e1, Some e2) : env) <- MR.ask
  throwError $ ExpressionMismatch e1 e2 env

assertEqCheck :: Bool -> EqCheckM t ()
assertEqCheck True = return ()
assertEqCheck False = throwMismatch

assertEquality :: TestEquality f => f a1 -> f a2 -> EqCheckM t (a1 :~: a2)
assertEquality a1 a2 = case testEquality a1 a2 of
  Just Refl -> return Refl
  Nothing -> throwMismatch

whenUnequal :: TestEquality f => f tp1 -> f tp2 -> EqCheckM t () -> EqCheckM t ()
whenUnequal e1 e2 m =
  case testEquality e1 e2 of
    Just Refl -> return ()
    Nothing -> m

checkSymFnEq :: forall sym st fs t args ret
             . sym ~ B.ExprBuilder t st fs
            => sym
            -> B.ExprSymFn t args ret
            -> B.ExprSymFn t args ret
            -> Ctx.Assignment (S.Expr t) args
            -> Ctx.Assignment (S.Expr t) args
            -> EqCheckM t ()
checkSymFnEq sym symFn1 symFn2 argEs1 argEs2 = do
  Refl <- assertEquality (S.symFnReturnType symFn1) (S.symFnReturnType symFn2)
  assertEqCheck (B.symFnName symFn1 == B.symFnName symFn2)
  case (B.symFnInfo symFn1, B.symFnInfo symFn2) of
    (B.DefinedFnInfo _argBVs1 expr1 _, B.DefinedFnInfo _argBVs2 expr2 _)  -> do
      _ <- checkExprsEq sym argEs1 argEs2
      checkExprEq sym expr1 expr2
    (B.UninterpFnInfo _argBVs1 retT1, B.UninterpFnInfo _argBVs2 retT2) -> do
      _ <- assertEquality retT1 retT2
      assertEqCheck True
    (B.MatlabSolverFnInfo _ _ _, B.MatlabSolverFnInfo _ _ _) -> do
      assertEqCheck True -- FIXME: what to check here?
    _ -> throwMismatch

checkExprsEq :: forall sym t st fs tps1 tps2
              . sym ~ B.ExprBuilder t st fs
             => sym
             -> Ctx.Assignment (S.Expr t) tps1
             -> Ctx.Assignment (S.Expr t) tps2
             -> EqCheckM t (tps1 :~: tps2)
checkExprsEq sym es1 es2 = do
   let reprs1 = FC.fmapFC S.exprType es1
   let reprs2 = FC.fmapFC S.exprType es2

   case testEquality reprs1 reprs2 of
     Just Refl -> do
       go es1 es2
       return Refl
     Nothing -> throwMismatch
   where
     go :: forall tps'
         . Ctx.Assignment (S.Expr t) tps'
        -> Ctx.Assignment (S.Expr t) tps'
        -> EqCheckM t ()
     go reprs1 reprs2 = case Ctx.viewAssign reprs1 of
       Ctx.AssignEmpty -> return ()
       Ctx.AssignExtend _ _ -> case (Ctx.decompose reprs1, Ctx.decompose reprs2) of
         ((reprs1', e1), (reprs2', e2)) -> do
           checkExprEq sym e1 e2
           go reprs1' reprs2'

checkExprEq' :: forall sym t st fs tp1 tp2
            . sym ~ B.ExprBuilder t st fs
            => sym
            -> B.Expr t tp1
            -> B.Expr t tp2
            -> EqCheckM t ()
checkExprEq' sym e1 e2 = withExprs e1 e1 $ do
   Refl <- assertEquality (S.exprType e1) (S.exprType e2)
   checkExprEq sym e1 e2

checkExprEq :: forall sym t st fs tp
            . sym ~ B.ExprBuilder t st fs
            => sym
            -> B.Expr t tp
            -> B.Expr t tp
            -> EqCheckM t ()
checkExprEq sym e1 e2 = withExprs e1 e2 $ do
  go e1 e2
  where go :: B.Expr t tp -> B.Expr t tp -> EqCheckM t ()
        go (B.SemiRingLiteral S.SemiRingIntegerRepr val1 _) (B.SemiRingLiteral S.SemiRingIntegerRepr val2 _)
          = assertEqCheck (val1 == val2)
        go (B.AppExpr appExpr1) (B.AppExpr appExpr2) = checkAppExprEq sym appExpr1 appExpr2
        go (B.NonceAppExpr nae1) (B.NonceAppExpr nae2) = whenUnequal (B.nonceExprId nae1) (B.nonceExprId nae2) $ do
          case (B.nonceExprApp nae1, B.nonceExprApp nae2) of
            (B.FnApp fn1 args1, B.FnApp fn2 args2) -> do
              Refl <- checkExprsEq sym args1 args2
              checkSymFnEq sym fn1 fn2 args1 args2
            (B.Forall _ _, B.Forall _ _) -> assertEqCheck True
            (B.Exists _ _, B.Exists _ _) -> assertEqCheck True
            (B.ArrayFromFn _, B.ArrayFromFn _) -> assertEqCheck True
            (B.MapOverArrays _ _ _, B.MapOverArrays _ _ _) -> assertEqCheck True
            (B.ArrayTrueOnEntries _ _, B.ArrayTrueOnEntries _ _) -> assertEqCheck True
            _ -> throwMismatch
        go _ _ = assertEqCheck True


checkExprListsEq :: sym ~ S.ExprBuilder t st fs
                 => sym
                 -> [Some (S.Expr t)]
                 -> [Some (S.Expr t)]
                 -> EqCheckM t ()
checkExprListsEq sym exprs1 exprs2 = do
  assertEqCheck (length exprs1 == length exprs2)
  _ <- zipWithM (\(Some e1) (Some e2) -> checkExprEq' sym e1 e2) exprs1 exprs2
  return ()

checkAppExprEq :: forall sym st fs t tp
                . sym ~ S.ExprBuilder t st fs
               => sym
               -> S.AppExpr t tp
               -> S.AppExpr t tp
               -> EqCheckM t ()
checkAppExprEq sym ae1 ae2 = do
  go (S.appExprApp ae1) (S.appExprApp ae2)
  where
    go :: S.App (S.Expr t) tp -> S.App (S.Expr t) tp -> EqCheckM t ()

    go (S.BaseIte _ _ test1 then1 else1) (S.BaseIte _ _ test2 then2 else2) = do
      checkExprEq sym test1 test2
      checkExprEq sym then1 then2
      checkExprEq sym else1 else2
      return ()

    go (S.BVOrBits width1 bs1) (S.BVOrBits width2 bs2) = do
      _ <- assertEquality width1 width2
      let lst1 = B.bvOrToList bs1
      let lst2 = B.bvOrToList bs2
      assertEqCheck (length lst1 == length lst2)
      _ <- zipWithM (checkExprEq sym) lst1 lst2
      return ()

    go (S.ConjPred bm1) (S.ConjPred bm2) = do
      case (BooM.viewBoolMap bm1, BooM.viewBoolMap bm2) of
        (BooM.BoolMapTerms nels1, BooM.BoolMapTerms nels2) -> do
          let ls1 = NE.toList nels1
          let ls2 = NE.toList nels2
          assertEqCheck (length ls1 == length ls2)
          _ <- zipWithM checkBooM ls1 ls2
          return ()
        (BooM.BoolMapUnit, BooM.BoolMapUnit) -> return ()
        (BooM.BoolMapDualUnit, BooM.BoolMapDualUnit) -> return ()
        _ -> throwMismatch
      where
        checkBooM :: (S.Expr t S.BaseBoolType, BooM.Polarity)
                  -> (S.Expr t S.BaseBoolType, BooM.Polarity)
                  -> EqCheckM t ()
        checkBooM (e1, p1) (e2, p2) = do
          assertEqCheck (p1 == p2)
          checkExprEq sym e1 e2

    go (S.NotPred e1) (S.NotPred e2) = checkExprEq sym e1 e2

    go (S.StructField structE1 idx1 tp1) (S.StructField structE2 idx2 tp2) = do
      Refl <- assertEquality tp1 tp2
      Refl <- assertEquality (S.exprType structE1)  (S.exprType structE2)
      checkExprEq sym structE1 structE2
      assertEqCheck (idx1 == idx2)

    go (S.StructCtor fieldTs1 fieldEs1) (S.StructCtor fieldTs2 fieldEs2) = do
      _ <- assertEquality fieldTs1 fieldTs2
      _ <- checkExprsEq sym fieldEs1 fieldEs2
      return ()

    go (S.SemiRingLe sr1 e1 e'1) (S.SemiRingLe sr2 e2 e'2) = do
      Refl <- assertEquality sr1 sr2
      checkExprEq sym e1 e2
      checkExprEq sym e'1 e'2

    go (S.SemiRingSum sm1) (S.SemiRingSum sm2) = do
      Refl <- assertEquality (WSum.sumRepr sm1) (WSum.sumRepr sm2)
      let exprs1 = exprsOfSum sm1
      let exprs2 = exprsOfSum sm2
      checkExprListsEq sym exprs1 exprs2

      let coeffs1 = coeffsOfSum sm1
      let coeffs2 = coeffsOfSum sm2
      _ <- zipWithM (\coef1 coef2 -> assertEqCheck (SR.eq (WSum.sumRepr sm1) coef1 coef2)) coeffs1 coeffs2

      return ()

    go e1 e2 = do
      Refl <- assertEquality e1 e2
      return ()


exprsOfSum :: WSum.WeightedSum (S.Expr t) sr -> [Some (S.Expr t)]
exprsOfSum ws = snd $ MW.runWriter (WSum.traverseVars (\e -> MW.tell [(Some e)] >> return e) ws)

coeffsOfSum :: WSum.WeightedSum (S.Expr t) sr -> [SR.Coefficient sr]
coeffsOfSum ws = snd $ MW.runWriter (WSum.traverseCoeffs (\e -> MW.tell [e] >> return e) ws)

data ExprEquivResult t where
  ExprEquivalent :: ExprEquivResult t
  ExprNormEquivalent :: ExprEquivResult t
  ExprUnequal :: forall t ret1 ret2.
    (S.Expr t ret1) -> (S.Expr t ret2) -> [(Some (S.Expr t), Some (S.Expr t))] -> ExprEquivResult t

testEquivExpr :: forall sym st fs t tp tp'. sym ~ S.ExprBuilder t st fs => sym -> B.Expr t tp -> B.Expr t tp' -> IO (ExprEquivResult t)
testEquivExpr sym e1 e2 = case testEquality e1 e2 of
  Just Refl -> return ExprEquivalent
  _ -> do
    e1' <- normExpr sym e1
    e2' <- normExpr sym e2
    case testEquality e1' e2' of
      Just Refl -> return ExprNormEquivalent
      _ -> runSymExprEqCheck sym e1' e2' >>= \case
        Just (ExpressionMismatch subexp1 subexp2 env) -> return $ ExprUnequal subexp1 subexp2 env
        Nothing -> return $ ExprUnequal e1' e2' []

fnAsExpr :: sym ~ S.ExprBuilder t st fs => sym -> S.SymFn sym args ret -> IO (S.Expr t ret)
fnAsExpr sym fn = do
  args <- FC.traverseFC (S.freshConstant sym (S.safeSymbol "bv")) (S.fnArgTypes fn)
  S.applySymFn sym fn args

testEquivSymFn :: forall sym st fs t args ret args' ret'. sym ~ S.ExprBuilder t st fs => sym -> S.SymFn sym args ret -> S.SymFn sym args' ret' -> IO (ExprEquivResult t)
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
             testEquivExpr sym expr1 expr2
           (S.UninterpFnInfo _ _, S.UninterpFnInfo _ _) -> return ExprEquivalent
           (_, _) -> do
             args <- FC.traverseFC (S.freshConstant sym (S.safeSymbol "bv")) argTypes1
             expr1 <- S.applySymFn sym fn1 args
             expr2 <- S.applySymFn sym fn2 args
             return $ ExprUnequal expr1 expr2 []
        | otherwise -> do
            expr1 <- fnAsExpr sym fn1
            expr2 <- fnAsExpr sym fn2
            return $ ExprUnequal expr1 expr2 []
