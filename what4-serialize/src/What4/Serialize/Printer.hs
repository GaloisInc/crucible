{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Serialize.Printer
  (
    printSymFn
  , printSymFnEnv
  , convertExprWithLet
  , convertBaseType
  , convertBaseTypes
  , convertSymFn
  , convertSymFnEnv
  , ParamLookup
  ) where

import qualified Data.Foldable as F
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as Nonce
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Text as T
import           Data.Word ( Word64 )

import           Control.Monad.State (State)
import qualified Control.Monad.State as State


import qualified Data.SCargot.Repr.Rich as SE

import           What4.BaseTypes
import qualified What4.Expr as S
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as S
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Interface as S
import qualified What4.Symbol as S
import           What4.Utils.Util ( fromJust', SomeSome(..) )

import           What4.Serialize.SETokens ( FAtom(..), printTokens'
                                          , ident', int', nat', string'
                                          , bitvec', bool'
                                          )

type SExp = SE.RichSExpr FAtom

-- This file is organized top-down, i.e., from high-level to low-level.

printSymFn :: S.ExprSymFn t args ret -> T.Text
printSymFn = printTokens' mempty . (convertSymFn simpleParamLookup)

printSymFnEnv :: Map T.Text (SomeSome (S.ExprSymFn t)) -> T.Text
printSymFnEnv = printTokens' mempty . (convertSymFnEnv simpleParamLookup)

simpleParamLookup :: forall t. ParamLookup t
simpleParamLookup var = Just $ ident' (T.unpack (S.solverSymbolAsText (S.bvarName var)))


convertSymFnEnv :: ParamLookup t -> Map T.Text (SomeSome (S.ExprSymFn t)) -> SExp
convertSymFnEnv paramLookup sigs =
  let
    sSymFnEnv = SE.L $ map convertSomeSymFn $ Map.assocs sigs
  in SE.L [ ident' "symfnenv", sSymFnEnv ]
  where
    convertSomeSymFn (name, SomeSome symFn) =
      SE.L [ ident' (T.unpack name), convertSymFn paramLookup symFn ]

convertExprWithLet :: ParamLookup t -> S.Expr t tp -> SExp
convertExprWithLet paramLookup expr = SE.L [SE.A (AIdent "let")
                                              , bindings
                                              , body
                                              ]
  where (body, bindingMap) = State.runState (convertExpr paramLookup expr) OMap.empty
        bindings = SE.L
          $ reverse -- OMap is LIFO, we want FIFO for binding ordering
          $ (\(key, sexp) -> SE.L [ skeyAtom key, sexp ])
          <$> OMap.assocs bindingMap

convertSymFn :: forall t args ret
              . ParamLookup t 
             -> S.ExprSymFn t args ret
             -> SExp
convertSymFn paramLookup (S.ExprSymFn _ symFnName symFnInfo _) =
  SE.L [ ident' "symfn", ident' (T.unpack $ S.solverSymbolAsText symFnName), convertInfo ]
 where
   getBoundVar :: forall tp. S.ExprBoundVar t tp -> SExp
   getBoundVar var =
      let nameExpr = ident' (T.unpack (S.solverSymbolAsText (S.bvarName var)))
          typeExpr = convertBaseType (S.bvarType var)
      in SE.L [ nameExpr, typeExpr ]
   convertInfo = case symFnInfo of
     S.DefinedFnInfo argVars expr _ ->
       let
         sArgVars = SE.L $ reverse $ FC.toListFC getBoundVar argVars
         sExpr = convertExprWithLet paramLookup expr
       in SE.L [ ident' "definedfn", sArgVars, sExpr ]
     S.UninterpFnInfo argTs retT ->
       let
         sArgTs = convertBaseTypes argTs
         sRetT = convertBaseType retT
       in SE.L [ ident' "uninterpfn", sArgTs, sRetT]
     _ -> error "Unsupported ExprSymFn kind in convertSymFn"

-- | Used for substituting in the result expression when a variable is
-- encountered in a definition.
type ParamLookup t = forall tp. S.ExprBoundVar t tp -> Maybe SExp


type Memo a = State (OMap SKey SExp) a

-- | Key for sharing SExp construction (i.e., the underlying
-- nonce 64bit integers in the What4 AST nodes)
newtype SKey = SKey {sKeyValue :: Word64}
  deriving (Eq, Ord, Show)


skeyAtom :: SKey -> SExp
skeyAtom key = ident' $ "_g"++(show $ sKeyValue key)

exprSKey :: S.Expr t tp -> Maybe SKey
exprSKey x = SKey . Nonce.indexValue <$> S.exprMaybeId x


convertExpr :: forall t tp . ParamLookup t -> S.Expr t tp -> Memo SExp
convertExpr paramLookup initialExpr = do
  case exprSKey initialExpr of
    Nothing -> go initialExpr
    Just key -> do
      cache <- State.get
      if OMap.member key cache
        then do
        return $ skeyAtom key
        else do
        sexp <- go initialExpr
        case sexp of
          SE.A _ -> return sexp -- don't memoize atomic s-expressions
          _ -> do 
            State.modify ((key, sexp) OMap.<|)
            return $ skeyAtom key
  where go :: S.Expr t tp -> Memo SExp
        go (S.SemiRingLiteral S.SemiRingNatRepr val _) = return $ SE.A $ ANat val
        go (S.SemiRingLiteral S.SemiRingIntegerRepr val _) = return $ SE.A $ AInt val -- do we need/want these?
        go (S.SemiRingLiteral S.SemiRingRealRepr _ _) = error "RatExpr not supported"
        go (S.SemiRingLiteral (S.SemiRingBVRepr _ sz) val _) = return $ SE.A (ABV (widthVal sz) val)
        go (S.StringExpr {}) = error "StringExpr is not supported"
        go (S.BoolExpr b _) = return $ bool' b
        go (S.AppExpr appExpr) = convertAppExpr' paramLookup appExpr
        go (S.NonceAppExpr nae) =
          case S.nonceExprApp nae of
            S.FnApp fn args -> convertFnApp paramLookup fn args
            S.Forall {} -> error "Forall NonceAppExpr not supported"
            S.Exists {} -> error "Exists NonceAppExpr not supported"
            S.ArrayFromFn {} -> error "ArrayFromFn NonceAppExpr not supported"
            S.MapOverArrays {} -> error "MapOverArrays NonceAppExpr not supported"
            S.ArrayTrueOnEntries {} -> error "ArrayTrueOnEntries NonceAppExpr not supported"
        go (S.BoundVarExpr var) = return $ fromJust' ("What4.Serialize.Printer paramLookup " ++ show (S.bvarName var)) $ paramLookup var


convertAppExpr' :: forall t tp . ParamLookup t -> S.AppExpr t tp -> Memo SExp
convertAppExpr' paramLookup = go . S.appExprApp
  where go :: forall tp' . S.App (S.Expr t) tp' -> Memo SExp
        go (S.BaseIte _bt _ e1 e2 e3) = do
          s1 <- goE e1
          s2 <- goE e2
          s3 <- goE e3
          return $ SE.L [ident' "ite", s1, s2, s3]
        go (S.BaseEq _bt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "=", s1, s2]
        go (S.NotPred e) = do
          s <- goE e
          return $ SE.L [ident' "notp", s]
        go (S.ConjPred bm) = convertBoolMap "andp" True bm
        go (S.DisjPred bm) = convertBoolMap "orp" False bm
        go (S.BVSlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvslt", s1, s2]
        go (S.BVUlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvult", s1, s2]
        go (S.BVConcat _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "concat", s1, s2]
        go (S.BVSelect idx n bv) = extract i j bv
          -- See SemMC.Formula.Parser.readExtract for the explanation behind
          -- these values.
          where i = intValue n + j - 1
                j = intValue idx

        -- Note that because the SemiRing has an identity element that
        -- always gets applied, resulting in lots of additional,
        -- unnecessary elements like: "(bvand #xffffffff TERM)".
        -- These will get manifested in the stored form (but generally
        -- _not_ via DSL-generated versions since they don't output
        -- via Printer) and result in longer stored forms.  They could
        -- be eliminated by checking for the identity (e.g. "if mul ==
        -- SR.one (WSum.sumRepr sm)") but the re-loaded representation
        -- will still use the SemiRing, so it's probably not worth the
        -- effort to reduce these.
        go (S.SemiRingSum sm) =
          case WSum.sumRepr sm of
            S.SemiRingBVRepr S.BVArithRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ SE.L [ ident' "bvmul", bitvec' (natValue w) mul, s]
                  sval v = return $ bitvec' (natValue w) v
                  add x y = return $ SE.L [ ident' "bvadd", x, y ]
              in WSum.evalM add smul sval sm
            S.SemiRingBVRepr S.BVBitsRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ SE.L [ ident' "bvand", bitvec' (natValue w) mul, s]
                  sval v = return $ bitvec' (natValue w) v
                  add x y = let op = ident' "bvxor" in return $ SE.L [ op, x, y ]
              in WSum.evalM add smul sval sm
            S.SemiRingNatRepr ->
              let smul mul e = do
                    s <- goE e
                    return $ SE.L [ ident' "natmul", nat' mul, s]
                  sval v = return $ nat' v
                  add x y = return $ SE.L [ ident' "natadd", x, y ]
              in WSum.evalM add smul sval sm
            S.SemiRingIntegerRepr ->
              let smul mul e = do
                    s <- goE e
                    return $ SE.L [ ident' "intmul", int' mul, s]
                  sval v = return $ int' v
                  add x y = return $ SE.L [ ident' "intadd", x, y ]
              in WSum.evalM add smul sval sm
            S.SemiRingRealRepr    -> error "SemiRingSum RealRepr not supported"

        go (S.SemiRingProd pd) =
          case WSum.prodRepr pd of
            S.SemiRingBVRepr S.BVArithRepr w -> do
              let pmul x y = return $ SE.L [ ident' "bvmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec' (natValue w) 1
            S.SemiRingBVRepr S.BVBitsRepr w -> do
              let pmul x y = return $ SE.L [ ident' "bvand", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec' (natValue w) 1
            S.SemiRingIntegerRepr -> do
              let pmul x y = return $ SE.L [ ident' "intmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ int' 1
            S.SemiRingNatRepr     -> error "convertApp S.SemiRingProd Nat unsupported"
            S.SemiRingRealRepr    -> error "convertApp S.SemiRingProd Real unsupported"

        go (S.SemiRingLe sr e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          case sr of
            S.OrderedSemiRingIntegerRepr -> do
              return $ SE.L [ ident' "intle", s1, s2]
            S.OrderedSemiRingNatRepr -> do
              return $ SE.L [ ident' "natle", s1, s2]
            S.OrderedSemiRingRealRepr -> error $ "Printer: SemiRingLe is not supported for reals"

        go (S.BVOrBits pd) =
          case WSum.prodRepr pd of
            S.SemiRingBVRepr _ w -> do
              let pmul x y = return $ SE.L [ ident' "bvor", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec' (natValue w) 0
        go (S.BVUdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvudiv", s1, s2]
        go (S.BVUrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvurem", s1, s2]
        go (S.BVSdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvsdiv", s1, s2]
        go (S.BVSrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvsrem", s1, s2]
        go (S.BVShl _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvshl", s1, s2]
        go (S.BVLshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvlshr", s1, s2]
        go (S.BVAshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "bvashr", s1, s2]
        go (S.BVZext r e) = extend "zero" (intValue r) e
        go (S.BVSext r e) = extend "sign" (intValue r) e

        go (S.BVToInteger e) = do
          s <- goE e
          return $ SE.L [ident' "bvToInteger", s]

        go (S.SBVToInteger e) = do
          s <- goE e
          return $ SE.L [ident' "sbvToInteger", s]

        go (S.IntDiv e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "intdiv", s1, s2]
        go (S.IntMod e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ SE.L [ident' "intmod", s1, s2]
        go (S.IntegerToBV e wRepr)  = do
          s <- goE e
          return $ SE.L [ident' "integerToBV"
                        , nat' (natValue wRepr)
                        , s]

        go (S.StructCtor _tps es) = do
          ss <- convertExprAssignment paramLookup es
          return $ SE.L [ident' "struct", ss]
        go (S.StructField e ix _fieldTp) = do
          s <- goE e
          return $ SE.L [ident' "field"
                        , s
                        , int' $ toInteger $ Ctx.indexVal ix
                        ]

        go (S.UpdateArray _ _ e1 es e2) = do
          s1 <- goE e1
          ss <- convertExprAssignment paramLookup es
          s2 <- goE e2
          case ss of
            SE.RSList [idx] -> return $ SE.L [ ident' "updateArray", s1, idx, s2]
            _ -> error $ "multidimensional arrays not supported"
        go (S.SelectArray _ e es) = do
          s <- goE e
          ss <- convertExprAssignment paramLookup es
          case ss of
            SE.RSList [idx] -> return $ SE.L [ ident' "select", s, idx]
            _ -> error $ "multidimensional arrays not supported"

        go app = error $ "unhandled App: " ++ show app


        -- -- -- -- Helper functions! -- -- -- --
        
        goE :: forall tp' . S.Expr t tp' -> Memo SExp
        goE = convertExpr paramLookup

        extend :: forall w. String -> Integer -> S.Expr t (BaseBVType w) -> Memo SExp
        extend op r e = do
          let w = case S.exprType e of BaseBVRepr len -> intValue len
              extension = r - w
          s <- goE e
          return $ SE.L [ SE.L [ ident' "_", ident' $ op <> "_extend", int' extension ]
                        , s
                        ]

        extract :: forall tp'. Integer -> Integer -> S.Expr t tp' -> Memo SExp
        extract i j bv = do
          s <- goE bv
          return $ SE.L [ SE.L [ ident' "_", ident' "extract", int' i, int' j ]
                        , s
                        ]

        convertBoolMap :: String -> Bool -> BooM.BoolMap (S.Expr t) -> Memo SExp
        convertBoolMap op base bm =
          let strBase b = if b
                          then SE.L [ident' "=", bitvec' 1 0, bitvec' 1 0]  -- true
                          else SE.L [ident' "=", bitvec' 1 0, bitvec' 1 1]  -- false
              strNotBase = strBase . not
          in case BooM.viewBoolMap bm of
               BooM.BoolMapUnit -> return $ strBase base
               BooM.BoolMapDualUnit -> return $ strNotBase base
               BooM.BoolMapTerms ts ->
                 let onEach e r = do
                       s <- arg e
                       return $ SE.L [ident' op, s, r]
                     arg (t, BooM.Positive) = goE t
                     arg (t, BooM.Negative) = do
                       s <- goE t
                       return $ SE.L [ident' "notp", s]
                 in F.foldrM onEach (strBase base) ts


convertExprAssignment ::
  ParamLookup t
  -> Ctx.Assignment (S.Expr t) sh
  -> Memo SExp
convertExprAssignment paramLookup es = case es of
  Ctx.Empty -> return $ SE.Nil
  es' Ctx.:> e -> do
    s <- convertExpr paramLookup e
    ss <- convertExprAssignment paramLookup es'
    return $ SE.cons s ss



convertFnApp ::
  ParamLookup t
  -> S.ExprSymFn t args ret
  -> Ctx.Assignment (S.Expr t) args
  -> Memo SExp
convertFnApp paramLookup fn args
  | name == "undefined"
  , BaseBVRepr nr <- S.fnReturnType fn = do
      let call = SE.L [ ident' "_", ident' "call", string' "uf.undefined" ]
      return $ SE.L [ call, int' (NR.intValue nr) ]
  | otherwise = do
    let call = SE.L [ ident' "_", ident' "call", string' (prefix ++ T.unpack name) ]
    ss <- convertExprAssignment paramLookup args
    return $ SE.cons call ss
  where
    name = S.solverSymbolAsText (S.symFnName fn)
    prefix = case S.symFnInfo fn of
      S.UninterpFnInfo _ _ -> "uf."
      S.DefinedFnInfo _ _ _ -> "df."
      _ -> error ("Unsupported function: " ++ T.unpack name)

convertBaseType :: BaseTypeRepr tp
              -> SExp
convertBaseType tp = case tp of
  S.BaseBoolRepr -> SE.A (AQuoted "bool")
  S.BaseNatRepr -> SE.A (AQuoted "nat")
  S.BaseIntegerRepr -> SE.A (AQuoted "int")
  S.BaseRealRepr -> SE.A (AQuoted "real")
  S.BaseStringRepr _ -> SE.A (AQuoted "string") -- parser assumes unicode
  S.BaseComplexRepr -> SE.A (AQuoted "complex")
  S.BaseBVRepr wRepr -> SE.L [SE.A (AQuoted "bv"), SE.A (AInt (NR.intValue wRepr)) ]
  S.BaseStructRepr tps -> SE.L [SE.A (AQuoted "struct"), convertBaseTypes tps]
  S.BaseArrayRepr ixs repr -> SE.L [SE.A (AQuoted "array"), convertBaseTypes ixs , convertBaseType repr]
  _ -> error "can't print base type"

convertBaseTypes ::
  Ctx.Assignment BaseTypeRepr tps
  -> SExp
convertBaseTypes = go SE.Nil
  where go :: SExp -> Ctx.Assignment BaseTypeRepr tps -> SExp
        go acc Ctx.Empty = acc
        go acc (tps Ctx.:> tp) = go (SE.cons (convertBaseType tp) acc) tps

