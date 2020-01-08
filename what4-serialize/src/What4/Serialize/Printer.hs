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
module SemMC.Formula.Printer
  ( printParameterizedFormula
  , printFormula
  , printFunctionFormula
  ) where

import qualified Data.Foldable as F
import qualified Data.Map as LMap
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as SL
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Pair
import qualified Data.Parameterized.Nonce as Nonce
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as Set
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           SemMC.Util ( fromJust' )

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

import qualified SemMC.Architecture as A
import qualified SemMC.BoundVar as BV
import           SemMC.Formula.Formula
import           SemMC.Formula.SETokens ( FAtom(..), printTokens'
                                        , ident', quoted', int', nat', string'
                                        , bitvec', bool'
                                        )

type SExp = SE.RichSExpr FAtom

-- This file is organized top-down, i.e., from high-level to low-level.

-- | Serialize a 'ParameterizedFormula' into its textual s-expression form.
printParameterizedFormula :: (A.Architecture arch)
                          => A.ShapeRepr arch sh
                          -> ParameterizedFormula (S.ExprBuilder t st fs) arch sh
                          -> T.Text
printParameterizedFormula rep =
  printTokens' mempty . sexprConvertParameterized rep

printFormula :: (ShowF (A.Location arch))
             => Formula (S.ExprBuilder t st fs) arch
             -> T.Text
printFormula = printTokens' mempty . sexprConvert

printFunctionFormula :: FunctionFormula (S.ExprBuilder t st fs) '(tps, tp)
                     -> T.Text
printFunctionFormula = printTokens' mempty . sexprConvertFunction

sexprConvert :: forall t st fs arch
              . (ShowF (A.Location arch))
             => Formula (S.ExprBuilder t st fs) arch
             -> SExp
sexprConvert f =
  SE.L $ (ident' "defs") : map (convertSimpleDef (Proxy @arch) (formParamVars f)) (MapF.toList (formDefs f))

convertSimpleDef :: forall arch proxy t
                  . (ShowF (A.Location arch))
                 => proxy arch
                 -> MapF.MapF (A.Location arch) (S.ExprBoundVar t)
                 -> MapF.Pair (A.Location arch) (S.Expr t)
                 -> SExp
convertSimpleDef _ paramVars (MapF.Pair loc elt) =
  SE.L [ convertLocation loc, convertExprWithLet paramLookup elt ]
  where
    tbl = LMap.fromList [ (Some bv, convertLocation l) | MapF.Pair l bv <- MapF.toList paramVars ]
    paramLookup :: ParamLookup t
    paramLookup bv = LMap.lookup (Some bv) tbl

-- | Intermediate serialization.
sexprConvertParameterized :: (A.Architecture arch)
                          => A.ShapeRepr arch sh
                          -> ParameterizedFormula (S.ExprBuilder t st fs) arch sh
                          -> SExp
sexprConvertParameterized rep (ParameterizedFormula { pfUses = uses
                                                    , pfOperandVars = opVars
                                                    , pfLiteralVars = litVars
                                                    , pfDefs = defs
                                                    }) =
  SE.L [ SE.L [SE.A (AIdent "operands"), convertOperandVars rep opVars]
       , SE.L [SE.A (AIdent "in"),       convertUses opVars uses]
       , SE.L [SE.A (AIdent "defs"),     convertDefs opVars litVars defs]
       ]

sexprConvertFunction :: FunctionFormula (S.ExprBuilder t st fs) '(tps, tp)
                     -> SExp
sexprConvertFunction (FunctionFormula { ffName = name
                                      , ffArgTypes = argTypes
                                      , ffArgVars = argVars
                                      , ffRetType = retType
                                      , ffDef = def
                                      }) =
  SE.L [ SE.L [ SE.A (AIdent "function"), SE.A (AIdent name)]
       , SE.L [ SE.A (AIdent "arguments"), convertArgumentVars argTypes argVars ]
       , SE.L [ SE.A (AIdent "return"), convertBaseType retType ]
       , SE.L [ SE.A (AIdent "body"), convertFnBody def ]
       ]

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

convertFnBody :: forall t args ret .
                 S.ExprSymFn t args ret
              -> SExp
convertFnBody (S.ExprSymFn _ _ symFnInfo _) = case symFnInfo of
  S.DefinedFnInfo argVars expr _ ->
    let paramLookup :: ParamLookup t
        -- FIXME: For now, we are just going to print the variable name because we
        -- are using FunctionFormula when we should be using ParameterizedFormula.
        paramLookup var = Just $ ident' (T.unpack (S.solverSymbolAsText (S.bvarName var)))
        -- paramLookup = flip Map.lookup argMapping . Some
        -- argMapping = buildArgsMapping argVars
    in convertExprWithLet paramLookup expr
  _ -> error "PANIC"


convertUses :: (ShowF (A.Location arch))
            => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
            -> Set.Set (Some (Parameter arch sh))
            -> SExp
convertUses oplist = SE.L . fmap (viewSome (convertParameter oplist)) . Set.toList

convertParameter :: (ShowF (A.Location arch))
                 => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
                 -> Parameter arch sh tp
                 -> SExp
convertParameter opVars (OperandParameter _ idx) = ident' name
  where name = varName (opVars SL.!! idx)
convertParameter _ (LiteralParameter loc) = quoted' (showF loc)
convertParameter opVars (FunctionParameter fnName (WrappedOperand orep oix) _) =
  SE.L [uf, args]
  where
    uf = SE.L [ ident' "_", ident' "call", string' fnName ]
    args = SE.L [convertParameter opVars (OperandParameter orep oix) ]

-- | Used for substituting in the result expression when a variable is
-- encountered in a definition.
type ParamLookup t = forall tp. S.ExprBoundVar t tp -> Maybe SExp

convertDefs :: forall t st fs arch sh.
               (ShowF (A.Location arch))
            => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
            -> MapF.MapF (A.Location arch) (S.ExprBoundVar t)
            -> MapF.MapF (Parameter arch sh) (S.Expr t)
            -> SExp
convertDefs opVars locVars = SE.L . fmap (convertDef opVars paramLookup) . MapF.toList
  where paramLookup :: ParamLookup t
        paramLookup = flip LMap.lookup paramMapping . Some
        paramMapping = MapF.foldrWithKey insertLoc opMapping locVars
        insertLoc loc var = LMap.insert (Some var) (convertLocation loc)
        opMapping = buildOpMapping opVars

convertLocation :: (ShowF loc) => loc tp -> SExp
convertLocation = quoted' . showF

-- | For use in the parameter lookup function.
buildOpMapping :: SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
               -> LMap.Map (Some (S.ExprBoundVar t)) SExp
buildOpMapping SL.Nil = LMap.empty
buildOpMapping (var SL.:< rest) =
  LMap.insert (Some (BV.unBoundVar var)) (ident' name) $ buildOpMapping rest
  where name = varName var

buildArgsMapping :: Ctx.Assignment (S.ExprBoundVar t) sh
                 -> LMap.Map (Some (S.ExprBoundVar t)) SExp
buildArgsMapping Ctx.Empty = LMap.empty
buildArgsMapping (rest Ctx.:> var) =
  LMap.insert (Some var) (ident' name) $ buildArgsMapping rest
  where name = T.unpack (S.solverSymbolAsText (S.bvarName var))

convertDef :: (ShowF (A.Location arch))
           => SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
           -> ParamLookup t
           -> Pair (Parameter arch sh) (S.Expr t)
           -> SExp
convertDef opVars paramLookup (Pair param expr) =
  SE.L [ convertParameter opVars param, convertExprWithLet paramLookup expr ]


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
        go (S.BoundVarExpr var) = return $ fromJust' ("SemMC.Formula.Printer paramLookup " ++ show (S.bvarName var)) $ paramLookup var


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
      

-- | Extract the name, as a String, of a wrapped bound variable.
varName :: BV.BoundVar (S.ExprBuilder t st fs) arch op -> String
varName (BV.BoundVar var) = show (S.bvarName var)

convertBaseType :: BaseTypeRepr tp
              -> SExp
convertBaseType tp = case tp of
  S.BaseBoolRepr -> SE.A (AQuoted "bool")
  S.BaseNatRepr -> SE.A (AQuoted "nat")
  S.BaseIntegerRepr -> SE.A (AQuoted "int")
  S.BaseRealRepr -> SE.A (AQuoted "real")
  S.BaseStringRepr -> SE.A (AQuoted "string")
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

convertOperandVars :: forall arch sh t st fs
                    . (A.Architecture arch)
                   => A.ShapeRepr arch sh
                   -> SL.List (BV.BoundVar (S.ExprBuilder t st fs) arch) sh
                   -> SExp
convertOperandVars rep l =
  case (rep, l) of
    (SL.Nil, SL.Nil) -> SE.Nil
    (r SL.:< rep', var SL.:< rest) ->
      let nameExpr = ident' (varName var)
          typeExpr = AQuoted (A.operandTypeReprSymbol (Proxy @arch) r)
      in SE.cons (SE.DL [nameExpr] typeExpr) (convertOperandVars rep' rest)

convertArgumentVars :: forall sh t st fs
                     . SL.List BaseTypeRepr sh
                    -> SL.List (S.BoundVar (S.ExprBuilder t st fs)) sh
                    -> SExp
convertArgumentVars rep l =
  case (rep, l) of
    (SL.Nil, SL.Nil) -> SE.Nil
    (r SL.:< rep', var SL.:< rest) ->
      let nameExpr = ident' (T.unpack (S.solverSymbolAsText (S.bvarName var)))
          typeExpr = convertBaseType r
      in SE.cons (SE.L [ nameExpr, typeExpr ]) (convertArgumentVars rep' rest)
