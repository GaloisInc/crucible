{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.BSV.Translation
-- Description      : This module performs the work of tranlating Bluespec System Verilog (BSV)
--                    into a Cucible control-flow graph.
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3


module Lang.Crucible.BSV.Translation where

import           Control.Monad.State
import           Control.Monad.ST

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some

import qualified Lang.Crucible.Core as C
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Generator
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.SSAConversion
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

import qualified Lang.BSV.AST as S
import           Lang.Crucible.BSV.Analysis

data BSVBinding s where
  BSV_BindExpr :: S.Type -> TypeRepr tp -> Expr s tp -> BSVExpr s
  BSV_BindCAF  :: S.Type -> TypeRepr tp -> FunctionHandle Ctx.Empty tp -> BSVExpr s

type ValueEnv s = Map S.Ident (BSVBinding s)


data BSVExpr s where
  BSVExpr :: S.Type -> TypeRepr tp -> Expr s tp -> BSVExpr s

exprTy :: BSVExpr s -> S.Type
exprTy (BSVExpr t _ _) = t

type VarEnv s = Map S.Ident (BSVExpr s)

data BSVState s =
  BSVState
  { bsvStateVars :: VarEnv s
  , bsvTypeEnv   :: TypeEnv
  , bsvLastExpr  :: Maybe (BSVExpr s)
  }

type BSVGen h s ret a = Generator h s BSVState ret a

lookupVar :: S.Ident
          -> BSVGen h s ret (BSVExpr s)
lookupVar nm = do
  mp <- bsvStateVars <$> get
  case Map.lookup nm mp of
    Just x  -> return x
    Nothing -> fail $ unwords ["Variable not found in local scope: ", show nm]

stashExpr :: BSVExpr s
          -> BSVGen h s ret ()
stashExpr ex = do
  modify $ \st -> st{ bsvLastExpr = Just ex }

returnStashedVal :: TypeRepr ret
                 -> BSVGen h s ret (Expr s ret)
returnStashedVal tpr = do
  st <- get
  case bsvLastExpr st of
    Just (BSVExpr _t tpr' x)
      | Just Refl <- testEquality tpr tpr' -> return x
      | otherwise -> fail $ "Returned value does not match expected return type"
    Nothing -> fail "No value returned from function!"



logicalBinOp
  :: String
  -> (Expr s BoolType -> Expr s BoolType -> C.App (Expr s) BoolType)
  -> BSVExpr s -> BSVExpr s -> BSVGen h s ret (BSVExpr s)
logicalBinOp _nm f (BSVExpr (S.TypeCon "Bool" []) BoolRepr x)
                   (BSVExpr (S.TypeCon "Bool" []) BoolRepr y) =
  return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr (app $ f x y)
logicalBinOp nm _ x y =
  fail $ unwords ["Type error in binary logical operation", nm
                 , show $ exprTy x, show $ exprTy y
                 ]

logicalUnaryOp
  :: String
  -> (Expr s BoolType -> C.App (Expr s) BoolType)
  -> BSVExpr s -> BSVGen h s ret (BSVExpr s)
logicalUnaryOp _nm f (BSVExpr (S.TypeCon "Bool" []) BoolRepr x) =
  return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr (app $ f x)
logicalUnaryOp nm _ x =
  fail $ unwords ["Type error in unary logical operation", nm
                 , show $ exprTy x
                 ]


baseCmpMethod
   :: String
   -> (Expr s IntegerType -> Expr s IntegerType -> Expr s BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseCmpMethod nm integerF intF uintF bitsF args = case args of
  [  BSVExpr (S.TypeCon "Integer" []) IntegerRepr x
   , BSVExpr (S.TypeCon "Integer" []) IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ integerF x y

  [  BSVExpr (S.TypeCon "Int" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Int" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ app $ intF wx x y

  [  BSVExpr (S.TypeCon "Bit" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Bit" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ app $ uintF wx x y

  [  BSVExpr (S.TypeCon "UInt" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "UInt" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ app $ bitsF wx x y

  _ -> fail $ unwords ["Invalid types for comparison operation", nm, show (map exprTy args)]

baseBitwiseMethod
   :: String
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseBitwiseMethod nm bitsF args = case args of
  [  BSVExpr (S.TypeCon "Int" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Int" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Int" [S.TypeNat ix]) (BVRepr wx)
               $ app $ bitsF wx x y

  [  BSVExpr (S.TypeCon "Bit" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Bit" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat ix]) (BVRepr wx)
               $ app $ bitsF wx x y

  [  BSVExpr (S.TypeCon "UInt" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "UInt" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "UInt" [S.TypeNat ix]) (BVRepr wx)
               $ app $ bitsF wx x y

  _ -> fail $ unwords ["Invalid types for bitwise operation", nm, show (map exprTy args)]

baseArithMethod
   :: String
   -> (Expr s IntegerType -> Expr s IntegerType -> Expr s IntegerType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseArithMethod nm integerF intF uintF bitsF args = case args of
  [  BSVExpr (S.TypeCon "Integer" []) IntegerRepr x
   , BSVExpr (S.TypeCon "Integer" []) IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Integer" []) IntegerRepr
               $ integerF x y

  [  BSVExpr (S.TypeCon "Int" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Int" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Int" [S.TypeNat ix]) (BVRepr wx)
               $ app $ intF wx x y

  [  BSVExpr (S.TypeCon "Bit" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "Bit" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat ix]) (BVRepr wx)
               $ app $ uintF wx x y

  [  BSVExpr (S.TypeCon "UInt" [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (S.TypeCon "UInt" [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy
     , Just Refl <- testEquality wx wy
     -> return $ BSVExpr (S.TypeCon "UInt" [S.TypeNat ix]) (BVRepr wx)
               $ app $ bitsF wx x y

  _ -> fail $ unwords ["Invalid types for arithmetic operation", nm, show (map exprTy args)]


-- FIXME, we really need to to a typechecking pass on the AST first.
-- Otherwise, we can only resolve typeclasses based on the types of the
-- argument and not based on the result type.  This is less expressive
-- than full typeclass resolution, but does the job for many useful cases
-- of interest...
--
-- FIXME, this very explicit listing of typeclass methods isn't really
-- very sustanable...
applyTypeclassMethod
   :: S.Ident
   -> S.Ident
   -> [BSVExpr s]
   -> BSVGen h s ret (BSVExpr s)
applyTypeclassMethod "Arith" "+" =
   baseArithMethod "+" (.+) C.BVAdd C.BVAdd C.BVAdd
applyTypeclassMethod "Arith" "-" =
   baseArithMethod "-" (.-) C.BVSub C.BVSub C.BVSub
applyTypeclassMethod "Arith" "*" =
   baseArithMethod "*" (.*) C.BVMul C.BVMul C.BVMul
applyTypeclassMethod "Arith" "/" =
   baseArithMethod "/" (error "Integer division") C.BVSdiv C.BVUdiv C.BVUdiv
applyTypeclassMethod "Arith" "%" =
   baseArithMethod "/" (error "Integer modulus") C.BVSrem C.BVUrem C.BVUrem

applyTypeclassMethod "Eq" "==" =
   baseCmpMethod "==" (.==) C.BVEq C.BVEq C.BVEq
applyTypeclassMethod "Eq" "/=" =
   baseCmpMethod "/=" (./=)
                      (\w x y -> C.Not (app (C.BVEq w x y)))
                      (\w x y -> C.Not (app (C.BVEq w x y)))
                      (\w x y -> C.Not (app (C.BVEq w x y)))

applyTypeclassMethod "Ord" "<" =
   baseCmpMethod "<"  (.<) C.BVSlt C.BVUlt C.BVUlt
applyTypeclassMethod "Ord" "<=" =
   baseCmpMethod "<=" (.<=) C.BVSle C.BVUle C.BVUle
applyTypeclassMethod "Ord" ">" =
   baseCmpMethod ">"  (.>)
                      (\w -> flip $ C.BVSlt w)
                      (\w -> flip $ C.BVUlt w)
                      (\w -> flip $ C.BVUlt w)
applyTypeclassMethod "Ord" ">=" =
   baseCmpMethod ">=" (.>=)
                      (\w -> flip $ C.BVSle w)
                      (\w -> flip $ C.BVUle w)
                      (\w -> flip $ C.BVUle w)

applyTypeclassMethod "Bitwise" "negate" = \xs ->
   -- FIXME, bit of a hack...
   baseBitwiseMethod "negate" (\w x _ -> C.BVNot w x) (xs ++ xs)

applyTypeclassMethod "Bitwise" "&" =
   baseBitwiseMethod "&" C.BVAnd
applyTypeclassMethod "Bitwise" "|" =
   baseBitwiseMethod "|" C.BVOr
applyTypeclassMethod "Bitwise" "^" =
   baseBitwiseMethod "^" C.BVXor
applyTypeclassMethod "Bitwise" "~^" =
   baseBitwiseMethod "~^" (\w x y -> C.BVNot w (app $ C.BVXor w x y))
applyTypeclassMethod "Bitwise" "^~" =
   baseBitwiseMethod "^~" (\w x y -> C.BVNot w (app $ C.BVXor w x y))

applyTypeclassMethod cls mth =
  fail $ unwords ["Unknown typelcass method:", cls, mth]


unaryOp :: S.UnaryOp
        -> BSVExpr s
        -> BSVGen h s ret (BSVExpr s)
unaryOp op x =
  case op of
    S.UOpPlus      -> return x
    S.UOpMinus     -> applyTypeclassMethod "Arith" "negate" [x]
    S.UOpBang      -> logicalUnaryOp "!" C.Not x
    S.UOpTilde     -> applyTypeclassMethod "Bitwise" "invert" [x]
    S.UOpAmp       -> applyTypeclassMethod "BitReduction" "reduceAnd" [x]
    S.UOpTildeAmp  -> applyTypeclassMethod "BitReduction" "reduceNand" [x]
    S.UOpVBar      -> applyTypeclassMethod "BitReduction" "reduceOr" [x]
    S.UOpTildeVBar -> applyTypeclassMethod "BitReduction" "reduceNor" [x]
    S.UOpHat       -> applyTypeclassMethod "BitReduction" "reduceXor" [x]
    S.UOpTildeHat  -> applyTypeclassMethod "BitReduction" "reduceXnor" [x]
    S.UOpHatTilde  -> applyTypeclassMethod "BitReduction" "reduceXnor" [x]

binaryOp :: S.BinaryOp
         -> BSVExpr s
         -> BSVExpr s
         -> BSVGen h s ret (BSVExpr s)
binaryOp op x y =
  case op of
    S.BinOpPlus    -> applyTypeclassMethod "Arith" "+" [x,y]
    S.BinOpMinus   -> applyTypeclassMethod "Arith" "-" [x,y]
    S.BinOpStar    -> applyTypeclassMethod "Arith" "*" [x,y]
    S.BinOpSlash   -> applyTypeclassMethod "Arith" "/" [x,y]
    S.BinOpPercent -> applyTypeclassMethod "Arith" "%" [x,y]

    S.BinOpEqEq    -> applyTypeclassMethod "Eq" "==" [x,y]
    S.BinOpSlashEq -> applyTypeclassMethod "Eq" "/=" [x,y]

    S.BinOpLt      -> applyTypeclassMethod "Ord" "<"   [x,y]
    S.BinOpLtEq    -> applyTypeclassMethod "Ord" "<="  [x,y]
    S.BinOpGt      -> applyTypeclassMethod "Ord" ">"   [x,y]
    S.BinOpGtEq    -> applyTypeclassMethod "Ord" ">="  [x,y]

    S.BinOpAmp      -> applyTypeclassMethod "Bitwise" "&" [x,y]
    S.BinOpVBar     -> applyTypeclassMethod "Bitwise" "|" [x,y]
    S.BinOpHat      -> applyTypeclassMethod "Bitwise" "^" [x,y]
    S.BinOpTildeHat -> applyTypeclassMethod "Bitwise" "~^" [x,y]
    S.BinOpHatTilde -> applyTypeclassMethod "Bitwise" "^~" [x,y]
    S.BinOpLtLt     -> applyTypeclassMethod "Bitwise" "<<" [x,y]
    S.BinOpGtGt     -> applyTypeclassMethod "Bitwise" ">>" [x,y]

    S.BinOpAmpAmp   -> logicalBinOp "&&" C.And x y
    S.BinOpVBarVBar -> logicalBinOp "||" C.Or  x y


translateCondPred
  :: S.CondPredicate
  -> BSVGen h s ret (Expr s BoolType)
translateCondPred = undefined


translateCondPreds
  :: [S.CondPredicate]
  -> BSVGen h s ret (Expr s BoolType)
translateCondPreds =
  foldM (\xs p -> do x <- translateCondPred p 
                     return (xs .&& x))
        (litExpr True)

translateExpr :: S.Expr
              -> BSVGen h s ret (BSVExpr s)
translateExpr ex = case ex of
  S.ExprVar nm -> lookupVar nm
  S.ExprIntLit n        -> return $ BSVExpr (S.TypeCon "Integer" []) IntegerRepr $ app $ C.IntLit n
  S.ExprRealLit r       -> return $ BSVExpr (S.TypeCon "Real" []) RealValRepr $ app $ C.RationalLit r
  S.ExprStringLit s     -> return $ BSVExpr (S.TypeCon "String" []) StringRepr $ app $ C.TextLit $ Text.pack s
  S.ExprUnaryOp op x    -> join (unaryOp op <$> translateExpr x)
  S.ExprBinaryOp x op y -> join (binaryOp op <$> translateExpr x <*> translateExpr y)
  S.ExprCond ps x y -> do
      cond <- translateCondPreds ps
      BSVExpr xt xtr x' <- translateExpr x
      BSVExpr yt ytr y' <- translateExpr y
      case testEquality xtr ytr of
        Just Refl | xt == yt ->
          BSVExpr xt xtr <$> ifte' xtr cond (return x') (return y')
        _ -> fail $ unwords ["Expression types failed to match in conditional expression:"
                            , show xt, show yt ]

  S.ExprBitConcat xs -> concatEx =<< mapM translateExpr xs

  -- FIXME, we currently only support selecting from statically-known bit positions
  -- select a single bit
  S.ExprBitSelect x n Nothing -> do
    x' <- translateExpr x
    case x' of
      BSVExpr (S.TypeCon "Bit" _) (BVRepr w) xw ->
        toStaticIndex n $ \idx ->
          case testLeq (addNat idx (knownNat :: NatRepr 1)) w of
            Just LeqProof ->
              return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat 1]) (BVRepr knownNat)
                     $ app $ C.BVSelect idx (knownNat :: NatRepr 1) w xw
            _ -> fail $ unwords ["Index out of bounds in bit selection", show n, show w]

      _ -> fail $ unwords ["Expected bit type in bit selection", show $ exprTy x']

  -- select a range of bits
  S.ExprBitSelect x n (Just m) -> do
    x' <- translateExpr x
    case x' of
      BSVExpr (S.TypeCon "Bit" _) (BVRepr w) xw ->
        toStaticIndex m $ \(start :: NatRepr start) ->
        toStaticIndex n $ \(stop  :: NatRepr stop) ->
          case testLeq start stop of
            Just LeqProof ->
              let len = addNat (subNat stop start) (knownNat :: NatRepr 1) in
              case testLeq (addNat start len) w of
                Just LeqProof ->
                  withLeqProof (addPrefixIsLeq (subNat stop start) (knownNat :: NatRepr 1) :: LeqProof 1 ((stop-start)+1)) $
                    return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat (natValue len)]) (BVRepr len)
                           $ app $ C.BVSelect start len w xw
                _ -> fail $ unwords ["Index out of bounds in bit selection", show n, show m, show w]
            _ -> fail $ unwords ["Invalid index range in bit selection", show n, show m]
      _ -> fail $ unwords ["Expected bit type in bit selection", show $ exprTy x']

  _ -> fail $ "Expression form not implemented: " ++ show ex


concatEx :: [BSVExpr s]
          -> BSVGen h s ret (BSVExpr s)
concatEx []     = fail "Cannot concatenate zero bitvectors"
concatEx (a:as) = go a as
 where
  go x [] = return x
  go x (y:zs) = do z <- concatOne x y
                   go z zs

concatOne :: BSVExpr s 
          -> BSVExpr s
          -> BSVGen h s ret (BSVExpr s)
concatOne (BSVExpr (S.TypeCon "Bit" [S.TypeNat xn]) (BVRepr xw) x)
           (BSVExpr (S.TypeCon "Bit" [S.TypeNat yn]) (BVRepr yw) y) =
  withLeqProof (leqAdd (leqProof (knownNat :: NatRepr 1) xw) yw) $
    return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat (xn+yn)])
                     (BVRepr (addNat xw yw))
                     (app $ C.BVConcat xw yw x y)                           

concatOne x y =
  fail $ unwords ["Expected bit types when concatenating", show $ exprTy x, show $ exprTy y]
           

toStaticIndex :: S.Expr
              -> (forall w. NatRepr w -> BSVGen h s ret a)
              -> BSVGen h s ret a
toStaticIndex (S.ExprIntLit n) k =
  case someNat n of
    Just (Some w) -> k w
    _ -> fail $ unwords ["Static index required to be nonnegative:", show n]
toStaticIndex x _ =
  fail $ unwords ["Static index required for bit selection:", show x]


translateStmt :: S.Stmt
              -> BSVGen h s ret ()
translateStmt s = case s of
  S.StmtExpr e -> stashExpr =<< translateExpr e
  _ -> fail $ unwords ["Unsupported statement:", show s]


translateType :: S.Type
              -> (forall tp. TypeRepr tp -> a)
              -> a
translateType t k = case t of
  S.TypeCon "Bool" [] -> k BoolRepr
  S.TypeCon "Integer" [] -> k IntegerRepr
  S.TypeCon "Bit" [S.TypeNat n] ->
    case someNat n of
      Just (Some w) | Just LeqProof <- isPosNat w -> k (BVRepr w)
      _ -> error $ unwords ["Illegal bit size:", show n]
  S.TypeCon "UInt" [S.TypeNat n] ->
    case someNat n of
      Just (Some w) | Just LeqProof <- isPosNat w -> k (BVRepr w)
      _ -> error $ unwords ["Illegal bit size:", show n]
  S.TypeCon "Int" [S.TypeNat n] ->
    case someNat n of
      Just (Some w) | Just LeqProof <- isPosNat w -> k (BVRepr w)
      _ -> error $ unwords ["Illegal bit size:", show n]


  _ -> error $ unwords ["Unsupported type form:", show t]

translateTypes :: forall a
                . [S.Type]
               -> (forall ctx. CtxRepr ctx -> a)
               -> a
translateTypes ts0 k = go Ctx.empty ts0
 where go :: forall ctx
           . CtxRepr ctx
          -> [S.Type]
          -> a
       go ctx [] = k ctx
       go ctx (t:ts) = translateType t $ \tpr ->
                         go (ctx Ctx.%> tpr) ts

translateFunProto
             :: S.FunProto
             -> (forall args ret. CtxRepr args -> TypeRepr ret -> a)
             -> a
translateFunProto proto k =
  translateTypes (map fst (S.funFormals proto)) $ \ctx ->
    translateType (S.funResultType proto) $ \ret ->
      k ctx ret

zipFormals :: forall s ctx
            . Ctx.Assignment (Atom s) ctx
           -> [(S.Type, S.Ident)]
           -> VarEnv s
zipFormals ctx0 fs0 = go ctx0 (reverse fs0) Map.empty
 where
  go :: forall ctx'
      . Ctx.Assignment (Atom s) ctx'
     -> [(S.Type, S.Ident)]
     -> VarEnv s
     -> VarEnv s
  go ctx fs !env =
    case (Ctx.view ctx, fs) of
      ( Ctx.AssignEmpty, [] ) -> env
      ( Ctx.AssignExtend ctx' a, (t,nm):fs' ) ->
         go ctx' fs' (Map.insert nm (BSVExpr t (typeOfAtom a) (AtomExpr a)) env)
      _ -> error "zipFormals: impossible! type assignment has different length than formal argument list"

initialState :: TypeEnv
             -> Ctx.Assignment (Atom s) ctx
             -> [(S.Type, S.Ident)]
             -> BSVState s
initialState tenv crucibleFormals bsvFormals =
  BSVState
  { bsvStateVars = zipFormals crucibleFormals bsvFormals
  , bsvTypeEnv   = tenv
  , bsvLastExpr  = Nothing
  }

translateFun :: HandleAllocator s
             -> TypeEnv
             -> S.FunDef
             -> ST s C.AnyCFG
translateFun halloc tenv fundef = do
  let proto = S.funDefProto fundef
  let nm = functionNameFromText $ Text.pack $ S.funName proto
  translateFunProto proto $ \(args :: CtxRepr args) (ret :: TypeRepr ret) -> do
    hdl <- mkHandle' halloc nm args ret
    let def :: FunctionDef h BSVState args ret
        def formals = ( initialState tenv formals (S.funFormals proto)
                      , do mapM_ translateStmt (S.funBody fundef)
                           returnStashedVal ret
                      )
    (SomeCFG g, []) <- defineFunction InternalPos hdl def
    case toSSA g of
      C.SomeCFG g_ssa -> return (C.AnyCFG g_ssa)
