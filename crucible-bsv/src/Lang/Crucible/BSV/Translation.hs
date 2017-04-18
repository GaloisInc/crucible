{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

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

--import           Control.Exception
import           Control.Monad.State
import           Control.Monad.ST

import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.STRef
import qualified Data.Text as Text
import qualified Data.Vector as V

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
import           Lang.Crucible.Utils.MonadST

import qualified Lang.BSV.AST as S
import           Lang.Crucible.BSV.Analysis

import qualified Debug.Trace as Debug

data TopBinding where
  -- A Binding for typeclass methods
  BSV_BindMethod :: S.Ident         -- name of the class
                 -> TopBinding

  -- A binding for a top-level function
  BSV_BindFun :: S.FunProto -> FnHandle ctx tp -> TopBinding

  -- A binding for a constant applicative form (CAF), i.e., a top-level
  -- value binding
  BSV_BindCAF :: S.Type -> FnHandle EmptyCtx tp -> TopBinding

  BSV_BindTopExpr :: S.Type -> TypeRepr tp -> (forall s. Expr s tp) -> TopBinding

  -- A binding that performs direct in-line code generation at every call site.
  -- This is mainly used as a hack to implement primitive operations that are
  -- polymorphic
  BSV_BindGen :: Int -> (forall h ret s. [BSVExpr s] -> BSVGen h s ret (BSVExpr s)) -> TopBinding


data BSVBinding s where
  BSV_Top        :: TopBinding -> BSVBinding s

  -- A binding for an expression
  BSV_BindExpr   :: S.Type -> TypeRepr tp -> Expr s tp -> BSVBinding s

  -- A binding for a CFG register
  BSV_BindReg    :: S.Type -> TypeRepr tp -> Reg s tp -> BSVBinding s

  -- A binding for a value bound in an outer function scope.  That is, when defining
  -- a function inside the scope of another function, values bound in the outer scope
  -- are make avaliable to the inner function via a closure binding.
  BSV_BindClosure :: S.Type -> TypeRepr tp -> BSVBinding s

type ValueEnv s = Map S.Ident (BSVBinding s)

-- Top level environments don't depend on the generation environment
type TopEnv = Map S.Ident TopBinding

topToValueEnv :: TopEnv -> ValueEnv s
topToValueEnv = fmap BSV_Top

nestBinding :: BSVBinding s -> Maybe (BSVBinding s')
nestBinding (BSV_Top tp)             = Just (BSV_Top tp)
nestBinding (BSV_BindReg _ _ _)      = Nothing
nestBinding (BSV_BindExpr tp tpr _)  = Just (BSV_BindClosure tp tpr)
nestBinding (BSV_BindClosure tp tpr) = Just (BSV_BindClosure tp tpr)

nestValueEnv :: ValueEnv s -> ValueEnv s'
nestValueEnv = Map.mapMaybe nestBinding

mkBind :: HandleAllocator h
       -> S.FunProto
       -> ST h (S.Ident, TopBinding)
mkBind halloc proto = do
  let ?tenv = initialTypeEnv
  let nm = functionNameFromText $ Text.pack $ S.funName proto
  translateFunProto proto $ \(args :: CtxRepr args) (ret :: TypeRepr ret) ->
    do hdl <- mkHandle' halloc nm args ret
       return (S.funName proto, BSV_BindFun proto hdl)


data BSVExpr s where
  BSVExpr  :: S.Type -> TypeRepr tp -> Expr s tp -> BSVExpr s
  BSVThunk :: S.Type -> Int -> (forall h ret. [BSVExpr s] -> BSVGen h s ret (BSVExpr s)) -> [BSVExpr s] -> BSVExpr s
  BSVUnpack :: (1 <= w) => NatRepr w -> Expr s (BVType w) -> BSVExpr s
  BSVFromInteger :: Expr s IntegerType -> BSVExpr s

instance Show (BSVExpr s) where
  show (BSVExpr tp _ ex) = "(" ++ show ex ++ " : " ++ show tp ++")"
  show (BSVThunk tp n _ _) = "<thunk:"++show n ++">"
  show (BSVUnpack _ ex)  = "(unpack: " ++ show ex ++ ")"
  show (BSVFromInteger ex) = "(fromInteger: "++show ex++")"

exprTy :: BSVExpr s -> S.Type
exprTy (BSVExpr t _ _) = t
exprTy (BSVThunk p _ _ _)  = p
exprTy (BSVUnpack w _) = S.TypeCon "Bit" [S.TypeNat (natValue w)]
exprTy (BSVFromInteger _) = S.TypeCon "Integer" []

data BSVState h s =
  BSVState
  { bsvStateVars    :: ValueEnv s
  , bsvTypeEnv      :: TypeEnv
  , bsvLastExpr     :: Maybe (BSVExpr s)
  , bsvCapturedVars :: Maybe (STRef h (Set S.Ident))
  , bsvClosure      :: Maybe (Expr s (StringMapType AnyType))
  }

type BSVGen h s ret a = Generator h s (BSVState h) ret a

addCapturedVar :: S.Ident -> BSVGen h s ret ()
addCapturedVar nm =
  do mref <- bsvCapturedVars <$> get
     case mref of
       Nothing  -> fail "Cannot capture variables in top-level function"
       Just ref -> liftST $ modifySTRef ref (Set.insert nm)

transposeProto :: S.FunProto
transposeProto =
  S.FunProto
  { S.funName = "transpose"
  , S.funResultType = S.TypeCon "Vector" [ S.TypeVar "m", S.TypeCon "Vector" [S.TypeVar "n", S.TypeVar "element_type"]]
  , S.funFormals = [(S.TypeCon "Vector" [ S.TypeVar "n", S.TypeCon "Vector" [S.TypeVar "m", S.TypeVar "element_type"]]
                    ,"matrix"
                    )]
  , S.funProvisos = []
  }

asVectorType :: TypeEnv
             -> S.Type
             -> Maybe (Integer, S.Type)
asVectorType tenv tp = do
  case normalizeType tenv tp of
    S.TypeCon "Vector" [x, tp'] ->
      case normalizeType tenv x of
        S.TypeNat i -> Just (i,tp')
        _ -> Nothing
    _ -> Nothing

expectVectorType :: S.Type
               -> BSVGen h s ret (Integer, S.Type)
expectVectorType tp = do
  tenv <- bsvTypeEnv <$> get
  maybe (fail $ unwords ["Expected vector type", show tp]) return (asVectorType tenv tp)

transposeGen :: [BSVExpr s]
             -> BSVGen h s ret (BSVExpr s)
transposeGen [BSVExpr tp (VectorRepr (VectorRepr tpr)) vss] = do
  (n,tp')    <- expectVectorType tp
  (m,elt_tp) <- expectVectorType tp'

  let out_ty = S.TypeCon "Vector" [S.TypeNat m, S.TypeCon "Vector" [S.TypeNat n, elt_tp]]

  let zss = vectorLit (VectorRepr tpr) $ V.fromList
              [ vectorLit tpr $ V.fromList
                  [ app $ C.VectorGetEntry tpr
                             (app $ C.VectorGetEntry (VectorRepr tpr) vss (litExpr $ fromInteger i))
                             (litExpr $ fromInteger j)
                  | i <- [0..(n-1)]
                  ]
              | j <- [0..(m-1)]
              ]

  return (BSVExpr out_ty (VectorRepr (VectorRepr tpr)) zss)

transposeGen args =
  fail $ unwords $ "transpose given incorrect arguments" : map show args


primIndexGen :: [BSVExpr s]
             -> BSVGen h s ret (BSVExpr s)
primIndexGen args@[BSVExpr tp (VectorRepr tpr) x, idx] =
  do tenv <- bsvTypeEnv <$> get
     case asIndexableType tenv tp of
       Just tp' ->
         do i <- asIndex idx
            return $ BSVExpr tp' tpr $ app $ C.VectorGetEntry tpr x i
       Nothing ->
         fail $ unwords $ "primIndex given incorrect arguments" : map show args

primIndexGen args =
  fail $ unwords $ "primIndex given incorrect arguments" : map show args


asIndexableType :: TypeEnv
                -> S.Type
                -> Maybe S.Type
asIndexableType tenv tp =
  case normalizeType tenv tp of
    S.TypeCon "Array"  [tp'] -> Just tp'
    S.TypeCon "Vector" [_sz, tp'] -> Just tp'
    _ -> Nothing

asIndex :: BSVExpr s
        -> BSVGen h s ret (Expr s NatType)
asIndex (BSVExpr _tp IntegerRepr x) = return $ app $ C.IntegerToNat x
asIndex (BSVExpr _tp (BVRepr w) x)  = return $ app $ C.BVToNat w x
asIndex (BSVFromInteger n)          = return $ app $ C.IntegerToNat n
asIndex x = fail $ unwords $ ["not an indexable type", show $ exprTy x]

mapProto :: S.FunProto
mapProto =
  S.FunProto
  { S.funName = "map"
  , S.funResultType = S.TypeCon "Vector" [S.TypeVar "vsize", S.TypeVar "b_type"]
  , S.funFormals = [(S.TypeFun (S.FunProto { S.funName = "func"
                                           , S.funResultType = S.TypeVar "b_type"
                                           , S.funFormals = [(S.TypeVar "a_type", "x")]
                                           , S.funProvisos = []
                                           }), "func")
                   ,(S.TypeCon "Vector" [S.TypeVar "vsize", S.TypeVar "a_type"], "vect")
                   ]
  , S.funProvisos = []
  }

mapGen :: [BSVExpr s]
       -> BSVGen h s ret (BSVExpr s)
mapGen [ BSVExpr (S.TypeFun p) (FunctionHandleRepr argTys ret) fn
       , BSVExpr tp (VectorRepr tpr) xs
       ] | Just Refl <- testEquality argTys (Ctx.empty Ctx.%> tpr)
       =
   do (n, _) <- expectVectorType tp
      zs <- forM [0 .. (n-1)] $ \i ->
                do let x = app $ C.VectorGetEntry tpr xs (litExpr $ fromInteger i)
                   call fn (Ctx.empty Ctx.%> x)
      return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n, S.funResultType p]) (VectorRepr ret)
             $ app $ C.VectorLit ret $ V.fromList zs

mapGen [ BSVThunk _ _ fn cls
       , BSVExpr tp (VectorRepr tpr) xs
       ]
           =
  do (n, tp') <- expectVectorType tp
     zs <- forM [0 .. (n-1) ] $ \i ->
                do let x = BSVExpr tp' tpr $ app $ C.VectorGetEntry tpr xs (litExpr $ fromInteger i)
                   fn (cls ++ [x])
     mkVector zs

mapGen args =
  fail $ unwords $ "incorrect arguments passed to map:" : map (show . exprTy) args



primBitConcat :: [BSVExpr s]
              -> BSVGen h s ret (BSVExpr s)
primBitConcat _args =
  reportError (litExpr "FIXME: implement PrimBitConcat!!")

zipWithGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
zipWithGen [ BSVExpr (S.TypeFun p) (FunctionHandleRepr argTys ret) fn
           , BSVExpr tp1 (VectorRepr tpr1) xs
           , BSVExpr tp2 (VectorRepr tpr2) ys
           ] | Just Refl <- testEquality argTys (Ctx.empty Ctx.%> tpr1 Ctx.%> tpr2)
           =
  do tenv <- bsvTypeEnv <$> get
     (n1, _) <- expectVectorType tp1
     (n2, _) <- expectVectorType tp2
     unless (n1 == n2) (fail "Vector length mismatch in zipWith")
     zs <- forM [0 .. (n1-1) ] $ \i ->
                    do let x = app $ C.VectorGetEntry tpr1 xs (litExpr $ fromInteger i)
                       let y = app $ C.VectorGetEntry tpr2 ys (litExpr $ fromInteger i)
                       call fn (Ctx.empty Ctx.%> x Ctx.%> y)
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n1, S.funResultType p]) (VectorRepr ret)
            $ app $ C.VectorLit ret $ V.fromList zs

zipWithGen [ BSVThunk _ _ fn cls
           , BSVExpr tp1 (VectorRepr tpr1) xs
           , BSVExpr tp2 (VectorRepr tpr2) ys
           ]
           =
  do tenv <- bsvTypeEnv <$> get
     (n1, tp1) <- expectVectorType tp1
     (n2, tp2) <- expectVectorType tp2
     unless (n1 == n2) (fail "Vector length mismatch in zipWith")
     zs <- forM [0 .. (n1-1) ] $ \i ->
                    do let x = BSVExpr tp1 tpr1 $ app $ C.VectorGetEntry tpr1 xs (litExpr $ fromInteger i)
                       let y = BSVExpr tp2 tpr2 $ app $ C.VectorGetEntry tpr2 ys (litExpr $ fromInteger i)
                       fn (cls ++ [x,y])
     mkVector zs

zipWithGen args =
  fail $ unwords $ "zipWith called on incorrect arguments" : map (show . exprTy) args

mkVector :: forall h s ret
          . [BSVExpr s]
         -> BSVGen h s ret (BSVExpr s)
mkVector [] = fail "Cannot figure out the type of a empty list of items"
mkVector vs@(BSVExpr tp tpr x : xs) =
    do zs <- go tpr [x] xs
       return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat $ toInteger $ length vs, tp]) (VectorRepr tpr)
              $ app $ C.VectorLit tpr $ V.fromList zs
  where
   go :: TypeRepr t -> [Expr s t] -> [BSVExpr s] -> BSVGen h s ret [Expr s t]
   go tpr zs [] = return $ reverse zs
   go tpr zs (BSVExpr _ tpr' x : xs)
     | Just Refl <- testEquality tpr tpr' = go tpr (x:zs) xs
     | otherwise = fail $ unwords ["Type mismatch in zipWith", show tpr, show tpr']
   go _ _ _ =
     fail "Unacceptable value produced by zipWith"

genWithGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
genWithGen [BSVExpr (S.TypeFun p) (FunctionHandleRepr args ret) fn]
    | Just Refl <- testEquality args (Ctx.empty Ctx.%> IntegerRepr) =

  do -- HACK!
     let n = 4
     zs <- forM [0 .. n-1] $ \i ->
             do let x = app $ C.IntLit $ fromIntegral i
                call fn (Ctx.empty Ctx.%> x)
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n, S.funResultType p]) (VectorRepr ret)
            $ app $ C.VectorLit ret $ V.fromList zs

genWithGen args =
  fail $ unwords $ "genWith called on incorrect arguments" : map (show . exprTy) args


replicateGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
replicateGen [BSVExpr tp tpr x] =
   do -- HACK!
      let n = 4
      return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n, tp]) (VectorRepr tpr)
             $ app $ C.VectorReplicate tpr (litExpr $ fromIntegral n) x
replicateGen [BSVFromInteger x] =
   do -- HACK!!
      let n = 4
      let w = knownNat :: NatRepr 8
      let tpr = BVRepr w
      let tp = S.TypeCon "Bit" [S.TypeNat 8]
      return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n, tp]) (VectorRepr tpr)
             $ app $ C.VectorReplicate tpr (litExpr $ fromIntegral n) (app $ C.IntegerToBV w x)

replicateGen args =
  fail $ unwords $ "replicate called on incorrect arguments" : map (show . exprTy) args


arrayToVectorGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
arrayToVectorGen args@[BSVExpr tp tpr x] =
  do tenv <- bsvTypeEnv <$> get
     case normalizeType tenv tp of
       S.TypeCon "Array" [tp'] ->
         -- HACK!
         let n = S.TypeNat 4 in
         return $ BSVExpr (S.TypeCon "Vector" [n,tp']) tpr x
       _ -> fail $ unwords $ "arrayToVectorGen called on incorrect arguments" : map (show . exprTy) args

arrayToVectorGen args =
  fail $ unwords $ "arrayToVectorGen called on incorrect arguments" : map (show . exprTy) args


rotateByGen :: [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
rotateByGen [ BSVExpr tp (VectorRepr tpr) xs
            , BSVExpr  _ (BVRepr w) n
            ] =
   do (sz, tp') <- expectVectorType tp
      zs <- forM [0 .. sz-1] $ \i ->
               do let j = app $ C.BVUrem w (app $ C.BVSub w (app $ C.BVLit w $ fromIntegral (i+sz)) n) (app $ C.BVLit w sz)
                  return $ app $ C.VectorGetEntry tpr xs (app $ C.BvToNat w j)
      return $ BSVExpr tp (VectorRepr tpr)
             $ app $ C.VectorLit tpr $ V.fromList zs

rotateByGen [ BSVExpr tp (VectorRepr tpr) xs
            , BSVExpr  _ IntegerRepr n
            ] =
   do (sz, tp') <- expectVectorType tp
      zs <- forM [0 .. sz-1] $ \i ->
               do let j = app $ C.IntMod (app $ C.IntSub (app $ C.IntLit $ fromIntegral (i+sz)) n) (app $ C.NatLit $ fromInteger sz)
                  return $ app $ C.VectorGetEntry tpr xs j
      return $ BSVExpr tp (VectorRepr tpr)
             $ app $ C.VectorLit tpr $ V.fromList zs

rotateByGen [ BSVExpr tp (VectorRepr tpr) xs
            , BSVFromInteger n
            ] =
   do (sz, tp') <- expectVectorType tp
      zs <- forM [0 .. sz-1] $ \i ->
               do let j = app $ C.IntMod (app $ C.IntSub (app $ C.IntLit $ fromIntegral (i+sz)) n) (app $ C.NatLit $ fromInteger sz)
                  return $ app $ C.VectorGetEntry tpr xs j
      return $ BSVExpr tp (VectorRepr tpr)
             $ app $ C.VectorLit tpr $ V.fromList zs

rotateByGen args =
  fail $ unwords $ "rotateBy called on incorrect arguments" : map (show . exprTy) args



reverseGen :: [BSVExpr s] -> BSVGen h s ret (BSVExpr s)

reverseGen [BSVExpr tp (VectorRepr tpr) (asApp -> Just (C.VectorLit _ v))] =
  return $ BSVExpr tp (VectorRepr tpr) (app $ C.VectorLit tpr (V.reverse v))

reverseGen [BSVExpr tp (VectorRepr tpr) vec] =
  do tenv <- bsvTypeEnv <$> get
     let Just (n,_tp') = asVectorType tenv tp
     let xs = [ app $ C.VectorGetEntry tpr vec (litExpr $ fromInteger i)
              | i <- [0..(n-1)]
              ]
     return $ BSVExpr tp (VectorRepr tpr) (app $ C.VectorLit tpr $ V.fromList $ reverse xs)

--- HACK! assume we unpack to a [4][4]Bit#(8) Vector
reverseGen [BSVUnpack w x] =
  do tenv <- bsvTypeEnv <$> get
     let tp = S.TypeCon "Vector" [S.TypeNat 4,
                S.TypeCon "Vector" [S.TypeNat 4,
                  S.TypeCon "Bit" [S.TypeNat 8]
                ]
              ]
     let tpr = VectorRepr (VectorRepr (BVRepr (knownNat :: NatRepr 8)))
     x' <- unpackExpr tenv tp tpr w x
     reverseGen [ BSVExpr tp tpr x' ]

reverseGen args =
  fail $ unwords $ "reverse called on incorrect arguments" : map show args

concatBSVExprs :: forall h s ret. [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
concatBSVExprs = concatBSVExprs' . reverse

concatBSVExprs' :: forall h s ret. [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
concatBSVExprs' []  = fail "Cannot produce 0-length bitvector"
concatBSVExprs' [x] = return x
concatBSVExprs' (BSVExpr _ (BVRepr w0) x0 : xs0) = go w0 x0 xs0
 where
  go :: (1 <= w) => NatRepr w -> Expr s (BVType w) -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
  go w x [] = return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat (toInteger $ natValue w)]) (BVRepr w) x
  go w x (BSVExpr _ (BVRepr w') y : ys) =
     withLeqProof (leqAdd (leqProof (knownNat :: NatRepr 1) w) w') $ do
        let x' = app $ C.BVConcat w w' x y
        go (addNat w w') x' ys

  go _ _ _ = fail "concatExprs given non-bitvector input"

concatBSVExprs' (_ : _) = fail "concatExprs given non-bitvector input"

-- HACK! assume the output of truncate is a 4-bit value
truncateGen :: [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
truncateGen [BSVExpr _ (BVRepr w) x] =
  do let w4 = knownNat :: NatRepr 4
     case testLeq (incNat w4) w of
       Just LeqProof ->
         return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat 4]) (BVRepr w4)
                $ app $ C.BVTrunc w4 w x
       Nothing ->
         fail $ unwords ["invalid truncate call", show w, show w4]

truncateGen args =
  fail $ unwords $ "truncate called on incorrect arguments" : map (show . exprTy) args


unpackExpr :: (1 <= w)
           => TypeEnv
           -> S.Type
           -> TypeRepr tp
           -> NatRepr w
           -> Expr s (BVType w)
           -> BSVGen h s ret (Expr s tp)
unpackExpr _tenv _tp (BVRepr w') w x
  | Just Refl <- testEquality w w' = return x

unpackExpr tenv tp (VectorRepr tpr) w x
  | Just (n,tp') <- asVectorType tenv tp =
      do unless (n /= 0) failMsg
         unless (natValue w `mod` n == 0) failMsg
         Just (Some w') <- return $ someNat (natValue w `div` n)
         Just LeqProof  <- return $ isPosNat w'
         let xs = [ case someNat (i*natValue w') of
                      Just (Some idx)
                        | Just LeqProof <- testLeq (addNat idx w') w
                        -> app $ C.BVSelect idx w' w x
                      _ -> error $ unwords ["Bad slice in unpack", show tp, show (VectorRepr tpr), show w, show i]

                  | i <- [0 .. n-1]
                  ]
         xs' <- mapM (unpackExpr tenv tp' tpr w') xs
         return $ app $ C.VectorLit tpr $ V.fromList $ xs'

  | otherwise = failMsg

 where
  failMsg :: BSVGen h s ret a
  failMsg = fail $ unwords ["Cannot unpack bitvector for type", show tp, show w]

unpackExpr _ tp tpr _ _ =
  fail $ unwords ["Invalid arguments to unpackExpr", show tp, show tpr]

doPack :: TypeEnv
       -> S.Type
       -> TypeRepr tp
       -> Expr s tp
       -> BSVGen h s ret (BSVExpr s)
doPack tenv tp (VectorRepr tpr) vec
  | Just (n,tp') <- asVectorType tenv tp =
      do let xs = [ app $ C.VectorGetEntry tpr vec (litExpr $ fromInteger i) | i <- [0..(n-1)] ]
         xs' <- mapM (doPack tenv tp' tpr) xs
         concatBSVExprs $ xs'

doPack _ tp tpr@(BVRepr _) x =
  return $ BSVExpr tp tpr x

doPack _ tp tpr _ =
  fail $ unwords ["doPack given bad argument types", show tp, show tpr]


packGen :: [BSVExpr s]
        -> BSVGen h s ret (BSVExpr s)
packGen [BSVExpr tp tpr x] =
  do tenv <- bsvTypeEnv <$> get
     doPack tenv tp tpr x

packGen _ =
  fail "pack given incorrect arguments"

-- HACK, assume that unpack always unpacks towards a vector if 8-bit values...
unpackGen :: [BSVExpr s]
          -> BSVGen h s ret (BSVExpr s)
unpackGen [BSVExpr _ (BVRepr w) x] =
  return $ BSVUnpack w x
unpackGen _ =
  fail "unpack given incorrect arguments"

fromIntegerGen ::
  [BSVExpr s] ->
  BSVGen h s ret (BSVExpr s)
fromIntegerGen [BSVExpr _ IntegerRepr x] =
  return $ BSVFromInteger x
fromIntegerGen _ =
  fail "fromInteger given incorrect arguments"

boolAndGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
boolAndGen [ BSVExpr _ BoolRepr x
           , BSVExpr _ BoolRepr y
           ] =
  do let z = app $ C.And x y
     return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr z

boolAndGen args =
  fail $ unwords $ "&& called on incorrect arguments" : map (show . exprTy) args

boolOrGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
boolOrGen [ BSVExpr _ BoolRepr x
          , BSVExpr _ BoolRepr y
          ] =
  do let z = app $ C.Or x y
     return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr z

boolOrGen args =
  fail $ unwords $ "|| called on incorrect arguments" : map (show . exprTy) args


bitXorGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
bitXorGen [ BSVExpr tp (BVRepr wx) x
          , BSVExpr _ (BVRepr wy) y
          ] | Just Refl <- testEquality wx wy =
  do let z = app $ C.BVXor wx x y
     return $ BSVExpr tp (BVRepr wx) z

bitXorGen args =
  fail $ unwords $ "^ called on incorrect arguments" : map (show . exprTy) args


tailGen :: [BSVExpr s]
        -> BSVGen h s ret (BSVExpr s)
tailGen [ BSVExpr tp (VectorRepr tpr) (asApp -> Just (C.VectorLit _ v)) ] =
  do (n,tp') <- expectVectorType tp
     unless (n >= 1) (fail "tail called on empty vector")
     let n' = n-1
     let v' = app $ C.VectorLit tpr $ V.tail v
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n', tp]) (VectorRepr tpr) v'

tailGen [ BSVExpr tp (VectorRepr tpr) v ] =
  do (n,tp') <- expectVectorType tp
     unless (n >= 1) (fail "tail called on empty vector")
     let n' = n-1
     let xs = [ app $ C.VectorGetEntry tpr v (litExpr $ fromIntegral i)
              | i <- [1 .. n']
              ]
     let v' = app $ C.VectorLit tpr $ V.fromList xs
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n', tp]) (VectorRepr tpr) v'

tailGen args =
  fail $ unwords $ "tail called on incorrect arguments" : map (show . exprTy) args


initGen :: [BSVExpr s]
        -> BSVGen h s ret (BSVExpr s)
initGen [ BSVExpr tp (VectorRepr tpr) (asApp -> Just (C.VectorLit _ v)) ] =
  do (n,tp') <- expectVectorType tp
     unless (n >= 1) (fail "init called on empty vector")
     let n' = n-1
     let v' = app $ C.VectorLit tpr $ V.init v
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n', tp]) (VectorRepr tpr) v'

initGen [ BSVExpr tp (VectorRepr tpr) v ] =
  do (n,tp') <- expectVectorType tp
     unless (n >= 1) (fail "init called on empty vector")
     let n' = n-1
     let xs = [ app $ C.VectorGetEntry tpr v (litExpr $ fromIntegral i)
              | i <- [0 .. (n'-1)]
              ]
     let v' = app $ C.VectorLit tpr $ V.fromList xs
     return $ BSVExpr (S.TypeCon "Vector" [S.TypeNat n', tp]) (VectorRepr tpr) v'

initGen args =
  fail $ unwords $ "init called on incorrect arguments" : map (show . exprTy) args


composeGen :: [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
composeGen [f, g, x] =
   do y <- applyExpr' g [x]
      applyExpr' f [y]

composeGen args =
  fail $ unwords $ "compose called on incorrect arguments" : map (show . exprTy) args



initialValEnv :: forall h
               . HandleAllocator h
              -> ST h TopEnv
initialValEnv halloc = do
    return $ Map.fromList
     [ ("+",  BSV_BindMethod "Arith")
     , ("-",  BSV_BindMethod "Arith")
     , ("-",  BSV_BindMethod "Arith")
     , ("*",  BSV_BindMethod "Arith")
     , ("/",  BSV_BindMethod "Arith")
     , ("%",  BSV_BindMethod "Arith")
     , ("negate", BSV_BindMethod "Arith")
     , ("==", BSV_BindMethod "Eq")
     , ("!=", BSV_BindMethod "Eq")
     , ("<",  BSV_BindMethod "Ord")
     , ("<=", BSV_BindMethod "Ord")
     , (">",  BSV_BindMethod "Ord")
     , (">=", BSV_BindMethod "Ord")
     , ("&" , BSV_BindMethod "Bitwise")
     , ("|" , BSV_BindMethod "Bitwise")
     , ("^" , BSV_BindMethod "Bitwise")
     , ("^~", BSV_BindMethod "Bitwise")
     , ("~^", BSV_BindMethod "Bitwise")
     , ("<<", BSV_BindMethod "Bitwise")
     , (">>", BSV_BindMethod "Bitwise")
     , ("invert", BSV_BindMethod "Bitwise")

     , ("pack", BSV_BindMethod "Bits")
     , ("unpack", BSV_BindMethod "Bits")
     , ("fromInteger", BSV_BindMethod "Literal")

     -- OMG, such a hack.  We _really_ need to do typechecking to figure out
     -- the correct thing to do here...
     , ("?", BSV_BindTopExpr (S.TypeCon "Bit" [S.TypeNat 8]) (BVRepr (knownNat :: NatRepr 8)) (litExpr 0))

     , ("transpose", BSV_BindGen 1 transposeGen)
     , ("map", BSV_BindGen 2 mapGen)
     , ("PrimIndex", BSV_BindGen 2 primIndexGen)
     , ("PrimBitConcat", BSV_BindGen 0 primBitConcat)
     , ("zipWith", BSV_BindGen 3 zipWithGen)
     , ("genWith", BSV_BindGen 1 genWithGen)
     , ("replicate", BSV_BindGen 1 replicateGen)
     , ("arrayToVector", BSV_BindGen 1 arrayToVectorGen)
     , ("reverse", BSV_BindGen 1 reverseGen)
     , ("truncate", BSV_BindGen 1 truncateGen)
     , ("rotateBy", BSV_BindGen 2 rotateByGen)
     , ("tail", BSV_BindGen 1 tailGen)
     , ("init", BSV_BindGen 1 initGen)
     , ("compose", BSV_BindGen 3 composeGen)

     , ("&&", BSV_BindGen 2 boolAndGen)
     , ("||", BSV_BindGen 2 boolOrGen)

     ]


lookupVar :: S.Ident
          -> BSVGen h s ret (BSVExpr s)
lookupVar nm = do
  mp <- bsvStateVars <$> get
  case Map.lookup nm mp of
    Just (BSV_BindExpr tp r x) -> return $ BSVExpr tp r x
    Just (BSV_BindReg tp r x) -> BSVExpr tp r <$> readReg x
    Just (BSV_Top (BSV_BindTopExpr tp r x)) -> return $ BSVExpr tp r x
    Just (BSV_Top (BSV_BindFun proto hdl)) -> return $ BSVExpr (S.TypeFun proto) (handleType hdl) (litExpr hdl)
    Just (BSV_Top (BSV_BindCAF tp hdl)) -> BSVExpr tp (handleReturnType hdl) <$> call (litExpr hdl) Ctx.empty

    Just (BSV_Top (BSV_BindMethod cls)) ->
      if | nm == "^"    -> return $ BSVThunk (S.TypeVar "unknown") 2 bitXorGen []
         | nm == "pack" -> return $ BSVThunk (S.TypeVar "unknown") 1 packGen []
         | otherwise    -> fail $ unwords ["FIXME: implement typeclass method lookup", nm, cls]

    Just (BSV_Top (BSV_BindGen arity m)) ->
         return $ BSVThunk (S.TypeVar "unknown") arity m []
    Just (BSV_BindClosure tp tpr) -> do
      mclosure <- bsvClosure <$> get
      case mclosure of
        Nothing -> fail "No closure avalaible"
        Just cls -> do
           let expr = app $ C.FromJustValue tpr
                               (app $ C.UnpackAny tpr $ app $ C.FromJustValue AnyRepr
                                  (app $ C.LookupStringMapEntry AnyRepr cls (litExpr $ Text.pack nm))
                                  (litExpr $ Text.pack $ unwords ["captured variable not found in closure!", nm]))
                               (litExpr $ Text.pack $ unwords ["type mismatch on captured variable:", nm])

           addCapturedVar nm
           return $ BSVExpr tp tpr expr

    Nothing -> fail $ unwords ["Variable not found in local scope: ", show nm]


applyVar :: S.Ident
         -> [BSVExpr s]
         -> BSVGen h s ret (BSVExpr s)
applyVar nm args = do
  mp <- bsvStateVars <$> get
  case Map.lookup nm mp of
    Just (BSV_Top (BSV_BindMethod classId)) -> applyTypeclassMethod classId nm args
    Just (BSV_BindExpr _tp _r _x) -> fail "FIXME: implement application for expressions"
    Just (BSV_Top (BSV_BindTopExpr _tp _r _x)) -> fail "FIXME: implement application for expressions"
    Just (BSV_BindClosure _ _)  -> fail "FIXME: implement closure lookup for applications"
    Just (BSV_BindReg _ _ _) -> fail "Cannot (?) apply arguments to a register value"
    Just (BSV_Top (BSV_BindCAF _ _)) -> fail "Cannot apply arguments to a CAF"
    Just (BSV_Top (BSV_BindFun proto hdl)) ->
       do args' <- prepareArgs proto (handleArgTypes hdl) args
          BSVExpr (S.funResultType proto) (handleReturnType hdl) <$> call (litExpr hdl) args'
    Just (BSV_Top (BSV_BindGen arity gen)) ->
       let len = length args in
       if | len == arity -> gen args
          | len <  arity -> return $ BSVThunk (S.TypeVar "unknown") (arity - len) gen args
          | otherwise    -> fail $ unwords ["Tried to apply too many arguments to a thunk", show len, show nm]

    Nothing -> fail $ unwords ["Variable not found in local scope: ", show nm]


prepareArgs :: S.FunProto
            -> CtxRepr ctx
            -> [BSVExpr s]
            -> BSVGen h s ret (Ctx.Assignment (Expr s) ctx)
prepareArgs proto ctx0 args0 = go ctx0 (reverse args0)
 where
  go :: CtxRepr ctx -> [BSVExpr s] -> BSVGen h s ret (Ctx.Assignment (Expr s) ctx)
  go (Ctx.view -> Ctx.AssignEmpty) [] = return Ctx.empty
  go (Ctx.view -> Ctx.AssignExtend ctx t) (BSVExpr _tp tpr x:xs) =
    case testEquality t tpr of
      Just Refl -> do args <- go ctx xs
                      return (args Ctx.%> x)
      Nothing   -> failMsg
  go (Ctx.view -> Ctx.AssignExtend ctx t) (BSVFromInteger n:xs) =
       do x <- case t of
                 BVRepr w    -> return $ app $ C.IntegerToBV w n
                 IntegerRepr -> return n
                 _ -> failMsg
          args <- go ctx xs
          return (args Ctx.%> x)

  go _ _ = failMsg

  failMsg :: Monad m => m a
  failMsg = fail $ unlines $ "Argument arity mismatch!" : show proto : show ctx0 : map show args0

applyExpr :: S.Expr
          -> [BSVExpr s]
          -> BSVGen h s ret (BSVExpr s)
applyExpr (S.ExprVar nm) args = applyVar nm args
applyExpr fn args = do
  fn' <- translateExpr fn
  applyExpr' fn' args

applyExpr' :: BSVExpr s
           -> [BSVExpr s]
           -> BSVGen h s ret (BSVExpr s)
applyExpr' fn args = do
  tenv <- bsvTypeEnv <$> get
  case fn of
    BSVExpr (normalizeType tenv -> S.TypeFun proto) (FunctionHandleRepr argTys retTy) f ->
      do args' <- prepareArgs proto argTys args
         z <- call f args'
         return $ BSVExpr (S.funResultType proto) retTy z

    BSVThunk tp n gen cls
      | length args < n  -> return $ BSVThunk (S.TypeVar "unknown") (n - length args) gen (cls ++ args)
      | length args == n -> gen (cls++args)
      | otherwise ->
            do let (args',rest) = splitAt n args
               f <- gen (cls++args')
               applyExpr' f rest

    _ -> fail $ unwords ["unexpected function value in applyExpr'"]


bindVar :: S.Ident
        -> BSVExpr s
        -> BSVGen h s ret ()
bindVar nm (BSVExpr tp repr x) =
  modify $ \st -> st{ bsvStateVars = Map.insert nm (BSV_BindExpr tp repr x) (bsvStateVars st) }
bindVar _nm (BSVUnpack _ _) =
  fail "Cannot bind an unpacking..."
bindVar _nm (BSVFromInteger _) =
  fail "Cannot bind a fromInteger..."
bindVar nm (BSVThunk _ _ _ _) =
  fail "Cannot bind a thunk..."
--  modify $ \st -> st{ bsvStateVars = Map.insert nm (BSV_Top (BSV_BindGen m)) (bsvStateVars st) }


bindReg :: S.Ident
        -> S.Type
        -> TypeRepr t
        -> Reg s t
        -> BSVGen h s ret ()
bindReg nm tp repr x =
  modify $ \st -> st{ bsvStateVars = Map.insert nm (BSV_BindReg tp repr x) (bsvStateVars st) }


stashExpr :: BSVExpr s
          -> BSVGen h s ret ()
stashExpr ex = do
  modify $ \st -> st{ bsvLastExpr = Just ex }

clearStash :: BSVGen h s ret ()
clearStash =
  modify $ \st -> st{ bsvLastExpr = Nothing }

useStash :: BSVGen h s ret (BSVExpr s)
useStash = do
  st <- get
  case bsvLastExpr st of
    Just expr -> do
      put st{ bsvLastExpr = Nothing }
      return expr
    Nothing ->
      fail "Expression block must end with an expression!"

returnStashedVal :: TypeRepr ret
                 -> BSVGen h s ret (Expr s ret)
returnStashedVal tpr = do
  st <- get
  case bsvLastExpr st of
    Just (BSVExpr _t tpr' x)
      | Just Refl <- testEquality tpr tpr' -> return x
      | otherwise -> fail $ "Returned value does not match expected return type"
    _ -> fail "No value returned from function!"

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
   :: forall h s ret
    . String
   -> (Expr s IntegerType -> Expr s IntegerType -> Expr s BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) BoolType)
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseCmpMethod nm integerF intF uintF bitsF args = do
 tenv <- bsvTypeEnv <$> get
 case args of
  [  BSVExpr _ IntegerRepr x
   , BSVExpr _ IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ integerF x y

  [  BSVFromInteger x
   , BSVExpr _ IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ integerF x y

  [  BSVExpr _ IntegerRepr x
   , BSVFromInteger y
   ] -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ integerF x y

  [  BSVFromInteger x
   , BSVFromInteger y
   ] -> return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr
               $ integerF x y

  _ -> selectBitvectorOperation nm op args
        where
        op :: forall w. (1<=w) => String -> Integer -> NatRepr w -> Expr s (BVType w) -> Expr s (BVType w) -> BSVGen h s ret (BSVExpr s)
        op "Int" _i w x y =
           return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr $ app $ intF w x y
        op "UInt" _i w x y =
           return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr $ app $ uintF w x y
        op "Bit" _i w x y =
           return $ BSVExpr (S.TypeCon "Bool" []) BoolRepr $ app $ bitsF w x y
        op tp _i _w _x _y = fail $ "Expected bitvector type: " ++ tp

selectBitvectorOperation
   :: String
   -> (forall w. (1<=w) => String -> Integer -> NatRepr w -> Expr s (BVType w) -> Expr s (BVType w) -> BSVGen h s ret a)
   -> [BSVExpr s] -> BSVGen h s ret a
selectBitvectorOperation nm op args = do
 tenv <- bsvTypeEnv <$> get
 case args of
  [  BSVExpr (normalizeType tenv -> S.TypeCon cx [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr (normalizeType tenv -> S.TypeCon cy [S.TypeNat iy]) (BVRepr wy) y
   ] | ix == iy, cx == cy
     , Just Refl <- testEquality wx wy
     -> op cx ix wx x y

  [  BSVExpr (normalizeType tenv -> S.TypeCon cx [S.TypeNat ix]) (BVRepr wx) x
   , BSVFromInteger y
   ] -> op cx ix wx x (castOp cx wx y)

  [  BSVExpr (normalizeType tenv -> S.TypeCon cx [S.TypeNat ix]) (BVRepr wx) x
   , BSVExpr _ IntegerRepr y
   ] -> op cx ix wx x (castOp cx wx y)

  [  BSVExpr _ IntegerRepr x
   , BSVExpr (normalizeType tenv -> S.TypeCon cy [S.TypeNat iy]) (BVRepr wy) y
   ] -> op cy iy wy (castOp cy wy x) y

  [  BSVFromInteger x
   , BSVExpr (normalizeType tenv -> S.TypeCon cy [S.TypeNat iy]) (BVRepr wy) y
   ] -> op cy iy wy (castOp cy wy x) y

  _ -> fail $ unwords ["Invalid types for bitvector operation", nm, show (map exprTy args)]

 where castOp :: (1 <= w) => String -> NatRepr w -> Expr s IntegerType -> Expr s (BVType w)
       castOp "Int"  w x = app $ C.IntegerToSBV w x
       castOp "UInt" w x = app $ C.IntegerToBV w x
       castOp "Bit"  w x = app $ C.IntegerToBV w x
       castOp c _ _ = error $ unwords ["Unknown bitvector type", c]


baseBitwiseMethod
   :: forall h s ret
    . String
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseBitwiseMethod nm bitsF = selectBitvectorOperation nm op
 where
  op :: forall w. (1<=w) => String -> Integer -> NatRepr w -> Expr s (BVType w) -> Expr s (BVType w) -> BSVGen h s ret (BSVExpr s)
  op c i w x y | c `elem` ["Int","UInt","Bit"] =
       return $ BSVExpr (S.TypeCon c [S.TypeNat i]) (BVRepr w) $ app $ bitsF w x y
  op tp _i _w _x _y = fail $ "Expected bitvector type: " ++ tp


baseArithMethod
   :: forall h s ret
    . String
   -> (Expr s IntegerType -> Expr s IntegerType -> Expr s IntegerType)
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> (forall w. (1 <= w) => NatRepr w
      -> Expr s (BVType w) -> Expr s (BVType w) -> C.App (Expr s) (BVType w))
   -> [BSVExpr s] -> BSVGen h s ret (BSVExpr s)
baseArithMethod nm integerF intF uintF bitsF args = do
 tenv <- bsvTypeEnv <$> get
 case args of
  [  BSVExpr _ IntegerRepr x
   , BSVExpr _ IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Integer" []) IntegerRepr
               $ integerF x y

  [  BSVFromInteger x
   , BSVExpr _ IntegerRepr y
   ] -> return $ BSVExpr (S.TypeCon "Integer" []) IntegerRepr
               $ integerF x y

  [  BSVExpr _ IntegerRepr x
   , BSVFromInteger y
   ] -> return $ BSVExpr (S.TypeCon "Integer" []) IntegerRepr
               $ integerF x y

  [  BSVFromInteger x
   , BSVFromInteger y
   ] -> return $ BSVFromInteger $ integerF x y

  _ -> selectBitvectorOperation nm op args
        where
        op :: forall w. (1<=w) => String -> Integer -> NatRepr w -> Expr s (BVType w) -> Expr s (BVType w) -> BSVGen h s ret (BSVExpr s)
        op "Int" i w x y =
           return $ BSVExpr (S.TypeCon "Int" [S.TypeNat i]) (BVRepr w) $ app $ intF w x y
        op "UInt" i w x y =
           return $ BSVExpr (S.TypeCon "UInt" [S.TypeNat i]) (BVRepr w) $ app $ uintF w x y
        op "Bit" i w x y =
           return $ BSVExpr (S.TypeCon "Bit" [S.TypeNat i]) (BVRepr w) $ app $ bitsF w x y
        op tp _i _w _x _y = fail $ "Expected bitvector type: " ++ tp

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
   baseArithMethod "/" (\x y -> app $ C.NatToInteger (app $ C.IntMod x (app $ C.IntegerToNat y)))
                       C.BVSrem C.BVUrem C.BVUrem

applyTypeclassMethod "Eq" "==" =
   baseCmpMethod "==" (.==) C.BVEq C.BVEq C.BVEq
applyTypeclassMethod "Eq" "!=" =
   baseCmpMethod "!=" (./=)
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

applyTypeclassMethod "Bitwise" "invert" = \xs ->
   -- FIXME, bit of a hack...
   baseBitwiseMethod "invert" (\w x _ -> C.BVNot w x) (xs ++ xs)

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

applyTypeclassMethod "Bitwise" "<<" =
   baseBitwiseMethod "<<" (\w x y -> C.BVShl w x y)
applyTypeclassMethod "Bitwise" ">>" =
   selectBitvectorOperation ">>" (\c i w x y ->
    case c of
      "Int"  -> return $ BSVExpr (S.TypeCon "Int"  [S.TypeNat i]) (BVRepr w) $ app $ C.BVAshr w x y
      "UInt" -> return $ BSVExpr (S.TypeCon "UInt" [S.TypeNat i]) (BVRepr w) $ app $ C.BVLshr w x y
      "Bit"  -> return $ BSVExpr (S.TypeCon "Bit"  [S.TypeNat i]) (BVRepr w) $ app $ C.BVLshr w x y
      _ -> fail $ "Expected bit type in right shift: " ++ c
    )

applyTypeclassMethod "Bits" "unpack" = unpackGen
applyTypeclassMethod "Bits" "pack" = packGen

applyTypeclassMethod "Literal" "fromInteger" = fromIntegerGen


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
translateCondPred (S.CondExpr e) =
  do e' <- translateExpr e
     case e' of
       BSVExpr _tp BoolRepr x -> return x
       _ -> fail "Condition expected to have boolean type!"
translateCondPred (S.CondMatch _ _) = fail "FIXME: implement translateCondPred pattern matchning"

translateCondPreds
  :: [S.CondPredicate]
  -> BSVGen h s ret (Expr s BoolType)
translateCondPreds =
  foldM (\xs p -> do x <- translateCondPred p
                     return (xs .&& x))
        (litExpr True)

translateExprStmt :: S.ExprStmt
                  -> BSVGen h s ret ()
translateExprStmt (S.ExprStmtExpr ex) =
  stashExpr =<< translateExpr ex
translateExprStmt (S.ExprStmtVarDecl decls) =
  mapM_ translateVarDecl decls
translateExprStmt (S.ExprStmtBlock ss) =
  clearStash >> mapM_ translateExprStmt ss
translateExprStmt s = fail $ unwords ["Unsupported expression statement:", show s]

translateExpr :: S.Expr
              -> BSVGen h s ret (BSVExpr s)
translateExpr ex = case ex of
  S.ExprVar nm          -> lookupVar nm
  S.ExprIntLit n        -> return $ BSVFromInteger (litExpr n)
  S.ExprRealLit r       -> return $ BSVExpr (S.TypeCon "Real" []) RealValRepr $ app $ C.RationalLit r
  S.ExprStringLit s     -> return $ BSVExpr (S.TypeCon "String" []) StringRepr $ app $ C.TextLit $ Text.pack s
  S.ExprUnaryOp op x    -> join (unaryOp op <$> translateExpr x)
  S.ExprBinaryOp x op y -> join (binaryOp op <$> translateExpr x <*> translateExpr y)
  S.ExprCond ps x y -> do
      cond <- translateCondPreds ps
      BSVExpr xt xtr x' <- translateExpr x
      BSVExpr yt ytr y' <- translateExpr y
      case testEquality xtr ytr of
        Just Refl ->
          BSVExpr xt xtr <$> ifte' xtr cond (return x') (return y')
        _ -> fail $ unwords ["Expression types failed to match in conditional expression:"
                            , show xt, show yt ]
  S.ExprFunCall fn args ->
      applyExpr fn =<< mapM translateExpr args

  S.ExprBitConcat xs -> concatEx =<< mapM translateExpr xs

  S.ExprBlock ss ->
     do clearStash
        mapM_ translateExprStmt ss
        useStash

  -- FIXME, we currently only support selecting from statically-known bit positions
  -- select a single bit
  S.ExprBitSelect x n Nothing -> do
    x' <- translateExpr x
    case x' of
      BSVExpr _ (BVRepr w) xw ->
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
      BSVExpr _ (BVRepr w) xw ->
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

recognize :: (?tenv :: TypeEnv)
          => (S.Type -> Maybe a)
          -> (S.Type -> Maybe a)
recognize f tp | Just x <- f tp =
  Just x
recognize f (S.TypeCon nm args) =
  recognize f =<< applyTypes ?tenv nm args
recognize _f _tp =
  Nothing

typeNat :: S.Type -> Maybe Integer
typeNat (S.TypeNat n) = Just n
typeNat _             = Nothing

bitType :: (?tenv :: TypeEnv) => S.Type -> Maybe Integer
bitType (S.TypeCon "Bit" [tn]) = recognize typeNat tn
bitType _ = Nothing

bitsType :: (?tenv :: TypeEnv) => S.Type -> Maybe (String, Integer)
bitsType (S.TypeCon nm [tn])
  | nm `elem` ["Bit", "Int", "UInt"] =
     do n <- recognize typeNat tn
        Just (nm, n)
bitsType _ = Nothing


toType :: String
       -> ((?tenv :: TypeEnv) => S.Type -> Maybe a)
       -> S.Type
       -> BSVGen h s ret a
toType msg f tp = do
  env <- bsvTypeEnv <$> get
  let ?tenv = env
  maybe (fail $ unwords ["Expected", msg, "type:", show tp])
        return
        (recognize f tp)

concatOne :: BSVExpr s
          -> BSVExpr s
          -> BSVGen h s ret (BSVExpr s)
concatOne (BSVExpr tx (BVRepr xw) x)
          (BSVExpr ty (BVRepr yw) y) = do
  xn <- toType "Bit" bitType tx
  yn <- toType "Bit" bitType ty
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


translateStmt :: forall h s r.
                 HandleAllocator h
              -> TypeRepr r
              -> S.Stmt
              -> BSVGen h s r ()
translateStmt halloc ret s = case s of
  S.StmtExpr e -> stashExpr =<< translateExpr e
  S.StmtReturn e -> do
      e' <- translateExpr e
      case e' of
        BSVExpr _tp r x ->
          case testEquality r ret of
            Just Refl -> returnFromFunction x
            Nothing   -> fail $ unwords ["Type mismatch at return statement", show r, show ret]
        BSVThunk _ _ _ _ -> fail $ unwords ["Cannot return a code-gen thunk from a function :-("]

  S.StmtLet nm (S.BindingEq e) -> do
      bindVar nm =<< translateExpr e

  S.StmtVarDecl decls ->
      mapM_ translateVarDecl decls

  -- FIXME!! Actually implement actions...
  S.StmtBlock S.Action _ ->
      case testEquality ret UnitRepr of
        Just Refl -> returnFromFunction (litExpr ())
        Nothing -> fail "Type mismatch in action block"

  S.StmtFunDef fundef -> do
    let proto = S.funDefProto fundef
    let nm = S.funName proto
    let nm' = functionNameFromText $ Text.pack nm
    st <- get
    let tenv = bsvTypeEnv st
    let ?tenv = tenv
    let venv = bsvStateVars st
    translateFunProto proto $ \(args :: CtxRepr args) (ret' :: TypeRepr ret) -> do
      let args' = args Ctx.%> closureRepr
      hdl <- liftST $ mkHandle' halloc nm' args' ret'
      (C.SomeCFG g,captured,ls) <- liftST $ translateInnerFun halloc hdl tenv venv fundef
      mapM_ recordCFG (C.AnyCFG g : ls)

      cls <- mkClosure venv captured

      let expr = BSVExpr (S.TypeFun proto) (FunctionHandleRepr args ret') $
                   app $ C.Closure args ret' (litExpr hdl) closureRepr cls

      bindVar nm expr

  S.StmtFor init test incr body ->
     do mapM_ transInit init
        while (InternalPos, transTest test)
              (InternalPos, do translateStmt halloc ret body
                               mapM_ transIncr incr)
    where
      transInit (Just tp, nm, expr) = translateVarDecl (S.VarDecl tp nm [] [expr])
      transInit (Nothing, nm, expr) = translateVarAssign (S.VarAssignEq (S.LValueIdent nm) expr)

      transTest :: S.Expr -> BSVGen h s r (Expr s BoolType)
      transTest ex =
         do x <- translateExpr ex
            case x of
              BSVExpr _ BoolRepr t -> return t
              _ -> fail "Expected boolean result from for loop test"

      transIncr (nm,ex) = translateVarAssign (S.VarAssignEq (S.LValueIdent nm) ex)

  S.StmtBlock S.Value ss ->
      mapM_ (translateStmt halloc ret) ss

  S.StmtVarAssign asgn ->
      translateVarAssign asgn

  _ -> fail $ "Unsupported statement form: " ++ show s


translateVarAssign :: forall h s ret.
  S.VarAssign ->
  BSVGen h s ret ()
translateVarAssign (S.VarAssignEq lhs expr) =
  do x <- translateExpr expr
     case x of
       BSVExpr _tp tpr x' -> goLHS tpr (\_ -> return x') lhs
       _ -> fail $ unwords $ ["Expected expression in variable assignment"]

 where
  goLHS :: TypeRepr tp -> (Expr s tp -> BSVGen h s ret (Expr s tp)) -> S.LValue -> BSVGen h s ret ()
  goLHS tpr fn (S.LValueIdent nm) =
     do mp <- bsvStateVars <$> get
        case Map.lookup nm mp of
           Just (BSV_BindReg _tp tpr' reg) | Just Refl <- testEquality tpr tpr' ->
             do v <- readReg reg
                v' <- fn v
                assignReg reg v'
           _ -> fail $ unwords $ ["Type mismatch assigning to", nm, show tpr]
  goLHS tpr fn (S.LValueIdx lhs ex) =
     do ex' <- translateExpr ex
        case ex' of
          BSVExpr _ IntegerRepr i ->
            do let idx = app $ C.IntegerToNat i
               goLHS (VectorRepr tpr)
                     (\vs -> do let v = app $ C.VectorGetEntry tpr vs idx
                                v' <- fn v
                                let vs' = app $ C.VectorSetEntry tpr vs idx v'
                                return vs'
                     )
                     lhs

  goLHS _tpr _fn lhs =
    fail $ unwords ["FIXME implement assignment for LHS:", show lhs]

translateVarAssign s =
  reportError $ litExpr $ Text.pack $ unwords ["FIXME! implement translateVarAssign", show s]


mkClosure :: forall h s ret
           . ValueEnv s
          -> Set S.Ident
          -> BSVGen h s ret (Expr s Closure)
mkClosure env vars =
   do let vars' = Set.toList vars
      Debug.trace (unwords $ "Closure variables:" : vars')
        go (app $ C.EmptyStringMap AnyRepr) vars'
 where
  go :: Expr s Closure
     -> [S.Ident]
     -> BSVGen h s ret (Expr s Closure)
  go cls [] = return cls
  go cls (s:ss) =
    case Map.lookup s env of
      Just (BSV_BindExpr _tp tpr ex) -> do
        let ex'  = app $ C.JustValue AnyRepr $ app $ C.PackAny tpr ex
        let cls' = app $ C.InsertStringMapEntry AnyRepr cls (litExpr $ Text.pack s) ex'
        go cls' ss
      _ -> fail $ "Captured variable not found in environment! " ++ s


translateVarDecl :: S.VarDecl
                 -> BSVGen h s ret ()
translateVarDecl (S.VarDecl tp nm dims es) = do
  env <- bsvTypeEnv <$> get
  let ?tenv = env
  translateArrayType tp dims $ \dims' tpr -> do
    reg <- case es of
             [] -> newReg =<< translateUninit tp dims' tpr
             _  -> newReg =<< translateArrayInit tp dims' tpr es
    bindReg nm (arrayTp dims' tp) tpr reg


translateVarDecl vd = fail $ unwords ["Unsupported var declaration form", show vd]


translateUninit :: S.Type -> [Integer] -> TypeRepr tp
                -> BSVGen h s ret (Expr s tp)
translateUninit tp [] (VectorRepr tpr) =
  do (n,tp') <- expectVectorType tp
     x <- translateUninit tp' [] tpr
     return $ app $ C.VectorReplicate tpr (litExpr $ fromInteger n) x

translateUninit tp [] (BVRepr w) =
  do return $ app $ C.BVUndef w



-- FIXME, this only handles one dimesnion at the moment!
translateArrayInit :: S.Type -> [Integer] -> TypeRepr tp -> [S.Expr]
                   -> BSVGen h s ret (Expr s tp)
translateArrayInit tp [] tpr [x] = do
  x' <- translateExpr x
  case x' of
    BSVExpr _ tpr' x'' ->
      case testEquality tpr tpr' of
        Just Refl -> return x''
        Nothing -> fail $ unwords ["Type mismatch in initializer", show tpr, show tpr']
    BSVThunk _ _ _ _ ->
      fail $ unwords ["unexpected code-gen thunk in array initializer"]
    BSVUnpack w expr ->
      do tenv <- bsvTypeEnv <$> get
         unpackExpr tenv tp tpr w expr
    BSVFromInteger n ->
      case tpr of
        IntegerRepr -> return n
        _ -> fail "FIXME, more cases in translateArrayInit for 'fromInteger'"


translateArrayInit _tp [n] (VectorRepr (elt_tp :: TypeRepr elt_tp)) xs | toInteger (length xs) == n =
  do let f :: BSVExpr s -> BSVGen h s ret (Expr s elt_tp)
         f (BSVThunk _ _ _ _) =
             fail $ unwords ["unexpected code-gen thunk in array initializer"]
         f (BSVFromInteger n) =
             case elt_tp of
               IntegerRepr -> return n
               BVRepr w    -> return $ app $ C.IntegerToBV w n
         f (BSVExpr _tp tpr x) =
             case testEquality elt_tp tpr of
               Just Refl -> return x
     xs' <- mapM (f <=< translateExpr) xs
     return $ app $ C.VectorLit elt_tp $ V.fromList $ xs'
translateArrayInit tp dims _tpr xs =
  fail $ unwords ["FIXME: implement translateArrayInit for", show tp, show dims, show xs]

translateArrayType :: (?tenv :: TypeEnv)
                   => S.Type
                   -> [S.Expr]
                   -> (forall tp. [Integer] -> TypeRepr tp -> a)
                   -> a
translateArrayType t dims0 k0 =
  translateType t $ \tpr ->
    goDims tpr dims0 k0

 where
  -- FIXME: pay attention to the given array dimensions?
  goDims :: forall a tp
          . TypeRepr tp
         -> [S.Expr]
         -> (forall tp'. [Integer] -> TypeRepr tp' -> a)
         -> a
  goDims tpr [] k = k [] tpr
  goDims tpr (S.ExprIntLit d:ds) k =
     goDims tpr ds $ \dims tpr' ->
       k (d:dims) (VectorRepr tpr')
  goDims _ (d:_) _ = error $ "Expected integer constant in array declaration: " ++ show d

translateType :: (?tenv :: TypeEnv)
              => S.Type
              -> (forall tp. TypeRepr tp -> a)
              -> a
translateType t k = case t of
  S.TypeFun proto ->
    translateTypes (map fst (S.funFormals proto)) $ \args ->
      translateType (S.funResultType proto) $ \res ->
        k (FunctionHandleRepr args res)

  -- FIXME!
  S.TypeCon "Action" [] -> k UnitRepr

  S.TypeCon "Bool" [] -> k BoolRepr
  S.TypeCon "Integer" [] -> k IntegerRepr
  S.TypeVar "Integer" -> k IntegerRepr
  S.TypeCon nm [tn]
    | nm `elem` ["Bit", "Int", "UInt"]
    , Just n <- recognize typeNat tn ->
      case someNat n of
        Just (Some w) | Just LeqProof <- isPosNat w -> k (BVRepr w)
        _ -> error $ unwords ["Illegal bit size:", show n]
  S.TypeCon "Vector" [_tn,telem] ->
    -- FIXME, check the length argument?
    translateType telem $ \elemRepr ->
      k (VectorRepr elemRepr)
  S.TypeCon "Array" [telem] ->
    translateType telem $ \elemRepr ->
      k (VectorRepr elemRepr)
  S.TypeCon nm args -> do
    case applyTypes ?tenv nm args of
      Just tp' -> translateType tp' k
      Nothing  -> error $ unwords ["Unsupported type form:", show t]

  S.TypeVar nm ->
    case applyTypes ?tenv nm [] of
      Just tp' -> translateType tp' k
      Nothing ->  error $ unwords ["Unsupported type form:", show t]

  _ -> error $ unwords ["Unsupported type form:", show t]


translateTypes :: forall a
                . (?tenv :: TypeEnv)
               => [S.Type]
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
             :: (?tenv :: TypeEnv)
             => S.FunProto
             -> (forall args r. CtxRepr args -> TypeRepr r -> a)
             -> a
translateFunProto proto k =
  translateTypes (map fst (S.funFormals proto)) $ \ctx ->
    translateType (S.funResultType proto) $ \ret ->
      k ctx ret

zipFormals :: forall s ctx
            . Ctx.Assignment (Atom s) ctx
           -> [(S.Type, S.Ident)]
           -> ValueEnv s
           -> ValueEnv s
zipFormals ctx0 fs0 = go ctx0 (reverse fs0)
 where
  go :: forall ctx'
      . Ctx.Assignment (Atom s) ctx'
     -> [(S.Type, S.Ident)]
     -> ValueEnv s
     -> ValueEnv s
  go ctx fs !env =
    case (Ctx.view ctx, fs) of
      ( Ctx.AssignEmpty, [] ) -> env
      ( Ctx.AssignExtend ctx' a, (t,nm):fs' ) ->
         go ctx' fs' (Map.insert nm (BSV_BindExpr t (typeOfAtom a) (AtomExpr a)) env)
      _ -> error "zipFormals: impossible! type assignment has different length than formal argument list"

initialState :: TypeEnv
             -> TopEnv
             -> Ctx.Assignment (Atom s) ctx
             -> [(S.Type, S.Ident)]
             -> BSVState h s
initialState tenv venv crucibleFormals bsvFormals =
  BSVState
  { bsvStateVars    = zipFormals crucibleFormals bsvFormals (topToValueEnv venv)
  , bsvTypeEnv      = tenv
  , bsvLastExpr     = Nothing
  , bsvCapturedVars = Nothing
  , bsvClosure      = Nothing
  }

nestedInitialState :: TypeEnv
             -> ValueEnv s
             -> Ctx.Assignment (Atom s) (ctx ::> Closure)
             -> [(S.Type, S.Ident)]
             -> STRef h (Set S.Ident)
             -> BSVState h s
nestedInitialState tenv venv assgn bsvFormals capturedRef =
  case Ctx.view assgn of
    Ctx.AssignExtend crucibleFormals cls ->
      BSVState
      { bsvStateVars    = zipFormals crucibleFormals bsvFormals venv
      , bsvTypeEnv      = tenv
      , bsvLastExpr     = Nothing
      , bsvCapturedVars = Just capturedRef
      , bsvClosure      = Just (AtomExpr cls)
      }


translateFun :: forall h args ret
              . HandleAllocator h
             -> FnHandle args ret
             -> TypeEnv
             -> TopEnv
             -> S.FunDef
             -> ST h (C.SomeCFG args ret, [C.AnyCFG])
translateFun halloc hdl tenv venv fundef = do
  let proto = S.funDefProto fundef
  let ?tenv = tenv
  let ret = handleReturnType hdl
  let nm = functionName $ handleName hdl
  let def :: FunctionDef h (BSVState h) args ret
      def formals = ( initialState tenv venv formals (S.funFormals proto)
                    , do mapM_ (translateStmt halloc ret) (S.funBody fundef)
                         returnStashedVal ret
                    )
  Debug.trace ("Translating function: " ++ Text.unpack nm) $ do
   (SomeCFG g, cfgs) <- defineFunction (SourcePos nm 0 0) hdl def
   let g' = toSSA g
   return (g', cfgs)

type Closure = StringMapType AnyType

closureRepr :: TypeRepr Closure
closureRepr = knownRepr

arrayTp :: [Integer] -> S.Type -> S.Type
arrayTp [] tp = tp
arrayTp (d:ds) tp = S.TypeCon "Array" [arrayTp ds tp]

translateInnerFun :: forall h s0 args ret
                   . HandleAllocator h
                  -> FnHandle (args ::> Closure) ret
                  -> TypeEnv
                  -> ValueEnv s0
                  -> S.FunDef
                  -> ST h (C.SomeCFG (args ::> Closure) ret, Set S.Ident, [C.AnyCFG])
translateInnerFun halloc hdl tenv venv fundef = do
  let proto = S.funDefProto fundef
  let ?tenv = tenv
  let ret = handleReturnType hdl
  let nm = functionName $ handleName hdl
  -- the type of 'defineFunction' doesn't let us direclty return additional information
  -- from running the generator.  So we use an STRef to leak some additional information
  -- out of the computation
  capturedRef <- newSTRef Set.empty
  let def :: FunctionDef h (BSVState h) (args ::> Closure) ret
      def formals = ( nestedInitialState tenv (nestValueEnv venv) formals (S.funFormals proto) capturedRef
                    , do mapM_ (translateStmt halloc ret) (S.funBody fundef)
                         returnStashedVal ret
                    )

  Debug.trace ("Translating inner function: " ++ Text.unpack nm) $ do
   (SomeCFG g, ls) <- defineFunction (SourcePos nm 0 0) hdl def
   captured <- readSTRef capturedRef
   let g' = toSSA g
   return (g', captured, ls)


translatePackageFuns :: forall h
                      . HandleAllocator h
                     -> TypeEnv
                     -> TopEnv
                     -> [S.PackageStmt]
                     -> ST h (TopEnv, [C.AnyCFG])
translatePackageFuns halloc tenv env0 ps0 =
    do (envfinal, defs) <- go env0 ps0 []
       cfgs <- mapM ($ envfinal) defs
       return (envfinal, concat cfgs)

  where
   goDecls :: TopEnv -> [S.VarDecl] -> [S.PackageStmt]
           -> [TopEnv -> ST h [C.AnyCFG]] -> ST h (TopEnv, [TopEnv -> ST h [C.AnyCFG]])
   goDecls venv [] ps defs = go venv ps defs
   goDecls venv (S.VarDecl tp nm dims initExprs : vdefs) ps defs = do
      let ?tenv = tenv
      let nm' = functionNameFromText $ Text.pack $ nm
      translateArrayType tp dims $ \dims' (ret :: TypeRepr ret) ->
        do hdl <- mkHandle' halloc nm' Ctx.empty ret
           let venv' = Map.insert nm (BSV_BindCAF (arrayTp dims' tp) hdl) venv
           let def venvfinal = do
                    let cafdef :: FunctionDef h (BSVState h) EmptyCtx ret
                        cafdef formals = ( initialState tenv venvfinal formals []
                                         , do e <- translateArrayInit tp dims' ret initExprs
                                              stashExpr (BSVExpr (arrayTp dims' tp) ret e)
                                              returnStashedVal ret
                                         )
                    (SomeCFG g, ls) <- defineFunction (SourcePos (Text.pack nm) 0 0) hdl cafdef
                    case toSSA g of C.SomeCFG g_ssa -> return (C.AnyCFG g_ssa : ls)
           goDecls venv' vdefs ps (def : defs)

   goDecls _ (vd : _) _ _ =
     fail $ unwords ["Unsupported package-level variable declaration:", show vd]

   go :: TopEnv -> [S.PackageStmt] -> [TopEnv -> ST h [C.AnyCFG]] -> ST h (TopEnv, [TopEnv -> ST h [C.AnyCFG]])
   go venv [] defs = return (venv, defs)
   go venv (S.PackageVarDecl decls : ps) defs =
      goDecls venv decls ps defs
   go venv (S.FunctionDefStmt fundef : ps) defs =
      do let proto = S.funDefProto fundef
         let nm = functionNameFromText $ Text.pack $ S.funName proto
         let ?tenv = tenv
         translateFunProto proto $ \(args :: CtxRepr args) (ret :: TypeRepr ret) ->
            do hdl <- mkHandle' halloc nm args ret
               let venv' = Map.insert (S.funName proto) (BSV_BindFun proto hdl) venv
               let def venvfinal =
                     do (C.SomeCFG g, ls) <- translateFun halloc hdl tenv venvfinal fundef
                        return (C.AnyCFG g : ls)
               go venv' ps (def : defs)

   go venv (_ : ps) defs = go venv ps defs
