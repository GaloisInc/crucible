-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Backend.SAWCore
-- Description      : Crucible interface for generating SAWCore
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides a Crucible backend that produces SAWCore terms.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Backend.SAWCore where

import           Control.Exception ( bracket )
import           Control.Lens
import           Control.Monad
import           Data.IORef
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableFC
import           Data.Ratio
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word(Word64)
import qualified Data.Text as Text

import           Numeric.Natural

import           What4.BaseTypes
import           What4.Config
import           What4.Interface
import qualified What4.Expr.Builder as B
import qualified What4.Expr.BoolMap as BM
import qualified What4.Expr.WeightedSum as WSum
import           What4.ProgramLoc
import           What4.Protocol.Online
import           What4.SatResult
import qualified What4.SemiRing as B
import qualified What4.Solver.Yices as Yices
import           What4.Symbol
import           What4.Utils.Hashable (hashedMap)

import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.Backend
import           Lang.Crucible.Backend.Online
import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Simulator.SimError

import qualified Verifier.SAW.Recognizer as SC (asLambda)
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.TypedAST as SC

data SAWCruciblePersonality sym = SAWCruciblePersonality

-- | The SAWCoreBackend is a crucible backend that represents symbolic values
--   as SAWCore terms.
data SAWCoreState solver n
  = SAWCoreState
    { saw_ctx       :: SC.SharedContext                         -- ^ the main SAWCore datastructure for building shared terms
    , saw_inputs    :: IORef (Seq (SC.ExtCns SC.Term ))
      -- ^ a record of all the symbolic input variables created so far,
      --   in the order they were created

    , saw_symMap :: !(Map Word64 (SC.SharedContext -> [SC.Term] -> IO SC.Term))
      -- ^ What to do with uninterpreted functions.
      -- The key is the "indexValue" of the "symFunId" for the function

    , saw_elt_cache :: B.IdxCache n SAWExpr

    , saw_online_state :: OnlineBackendState solver n
    }

data SAWExpr (bt :: BaseType) where
  SAWExpr :: !SC.Term -> SAWExpr bt

  -- This is a term that represents an integer, but has an
  -- implicit integer-to-real conversion.
  IntToRealSAWExpr :: !(SAWExpr BaseIntegerType) -> SAWExpr BaseRealType
  -- This is a SAWCore term that represents a natural number, but has an
  -- implicit nat-to-integer conversion.
  NatToIntSAWExpr :: !(SAWExpr BaseNatType) -> SAWExpr BaseIntegerType

type SAWCoreBackend n solver fs = B.ExprBuilder n (SAWCoreState solver) fs


-- | Run the given IO action with the given SAW backend.
--   While while running the action, the SAW backend is
--   set up with a fresh naming context.  This means that all
--   symbolic inputs, symMap entries, element cache entires,
--   assertions and proof obligations start empty while
--   running the action.  After the action completes, the
--   state of these fields is restored.
inFreshNamingContext :: SAWCoreBackend n solver fs -> IO a -> IO a
inFreshNamingContext sym f =
  do old <- readIORef (B.sbStateManager sym)
     bracket (mkNew (B.exprCounter sym) old) (restore old) action

 where
 action new =
   do writeIORef (B.sbStateManager sym) new
      f

 restore old _new =
   do writeIORef (B.sbStateManager sym) old

 mkNew _gen old =
   do ch <- B.newIdxCache
      iref <- newIORef mempty
      let new = SAWCoreState
                { saw_ctx = saw_ctx old
                , saw_inputs = iref
                , saw_symMap = mempty
                , saw_elt_cache = ch
                , saw_online_state = saw_online_state old
                }
      return new

getInputs :: SAWCoreBackend n solver fs -> IO (Seq (SC.ExtCns SC.Term))
getInputs sym =
  do st <- readIORef (B.sbStateManager sym)
     readIORef (saw_inputs st)

baseSCType ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  IO SC.Term
baseSCType sym sc bt =
  case bt of
    BaseBoolRepr -> SC.scBoolType sc
    BaseBVRepr w -> SC.scBitvector sc $ fromIntegral (natValue w)
    BaseNatRepr  -> SC.scNatType sc
    BaseIntegerRepr -> SC.scIntegerType sc
    BaseArrayRepr indexTypes range ->
      do ts <- baseSCTypes indexTypes
         t <- baseSCType sym sc range
         SC.scFunAll sc ts t
    BaseFloatRepr _ ->
      unsupported sym "SAW backend does not support IEEE-754 floating point values: baseSCType"
    BaseStringRepr   ->
      unsupported sym "SAW backend does not support string values: baseSCType"
    BaseComplexRepr  ->
      unsupported sym "SAW backend does not support complex values: baseSCType"
    BaseRealRepr     ->
      unsupported sym "SAW backend does not support real values: baseSCType"
    BaseStructRepr ts ->
      SC.scTupleType sc =<< baseSCTypes ts
  where
    baseSCTypes :: Ctx.Assignment BaseTypeRepr args -> IO [SC.Term]
    baseSCTypes Ctx.Empty = return []
    baseSCTypes (xs Ctx.:> x) =
      do ts <- baseSCTypes xs
         t <- baseSCType sym sc x
         return (ts ++ [t])

-- | Create a new symbolic variable.
sawCreateVar :: SAWCoreBackend n solver fs
             -> String                                       -- ^ the name of the variable
             -> SC.Term
             -> IO SC.Term
sawCreateVar sym nm tp = do
  st <- readIORef (B.sbStateManager sym)
  let sc = saw_ctx st
  i <- SC.scFreshGlobalVar sc
  let ec = SC.EC i ("var_"++nm++"_"++show i) tp
  t <- SC.scFlatTermF sc (SC.ExtCns ec)
  modifyIORef (saw_inputs st) (\xs -> xs Seq.|> ec)
  return t

bindSAWTerm :: SAWCoreBackend n solver fs
            -> BaseTypeRepr bt
            -> SC.Term
            -> IO (B.Expr n bt)
bindSAWTerm sym bt t = do
  st <- readIORef $ B.sbStateManager sym
  sbVar@(B.BoundVarExpr bv) <- freshConstant sym emptySymbol bt
  B.insertIdxValue (saw_elt_cache st) (B.bvarId bv) (SAWExpr t)
  return sbVar

newSAWCoreBackend ::
  SC.SharedContext ->
  NonceGenerator IO s ->
  IO (SAWCoreBackend s (Yices.Connection s) fs)
newSAWCoreBackend sc gen = do
  inpr <- newIORef Seq.empty
  ch   <- B.newIdxCache
  let feats = Yices.yicesDefaultFeatures
  ob_st  <- initialOnlineBackendState gen feats
  let st = SAWCoreState
              { saw_ctx = sc
              , saw_inputs = inpr
              , saw_symMap = Map.empty
              , saw_elt_cache = ch
              , saw_online_state = ob_st
              }
  sym <- B.newExprBuilder st gen
  let options = onlineBackendOptions ++ Yices.yicesOptions
  extendConfig options (getConfiguration sym)
  writeIORef (B.sbStateManager sym) st
  return sym


-- | Register an interpretation for a symbolic function. This is not
-- used during simulation, but rather, when we translate Crucible
-- values back into SAW. The interpretation function takes a list of
-- arguments in regular (left-to-right) order.
sawRegisterSymFunInterp ::
  SAWCoreBackend n solver fs ->
  B.ExprSymFn n args ret ->
  (SC.SharedContext -> [SC.Term] -> IO SC.Term) ->
  IO ()
sawRegisterSymFunInterp sym f i =
  modifyIORef (B.sbStateManager sym) $ \s ->
      s { saw_symMap = Map.insert (indexValue (B.symFnId f)) i (saw_symMap s) }


sawBackendSharedContext :: SAWCoreBackend n solver fs -> IO SC.SharedContext
sawBackendSharedContext sym =
  saw_ctx <$> readIORef (B.sbStateManager sym)


toSC :: SAWCoreBackend n solver fs -> B.Expr n tp -> IO SC.Term
toSC sym elt =
  do st <- readIORef $ B.sbStateManager sym
     evaluateExpr sym (saw_ctx st) (saw_elt_cache st) elt


-- | Return a shared term with type nat from a SAWExpr.
scAsIntExpr ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  IO SC.Term
scAsIntExpr _ sc (IntToRealSAWExpr (NatToIntSAWExpr (SAWExpr t))) = SC.scNatToInt sc t
scAsIntExpr _ _ (IntToRealSAWExpr (SAWExpr t)) = return t
scAsIntExpr sym _ SAWExpr{} = unsupported sym
                                  "SAWbackend does not support real values."

-- | Create a Real SAWELT value from a Rational.
--
-- This fails on non-integer expressions.
scRealLit ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  Rational ->
  IO (SAWExpr BaseRealType)
scRealLit sym sc r
  | denominator r /= 1 =
    unsupported sym "SAW backend does not support real values"
  | r >= 0 =
    IntToRealSAWExpr . NatToIntSAWExpr . SAWExpr <$> SC.scNat sc (fromInteger (numerator r))
  | otherwise =
    IntToRealSAWExpr <$> scIntLit sc (numerator r)

-- | Create a SAWCore term with type 'Integer' from a Haskell Integer.
scIntLit :: SC.SharedContext -> Integer -> IO (SAWExpr BaseIntegerType)
scIntLit sc i
  | i >= 0 =
    SAWExpr <$> (SC.scNatToInt sc =<< SC.scNat sc (fromInteger i))
  | otherwise =
    SAWExpr <$> (SC.scIntNeg sc =<< SC.scNatToInt sc =<< SC.scNat sc (fromInteger (negate i)))

-- | Create a SAWCore term with type 'Nat' from a Haskell Nat.
scNatLit :: SC.SharedContext -> Natural -> IO (SAWExpr BaseNatType)
scNatLit sc n = SAWExpr <$> SC.scNat sc n

scBvLit :: SC.SharedContext -> NatRepr w -> Integer -> IO (SAWExpr (BaseBVType w))
scBvLit sc w x = SAWExpr <$> SC.scBvConst sc (natValue w) x


scRealCmpop ::
  (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseBoolType)) ->
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealCmpop intOp _ sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  intOp sc x y
scRealCmpop _ sym _ _ _ =
  unsupported sym "SAW backend does not support real values"

scRealBinop ::
  (SC.SharedContext -> SAWExpr BaseIntegerType -> SAWExpr BaseIntegerType -> IO (SAWExpr BaseIntegerType)) ->
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scRealBinop intOp _ sc (IntToRealSAWExpr x) (IntToRealSAWExpr y) =
  IntToRealSAWExpr <$> intOp sc x y
scRealBinop _ sym _ _ _ =
  unsupported sym "SAW backend does not support real values"


scIntBinop ::
  (SC.SharedContext -> SAWExpr BaseNatType -> SAWExpr BaseNatType -> IO (SAWExpr BaseNatType))
    {- ^ operation on naturals -} ->
  (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) {- ^ operation on integers -} ->
  SC.SharedContext ->
  SAWExpr BaseIntegerType ->
  SAWExpr BaseIntegerType ->
  IO (SAWExpr BaseIntegerType)
scIntBinop natOp _intOp sc (NatToIntSAWExpr x) (NatToIntSAWExpr y) =
  NatToIntSAWExpr <$> natOp sc x y
scIntBinop _natOp intOp sc (NatToIntSAWExpr (SAWExpr x)) (SAWExpr y) =
  SAWExpr <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntBinop _natOp intOp sc (SAWExpr x) (NatToIntSAWExpr (SAWExpr y)) =
  SAWExpr <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntBinop _natOp intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scIntCmpop ::
  (SC.SharedContext -> SAWExpr BaseNatType -> SAWExpr BaseNatType -> IO (SAWExpr BaseBoolType))
    {- ^ operation on naturals -} ->
  (SC.SharedContext -> SC.Term -> SC.Term -> IO SC.Term) {- ^ operation on integers -} ->
  SC.SharedContext ->
  SAWExpr BaseIntegerType ->
  SAWExpr BaseIntegerType ->
  IO (SAWExpr BaseBoolType)
scIntCmpop natOp _intOp sc (NatToIntSAWExpr x) (NatToIntSAWExpr y) =
  natOp sc x y
scIntCmpop _natOp intOp sc (NatToIntSAWExpr (SAWExpr x)) (SAWExpr y) =
  SAWExpr <$> join (intOp sc <$> SC.scNatToInt sc x <*> pure y)
scIntCmpop _natOp intOp sc (SAWExpr x) (NatToIntSAWExpr (SAWExpr y)) =
  SAWExpr <$> join (intOp sc <$> pure x <*> SC.scNatToInt sc y)
scIntCmpop _natOp intOp sc (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> intOp sc x y

scAddReal ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scAddReal = scRealBinop scAddInt

scAddInt :: SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scAddInt = scIntBinop scAddNat SC.scIntAdd

scAddNat :: SC.SharedContext
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scAddNat sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scAddNat sc x y


scMulReal ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scMulReal = scRealBinop scMulInt

scMulInt :: SC.SharedContext
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scMulInt = scIntBinop scMulNat SC.scIntMul

scMulNat :: SC.SharedContext
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scMulNat sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scMulNat sc x y

scIteReal ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SC.Term ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseRealType)
scIteReal sym sc p = scRealBinop (\sc' -> scIteInt sc' p) sym sc

scIteInt :: SC.SharedContext
            -> SC.Term
            -> SAWExpr BaseIntegerType
            -> SAWExpr BaseIntegerType
            -> IO (SAWExpr BaseIntegerType)
scIteInt sc p = scIntBinop
    (\sc' -> scIteNat sc' p)
    (\sc' x y -> SC.scIntegerType sc >>= \tp -> SC.scIte sc' tp p x y)
    sc

scIteNat :: SC.SharedContext
            -> SC.Term
            -> SAWExpr BaseNatType
            -> SAWExpr BaseNatType
            -> IO (SAWExpr BaseNatType)
scIteNat sc p (SAWExpr x) (SAWExpr y) =
  SAWExpr <$> (SC.scNatType sc >>= \tp -> SC.scIte sc tp p x y)

scIte ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  SAWExpr BaseBoolType ->
  SAWExpr tp ->
  SAWExpr tp ->
  IO (SAWExpr tp)
scIte sym sc tp (SAWExpr p) x y =
  case tp of
    BaseRealRepr    -> scIteReal sym sc p x y
    BaseNatRepr     -> scIteNat sc p x y
    BaseIntegerRepr -> scIteInt sc p x y
    BaseArrayRepr indexTypes range ->
        makeArray sym sc indexTypes $ \vars ->
        do x' <- applyArray sym sc x vars
           y' <- applyArray sym sc y vars
           scIte sym sc range (SAWExpr p) x' y'
    _ ->
      do tp' <- baseSCType sym sc tp
         x' <- termOfSAWExpr sym sc x
         y' <- termOfSAWExpr sym sc y
         SAWExpr <$> SC.scIte sc tp' p x' y'


scRealEq ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealEq = scRealCmpop scIntEq

scIntEq :: SC.SharedContext
        -> SAWExpr BaseIntegerType
        -> SAWExpr BaseIntegerType
        -> IO (SAWExpr BaseBoolType)
scIntEq = scIntCmpop scNatEq SC.scIntEq

scNatEq :: SC.SharedContext
        -> SAWExpr BaseNatType
        -> SAWExpr BaseNatType
        -> IO (SAWExpr BaseBoolType)
scNatEq sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scEqualNat sc x y

scBoolEq ::
  SC.SharedContext ->
  SAWExpr BaseBoolType ->
  SAWExpr BaseBoolType ->
  IO (SAWExpr BaseBoolType)
scBoolEq sc (SAWExpr x) (SAWExpr y) = SAWExpr <$> SC.scBoolEq sc x y

scEq ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  BaseTypeRepr tp ->
  SAWExpr tp ->
  SAWExpr tp ->
  IO (SAWExpr BaseBoolType)
scEq sym sc tp x y =
  case tp of
    BaseBoolRepr    -> scBoolEq sc x y
    BaseRealRepr    -> scRealEq sym sc x y
    BaseNatRepr     -> scNatEq sc x y
    BaseIntegerRepr -> scIntEq sc x y
    BaseBVRepr w    ->
      do let SAWExpr x' = x
         let SAWExpr y' = y
         w' <- SC.scNat sc $ fromIntegral (natValue w)
         SAWExpr <$> SC.scBvEq sc w' x' y'
    _ -> unsupported sym ("SAW backend: equality comparison on unsupported type:" ++ show tp)


scAllEq ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  Ctx.Assignment BaseTypeRepr ctx ->
  Ctx.Assignment SAWExpr ctx ->
  Ctx.Assignment SAWExpr ctx ->
  IO (SAWExpr BaseBoolType)
scAllEq _sym sc Ctx.Empty _ _ = SAWExpr <$> SC.scBool sc True
scAllEq sym sc (ctx Ctx.:> tp) (xs Ctx.:> x) (ys Ctx.:> y)
  | Ctx.null ctx = scEq sym sc tp x y
  | otherwise =
    do SAWExpr p <- scAllEq sym sc ctx xs ys
       SAWExpr q <- scEq sym sc tp x y
       SAWExpr <$> SC.scAnd sc p q

scRealLe ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr BaseRealType ->
  SAWExpr BaseRealType ->
  IO (SAWExpr BaseBoolType)
scRealLe = scRealCmpop scIntLe

scIntLe :: SC.SharedContext
        -> SAWExpr BaseIntegerType
        -> SAWExpr BaseIntegerType
        -> IO (SAWExpr BaseBoolType)
scIntLe = scIntCmpop scNatLe SC.scIntLe

scNatLe :: SC.SharedContext
        -> SAWExpr BaseNatType
        -> SAWExpr BaseNatType
        -> IO (SAWExpr BaseBoolType)
scNatLe sc (SAWExpr x) (SAWExpr y) =
  do lt <- SC.scLtNat sc x y
     eq <- SC.scEqualNat sc x y
     SAWExpr <$> SC.scOr sc lt eq

scBvAdd ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvAdd sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvAdd sc n x y

scBvNot ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvNot sc w (SAWExpr x) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvNot sc n x

scBvMul ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvMul sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvMul sc n x y

scBvAnd ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvAnd sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvAnd sc n x y

scBvXor ::
  SC.SharedContext ->
  NatRepr w ->
  SAWExpr (BaseBVType w) ->
  SAWExpr (BaseBVType w) ->
  IO (SAWExpr (BaseBVType w))
scBvXor sc w (SAWExpr x) (SAWExpr y) =
  do n <- SC.scNat sc (natValue w)
     SAWExpr <$> SC.scBvXor sc n x y

termOfSAWExpr ::
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr tp -> IO SC.Term
termOfSAWExpr sym sc expr =
  case expr of
    SAWExpr t -> return t
    NatToIntSAWExpr (SAWExpr t) -> SC.scNatToInt sc t
    IntToRealSAWExpr _
      -> unsupported sym "SAW backend does not support real values"

makeArray ::
  forall n solver fs idx tp.
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  Ctx.Assignment BaseTypeRepr idx ->
  (Ctx.Assignment SAWExpr idx -> IO (SAWExpr tp)) ->
  IO (SAWExpr (BaseArrayType idx tp))
makeArray sym sc idx k =
  do vars <- mkVars 0 idx
     body <- k vars >>= termOfSAWExpr sym sc
     SAWExpr <$> mkLambdas idx body
  where
    mkVars :: Int -> Ctx.Assignment BaseTypeRepr idx' -> IO (Ctx.Assignment SAWExpr idx')
    mkVars _ Ctx.Empty = return Ctx.Empty
    mkVars i (tys Ctx.:> _) =
      do v <- SAWExpr <$> SC.scLocalVar sc i
         vs <- mkVars (i+1) tys
         return (vs Ctx.:> v)

    mkLambdas :: Ctx.Assignment BaseTypeRepr idx' -> SC.Term -> IO SC.Term
    mkLambdas Ctx.Empty e = return e
    mkLambdas (tys Ctx.:> ty) e =
      do let x = "x" ++ show (Ctx.size tys)
         ty' <- baseSCType sym sc ty
         mkLambdas tys =<< SC.scLambda sc x ty' e

applyArray ::
  forall n solver fs idx tp.
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SAWExpr (BaseArrayType idx tp) ->
  Ctx.Assignment SAWExpr idx ->
  IO (SAWExpr tp)
applyArray sym sc (SAWExpr f) args = SAWExpr <$> go args
  where
    go :: Ctx.Assignment SAWExpr idx' -> IO SC.Term
    go Ctx.Empty = return f
    go (xs Ctx.:> x) =
      do f' <- go xs
         x' <- termOfSAWExpr sym sc x
         -- beta-reduce application if possible
         case SC.asLambda f' of
           Just (_, _, body) -> SC.instantiateVar sc 0 x' body
           Nothing           -> SC.scApply sc f' x'

maxIndexLit :: IndexLit tp -> IndexLit tp -> IndexLit tp
maxIndexLit (NatIndexLit x) (NatIndexLit y) = NatIndexLit (max x y)
maxIndexLit (BVIndexLit w x) (BVIndexLit _ y) = BVIndexLit w (max x y)

sizeIndexLit :: forall tp. IndexLit tp -> Integer
sizeIndexLit (NatIndexLit n) = toInteger n + 1
sizeIndexLit (BVIndexLit _ n) = n + 1

evalIndexLit :: SC.SharedContext -> IndexLit tp -> IO (SAWExpr tp)
evalIndexLit sc l =
  case l of
    NatIndexLit n ->
      do SAWExpr <$> SC.scNat sc (fromInteger (toInteger n))
    BVIndexLit w n ->
      do w' <- SC.scNat sc (natValue w)
         n' <- SC.scNat sc (fromInteger n)
         SAWExpr <$> SC.scBvNat sc w' n'

makeTable ::
  SC.SharedContext ->
  Ctx.Assignment IndexLit ctx {- ^ maximum index -} ->
  (Ctx.Assignment IndexLit ctx -> IO SC.Term) {- ^ generating function -} ->
  SC.Term {- ^ table element type -} ->
  IO SC.Term
makeTable _sc Ctx.Empty mkElem _elemTy = mkElem Ctx.Empty
makeTable sc (idxs Ctx.:> idx) mkElem elemTy =
  do len <- SC.scNat sc (fromInteger (sizeIndexLit idx))
     elemTy' <- SC.scVecType sc len elemTy
     let mkElem' vars =
           do elems <- traverse (\v -> mkElem (vars Ctx.:> v)) (upto idx)
              SC.scVector sc elemTy elems
     makeTable sc idxs mkElem' elemTy'
  where
    upto :: IndexLit tp -> [IndexLit tp]
    upto (NatIndexLit n) = [ NatIndexLit i | i <- [0 .. n] ]
    upto (BVIndexLit w n) = [ BVIndexLit w i | i <- [0 .. n] ]

applyTable ::
  forall n solver fs ctx ret.
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  SC.Term {- ^ table (nested vectors) -} ->
  Ctx.Assignment IndexLit ctx {- ^ maximum index -} ->
  Ctx.Assignment SAWExpr ctx {- ^ indices -} ->
  SC.Term {- ^ element type -} ->
  SAWExpr ret {- ^ fallback value for out-of-bounds -} ->
  IO (SAWExpr ret)
applyTable sym sc t0 maxidx vars ret fallback =
  do fallback' <- termOfSAWExpr sym sc fallback
     SAWExpr <$> go ret maxidx vars fallback'
  where
    go ::
      SC.Term ->
      Ctx.Assignment IndexLit ctx' ->
      Ctx.Assignment SAWExpr ctx' ->
      SC.Term ->
      IO SC.Term
    go _ty Ctx.Empty Ctx.Empty _fb = return t0
    go ty (imax Ctx.:> NatIndexLit n) (xs Ctx.:> SAWExpr x) fb =
      do len <- SC.scNat sc (fromInteger (toInteger (n + 1)))
         ty' <- SC.scVecType sc len ty
         fb' <- SC.scGlobalApply sc (SC.mkIdent SC.preludeName "replicate") [len, ty, fb]
         vec <- go ty' imax xs fb'
         SC.scGlobalApply sc (SC.mkIdent SC.preludeName "atWithDefault") [len, ty, fb, vec, x]
    go ty (imax Ctx.:> BVIndexLit w n) (xs Ctx.:> SAWExpr x) fb =
      do len <- SC.scNat sc (fromInteger (n + 1))
         ty' <- SC.scVecType sc len ty
         fb' <- SC.scGlobalApply sc (SC.mkIdent SC.preludeName "replicate") [len, ty, fb]
         vec <- go ty' imax xs fb'
         x' <- SC.scBvToNat sc (natValue w) x
         SC.scGlobalApply sc (SC.mkIdent SC.preludeName "atWithDefault") [len, ty, fb, vec, x']

applyExprSymFn ::
  forall n solver fs args ret.
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  B.ExprSymFn n args ret ->
  Ctx.Assignment SAWExpr args ->
  IO (SAWExpr ret)
applyExprSymFn sym sc fn args =
  do st <- readIORef (B.sbStateManager sym)
     mk <-
       case Map.lookup (indexValue (B.symFnId fn)) (saw_symMap st) of
         Nothing -> panic "SAWCore.applyExprSymFn"
                    [ "Unknown symbolic function."
                    , "*** Name: " ++ show fn
                    ]
         Just mk -> return mk
     ts <- evaluateAsgn args
     SAWExpr <$> mk sc (reverse ts)
  where
    evaluateAsgn :: Ctx.Assignment SAWExpr args' -> IO [SC.Term]
    evaluateAsgn Ctx.Empty = return []
    evaluateAsgn (xs Ctx.:> x) =
      do vs <- evaluateAsgn xs
         v <- termOfSAWExpr sym sc x
         return (v : vs)


considerSatisfiability ::
  (OnlineSolver n solver) =>
  SAWCoreBackend n solver fs ->
  Maybe ProgramLoc ->
  B.BoolExpr n ->
  IO BranchResult
considerSatisfiability sym mbPloc p =
  do proc <- getSolverProcess' (\sym' -> saw_online_state <$> readIORef (B.sbStateManager sym')) sym
     pnot <- notPred sym p
     let locDesc = case mbPloc of
           Just ploc -> show (plSourceLoc ploc)
           Nothing -> "(unknown location)"
     let rsn = "branch sat: " ++ locDesc
     p_res <- checkSatisfiable proc rsn p
     pnot_res <- checkSatisfiable proc rsn pnot
     case (p_res, pnot_res) of
       (Unsat{}, Unsat{}) -> return UnsatisfiableContext
       (_      , Unsat{}) -> return (NoBranch True)
       (Unsat{}, _      ) -> return (NoBranch False)
       _                  -> return IndeterminateBranchResult

{- | Declare that we don't support something or other.
This aborts the current path of execution, and adds a proof
obligation to ensure that we won't get there.
These proof obligations are all tagged with "Unsupported", so that
users of the library can choose if they will try to discharge them,
fail in some other way, or just ignore them. -}
unsupported :: SAWCoreBackend n solver fs -> String -> IO a
unsupported sym x = addFailedAssertion sym (Unsupported x)

evaluateExpr :: forall n solver tp fs.
  SAWCoreBackend n solver fs ->
  SC.SharedContext ->
  B.IdxCache n SAWExpr ->
  B.Expr n tp ->
  IO SC.Term
evaluateExpr sym sc cache = f
  where
    -- Evaluate the element, and expect the result to have the same type.
    f :: B.Expr n tp' -> IO SC.Term
    f elt = termOfSAWExpr sym sc =<< eval elt

    eval :: B.Expr n tp' -> IO (SAWExpr tp')
    eval elt = B.idxCacheEval cache elt (go elt)

    realFail :: IO a
    realFail = unsupported sym "SAW backend does not support real values"

    cplxFail :: IO a
    cplxFail = unsupported sym "SAW backend does not support complex values"

    floatFail :: IO a
    floatFail = unsupported sym "SAW backend does not support floating-point values"

    go :: B.Expr n tp' -> IO (SAWExpr tp')

    go (B.BoolExpr b _) = SAWExpr <$> SC.scBool sc b

    go (B.SemiRingLiteral sr x _) =
      case sr of
        B.SemiRingNatRepr     -> scNatLit sc x
        B.SemiRingBVRepr _ w  -> scBvLit sc w x
        B.SemiRingIntegerRepr -> scIntLit sc x
        B.SemiRingRealRepr    -> scRealLit sym sc x

    go (B.StringExpr{}) =
      unsupported sym "SAW backend does not support string values"

    go (B.BoundVarExpr bv) =
      case B.bvarKind bv of
        B.UninterpVarKind -> do
           tp <- baseSCType sym sc (B.bvarType bv)
           -- SAWExpr <$> sawCreateVar sym "x" tp
           SAWExpr <$> sawCreateVar sym nm tp
             where nm = Text.unpack $ solverSymbolAsText $ B.bvarName bv
        B.LatchVarKind ->
          unsupported sym "SAW backend does not support latch variables"
        B.QuantifierVarKind ->
          unsupported sym "SAW backend does not support quantifier variables"

    go (B.NonceAppExpr p) =
      case B.nonceExprApp p of
        B.Forall{} ->
          unsupported sym "SAW backend does not support quantifiers"
        B.Exists{} ->
          unsupported sym "SAW backend does not support quantifiers"
        B.ArrayFromFn fn ->
          makeArray sym sc (B.symFnArgTypes fn) $ \vars ->
          applyExprSymFn sym sc fn vars
        B.MapOverArrays fn idxs arrs ->
          makeArray sym sc idxs $ \vars ->
          do args <- traverseFC
                     (\arr -> do t <- eval (unwrapArrayResult arr); applyArray sym sc t vars)
                     arrs
             applyExprSymFn sym sc fn args
        B.ArrayTrueOnEntries{} ->
          unsupported sym "SAW backend: not yet implemented: ArrayTrueOnEntries"
        B.FnApp fn asgn ->
          do args <- traverseFC eval asgn
             applyExprSymFn sym sc fn args

    go a0@(B.AppExpr a) =
      let nyi = unsupported sym $
                  "Expression form not yet implemented in SAWCore backend:\n"
                        ++ show a0
      in
      case B.appExprApp a of
        B.BaseIte bt _ c xe ye -> join (scIte sym sc bt <$> eval c <*> eval xe <*> eval ye)
        B.BaseEq bt xe ye -> join (scEq sym sc bt <$> eval xe <*> eval ye)

        B.SemiRingLe sr xe ye ->
          case sr of
            B.OrderedSemiRingRealRepr    -> join (scRealLe sym sc <$> eval xe <*> eval ye)
            B.OrderedSemiRingIntegerRepr -> join (scIntLe sc <$> eval xe <*> eval ye)
            B.OrderedSemiRingNatRepr     -> join (scNatLe sc <$> eval xe <*> eval ye)

        B.NotPred x ->
          SAWExpr <$> (SC.scNot sc =<< f x)

        B.ConjPred xs ->
          case BM.viewBoolMap xs of
            BM.BoolMapUnit -> SAWExpr <$> SC.scBool sc True
            BM.BoolMapDualUnit -> SAWExpr <$> SC.scBool sc False
            BM.BoolMapTerms (t:|ts) ->
              let pol (x,BM.Positive) = f x
                  pol (x,BM.Negative) = SC.scNot sc =<< f x
              in SAWExpr <$> join (foldM (SC.scAnd sc) <$> pol t <*> mapM pol ts)

        B.DisjPred xs ->
          case BM.viewBoolMap xs of
            BM.BoolMapUnit -> SAWExpr <$> SC.scBool sc False
            BM.BoolMapDualUnit -> SAWExpr <$> SC.scBool sc True
            BM.BoolMapTerms (t:|ts) ->
              let pol (x,BM.Positive) = f x
                  pol (x,BM.Negative) = SC.scNot sc =<< f x
              in SAWExpr <$> join (foldM (SC.scOr sc) <$> pol t <*> mapM pol ts)

        B.SemiRingProd pd ->
           case WSum.prodRepr pd of
             B.SemiRingRealRepr ->
               do pd' <- WSum.prodEvalM (scMulReal sym sc) eval pd
                  maybe (scRealLit sym sc 1) return pd'
             B.SemiRingIntegerRepr ->
               do pd' <- WSum.prodEvalM (scMulInt sc) eval pd
                  maybe (scIntLit sc 1) return pd'
             B.SemiRingNatRepr ->
               do pd' <- WSum.prodEvalM (scMulNat sc) eval pd
                  maybe (scNatLit sc 1) return pd'
             B.SemiRingBVRepr B.BVArithRepr w ->
               do n <- SC.scNat sc (natValue w)
                  pd' <- WSum.prodEvalM (SC.scBvMul sc n) f pd
                  maybe (scBvLit sc w 1) (return . SAWExpr) pd'
             B.SemiRingBVRepr B.BVBitsRepr w ->
               do n <- SC.scNat sc (natValue w)
                  pd' <- WSum.prodEvalM (SC.scBvAnd sc n) f pd
                  maybe (scBvLit sc w (maxUnsigned w)) (return . SAWExpr) pd'

        B.SemiRingSum ss ->
          case WSum.sumRepr ss of
            B.SemiRingRealRepr -> WSum.evalM add smul (scRealLit sym sc) ss
               where add x y = scAddReal sym sc x y
                     smul 1  e = eval e
                     smul sm e = join $ scMulReal sym sc <$> scRealLit sym sc sm <*> eval e
            B.SemiRingIntegerRepr -> WSum.evalM add smul (scIntLit sc) ss
               where add x y = scAddInt sc x y
                     smul 1  e = eval e
                     smul sm e = join $ scMulInt sc <$> scIntLit sc sm <*> eval e
            B.SemiRingNatRepr -> WSum.evalM add smul (scNatLit sc) ss
               where add x y = scAddNat sc x y
                     smul 1  e = eval e
                     smul sm e = join $ scMulNat sc <$> scNatLit sc sm <*> eval e
            B.SemiRingBVRepr B.BVArithRepr w -> WSum.evalM add smul (scBvLit sc w) ss
               where add x y   = scBvAdd sc w x y
                     smul 1  e = eval e
                     smul sm e = join (scBvMul sc w <$> scBvLit sc w sm <*> eval e)
            B.SemiRingBVRepr B.BVBitsRepr w
               | ss^.WSum.sumOffset == one -> scBvNot sc w =<< gf2_eval (ss & WSum.sumOffset .~ 0)
               | otherwise -> gf2_eval ss

              where one = maxUnsigned w
                    gf2_eval = WSum.evalM add smul (scBvLit sc w)
                    add x y = scBvXor sc w x y
                    smul sm e
                       | sm == one = eval e
                       | otherwise = join (scBvAnd sc w <$> scBvLit sc w sm <*> eval e)

        B.RealIsInteger{} -> unsupported sym "SAW backend does not support real values"

        B.BVOrBits pd ->
          case WSum.prodRepr pd of
            B.SemiRingBVRepr _ w ->
              do n <- SC.scNat sc (natValue w)
                 pd' <- WSum.prodEvalM (SC.scBvOr sc n) f pd
                 maybe (scBvLit sc w 0) (return . SAWExpr) pd'

        B.BVFill w p ->
          do bit <- SC.scBoolType sc
             n <- SC.scNat sc (natValue w)
             x <- f p
             SAWExpr <$> SC.scGlobalApply sc (SC.mkIdent SC.preludeName "replicate") [n, bit, x]

        B.BVTestBit i bv -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth bv))
             bit <- SC.scBoolType sc
             join (SC.scAt sc w bit <$> f bv <*> SC.scNat sc (fromIntegral i))
        B.BVSlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth x))
             join (SC.scBvSLt sc w <$> f x <*> f y)
        B.BVUlt x y -> fmap SAWExpr $ do
             w <- SC.scNat sc (natValue (bvWidth x))
             join (SC.scBvULt sc w <$> f x <*> f y)

        B.BVUnaryTerm{} -> unsupported sym "SAW backend does not support the unary bitvector representation"

        B.BVUdiv _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvUDiv sc n <$> f x <*> f y)
        B.BVUrem _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvURem sc n <$> f x <*> f y)
        B.BVSdiv _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvSDiv sc n <$> f x <*> f y)
        B.BVSrem _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           join (SC.scBvSRem sc n <$> f x <*> f y)
        B.BVShl _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           n <- SC.scNat sc w
           join (SC.scBvShl sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        B.BVLshr _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           n <- SC.scNat sc w
           join (SC.scBvShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        B.BVAshr _ x y -> fmap SAWExpr $ do
           let w = natValue (bvWidth x)
           -- NB: bvSShr applies a `Succ` to its width argument, so we subtract
           --     1 here to make things match up.
           n <- SC.scNat sc (w - 1)
           join (SC.scBvSShr sc n <$> f x <*> (SC.scBvToNat sc w =<< f y))
        B.BVRol w x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue w)
           bit <- SC.scBoolType sc
           x' <- f x
           y' <- SC.scBvToNat sc (natValue w) =<< f y
           SC.scGlobalApply sc (SC.mkIdent SC.preludeName "rotateL") [n,bit,x',y']
        B.BVRor w x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue w)
           bit <- SC.scBoolType sc
           x' <- f x
           y' <- SC.scBvToNat sc (natValue w) =<< f y
           SC.scGlobalApply sc (SC.mkIdent SC.preludeName "rotateR") [n,bit,x',y']
        B.BVConcat _ x y -> fmap SAWExpr $ do
           n <- SC.scNat sc (natValue (bvWidth x))
           m <- SC.scNat sc (natValue (bvWidth y))
           t <- SC.scBoolType sc
           join (SC.scAppend sc t n m <$> f x <*> f y)
        B.BVSelect start num x -> fmap SAWExpr $ do
           i <- SC.scNat sc (natValue (bvWidth x) - natValue num - natValue start)
           n <- SC.scNat sc (natValue num)
           o <- SC.scNat sc (natValue start)
           t <- SC.scBoolType sc
           x' <- f x
           SC.scSlice sc t i n o x'
        B.BVZext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          n <- SC.scNat sc (natValue w)
          m <- SC.scNat sc (natValue w' - natValue w)
          x' <- f x
          SC.scBvUExt sc m n x'
        B.BVSext w' x -> fmap SAWExpr $ do
          let w = bvWidth x
          -- NB: width - 1 to make SAWCore types work out
          n <- SC.scNat sc (natValue w - 1)
          m <- SC.scNat sc (natValue w' - natValue w)
          x' <- f x
          SC.scBvSExt sc m n x'
        B.BVPopcount w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f x
             SAWExpr <$> SC.scBvPopcount sc n x'
        B.BVCountLeadingZeros w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f x
             SAWExpr <$> SC.scBvCountLeadingZeros sc n x'
        B.BVCountTrailingZeros w x ->
          do n  <- SC.scNat sc (natValue w)
             x' <- f x
             SAWExpr <$> SC.scBvCountTrailingZeros sc n x'

        B.ArrayMap indexTypes range updates arr ->
          do let m = hashedMap updates
             let maxidx = foldr1 (Ctx.zipWith maxIndexLit) (Map.keys m)
             let sizes = toListFC sizeIndexLit maxidx
             case 2 * toInteger (Map.size m) >= product sizes of
               -- Make vector table if it would be sufficiently (1/2) full.
               True ->
                 do elemTy <- baseSCType sym sc range
                    arr' <- eval arr
                    let mkElem idxs =
                          termOfSAWExpr sym sc =<<
                          case Map.lookup idxs m of
                            Just x -> eval x
                            Nothing ->
                              do idxs' <- traverseFC (evalIndexLit sc) idxs
                                 applyArray sym sc arr' idxs'
                    table <- makeTable sc maxidx mkElem elemTy
                    makeArray sym sc indexTypes $ \vars ->
                      do fallback <- applyArray sym sc arr' vars
                         applyTable sym sc table maxidx vars elemTy fallback
               -- If table would be too sparse, treat as repeated updates.
               False ->
                 makeArray sym sc indexTypes $ \vars ->
                 do arr' <- eval arr
                    fallback <- applyArray sym sc arr' vars
                    let upd fb (idxs, x) =
                          do idxs' <- traverseFC (evalIndexLit sc) idxs
                             x' <- eval x
                             p <- scAllEq sym sc indexTypes vars idxs'
                             scIte sym sc range p x' fb
                    foldM upd fallback (Map.assocs m)

        B.ConstantArray indexTypes _range v ->
          makeArray sym sc indexTypes $ \_ -> eval v

        B.SelectArray _ arr indexTerms ->
          do arr' <- eval arr
             xs <- traverseFC eval indexTerms
             applyArray sym sc arr' xs


        B.UpdateArray range indexTypes arr indexTerms v ->
          makeArray sym sc indexTypes $ \vars ->
          do idxs <- traverseFC eval indexTerms
             p <- scAllEq sym sc indexTypes vars idxs
             v' <- eval v
             arr' <- eval arr
             x <- applyArray sym sc arr' vars
             scIte sym sc range p v' x

        B.NatToInteger x -> NatToIntSAWExpr <$> eval x
        B.IntegerToNat x ->
           eval x >>= \case
             NatToIntSAWExpr z -> return z
             SAWExpr z -> SAWExpr <$> (SC.scIntToNat sc z)

        B.NatDiv x y ->
          do x' <- f x
             y' <- f y
             SAWExpr <$> SC.scDivNat sc x' y'

        B.NatMod x y ->
          do x' <- f x
             y' <- f y
             SAWExpr <$> SC.scModNat sc x' y'

        B.IntDiv x y ->
          do x' <- f x
             y' <- f y
             SAWExpr <$> SC.scIntDiv sc x' y'
        B.IntMod x y ->
          do x' <- f x
             y' <- f y
             SAWExpr <$> SC.scIntMod sc x' y'
        B.IntAbs x ->
          eval x >>= \case
            NatToIntSAWExpr z -> return (NatToIntSAWExpr z)
            SAWExpr z -> SAWExpr <$> (SC.scIntAbs sc z)

        B.IntDivisible x 0 ->
          do x' <- f x
             SAWExpr <$> (SC.scIntEq sc x' =<< SC.scIntegerConst sc 0)
        B.IntDivisible x k ->
          do x' <- f x
             k' <- SC.scIntegerConst sc (toInteger k)
             z  <- SC.scIntMod sc x' k'
             SAWExpr <$> (SC.scIntEq sc z =<< SC.scIntegerConst sc 0)

        B.BVToNat x ->
          let n = natValue (bvWidth x) in
          SAWExpr <$> (SC.scBvToNat sc n =<< f x)

        B.IntegerToBV x w ->
          do n <- SC.scNat sc (natValue w)
             SAWExpr <$> (SC.scIntToBv sc n =<< f x)

        B.BVToInteger x ->
          do n <- SC.scNat sc (natValue (bvWidth x))
             SAWExpr <$> (SC.scBvToInt sc n =<< f x)

        B.SBVToInteger x ->
          do n <- SC.scNat sc (natValue (bvWidth x))
             SAWExpr <$> (SC.scSbvToInt sc n =<< f x)

        -- Proper support for real and complex numbers will require additional
        -- work on the SAWCore side
        B.IntegerToReal x -> IntToRealSAWExpr . SAWExpr <$> f x
        B.RealToInteger x ->
          eval x >>= \case
            IntToRealSAWExpr x' -> return x'
            _ -> realFail

        ------------------------------------------------------------------------
        -- Floating point operations

        B.FloatPZero{} -> floatFail
        B.FloatNZero{} -> floatFail
        B.FloatNaN{}   -> floatFail
        B.FloatPInf{}  -> floatFail
        B.FloatNInf{}  -> floatFail
        B.FloatNeg{}  -> floatFail
        B.FloatAbs{}  -> floatFail
        B.FloatSqrt{}  -> floatFail
        B.FloatAdd{}  -> floatFail
        B.FloatSub{}  -> floatFail
        B.FloatMul{}  -> floatFail
        B.FloatDiv{}  -> floatFail
        B.FloatRem{}  -> floatFail
        B.FloatMin{}  -> floatFail
        B.FloatMax{}  -> floatFail
        B.FloatFMA{}  -> floatFail
        B.FloatFpEq{}  -> floatFail
        B.FloatFpNe{}  -> floatFail
        B.FloatLe{}  -> floatFail
        B.FloatLt{}  -> floatFail
        B.FloatIsNaN{}  -> floatFail
        B.FloatIsInf{}  -> floatFail
        B.FloatIsZero{}  -> floatFail
        B.FloatIsPos{}  -> floatFail
        B.FloatIsNeg{}  -> floatFail
        B.FloatIsSubnorm{}  -> floatFail
        B.FloatIsNorm{}  -> floatFail
        B.FloatCast{}  -> floatFail
        B.FloatRound{} -> floatFail
        B.FloatFromBinary{}  -> floatFail
        B.BVToFloat{}  -> floatFail
        B.SBVToFloat{}  -> floatFail
        B.RealToFloat{}  -> floatFail
        B.FloatToBV{} -> floatFail
        B.FloatToSBV{} -> floatFail
        B.FloatToReal{} -> floatFail
        B.FloatToBinary{} -> floatFail

        B.RoundReal{} -> realFail
        B.FloorReal{} -> realFail
        B.CeilReal{} -> realFail
        B.RealDiv{} -> realFail
        B.RealSqrt{} -> realFail
        B.Pi{} -> realFail
        B.RealSin{} -> realFail
        B.RealCos{} -> realFail
        B.RealSinh{} -> realFail
        B.RealCosh{} -> realFail
        B.RealExp{} -> realFail
        B.RealLog{} -> realFail
        B.RealATan2{} -> realFail

        B.Cplx{}     -> cplxFail
        B.RealPart{} -> cplxFail
        B.ImagPart{} -> cplxFail

        B.StructCtor{} -> nyi -- FIXME
        B.StructField{} -> nyi -- FIXME

getAssumptionStack ::
  SAWCoreBackend s solver fs ->
  IO (AssumptionStack (B.BoolExpr s) AssumptionReason SimError)
getAssumptionStack sym =
  (assumptionStack . saw_online_state) <$> readIORef (B.sbStateManager sym)

instance IsBoolSolver (SAWCoreBackend n solver fs) where
  addProofObligation sym a =
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      _          -> AS.addProofObligation a =<< getAssumptionStack sym

  addAssumption sym a = do
    case asConstantPred (a^.labeledPred) of
      Just False -> abortExecBecause (AssumedFalse (a ^. labeledPredMsg))
      _ -> AS.assume a =<< getAssumptionStack sym

  addAssumptions sym ps = do
    stk <- getAssumptionStack sym
    AS.appendAssumptions ps stk

  getPathCondition sym = do
    stk <- getAssumptionStack sym
    ps <- AS.collectAssumptions stk
    andAllOf sym (folded.labeledPred) ps

  collectAssumptions sym =
    AS.collectAssumptions =<< getAssumptionStack sym

  getProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  clearProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.clearProofObligations stk

  pushAssumptionFrame sym = do
    stk <- getAssumptionStack sym
    AS.pushFrame stk

  popAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    AS.popFrame ident stk

  popAssumptionFrameAndObligations sym ident = do
    stk <- getAssumptionStack sym
    AS.popFrameAndGoals ident stk

  popUntilAssumptionFrame sym ident = do
    stk <- getAssumptionStack sym
    void $ AS.popFramesUntil ident stk

  saveAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.saveAssumptionStack stk

  restoreAssumptionState sym newstk = do
    stk <- getAssumptionStack sym
    AS.restoreAssumptionStack newstk stk
