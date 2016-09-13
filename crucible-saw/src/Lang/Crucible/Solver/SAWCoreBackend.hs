-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Solver.SAWCoreBackend
-- Description      : Crucible interface for generating SAWCore
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides a crucible backend that produces SAWCore terms.
------------------------------------------------------------------------

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Solver.SAWCoreBackend where

import Control.Exception( throw )
import Control.Lens
import Control.Monad
import Control.Monad.ST
import Control.Monad.IO.Class
import qualified Data.Bits as Bits
--import qualified Data.IntMap as IntMap
import Data.Foldable
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import Data.Ratio
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import Data.Parameterized.Nonce.Unsafe
import Data.Parameterized.TH.GADT

import Lang.MATLAB.Utils.Nat

import Lang.Crucible.ProgramLoc
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Solver.Interface
import Lang.Crucible.BaseTypes
import Lang.Crucible.Types
import Lang.Crucible.Solver.PartExpr
--import qualified Lang.Crucible.Simulator.MatlabValue as MV
import Lang.Crucible.Utils.Arithmetic ( roundAway )
import Lang.Crucible.Utils.AbstractDomains
import Lang.Crucible.Utils.SymArray

import qualified Verifier.SAW.Prim as SC
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Recognizer as SC
import qualified Verifier.SAW.TypedAST as SC hiding (incVars)

-- | Run a computation with a fresh SAWCoreBackend, in the context of the
--   given module.
withSAWCoreBackend :: SC.Module -> (forall s. SAWCoreBackend s -> IO a) -> IO a
withSAWCoreBackend md f = do
    sc   <- SC.mkSharedContext md
    psr  <- newIORef (SAWCoreSymPathState Seq.empty initializationLoc)
    inpr <- newIORef Seq.empty
    ngen <- stToIO $ newNonceGenerator
    f (SAWCoreBackend sc psr inpr ngen)


-- | The SAWCoreBackend is a crucible backend that represents symbolic values
--   as SAWCore terms.
data SAWCoreBackend s
  = SAWCoreBackend
    { saw_ctx       :: SC.SharedContext s                         -- ^ the main SAWCore datastructure for building shared terms
    , saw_pathstate :: IORef (SAWCoreSymPathState s)              -- ^ a place to stash state about the currently-executing branch
    , saw_inputs    :: IORef (Seq (SC.ExtCns (SC.SharedTerm s)))  -- ^ a record of all the symbolic input variables created so far,
                                                                  --   in the order they were created
    , saw_nonce_gen :: NonceGenerator RealWorld
    }

mkArrayElt :: SAWCoreBackend s
           -> ArrayApp (Elt s) dom range
           -> IO (ArrayElt (Elt s) dom range)
mkArrayElt sc arr = do
   n <- stToIO $ freshNonce (saw_nonce_gen sc)
   l <- pathProgLoc <$> readIORef (saw_pathstate sc)
   return $ ArrayEltCtor n l arr

type instance SymExpr (SAWCoreBackend s) = Elt s

data Elt s tp where
  SCApp   :: SCApp (Elt s) tp -> Elt s tp
  SCArrayElt :: !(IndexTypeRepr dom)
             -> !(BaseTypeRepr range)
             -> !(ArrayElt (Elt s) dom range)
             -> Elt s (BaseArrayType dom range)
  -- a symbolic SAWCore value
  SC      :: BaseTypeRepr tp -> SC.SharedTerm s -> Elt s tp

data SCApp (e :: BaseType -> *) tp where
  -- a concreate nat value
  SCNat   :: Nat -> SCApp e BaseNatType

  -- the concrete true value
  SCTrue  :: SCApp e BaseBoolType

  -- the concrete false value
  SCFalse :: SCApp e BaseBoolType

  -- a concrete bitvector value
  SCBV    :: (1 <= w) => NatRepr w -> Integer -> SCApp e (BaseBVType w)

  -- a concreate real (actually, rational) value
  SCReal  :: Ratio Integer -> SCApp e BaseRealType

  -- a concrete integer value
  SCInt :: Integer -> SCApp e BaseIntegerType

  -- a complex value
  SCCplx  :: Complex (e BaseRealType) -> SCApp e BaseComplexType

  -- interpret a boolean as a bitvector; 0 for false 1 for true.
  -- This special form exists because LLVM program frequently involve a pattern of rendering
  -- a boolean value as a bitvector and then branching on if that value is nonzero.  By using
  -- this intermediate form, we can easily recognize and eliminate this noisy pattern.
  SC_BoolToBV :: (1 <= w)
              => NatRepr w
              -> e BaseBoolType
              -> SCApp e (BaseBVType w)

  SC_BVConcat :: (1 <= u, 1 <= v, 1 <= u+v)
           => !(NatRepr (u+v))
           -> !(e (BaseBVType u))
           -> !(e (BaseBVType v))
           -> SCApp e (BaseBVType (u+v))

  SC_BVSelect :: (1 <= n, idx + n <= w)
              -- First bit to select from (least-significant bit has index 0)
           => !(NatRepr idx)
              -- Number of bits to select, counting up toward more significant bits
           -> !(NatRepr n)
              -- Bitvector to select from.
           -> !(e (BaseBVType w))
           -> SCApp e (BaseBVType n)

  SC_BVZext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> SCApp e (BaseBVType r)

  SC_BVSext :: (1 <= w, w+1 <= r, 1 <= r)
         => !(NatRepr r)
         -> !(e (BaseBVType w))
         -> SCApp e (BaseBVType r)

  -- boolean negation
  SC_BoolNot  :: e BaseBoolType -> SCApp e BaseBoolType


appType :: SCApp e tp -> BaseTypeRepr tp
appType e =
  case e of
    SCNat{} -> baseTypeRepr
    SCTrue  -> baseTypeRepr
    SCFalse -> baseTypeRepr
    SC_BoolNot{} -> baseTypeRepr
    SCReal{} -> baseTypeRepr
    SCInt{}  -> baseTypeRepr
    SCCplx{} -> baseTypeRepr
    SCBV w _ -> BaseBVRepr w
    SC_BoolToBV w _ -> BaseBVRepr w
    SC_BVConcat w _ _ -> BaseBVRepr w
    SC_BVSelect _ w _ -> BaseBVRepr w
    SC_BVZext w _ -> BaseBVRepr w
    SC_BVSext w _ -> BaseBVRepr w

eltType :: Elt s tp -> BaseTypeRepr tp
eltType (SC tp _) = tp
eltType (SCArrayElt dom range _) = BaseArrayRepr dom range
eltType (SCApp e) = appType e

-- | Render the given symbolic value as a shared term.  Currently, SAWCore has
--   no real support for real or complex values, so these generate an error.
toSC :: SAWCoreBackend s -> Elt s tp -> IO (SC.SharedTerm s)
toSC _ (SC _ x)  = return x

toSC sc (SCArrayElt (dom :: IndexTypeRepr dom) range (arrayEltApp -> arr)) = do
    idx_tp <- case dom of
                 NatIndexRepr -> SC.scNatType (saw_ctx sc)
                 BVIndexRepr w -> SC.scBitvector (saw_ctx sc) (fromIntegral (natValue w))
    range_tp <- baseSCType (saw_ctx sc) range
    idxVar <- SC.scFreshGlobalVar (saw_ctx sc)
    let idxEC = SC.EC idxVar "idx" idx_tp
    idx <- SC.scFlatTermF (saw_ctx sc) (SC.ExtCns idxEC)
    (idxEq :: SC.SharedTerm s -> IO (SC.SharedTerm s)) <-
                case dom of
                   NatIndexRepr -> return $ SC.scEqualNat (saw_ctx sc) idx
                   BVIndexRepr w -> do
                      n <- SC.scNat (saw_ctx sc) (fromIntegral (natValue w))
                      return $ SC.scBvEq (saw_ctx sc) n idx
    let mkIdx :: ConcreteValue (IndexToBase dom) -> IO (SC.SharedTerm s)
        mkIdx k = case dom of
                    NatIndexRepr -> SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral k))
                    BVIndexRepr w -> SC.scBvConst (saw_ctx sc) (fromIntegral (natValue w)) k

    def <- SC.scApply (saw_ctx sc) <$> toSC sc (arrayAppDefault arr) <*> return idx
    conc <- Map.foldWithKey
              (\k v r -> do
                 k' <- mkIdx k
                 v' <- toSC sc v
                 p  <- idxEq k'
                 r' <- r
                 SC.scIte (saw_ctx sc) range_tp p v' r'
              )
              def
              (arrayAppConcreteMap arr)
    syms <- foldr
              (\symwrite r -> do
                 idxeq <- idxEq =<< toSC sc (arrayWriteSymIndex symwrite)
                 notovwr <- foldr
                             (\x p -> do
                                noteqx <- SC.scNot (saw_ctx sc) =<< idxEq =<< mkIdx x
                                SC.scAnd (saw_ctx sc) noteqx =<< p)
                             (SC.scBool (saw_ctx sc) True)
                             $ Set.toList $ arrayWriteOverwrites symwrite
                 wcond <- join (SC.scAnd (saw_ctx sc) <$> toSC sc (arrayWriteCondition symwrite)
                                                      <*> SC.scAnd (saw_ctx sc) idxeq notovwr)
                 v' <- toSC sc $ arrayWriteVal symwrite
                 r' <- r
                 SC.scIte (saw_ctx sc) range_tp wcond v' r'
              )
              (return conc)
              (toList (arrayAppWrites arr))
    SC.scAbstractExts (saw_ctx sc) [idxEC] syms

toSC sc (SCApp app) =
 case app of
   SCTrue -> SC.scBool (saw_ctx sc) True
   SCFalse -> SC.scBool (saw_ctx sc) False
   SCBV w x -> SC.scBvConst (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w))) x
   SCNat n -> SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral n))
   SCInt i
     | 0 <= i -> do
        SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) (SC.Nat (fromInteger i))
     | otherwise ->
        SC.scIntNeg (saw_ctx sc) =<<
            SC.scNatToInt (saw_ctx sc) =<<
            SC.scNat (saw_ctx sc) (SC.Nat (fromInteger (negate i)))

   SC_BVConcat uv x y -> do
       -- dynamic check; must succeed, but GHC can't figure it out
       Just LeqProof <- return $ isPosNat uv
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal (bvWidth x))))
       m <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal (bvWidth y))))
       t <- SC.scBoolType (saw_ctx sc)
       x' <- toSC sc x
       y' <- toSC sc y
       SC.scAppend (saw_ctx sc) t n m x' y'

   SC_BVSelect start num x
    | Just _ <- testEquality (knownNat :: NatRepr 0) start -> do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal num)))
       m <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w - widthVal num)))
       x' <- toSC sc x
       SC.scBvTrunc (saw_ctx sc) m n x'
    | otherwise -> do
       i <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal (bvWidth x) - widthVal num - widthVal start)))
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal num)))
       o <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal start)))
       t <- SC.scBoolType (saw_ctx sc)
       x' <- toSC sc x
       SC.scSlice (saw_ctx sc) t i n o x'

   SC_BVZext w' x -> do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       m <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w' - widthVal w)))
       x' <- toSC sc x
       SC.scBvUExt (saw_ctx sc) m n x'

   SC_BVSext w' x -> do
       let w = bvWidth x
       -- NB: width - 1 to make SAWCore types work out
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w - 1)))
       m <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w' - widthVal w)))
       x' <- toSC sc x
       SC.scBvSExt (saw_ctx sc) m n x'

   SC_BoolToBV w (SCApp SCTrue) -> toSC sc (SCApp (SCBV w 1))
   SC_BoolToBV w (SCApp SCFalse) -> toSC sc (SCApp (SCBV w 0))
   SC_BoolToBV w c -> do
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       c' <- toSC sc c
       SC.scBvBool (saw_ctx sc) n c'

   SC_BoolNot x -> SC.scNot (saw_ctx sc) =<< toSC sc x

   SCReal _ -> fail "cannot turn reals into SAWCore terms"
   SCCplx _ -> fail "cannot turn complex numbers into SAWCore terms"

toBVWidth :: Elt s (BaseBVType w) -> NatRepr w
toBVWidth (SC (BaseBVRepr w) _) = w
toBVWidth (SCApp app) =
  case app of
    SCBV w _ -> w
    SC_BoolToBV w _ -> w
    SC_BVSelect _ w _ -> w
    SC_BVConcat w _ _ -> w
    SC_BVZext w _ -> w
    SC_BVSext w _ -> w

baseSCType :: SC.SharedContext s -> BaseTypeRepr tp -> IO (SC.SharedTerm s)
baseSCType ctx bt =
  case bt of
    BaseBoolRepr -> SC.scBoolType ctx
    BaseBVRepr w -> SC.scBitvector ctx $ fromIntegral (natValue w)
    BaseNatRepr  -> SC.scNatType ctx
    BaseIntegerRepr -> SC.scInteger ctx
    BaseArrayRepr dom range -> join (SC.scFun ctx <$> baseSCType ctx dom <*> baseSCType ctx range)
    BaseComplexRepr -> fail "SAW backend does not support complex values: baseSCType"
    BaseRealRepr -> fail "SAW backend does not support real values: baseSCType"
    BaseStructRepr _ -> fail "FIXME baseSCType for structures"


scTypeRepr :: Elt s tp -> BaseTypeRepr tp
scTypeRepr (SC tp _) = tp
scTypeRepr (SCArrayElt dom range _) = BaseArrayRepr dom range
scTypeRepr (SCApp app) =
  case app of
    SCTrue -> baseTypeRepr
    SCFalse -> baseTypeRepr
    SC_BoolNot _ -> baseTypeRepr
    SCNat _ -> baseTypeRepr
    SCInt _ -> baseTypeRepr
    SCReal _ -> baseTypeRepr
    SCCplx _ -> baseTypeRepr
    SCBV w _ -> BaseBVRepr w
    SC_BoolToBV w _ -> BaseBVRepr w
    SC_BVSelect _ w _ -> BaseBVRepr w
    SC_BVConcat w _ _ -> BaseBVRepr w
    SC_BVZext w _ -> BaseBVRepr w
    SC_BVSext w _ -> BaseBVRepr w

-- -- | Given a symbolic expression and a sequence of symbolic inputs, abstract the given term
-- --   with respect to the inputs by introducing lambdas.
-- closeOver :: SAWCoreBackend s
--           -> Seq (SC.ExtCns (SC.SharedTerm s))
--           -> Elt s tp
--           -> IO (Elt s tp)
-- closeOver sc exts x
--    | Seq.null exts = return x
--    | otherwise     = SC (scTypeRepr x) <$> (SC.scAbstractExts (saw_ctx sc) (toList exts) =<< toSC sc x)

-- -- | Given a symbolic value and a sequence of symbolic inputs, abstract the given value
-- --   with respect to the inputs by introducing lambdas.  NOTE: each basic value included
-- --   in arrays and such will be abstracted separately!
-- closeOverValue
--    :: SAWCoreBackend s
--    -> Seq (SC.ExtCns (SC.SharedTerm s))
--    -> MV.Value (SAWCoreBackend s)
--    -> IO (MV.Value (SAWCoreBackend s))
-- closeOverValue sc exts v
--   | Seq.null exts = return v
--   | otherwise =
--      case v of
--        MV.RealArray a -> MV.RealArray <$> traverse (closeOver sc exts) a
--        MV.UIntArray (MV.SomeBVArray w a) -> MV.UIntArray . MV.SomeBVArray w <$> traverse (closeOver sc exts) a
--        MV.IntArray (MV.SomeBVArray w a) -> MV.IntArray . MV.SomeBVArray w <$> traverse (closeOver sc exts) a
--        MV.LogicArray a -> MV.LogicArray <$> traverse (closeOver sc exts) a
--        MV.CellArray a -> MV.CellArray <$> traverse (closeOverValue sc exts) a
--        MV.MatlabStructArray (MV.StructArr flds a) ->
--            MV.MatlabStructArray . MV.StructArr flds <$> traverse (traverse (closeOverValue sc exts)) a
--        MV.CharArray _ -> return v
--        MV.FunctionHandle _ -> return v


-- | State related to the currently-executing branch.  This includes the source position
--   of the original input, and the path assertions related to our control-flow history.
data SAWCoreSymPathState s
  = SAWCoreSymPathState
    { assertions  :: Seq (Assertion (Pred (SAWCoreBackend s)))
    , pathProgLoc :: !ProgramLoc
    }

type instance SymPathState (SAWCoreBackend s) = SAWCoreSymPathState s

getAssertions :: SAWCoreBackend s -> IO (Seq (Assertion (Pred (SAWCoreBackend s))))
getAssertions sc = assertions <$> readIORef (saw_pathstate sc)

type BoolElt s = Elt s BaseBoolType

symImplies :: SAWCoreBackend s -> BoolElt s -> BoolElt s -> IO (BoolElt s)
symImplies sc x y = do
  case (asConstantPred x, asConstantPred y) of
    (Just True,  _) -> return y
    (Just False, _) -> return $ truePred sc
    (_, Just False) -> notPred sc x
    (_, Just True)  -> return $ truePred sc
    _ | x == y -> return $ truePred sc
    _ -> notPred sc x >>= \x' -> orPred sc x' y

impliesAssert :: SAWCoreBackend s
              -> Elt s BaseBoolType
              -> Seq (Assertion (Pred (SAWCoreBackend s)))
              -> IO (Seq (Assertion (Pred (SAWCoreBackend s))))
impliesAssert solver c = go Seq.empty
  where go prev next =
          case Seq.viewr next of
            Seq.EmptyR -> return prev
            new Seq.:> (Assertion loc p msg) -> do
              p' <- symImplies solver c p
              case asConstantPred p' of
                Just True -> go prev new
                _ -> go (prev Seq.|> Assertion loc p' msg) new


instance IsPred (BoolElt s) where
  asConstantPred x =
    case x of
      SCApp SCTrue  -> Just True
      SCApp SCFalse -> Just False
      SCApp (SC_BoolNot a) -> not <$> asConstantPred a
      SC _ t -> SC.asBool t

instance IsNat (Elt s BaseNatType) where
  asNat (SCApp (SCNat n)) = Just n
  asNat _         = Nothing

instance IsInteger (Elt s BaseIntegerType) where
  asInteger (SCApp (SCInt i)) = Just i
  asInteger _         = Nothing

instance IsRational (Elt s BaseRealType) where
  asRational (SCApp (SCReal r)) = Just r
  asRational _          = Nothing

instance IsCplx (Elt s BaseComplexType) where
  asComplex (SCApp (SCCplx (r :+ i))) = pure (:+) <*> asRational r <*> asRational i
  asComplex _          = Nothing

instance IsBV (Elt s) where
  bvWidth = toBVWidth

  asUnsignedBV (SCApp (SCBV _ x)) = Just x
  asUnsignedBV _          = Nothing

  asSignedBV (SCApp (SCBV w x)) = Just $ toSigned w x
  asSignedBV _          = Nothing

--instance HasFloat (SymExpr (SAWCoreBackend s)) where
--  asFloat _ _ = Nothing -- FIXME

instance HasProgramLoc (SAWCoreSymPathState s) where
  setProgramLoc loc ps = ps{ pathProgLoc = loc }

instance IsBoolExprBuilder (SAWCoreBackend s) where
  truePred  _ = SCApp SCTrue
  falsePred _ = SCApp SCFalse

  notPred _ (SCApp (SC_BoolNot x)) = return $ x
  notPred _ x
     | Just True  <- asConstantPred x = return $ SCApp $ SCFalse
     | Just False <- asConstantPred x = return $ SCApp $ SCTrue
     | otherwise = return $ SCApp $ SC_BoolNot x

  andPred sc (SCApp (SC_BoolNot x)) (SCApp (SC_BoolNot y)) = notPred sc =<< orPred sc x y
  andPred sc x y
     | Just True  <- asConstantPred x = return y
     | Just False <- asConstantPred x = return $ SCApp SCFalse
     | Just True  <- asConstantPred y = return x
     | Just False <- asConstantPred y = return $ SCApp SCFalse
     | otherwise = do
         x' <- toSC sc x
         y' <- toSC sc y
         SC baseTypeRepr <$> SC.scAnd (saw_ctx sc) x' y'

  orPred sc (SCApp (SC_BoolNot x)) (SCApp (SC_BoolNot y)) = notPred sc =<< andPred sc x y
  orPred sc x y
     | Just False <- asConstantPred x = return y
     | Just True  <- asConstantPred x = return $ SCApp SCTrue
     | Just False <- asConstantPred y = return x
     | Just True  <- asConstantPred y = return $ SCApp SCTrue
     | otherwise = do
         x' <- toSC sc x
         y' <- toSC sc y
         SC baseTypeRepr <$> SC.scOr (saw_ctx sc) x' y'

  xorPred sc (SCApp (SC_BoolNot x)) y = eqPred sc x y
  xorPred sc x (SCApp (SC_BoolNot y)) = eqPred sc x y
  xorPred sc x y
     | Just True  <- asConstantPred x = notPred sc y
     | Just False <- asConstantPred x = return y
     | Just True  <- asConstantPred y = notPred sc x
     | Just False <- asConstantPred y = return x
     | x == y = return $ SCApp $ SCFalse
     | otherwise = do
         x' <- toSC sc x
         y' <- toSC sc y
         SC baseTypeRepr <$> SC.scXor (saw_ctx sc) x' y'

  eqPred sc (SCApp (SC_BoolNot x)) y = xorPred sc x y
  eqPred sc x (SCApp (SC_BoolNot y)) = xorPred sc x y
  eqPred sc x y
     | Just True  <- asConstantPred x = return y
     | Just False <- asConstantPred x = notPred sc y
     | Just True  <- asConstantPred y = return x
     | Just False <- asConstantPred y = notPred sc x
     | x == y = return $ SCApp $ SCTrue
     | otherwise = do
         x' <- toSC sc x
         y' <- toSC sc y
         SC baseTypeRepr <$> SC.scBoolEq (saw_ctx sc) x' y'

  itePred sc (SCApp (SC_BoolNot c)) x y      = itePred sc c y x
  itePred sc c (SCApp (SC_BoolNot x)) (SCApp (SC_BoolNot y)) = notPred sc =<< itePred sc c x y
  itePred sc x y z
     | Just True  <- asConstantPred x = return y
     | Just False <- asConstantPred x = return z
     | Just True  <- asConstantPred y = orPred sc x z
     | Just False <- asConstantPred y = notPred sc x >>= \x' -> andPred sc x' z
     | Just True  <- asConstantPred z = notPred sc x >>= \x' -> orPred sc x' y
     | Just False <- asConstantPred z = andPred sc x y
     | otherwise = do
         do boolty <- SC.scBoolType (saw_ctx sc)
            x' <- toSC sc x
            y' <- toSC sc y
            z' <- toSC sc z
            SC baseTypeRepr <$> SC.scIte (saw_ctx sc) boolty x' y' z'

instance IsBoolSolver (SAWCoreBackend s) (BoolElt s) where
  getCurrentState sc = readIORef (saw_pathstate sc)
  resetCurrentState sc s = do
    writeIORef (saw_pathstate sc) s
  switchCurrentState sc _ s = do
    writeIORef (saw_pathstate sc) s

  getCurrentProgramLoc sc = pathProgLoc <$> getCurrentState sc
  setCurrentProgramLoc sc l =
    modifyIORef' (saw_pathstate sc) (setProgramLoc l)

  mergeState sc true_pred true_ps false_ps = do
    cur_ps <- getCurrentState sc
    let pre_cnt = Seq.length (assertions cur_ps)
    let pre_aseq = assertions cur_ps
        cur_aseq = Seq.drop pre_cnt $ assertions true_ps
        neg_aseq = Seq.drop pre_cnt $ assertions false_ps

    false_pred <- notPred sc true_pred

    t_aseq <- impliesAssert sc true_pred  cur_aseq
    f_aseq <- impliesAssert sc false_pred neg_aseq
    let new_aseq = pre_aseq Seq.>< t_aseq Seq.>< f_aseq
    let new_ps = true_ps{ assertions = new_aseq }
    writeIORef (saw_pathstate sc) new_ps

  evalBranch _sc p =
    return $!
      case asConstantPred p of
        Just b  -> NoBranch b
        Nothing -> SymbolicBranch True

  addAssertion sc p msg = do
    case asConstantPred p of
      Just True  -> return ()
      Just False -> liftIO $ do
           loc <- getCurrentProgramLoc sc
           throw (SimError loc msg)
      Nothing -> liftIO $ do
           loc <- getCurrentProgramLoc sc
           modifyIORef (saw_pathstate sc)
              (\ps -> ps{ assertions = assertions ps Seq.|> Assertion loc p msg })

  getAssertionPred sc = do
    ps <- fmap (view assertPred) <$> getAssertions sc
    foldrM (andPred sc) (SCApp SCTrue) ps


-- | Create a new symbolic variable.
sawCreateVar :: SAWCoreBackend s
             -> String                                       -- ^ the name of the variable
             -> SC.SharedTerm s
             -> IO (SC.SharedTerm s)
sawCreateVar sc nm tp = do
     i <- SC.scFreshGlobalVar (saw_ctx sc)
     let ec = SC.EC i ("var_"++nm++"_"++show i) tp
     t <- SC.scFlatTermF (saw_ctx sc) (SC.ExtCns ec)
     modifyIORef (saw_inputs sc) (\xs -> xs Seq.|> ec)
     return t

instance IsExprBuilder (SAWCoreBackend s) where
  -- FIXME, do we need real implementations of these?
  stopCaching _ = return ()
  restartCaching _ = return ()

  printSymExpr sc x = SC.scPrettyTermDoc <$> toSC sc x

  -- Nat operations.

  natLit _ n = return $ SCApp $ SCNat n

  natAdd _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $ SCApp $ SCNat (x+y)
  natAdd sc x y = do
      t <- join $ pure (SC.scAddNat (saw_ctx sc)) <*> toSC sc x <*> toSC sc y
      return (SC baseTypeRepr t)

  natIte _ (SCApp SCTrue) x _ = return x
  natIte _ (SCApp SCFalse) _ y = return y
  natIte sc (SCApp (SC_BoolNot c)) x y = natIte sc c y x
  natIte _ _ x y | x == y = return x
  natIte sc c x y = do
      natty <- SC.scNatType (saw_ctx sc)
      c' <- toSC sc c
      x' <- toSC sc x
      y' <- toSC sc y
      SC baseTypeRepr <$> SC.scIte (saw_ctx sc) natty c' x' y'

  natSub _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $! SCApp $! SCNat (x-y)
  natSub sc x y = do
      t <- join $ pure (SC.scSubNat (saw_ctx sc)) <*> toSC sc x <*> toSC sc y
      return (SC baseTypeRepr t)

  natMul _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $! SCApp $! SCNat (x*y)
  natMul sc x y = do
      t <- join $ pure (SC.scMulNat (saw_ctx sc)) <*> toSC sc x <*> toSC sc y
      return (SC baseTypeRepr t)

  natEq _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $! SCApp $! if x == y then SCTrue else SCFalse
  natEq sc x y = do
      t <- join $ pure (SC.scEqualNat (saw_ctx sc)) <*> toSC sc x <*> toSC sc y
      return (SC baseTypeRepr t)

  natLe _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $! SCApp $! if x <= y then SCTrue else SCFalse
  natLe sc x y = do
       x' <- toSC sc x
       y' <- toSC sc y
       mn <- SC.scMinNat (saw_ctx sc) x' y'
       SC baseTypeRepr <$> SC.scEqualNat (saw_ctx sc) x' mn

  natLt _ (SCApp (SCNat x)) (SCApp (SCNat y)) = return $! SCApp $! if x < y then SCTrue else SCFalse
  natLt sc x y = do
      t <- join $ pure (SC.scLtNat (saw_ctx sc)) <*> toSC sc x <*> toSC sc y
      return (SC baseTypeRepr t)

  -- integer operations
  intLit _ i = return $ SCApp $ SCInt i

  intAdd _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $ SCApp $ SCInt (x+y)
  intAdd sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntAdd (saw_ctx sc) x' y'

  intSub _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $ SCApp $ SCInt (x-y)
  intSub sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntSub (saw_ctx sc) x' y'

  intMul _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $ SCApp $ SCInt (x*y)
  intMul sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntMul (saw_ctx sc) x' y'

  intNeg _ (SCApp (SCInt x)) = return $ SCApp $ SCInt (-x)
  intNeg sc x = do
     x' <- toSC sc x
     SC baseTypeRepr <$> SC.scIntNeg (saw_ctx sc) x'

  intMod _ (SCApp (SCInt x)) (SCApp (SCNat y)) = return $ SCApp $ SCNat $ fromIntegral (x `mod` toInteger y)
  intMod sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntMod (saw_ctx sc) x' y'

  intIte _ (SCApp SCTrue) x _  = return x
  intIte _ (SCApp SCFalse) _ y = return y
  intIte _ _ x y | x == y = return x
  intIte sc c x y = do
     c' <- toSC sc c
     tp <- SC.scDataTypeApp (saw_ctx sc) "Prelude.Integer" []
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIte (saw_ctx sc) tp c' x' y'

  intEq _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $! SCApp $! if x == y then SCTrue else SCFalse
  intEq sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntEq (saw_ctx sc) x' y'

  intLe _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $! SCApp $! if x <= y then SCTrue else SCFalse
  intLe sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntLe (saw_ctx sc) x' y'

  intLt _ (SCApp (SCInt x)) (SCApp (SCInt y)) = return $! SCApp $! if x < y then SCTrue else SCFalse
  intLt sc x y = do
     x' <- toSC sc x
     y' <- toSC sc y
     SC baseTypeRepr <$> SC.scIntLt (saw_ctx sc) x' y'


  -- bitvector operations
  bvLit _ w x = return $ SCApp $ SCBV w $ toUnsigned w x

  testBitBV _ i (SCApp (SCBV _ x)) = return $ SCApp $ if Bits.testBit x (fromIntegral i) then SCTrue else SCFalse
  testBitBV sc i x = do
      let w = bvWidth x
      x' <- toSC sc x
      w' <- SC.scNat (saw_ctx sc) (fromIntegral (widthVal w))
      bty <- SC.scBoolType (saw_ctx sc)
      i' <- SC.scNat (saw_ctx sc) (fromIntegral i)
      SC baseTypeRepr <$> SC.scAt (saw_ctx sc) w' bty i' x'

  bvIte _ (SCApp SCTrue) x _ = return x
  bvIte _ (SCApp SCFalse) _ y = return y
  bvIte sc (SCApp (SC_BoolNot c)) x y = bvIte sc c y x
  bvIte sc c (SCApp (SC_BoolToBV w x)) (SCApp (SC_BoolToBV _ y)) = SCApp . SC_BoolToBV w <$> itePred sc c x y
  bvIte _ _ x y | x == y = return x
  bvIte sc c x y = do
      let w = bvWidth x
      ty <- SC.scBitvector (saw_ctx sc) (fromIntegral (widthVal w))
      c' <- toSC sc c
      x' <- toSC sc x
      y' <- toSC sc y
      SC (BaseBVRepr w) <$> SC.scIte (saw_ctx sc) ty c' x' y'

  bvEq _ (SCApp (SCBV _ x)) (SCApp (SCBV _ y)) = return $! SCApp $! if x == y then SCTrue else SCFalse
  bvEq sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvEq (saw_ctx sc) n x' y'

  bvUlt _ (SCApp (SCBV _ x)) (SCApp (SCBV _ y)) = return $! SCApp $! if x < y then SCTrue else SCFalse
  bvUlt sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvULt (saw_ctx sc) n x' y'

  bvUle _ (SCApp (SCBV _ x)) (SCApp (SCBV _ y)) = return $! SCApp $! if x <= y then SCTrue else SCFalse
  bvUle sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvULe (saw_ctx sc) n x' y'

  bvUgt _ (SCApp (SCBV _ x)) (SCApp (SCBV _ y)) = return $! SCApp $! if x > y then SCTrue else SCFalse
  bvUgt sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvUGt (saw_ctx sc) n x' y'

  bvUge _ (SCApp (SCBV _ x)) (SCApp (SCBV _ y)) = return $! SCApp $! if x >= y then SCTrue else SCFalse
  bvUge sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvUGe (saw_ctx sc) n x' y'

  bvSlt _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $! SCApp $!
         if toSigned w x < toSigned w y then SCTrue else SCFalse
  bvSlt sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvSLt (saw_ctx sc) n x' y'

  bvSle _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $! SCApp $!
         if toSigned w x <= toSigned w y then SCTrue else SCFalse
  bvSle sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvSLe (saw_ctx sc) n x' y'

  bvSgt _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $! SCApp $!
         if toSigned w x > toSigned w y then SCTrue else SCFalse
  bvSgt sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvSGt (saw_ctx sc) n x' y'

  bvSge _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $! SCApp $!
         if toSigned w x >= toSigned w y then SCTrue else SCFalse
  bvSge sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       SC baseTypeRepr <$> SC.scBvSGe (saw_ctx sc) n x' y'

  bvShl _ (SCApp (SCBV w x)) (SCApp (SCBV _ i)) =
       return $ SCApp $! SCBV w $ toUnsigned w $ Bits.shiftL x (fromIntegral i)
  bvShl sc x (SCApp (SCBV _ y)) = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral y))
       SC (BaseBVRepr w) <$> SC.scBvShl (saw_ctx sc) n x' y'
  bvShl sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       y'' <- SC.scGlobalApply (saw_ctx sc) "Prelude.bvToNat" [n, y']
       SC (BaseBVRepr w) <$> SC.scBvShl (saw_ctx sc) n x' y''

  bvLshr _ (SCApp (SCBV w x)) (SCApp (SCBV _ i)) =
       return $ SCApp $! SCBV w $ toUnsigned w $ Bits.shiftR x (fromIntegral i)
  bvLshr sc x (SCApp (SCBV _ y)) = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral y))
       SC (BaseBVRepr w) <$> SC.scBvShr (saw_ctx sc) n x' y'
  bvLshr sc x y = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- toSC sc y
       y'' <- SC.scGlobalApply (saw_ctx sc) "Prelude.bvToNat" [n, y']
       SC (BaseBVRepr w) <$> SC.scBvShr (saw_ctx sc) n x' y''

  bvAshr _ (SCApp (SCBV w x)) (SCApp (SCBV _ i)) =
       return $ SCApp $! SCBV w $ toUnsigned w $ Bits.shiftR (toSigned w x) (fromIntegral i)
  bvAshr sc x (SCApp (SCBV _ y)) = do
       let w = bvWidth x
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
       x' <- toSC sc x
       y' <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral y))
       SC (BaseBVRepr w) <$> SC.scBvSShr (saw_ctx sc) n x' y'
  bvAshr sc x y = do
       let w = bvWidth x
       -- NB: width - 1 to make SAWCore types work out
       n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w) - 1))
       x' <- toSC sc x
       y' <- toSC sc y
       y'' <- SC.scGlobalApply (saw_ctx sc) "Prelude.bvToNat" [n, y']
       SC (BaseBVRepr w) <$> SC.scBvSShr (saw_ctx sc) n x' y''

  bvZext _ w' (SCApp (SCBV _ x))
     | Just LeqProof <- testLeq (knownNat :: NatRepr 1) w' = return $ SCApp $ SCBV w' $ toUnsigned w' x
  bvZext _ w' (SCApp (SC_BVZext _ x)) = do
      Just LeqProof <- return $ testLeq (incNat (bvWidth x)) w'
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w'
      return $ SCApp $ SC_BVZext w' x
  bvZext _ w' x = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w'
      return $ SCApp $ SC_BVZext w' x

  bvSext _ w' (SCApp (SCBV w x))
     | Just LeqProof <- testLeq (knownNat :: NatRepr 1) w' =
           return $ SCApp $ SCBV w' $ toUnsigned w' $ toSigned w x
  bvSext _ w' (SCApp (SC_BVSext _ x)) = do
      Just LeqProof <- return $ testLeq (incNat (bvWidth x)) w'
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w'
      return $ SCApp $ SC_BVSext w' x
  bvSext _ w' x = do
      Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w'
      return $ SCApp $ SC_BVSext w' x

  predToBV _ x w = return $ SCApp $ SC_BoolToBV w x

  bvConcat _ (SCApp (SCBV w1 x)) (SCApp (SCBV w2 y)) = do
       let w' = addNat w1 w2
       -- dynamic check; must succeed, but GHC can't figure it out
       Just LeqProof <- return $ isPosNat w'
       let shft :: Int
           shft =  fromIntegral (natValue w2)
       return $ SCApp $ SCBV w' $ toUnsigned w' $ (x `Bits.shiftL` shft) Bits..|. y

  -- reassociate to combine constants where possible
  bvConcat sc (SCApp (SCBV w1 x)) (SCApp (SC_BVConcat _ (SCApp (SCBV w2 y)) z))
     | Just Refl <- testEquality (addNat w1 (addNat w2 (bvWidth z)))
                        (addNat (addNat w1 w2) (bvWidth z))
        , Just LeqProof <- isPosNat (addNat w1 w2) = do
            let shft :: Int
                shft =  fromIntegral (natValue w2)
            bvConcat sc (SCApp (SCBV (addNat w1 w2) ((x `Bits.shiftL` shft) Bits..|. y))) z

  -- concat of two adjacent selects is a larger select
  bvConcat sc (SCApp (SC_BVSelect idx1 n1 x)) (SCApp (SC_BVSelect idx2 n2 y))
     | Just Refl <- testEquality idx1 (addNat idx2 n2)
     , Just LeqProof <- isPosNat (addNat n1 n2)
     , Just LeqProof <- testLeq (addNat idx2 (addNat n1 n2)) (bvWidth x)
     , Just Refl <- testEquality x y =
          bvSelect sc idx2 (addNat n1 n2) x

  -- always reassociate to the right
  bvConcat sc (SCApp (SC_BVConcat _ x y)) z
     | Just Refl <- testEquality (addNat (bvWidth x) (addNat (bvWidth y) (bvWidth z)))
                              (addNat (addNat (bvWidth x) (bvWidth y)) (bvWidth z))
     , Just LeqProof <- isPosNat (addNat (bvWidth y) (bvWidth z)) = do
          yz <- bvConcat sc y z
          bvConcat sc x yz

  -- no special case, just emit a concat
  bvConcat _sc x y = do
       let w' = addNat (bvWidth x) (bvWidth y)
       Just LeqProof <- return $ testLeq (knownNat :: NatRepr 1) w'
       return $ SCApp $ SC_BVConcat w' x y


  -- select on a constant
  bvSelect _ start num (SCApp (SCBV _ x)) = do
      let z = toUnsigned num (x `Bits.shiftR` (fromIntegral (widthVal start)))
      return $ SCApp $ SCBV num z

  -- Select of the entire width of a bitvector is the identity function
  bvSelect _sc start num x
     | Just _ <- testEquality start (knownNat :: NatRepr 0)
     , Just Refl <- testEquality num (bvWidth x) =
         return x

  -- nested selects can be collapsed
  bvSelect sc start num (SCApp (SC_BVSelect start' _ b))
     | let start'' = addNat start start'
     , Just LeqProof <- testLeq (addNat start'' num) (bvWidth b) =
         bvSelect sc start'' num b

  -- select from a sign extension; decompose into a concat
  bvSelect sc start num (SCApp (SC_BVSext w x)) = do
    -- Add dynamic check
    Just LeqProof <- return $ testLeq (bvWidth x) w
    let ext = subNat w (bvWidth x)
    -- Add dynamic check
    Just LeqProof <- return $ isPosNat w
    Just LeqProof <- return $ isPosNat ext
    zeros <- minUnsignedBV sc ext
    ones  <- maxUnsignedBV sc ext
    c     <- bvIsNeg sc x
    hi    <- bvIte sc c ones zeros
    x'    <- bvConcat sc hi x
    -- Add dynamic check
    Just LeqProof <- return $ testLeq (addNat start num) (addNat ext (bvWidth x))
    bvSelect sc start num x'

  -- select from a zero extension; decompose into a concat
  bvSelect sc start num (SCApp (SC_BVZext w x)) = do
    -- Add dynamic check
    Just LeqProof <- return $ testLeq (bvWidth x) w
    let ext = subNat w (bvWidth x)
    Just LeqProof <- return $ isPosNat w
    Just LeqProof <- return $ isPosNat ext
    hi    <- bvLit sc ext 0
    x'    <- bvConcat sc hi x
    -- Add dynamic check
    Just LeqProof <- return $ testLeq (addNat start num) (addNat ext (bvWidth x))
    bvSelect sc start num x'

  -- select in the less-significant bits of a concat
  bvSelect sc start num (SCApp (SC_BVConcat _uv _a b))
     | Just LeqProof <- testLeq (addNat start num) (bvWidth b) = do
         bvSelect sc start num b

  -- select in the more-significant bits of a concat
  bvSelect sc start num (SCApp (SC_BVConcat _uv a b))
     | Just LeqProof <- testLeq (bvWidth b) start
     , Just LeqProof <- isPosNat start
     , let diff = subNat start (bvWidth b)
     , Just LeqProof <- testLeq (addNat diff num) (bvWidth a) = do
         bvSelect sc (subNat start (bvWidth b)) num a

   -- when the selected region overlaps a concat boundary we have:
   --  select idx n (concat a b) =
   --      concat (select 0 n1 a) (select idx n2 b)
   --   where n1 + n2 = n and idx + n2 = width b
   --
   -- NB: this case must appear after the two above that check for selects
   --     entirely within the first or second arguments of a concat, otherwise
   --     some of the arithmetic checks below may fail
  bvSelect sc start num (SCApp (SC_BVConcat _uv a b)) = do
     Just LeqProof <- return $ testLeq start (bvWidth b)
     let n2 = subNat (bvWidth b) start
     Just LeqProof <- return $ testLeq n2 num
     let n1 = subNat num n2
     let z  = knownNat :: NatRepr 0

     Just LeqProof <- return $ isPosNat n1
     Just LeqProof <- return $ testLeq (addNat z n1) (bvWidth a)
     a' <- bvSelect sc z n1 a

     Just LeqProof <- return $ isPosNat n2
     Just LeqProof <- return $ testLeq (addNat start n2) (bvWidth b)
     b' <- bvSelect sc start n2 b

     Just Refl <- return $ testEquality (addNat n1 n2) num
     bvConcat sc a' b'

  -- no special case, just emit a select
  bvSelect _sc start num x =
     return $ SCApp $ SC_BVSelect start num x

  bvIsNonzero _ (SCApp (SC_BoolToBV _ x)) = return x
  bvIsNonzero _ (SCApp (SCBV _ x)) = return $ SCApp $ if x /= 0 then SCTrue else SCFalse
  bvIsNonzero sc x = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     SC baseTypeRepr <$> SC.scBvNonzero (saw_ctx sc) n x'

  bvTrunc _ w' (SCApp (SCBV _ x)) = return $ SCApp $ SCBV w' $ toUnsigned w' x
  bvTrunc _sc w' x = do
     -- dynamic check; must succeed, but GHC can't figure it out
     Just LeqProof <- return $ testLeq w' (bvWidth x)
     return $ SCApp $ SC_BVSelect (knownNat :: NatRepr 0) w' x

  bvAndBits _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w (x Bits..&. y)
  bvAndBits sc (SCApp (SC_BoolToBV w x)) (SCApp (SC_BoolToBV _ y)) = SCApp . SC_BoolToBV w <$> andPred sc x y
  bvAndBits sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvAnd (saw_ctx sc) n x' y'

  bvOrBits _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w (x Bits..|. y)
  bvOrBits sc (SCApp (SC_BoolToBV w x)) (SCApp (SC_BoolToBV _ y))  = SCApp . SC_BoolToBV w <$> orPred sc x y
  bvOrBits sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvOr (saw_ctx sc) n x' y'

  bvXorBits _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w (x `Bits.xor` y)
  bvXorBits sc (SCApp (SC_BoolToBV w x)) (SCApp (SC_BoolToBV _ y)) = SCApp . SC_BoolToBV w <$> xorPred sc x y
  -- special case for the self-XOR trick
  bvXorBits sc x y | x == y = bvLit sc (bvWidth x) 0
  bvXorBits sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvXor (saw_ctx sc) n x' y'

  bvNotBits _ (SCApp (SCBV w x)) = return $ SCApp $ SCBV w $ toUnsigned w $ (Bits.complement x)
  bvNotBits sc (SCApp (SC_BoolToBV w x))
     | widthVal w == 1 = SCApp . SC_BoolToBV w <$> notPred sc x
  bvNotBits sc x = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     SC (BaseBVRepr w) <$> SC.scBvNot (saw_ctx sc) n x'

  bvNeg _ (SCApp (SCBV w x)) = return $ SCApp $ SCBV w $ toUnsigned w $ - (toSigned w x)
  bvNeg sc x = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     SC (BaseBVRepr w) <$> SC.scBvNeg (saw_ctx sc) n x'

  bvAdd _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $ toUnsigned w (x + y)
  bvAdd sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvAdd (saw_ctx sc) n x' y'

  bvSub _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $ toUnsigned w (x - y)
  bvSub sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvSub (saw_ctx sc) n x' y'

  bvMul _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $ toUnsigned w (x * y)
  bvMul sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvMul (saw_ctx sc) n x' y'

  bvUdiv _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $ toUnsigned w (x `div` y)
  bvUdiv sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvUDiv (saw_ctx sc) n x' y'

  bvUrem _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $ toUnsigned w (x `rem` y)
  bvUrem sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvURem (saw_ctx sc) n x' y'

  bvSdiv _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $
        toUnsigned w $ (toSigned w x `div` toSigned w y)
  bvSdiv sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvSDiv (saw_ctx sc) n x' y'

  bvSrem _ (SCApp (SCBV w x)) (SCApp (SCBV _ y)) = return $ SCApp $ SCBV w $
        toUnsigned w $ (toSigned w x `rem` toSigned w y)
  bvSrem sc x y = do
     let w = bvWidth x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal w)))
     x' <- toSC sc x
     y' <- toSC sc y
     SC (BaseBVRepr w) <$> SC.scBvSRem (saw_ctx sc) n x' y'

  ----------------------------------------------------------------------
  -- WordMap operations

  -- -- FIXME, IntMap uses machine integers... and that's no good
  -- newtype WordMap (SAWCoreBackend s) w a =
  --    SAWWordMap (IntMap.IntMap (PartExpr (Pred (SAWCoreBackend s)) (SymExpr (SAWCoreBackend s) a)))

  -- emptyWordMap _sym _w _tp = return $ SAWWordMap $ IntMap.empty

  -- muxWordMap sym _w tp p (SAWWordMap m1) (SAWWordMap m2) =
  --          let mboth _ x          Unassigned = only1 x
  --              mboth _ Unassigned y          = only2 y
  --              mboth _ (PE xp x) (PE yp y)   = Just $ do
  --                      xyp <- itePred sym p xp yp
  --                      xy  <- baseTypeIte tp sym p x y
  --                      return $ PE xyp xy

  --              only1 Unassigned = Nothing
  --              only1 (PE xp x) = Just $ do
  --                      xp' <- andPred sym p xp
  --                      return $ PE xp' x

  --              only2 Unassigned = Nothing
  --              only2 (PE yp y) = Just $ do
  --                      np <- notPred sym p
  --                      yp' <- andPred sym np yp
  --                      return $ PE yp' y

  --              intmerge = IntMap.mergeWithKey mboth (IntMap.mapMaybe only1) (IntMap.mapMaybe only2) m1 m2

  --           in SAWWordMap <$> traverse id intmerge

  -- insertWordMap sym _w _tp bv a (SAWWordMap m)
  --     | Just x <- asUnsignedBV bv =
  --           return $ SAWWordMap $ IntMap.insert (fromInteger x) (PE (truePred sym) a) m
  -- insertWordMap _ _ _ _ _ _ = fail "SimpleBuilder word map indices must be concrete in insertWordMap"

  -- lookupWordMap _sym _w _tp bv (SAWWordMap m)
  --     | Just x <- asUnsignedBV bv = return $ joinMaybePE $ IntMap.lookup (fromInteger x) m
  -- lookupWordMap _ _ _ _ _ = fail "SimpleBuilder word map indices must be concrete in lookupWordMap"

  data WordMap (SAWCoreBackend s) w tp =
     SAWWordMap (SymArray (SAWCoreBackend s) (BaseBVType w) BaseBoolType)
                (SymArray (SAWCoreBackend s) (BaseBVType w) tp)

  emptyWordMap sym w tp = do
     bs <- constantArray sym (BVIndexRepr w) (falsePred sym)
     xs <- baseDefaultValue sym (BaseArrayRepr (BVIndexRepr w) tp)
     return $ SAWWordMap bs xs

  muxWordMap sym _w _tp p (SAWWordMap bs1 xs1) (SAWWordMap bs2 xs2) = do
     bs' <- arrayIte sym p bs1 bs2
     xs' <- arrayIte sym p xs1 xs2
     return $ SAWWordMap bs' xs'

  insertWordMap sym w tp idx v (SAWWordMap bs xs) = do
     bs' <- updateArray sym (BVIndexRepr w) BaseBoolRepr bs idx (truePred sym)
     xs' <- updateArray sym (BVIndexRepr w) tp xs idx v
     return $ SAWWordMap bs' xs'

  lookupWordMap sym _w _tp idx (SAWWordMap bs xs) = do
     p <- lookupArray sym bs idx
     case asConstantPred p of
        Just False -> return Unassigned
        _ -> PE p <$> lookupArray sym xs idx


  ----------------------------------------------------------------------
  -- Symbolic Arrays

  arrayIte sc p (SCArrayElt dom range e1) (SCArrayElt _ _ e2) = do
     r <- withAbstractable dom $ withAbstractable range $
       muxArrayElts' sc dom
         (mkArrayElt sc)
         (\a i    -> do
             a' <- toSC sc a
             i' <- toSC sc i
             SC range <$> SC.scApply (saw_ctx sc) a' i')
         (\p' x y -> do
             domTy   <- baseSCType (saw_ctx sc) dom
             rangeTy <- baseSCType (saw_ctx sc) range
             ty <- SC.scFun (saw_ctx sc) domTy rangeTy
             p'' <- toSC sc p'
             x' <- toSC sc x
             y' <- toSC sc y
             SC (BaseArrayRepr dom range) <$> SC.scIte (saw_ctx sc) ty p'' x' y')
         (baseTypeIte range sc)
         p
         e1
         e2
     return $! SCArrayElt dom range r

  arrayIte sc p (SCArrayElt dom range x) y = do
     r <- withAbstractable dom $ withAbstractable range $
         mkArrayElt sc =<< muxArrayApps' sc dom
         (\a i    -> do
             a' <- toSC sc a
             i' <- toSC sc i
             SC range <$> SC.scApply (saw_ctx sc) a' i')
         (\p' a b -> do
             domTy   <- baseSCType (saw_ctx sc) dom
             rangeTy <- baseSCType (saw_ctx sc) range
             ty <- SC.scFun (saw_ctx sc) domTy rangeTy
             p'' <- toSC sc p'
             a' <- toSC sc a
             b' <- toSC sc b
             SC (BaseArrayRepr dom range) <$> SC.scIte (saw_ctx sc) ty p'' a' b')
         (baseTypeIte range sc)
         p
         (arrayEltApp x)
         (newArrayApp y)
     return $! SCArrayElt dom range r

  arrayIte sc p x (SCArrayElt dom range y) = do
     r <- withAbstractable dom $ withAbstractable range $
         mkArrayElt sc =<< muxArrayApps' sc dom
         (\a i    -> do
             a' <- toSC sc a
             i' <- toSC sc i
             SC range <$> SC.scApply (saw_ctx sc) a' i')
         (\p' a b -> do
             domTy   <- baseSCType (saw_ctx sc) dom
             rangeTy <- baseSCType (saw_ctx sc) range
             ty <- SC.scFun (saw_ctx sc) domTy rangeTy
             p'' <- toSC sc p'
             a' <- toSC sc a
             b' <- toSC sc b
             SC (BaseArrayRepr dom range) <$> SC.scIte (saw_ctx sc) ty p'' a' b')
         (baseTypeIte range sc)
         p
         (newArrayApp x)
         (arrayEltApp y)
     return $! SCArrayElt dom range r

  arrayIte sc p x y =
     case eltType x of
       BaseArrayRepr dom range -> do
         domTy   <- baseSCType (saw_ctx sc) dom
         rangeTy <- baseSCType (saw_ctx sc) range
         ty <- SC.scFun (saw_ctx sc) domTy rangeTy
         p' <- toSC sc p
         x' <- toSC sc x
         y' <- toSC sc y
         SC (BaseArrayRepr dom range) <$> SC.scIte (saw_ctx sc) ty p' x' y'

  arrayEq _sc _x _y =
     fail "SAWCore backend does not support equality on arrays"

  arrayLit _sc _dom _range _v =
     fail "SAWCore backend does not support array literals FIXME"

  constantArray sc dom v = do
     ty <- baseSCType (saw_ctx sc) dom
     let range = eltType v
     v' <- SC.incVars (saw_ctx sc) 0 1 =<< toSC sc v
     SC (BaseArrayRepr dom range) <$> SC.scLambda (saw_ctx sc) "_" ty v'

  lookupArray sc e idx =
    case eltType e of
      BaseArrayRepr (dom :: IndexTypeRepr dom) range ->
        withAbstractable dom $ withAbstractable range $ do
        let mkSelect a i = do
              a' <- toSC sc a
              i' <- toSC sc i
              SC range <$> SC.scApply (saw_ctx sc) a' i'
        case e of
          SCArrayElt _ _ arr ->
            lookupArrayElt sc
                           (mkSelect e idx)
                           mkSelect
                           (\_ -> avTop dom)
                           dom
                           (arrayEltApp arr)
                           idx
          _ -> mkSelect e idx

  updateArray sc dom range e idx v =
    withAbstractable dom $ withAbstractable range $
    case e of
      SCArrayElt _ _ arr ->
        SCArrayElt dom range <$>
          mkArrayElt sc (updateArrayApp sc dom (arrayEltApp arr) idx v)
      _ ->
        SCArrayElt dom range <$>
          mkArrayElt sc (updateArrayApp sc dom (newArrayApp e) idx v)

  ----------------------------------------------------------------------
  -- Conversions

  natToInteger _ (SCApp (SCNat n)) = return $ SCApp $ SCInt (fromIntegral n)
  natToInteger sc x = do
     x' <- toSC sc x
     SC baseTypeRepr <$> SC.scNatToInt (saw_ctx sc) x'

  integerToNat _ (SCApp (SCInt i))
     | 0 <= i = return $ SCApp $ SCNat (fromInteger i)
     | otherwise = return $ SCApp $ SCNat 0
  integerToNat sc x = do
     x' <- toSC sc x
     SC baseTypeRepr <$> SC.scIntToNat (saw_ctx sc) x'

  bvToInteger _ (SCApp (SCBV _ x)) = return $ SCApp $ SCInt (fromIntegral x)
  bvToInteger sc x = do
     x' <- toSC sc x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal (bvWidth x))))
     SC baseTypeRepr <$> SC.scBvToInt (saw_ctx sc) n x'

  sbvToInteger _ (SCApp (SCBV w i))
    | i <= maxSigned w = return $ SCApp $ SCInt i
    | otherwise        = return $ SCApp $ SCInt (negate i)
  sbvToInteger sc x = do
     x' <- toSC sc x
     n <- SC.scNat (saw_ctx sc) (SC.Nat (fromIntegral (widthVal (bvWidth x))))
     SC baseTypeRepr <$> SC.scSbvToInt (saw_ctx sc) n x'

  integerToBV _ (SCApp (SCInt i)) w
     | 0 <= i    = return $ SCApp $ SCBV w (min (maxSigned w) i)
     | otherwise = return $ SCApp $ SCBV w 0
  integerToBV sc x w = do
     x' <- toSC sc x
     tp <- SC.scBitvector (saw_ctx sc) (fromIntegral (widthVal w))
     zeroint <- SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) 0
     p <- SC.scIntLe (saw_ctx sc) zeroint x'
     maxbv <- SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) (fromIntegral (maxUnsigned w))
     ps <- SC.scIntMin (saw_ctx sc) x' maxbv
     SC (BaseBVRepr w) <$> SC.scIte (saw_ctx sc) tp p ps zeroint

  integerToSBV _ (SCApp (SCInt i)) w
     | 0 <= i    = return $ SCApp $ SCBV w (min (maxSigned w) i)
     | otherwise = return $ SCApp $ SCBV w (max (minSigned w) i)
  integerToSBV sc x w = do
     x' <- toSC sc x
     tp <- SC.scBitvector (saw_ctx sc) (fromIntegral (widthVal w))
     zeroint <- SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) 0
     p <- SC.scIntLe (saw_ctx sc) zeroint x'
     maxbv <- SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) (fromIntegral (maxSigned w))
     minbv <- SC.scNatToInt (saw_ctx sc) =<< SC.scNat (saw_ctx sc) (fromIntegral (minSigned w))
     ps <- SC.scIntMin (saw_ctx sc) x' maxbv
     neg <- SC.scIntMax (saw_ctx sc) x' minbv
     SC (BaseBVRepr w) <$> SC.scIte (saw_ctx sc) tp p ps neg

  realToNat _ (SCApp (SCReal r))
     | denominator r == 1 && numerator r >= 0 = return $ SCApp $ SCNat (fromInteger (numerator r))
     | otherwise = fail $ unwords ["cannot convert",show r,"into a natural number"]
  realToNat _ _ = fail "SAWCoreInterface: unsupported real passed to realToNat"

  realToInt _ (SCApp (SCReal r)) w' = return $ SCApp $ SCBV w' $ signedClamp w' $ roundAway r
  realToInt _ _ _ = fail "SAWCoreInterface: unsupported real passed to realToInt"

  realToUInt _ (SCApp (SCReal r)) w' = return $ SCApp $ SCBV w' $ unsignedClamp w' $ roundAway r
  realToUInt _ _ _ = fail "SAWCoreInterface: unsupported real passed to realToUInt"

  integerToReal _ (SCApp (SCInt i)) = return $ SCApp $ SCReal (fromIntegral i)
  integerToReal _ _ = fail "SAWCoreInterface: unsupported integer passed to integerToReal"

  natToReal _ (SCApp (SCNat n)) = return $ SCApp $ SCReal (fromIntegral n)
  natToReal _ _ = fail "SAWCoreInterface: unsupported nat passed to natToReal"

  ----------------------------------------------------------------------
  -- Real operations

  realLit _ r = return $ SCApp $ SCReal r

  realZero = return $ SCApp $ SCReal 0

  realEq _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $! SCApp $! if x == y then SCTrue else SCFalse
  realEq _ _ _ = fail "SAWCoreInterface: unsupported real value in eqReal"

  realLe _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $! SCApp $! if x <= y then SCTrue else SCFalse
  realLe _ _ _ = fail "SAWCoreInterface: unsupported real passed to leReal"

  realIte _ (SCApp SCTrue) x _  = return x
  realIte _ (SCApp SCFalse) _ y = return y
  realIte _ _ x y | x == y = return x
  realIte _ _ _ _ = fail "SAWCoreInterface: iteReal asked to mux reals based on a symbolic predicate"

  realNeg _ (SCApp (SCReal x)) = return $ SCApp $ SCReal (-x)
  realNeg _ _ = fail "SAWCoreInterface: unsupported real passed to realNeg"

  realAdd _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $ SCApp $ SCReal (x + y)
  realAdd _ _ _ = fail "SAWCoreInterface: unsupported real passed to addReal"

  realSub _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $ SCApp $ SCReal (x - y)
  realSub _ _ _ = fail "SAWCoreInterface: unsupported real passed to realSub"

  realMul _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $ SCApp $ SCReal (x * y)
  realMul _ _ _ = fail "SAWCoreInterface: unsupported real passed to realMul"

  realDiv _ (SCApp (SCReal x)) (SCApp (SCReal y)) = return $ SCApp $ SCReal (x / y)
  realDiv _ _ _ = fail "SAWCoreInterface: unsupported real passed to realDiv"

  realRound _ (SCApp (SCReal x)) = return $ SCApp $ SCInt (roundAway x)
  realRound _ _ = fail "SAWCoreInterface: unsupported real passed to realRoudn"

  realFloor _ (SCApp (SCReal x)) = return $ SCApp $ SCInt (floor x)
  realFloor _ _ = fail "SAWCoreInterface: unsupported real passed to realFloor"

  realCeil _ (SCApp (SCReal x)) = return $ SCApp $ SCInt (ceiling x)
  realCeil _ _ = fail "SAWCoreInterface: unsupported real passed to realCeil"

  isInteger _ (SCApp (SCReal r)) = return $! SCApp $ if denominator r == 1 then SCTrue else SCFalse
  isInteger _ _ = fail "SAWCoreInterface: unsupported real passed to isInteger"

  realSqrt _ _ = fail "SAWCoreInterface: square root not supported"

  realPi _ = fail "SAWCoreInterface: transendental functions not supported"
  realExp _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realLog _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realSin _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realCos _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realSinh _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realCosh _ _ = fail "SAWCoreInterface: transendental functions not supported"
  realAtan2 _ _ _ = fail "SAWCoreInterface: transendental functions not supported"

  ----------------------------------------------------------------------
  -- Cplx operations

  mkComplex _ c = return $ SCApp $ SCCplx c

  getRealPart _ (SCApp (SCCplx (r :+ _))) = return r
  getRealPart _ _ = fail "SAWCoreInterface: given unsupported complex value in getRealPart"

  getImagPart _ (SCApp (SCCplx (_ :+ i))) = return i
  getImagPart _ _ = fail "SAWCoreInterface: given unsupported complex value in getImagPart"

  coerceCplx _ (SCApp (SCCplx c)) = return c
  coerceCplx _ _ = fail "SAWCoreInterface: given unsupported complex value in coerceCplx"


instance IsSymInterface (SAWCoreBackend s) where
  freshConstant sc bt = do
     tp <- baseSCType (saw_ctx sc) bt
     SC bt <$> sawCreateVar sc "x" tp

  freshLatch = error "SAWCore backend does not support latches"


-- Dummy declaration splice to bring App into template haskell scope.
$(return [])


scappEq :: SCApp (Elt s) x -> SCApp (Elt s) y -> Maybe (x :~: y)
scappEq = $(structuralTypeEquality [t|SCApp|]
                 [ (TypeApp (ConType [t|NatRepr|]) AnyType, [|testEquality|])
                 , (TypeApp (ConType [t|IndexTypeRepr|]) AnyType, [|testEquality|])
                 , (TypeApp (ConType [t|BaseTypeRepr|]) AnyType, [|testEquality|])
                 , (TypeApp (DataArg 0) AnyType, [|testEquality|])
                 ]
           )

instance TestEquality (SCApp (Elt s)) where
  testEquality = scappEq
instance Eq (SCApp (Elt s) tp) where
  x == y = isJust (testEquality x y)


instance TestEquality (Elt s) where
  testEquality (SC tpx x) (SC tpy y) =
     case testEquality tpx tpy of
        Just Refl -> if x == y then Just Refl else Nothing
        Nothing   -> Nothing
  testEquality (SCApp x) (SCApp y) = testEquality x y
  testEquality _ _ = Nothing

instance Eq (Elt s tp) where
  x == y = isJust (testEquality x y)
