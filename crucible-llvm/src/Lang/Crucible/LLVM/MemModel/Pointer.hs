------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel
-- Description      : Representation of pointers in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.MemModel.Pointer where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.State.Strict
import           Data.Dynamic

import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import qualified Lang.Crucible.LLVM.MemModel.Common as G


type LLVMPtrExpr' sym = LLVMPtrExpr (SymExpr sym)
type PartLLVMVal sym w = PartExpr (Pred sym) (LLVMVal sym w)

-- | This provides a view of an address as a base + offset when possible.
data AddrDecomposeResult t
   = Symbolic t
   | ConcreteOffset t Integer
   | SymbolicOffset t t
  deriving (Show)

data LLVMPtrExpr e w
  = LLVMPtr (e BaseNatType)     --  Block number
            (e (BaseBVType w))  --  End-of-block offset (1 past end of valid bytes)
            (e (BaseBVType w))  --  Current offset in block
  | LLVMOffset (e (BaseBVType w))

-- NB, this is a somewhat strange Eq instance.  It is used by
-- the Generic memory model module to compare pointers that are
-- known to be concrete base pointers.
-- Thus, we simply assume that the given values are concrete and
-- have offset 0.  This essentially comes down to comparing the
-- allocation block numbers.
instance IsExpr e => Eq (LLVMPtrExpr e w) where
  LLVMPtr b1 _ _== LLVMPtr b2 _ _
    | Just blk1 <- asNat b1
    , Just blk2 <- asNat b2 = blk1 == blk2
         --Debug.trace (unwords ["Comparing blocks:",show blk1, show blk2]) $ blk1 == blk2
  _ == _ = False


instance (IsExpr e, OrdF e) => Ord (LLVMPtrExpr e w) where
  compare (LLVMPtr _ _ _) (LLVMOffset _) = LT
  compare (LLVMPtr b1 _ off1) (LLVMPtr b2 _ off2) =
    case compareF b1 b2 of
      LTF -> LT
      GTF -> GT
      EQF ->
        case compareF off1 off2 of
          LTF -> LT
          GTF -> GT
          EQF -> EQ
  compare (LLVMOffset _) (LLVMPtr _ _ _) = GT
  compare (LLVMOffset off1) (LLVMOffset off2) =
    case compareF off1 off2 of
      LTF -> LT
      GTF -> GT
      EQF -> EQ

data LLVMVal sym w where
  LLVMValPtr :: SymNat sym -> SymBV sym w -> SymBV sym w -> LLVMVal sym w
  LLVMValFunPtr :: CtxRepr args -> TypeRepr ret -> FnVal sym args ret -> LLVMVal sym w
  LLVMValInt :: (1 <= x) => NatRepr x -> SymBV sym x -> LLVMVal sym w
  LLVMValReal :: SymReal sym -> LLVMVal sym w
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym w) -> LLVMVal sym w
  LLVMValArray :: G.Type -> Vector (LLVMVal sym w) -> LLVMVal sym w


ptrConst :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> G.Size -> IO (LLVMPtrExpr' sym w)
ptrConst sym w x = LLVMOffset <$> bvLit sym w (fromIntegral x)

ptrDecompose :: (1 <= w, IsExprBuilder sym)
             => sym
             -> NatRepr w
             -> LLVMPtrExpr' sym w
             -> IO (AddrDecomposeResult (LLVMPtrExpr' sym w))
ptrDecompose sym w (LLVMPtr base@(asNat -> Just _) end (asUnsignedBV -> Just off)) =
  do z <- bvLit sym w 0
     return (ConcreteOffset (LLVMPtr base end z) off)
ptrDecompose sym w (LLVMPtr base@(asNat -> Just _) end off) =
  do z <- bvLit sym w 0
     return $ SymbolicOffset (LLVMPtr base end z) (LLVMOffset off)
ptrDecompose _sym _w p@(LLVMPtr _ _ _) =
  do return $ Symbolic p
ptrDecompose _ _ (LLVMOffset _) =
  do fail "Attempted to treat raw offset as pointer"

ptrSizeDecompose
  :: IsExprBuilder sym
  => sym
  -> NatRepr w
  -> LLVMPtrExpr' sym w
  -> IO (Maybe Integer)
ptrSizeDecompose _ _ (LLVMOffset (asUnsignedBV -> Just off)) =
  return (Just off)
ptrSizeDecompose _ _ _ = return Nothing


ptrEq :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtrExpr' sym w
      -> LLVMPtrExpr' sym w
      -> IO (Pred sym)
ptrEq sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do putStrLn "Executing ptrEq"
     p1 <- natEq sym base1 base2
     p2 <- bvEq sym off1 off2
     andPred sym p1 p2
ptrEq sym _w (LLVMOffset off1) (LLVMOffset off2) =
  do putStrLn "Executing ptrEq"
     bvEq sym off1 off2

-- Comparison of a pointer to the null pointer (offset 0) is allowed,
-- but all other direct ptr/offset comparisons are not allowed
ptrEq sym w (LLVMOffset off) (LLVMPtr _ _ _) =
  do putStrLn "Executing ptrEq"
     z <- bvLit sym w 0
     p <- bvEq sym off z
     addAssertion sym p (AssertFailureSimError "Invalid attempt to compare a pointer and a raw offset for equality")
     return (falsePred sym)
ptrEq sym w (LLVMPtr _ _ _) (LLVMOffset off) =
  do putStrLn "Executing ptrEq"
     z <- bvLit sym w 0
     p <- bvEq sym off z
     addAssertion sym p (AssertFailureSimError "Invalid attempt to compare a pointer and a raw offset for equality")
     return (falsePred sym)

ptrLe :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtrExpr' sym w
      -> LLVMPtrExpr' sym w
      -> IO (Pred sym)
ptrLe sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do putStrLn "Executing ptrLe"
     p1 <- natEq sym base1 base2
     addAssertion sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
     bvSle sym off1 off2
ptrLe sym _w (LLVMOffset off1) (LLVMOffset off2) =
  do putStrLn "Executing ptrLe"
     bvSle sym off1 off2
ptrLe _ _ _ _ =
  do fail "Invalid attempt to compare a pointer and a raw offset"


ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr' sym w
       -> LLVMPtrExpr' sym w
       -> IO (LLVMPtrExpr' sym w)
ptrAdd sym _w (LLVMPtr base end off1) (LLVMOffset off2) =
  do off' <- bvAdd sym off1 off2
     return $ LLVMPtr base end off'
ptrAdd sym _w (LLVMOffset off1) (LLVMPtr base end off2) =
  do off' <- bvAdd sym off1 off2
     return $ LLVMPtr base end off'
ptrAdd sym _w (LLVMOffset off1) (LLVMOffset off2) =
  do off' <- bvAdd sym off1 off2
     return $ LLVMOffset off'
ptrAdd _sym _w (LLVMPtr _ _ _) (LLVMPtr _ _ _) =
  do fail "Attempted to add to pointers"

ptrCheckedAdd
       :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr' sym w
       -> LLVMPtrExpr' sym w
       -> IO (Pred sym, LLVMPtrExpr' sym w)
ptrCheckedAdd sym w (LLVMPtr base end off1) (LLVMOffset off2) =
  do z <- bvLit sym w 0
     (p1, off') <- addSignedOF sym off1 off2
     p1' <- notPred sym p1
     p2 <- bvSle sym off' end
     p3 <- bvSle sym z off'
     p <- andPred sym p1' =<< andPred sym p2 p3
     return $ (p, LLVMPtr base end off')
ptrCheckedAdd sym w (LLVMOffset off1) (LLVMPtr base end off2) =
  do z <- bvLit sym w 0
     (p1, off') <- addSignedOF sym off1 off2
     p1' <- notPred sym p1
     p2 <- bvSle sym off' end
     p3 <- bvSle sym z off'
     p <- andPred sym p1' =<< andPred sym p2 p3
     return $ (p, LLVMPtr base end off')
ptrCheckedAdd sym _w (LLVMOffset off1) (LLVMOffset off2) =
  do (p, off') <- addSignedOF sym off1 off2
     p' <- notPred sym p
     return $ (p', LLVMOffset off')
ptrCheckedAdd _sym _w (LLVMPtr _ _ _) (LLVMPtr _ _ _) =
  do fail "Attempted to add to pointers"


ptrSub :: (1 <= w, IsSymInterface sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr' sym w
       -> LLVMPtrExpr' sym w
       -> IO (LLVMPtrExpr' sym w)
ptrSub sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) =
  do p <- natEq sym base1 base2
     addAssertion sym p (AssertFailureSimError "Attempted to subtract pointers from different allocations")
     diff <- bvSub sym off1 off2
     return (LLVMOffset diff)
ptrSub sym _w (LLVMOffset off1) (LLVMOffset off2) =
  do diff <- bvSub sym off1 off2
     return (LLVMOffset diff)
ptrSub _sym _w (LLVMOffset _) (LLVMPtr _ _ _) =
  do fail "Cannot substract pointer value from raw offset"
ptrSub sym _w (LLVMPtr base end off1) (LLVMOffset off2) =
  do diff <- bvSub sym off1 off2
     return (LLVMPtr base end diff)


applyCtorFLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ValueCtorF (PartLLVMVal sym w)
   -> IO (PartLLVMVal sym w)
applyCtorFLLVMVal sym _w ctor =
  case ctor of
    G.ConcatBV low_w  (PE p1 (LLVMValInt low_w' low))
               high_w (PE p2 (LLVMValInt high_w' high))
       | fromIntegral (low_w*8)  == natValue low_w' &&
         fromIntegral (high_w*8) == natValue high_w' ->
           do bv <- bvConcat sym high low
              Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
              p <- andPred sym p1 p2
              return $ PE p $ LLVMValInt (addNat high_w' low_w') bv
    G.ConsArray tp (PE p1 hd) n (PE p2 (LLVMValArray tp' vec))
       | tp == tp' && n == fromIntegral (V.length vec) ->
           do p <- andPred sym p1 p2
              return $ PE p $ LLVMValArray tp' (V.cons hd vec)
    G.AppendArray tp n1 (PE p1 (LLVMValArray tp1 v1)) n2 (PE p2 (LLVMValArray tp2 v2))
       | tp == tp1 && tp == tp2 &&
         n1 == fromIntegral (V.length v1) &&
         n2 == fromIntegral (V.length v2) ->
           do p <- andPred sym p1 p2
              return $ PE p $ LLVMValArray tp (v1 V.++ v2)
    G.MkArray tp vec ->
      do let f :: PartLLVMVal sym w -> StateT (Pred sym) (MaybeT IO) (LLVMVal sym w)
             f Unassigned = mzero
             f (PE p1 x) =
               do p0 <- get
                  p <- liftIO $ andPred sym p0 p1
                  put p
                  return x
         x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
         case x of
           Nothing -> return $ Unassigned
           Just (vec',p) -> return $ PE p $ LLVMValArray tp vec'

    G.MkStruct vec ->
      do let f :: (G.Field G.Type, PartLLVMVal sym w)
               -> StateT (Pred sym) (MaybeT IO) (G.Field G.Type, LLVMVal sym w)
             f (_fld, Unassigned) = mzero
             f (fld, PE p1 x) = do
                 p0 <- get
                 p <- liftIO $ andPred sym p0 p1
                 put p
                 return (fld, x)
         x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
         case x of
           Nothing -> return $ Unassigned
           Just (vec',p) -> return $ PE p $ LLVMValStruct vec'

    _ -> return $ Unassigned

    -- G.BVToFloat _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"
    -- G.BVToDouble _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"


applyViewFLLVMVal
   :: (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ViewF (PartLLVMVal sym w)
   -> IO (PartLLVMVal sym w)
applyViewFLLVMVal sym _wptr v =
  case v of
    G.SelectLowBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (fromIntegral low)
      , Just (Some (hi_w))  <- someNat (fromIntegral hi)
      , Just LeqProof <- isPosNat low_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      , Just LeqProof <- testLeq low_w w
      -> do
        bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
        return $ PE p $ LLVMValInt low_w bv'
    G.SelectHighBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (fromIntegral low)
      , Just (Some (hi_w))  <- someNat (fromIntegral hi)
      , Just LeqProof <- isPosNat hi_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      -> do
        bv' <- bvSelect sym low_w hi_w bv
        return $ PE p $ LLVMValInt hi_w bv'
    G.FloatToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.DoubleToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.ArrayElt sz tp idx (PE p (LLVMValArray tp' vec))
      | sz == fromIntegral (V.length vec)
      , 0 <= idx
      , idx < sz
      , tp == tp' ->
        return $ PE p $ (vec V.! fromIntegral idx)
    G.FieldVal flds idx (PE p (LLVMValStruct vec))
      | flds == fmap fst vec
      , 0 <= idx
      , idx < V.length vec ->
          return $ PE p $ snd $ (vec V.! idx)
    _ -> return Unassigned

muxLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> Pred sym
   -> PartLLVMVal sym w
   -> PartLLVMVal sym w
   -> IO (PartLLVMVal sym w)
muxLLVMVal sym _w p = mux
  where
    mux Unassigned Unassigned = return Unassigned
    mux Unassigned (PE p2 y)  = PE <$> (itePred sym p (falsePred sym) p2) <*> return y
    mux (PE p1 x) Unassigned  = PE <$> (itePred sym p p1 (falsePred sym)) <*> return x
    mux (PE p1 x) (PE p2 y) =
      do mz <- runMaybeT $ muxval x y
         case mz of
           Nothing -> return $ Unassigned
           Just z  -> PE <$> itePred sym p p1 p2 <*> return z

    muxval :: LLVMVal sym w -> LLVMVal sym w -> MaybeT IO (LLVMVal sym w)

    muxval (LLVMValPtr base1 end1 off1) (LLVMValPtr base2 end2 off2) =
      do base <- liftIO $ natIte sym p base1 base2
         end  <- liftIO $ bvIte sym p end1 end2
         off  <- liftIO $ bvIte sym p off1 off2
         return $ LLVMValPtr base end off

    muxval (LLVMValFunPtr args1 ret1 h1) (LLVMValFunPtr args2 ret2 h2)
      | Just Refl <- testEquality args1 args2
      , Just Refl <- testEquality ret1 ret2 =
        do h' <- liftIO $ muxHandle sym p h1 h2
           return $ LLVMValFunPtr args1 ret1 h'

    muxval (LLVMValReal x) (LLVMValReal y) =
      do z <- liftIO $ realIte sym p x y
         return $ LLVMValReal z

    muxval (LLVMValInt wx x) (LLVMValInt wy y)
      | Just Refl <- testEquality wx wy =
        do z <- liftIO $ bvIte sym p x y
           return $ LLVMValInt wx z

    muxval (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 = do
          fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval x y) fls1 fls2
          return $ LLVMValStruct fls

    muxval (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          v <- traverse id $ V.zipWith muxval v1 v2
          return $ LLVMValArray tp1 v

    muxval _ _ = mzero
