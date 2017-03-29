------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Evaluation
-- Description      : Provides functionality for simulating matlab instructions.
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides operations evaluating MATLAB expressions.
------------------------------------------------------------------------
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Simulator.Evaluation
  ( cplxArrayIsReal
  , cplxArrayAsPosNat
  , realArrayIsNonNeg
  , matlabIntArrayAsPosNat
  , matlabUIntArrayAsPosNat
  , logicArrayToIndices
  , evalApp
  , dimLit
  , asDimLit
  , resizeDimLit
  , failIfNothing
  , selectedIndices
  , asConstantIndex
  , setStructField
  , symDimAsVecN
  , symDimCount
  , symDimNull
  , symDimAt
  , indexSymbolic
  , mda_symbolic_lookup
  , mda_symbolic_update
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad
import qualified Data.Foldable as Fold
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Numeric ( showHex )

import qualified Lang.MATLAB.CharVector as CV
import           Lang.MATLAB.MatlabChar
import           Lang.MATLAB.MultiDimArray (ArrayDim, MultiDimArray)
import qualified Lang.MATLAB.MultiDimArray as MDA
import           Lang.MATLAB.Utils.Nat as Nat

import           Lang.Crucible.Core
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.MatlabValue
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Solver.Symbol (emptySymbol)
import           Lang.Crucible.Utils.Complex
import qualified Lang.Crucible.Utils.SymMultiDimArray as SMDA

------------------------------------------------------------------------
-- Utilities

-- | Call fail with the given message if the maybe value is nothing,
-- otherwise return the value.
failIfNothing :: Monad m => String -> Maybe a -> m a
failIfNothing msg Nothing = fail msg
failIfNothing _  (Just v) = return v

-- | Given a list of Booleans l, @selectedIndices@ returns the indices of
-- true values in @l@.
selectedIndices :: [Bool] -> [Nat]
selectedIndices l = catMaybes $ zipWith selectIndex l [1..]
  where selectIndex True i  = Just i
        selectIndex False _ = Nothing

------------------------------------------------------------------------
-- Evaluating expressions

-- | Add checks to confirm each argument is at least one.
checkAtLeast1 :: (IsExprBuilder sym, Traversable f) => sym -> f (SymNat sym) -> IO (Pred sym)
checkAtLeast1 sym s = do
  c0 <- natLit sym 0
  andAllOf sym folded =<< traverse (natLt sym c0) s

mkPE :: IsPred p => p -> a -> PartExpr p a
mkPE p v =
  case asConstantPred p of
    Just False -> Unassigned
    _ -> PE p v

asConstantIndex :: IsExpr e => V.Vector (e BaseNatType) -> Maybe MDA.Index
asConstantIndex v = MDA.indexFromVector <$> traverse asNat v

asDimLit :: (Monad m, IsExpr e)
         => V.Vector (e BaseNatType)
         -> m ArrayDim
asDimLit v =
  case traverse asNat v of
    Just vnat -> return $ MDA.fromDimList $ V.toList vnat
    Nothing -> fail "mss requires the dimensions are concrete."

resizeDimLit :: IsSymInterface sym
             => sym
             -> (Int -> String -> IO ())
                -- ^ Logging function
             -> ArrayDim
             -> V.Vector (SymNat sym)
             -> IO ArrayDim
resizeDimLit sym logFn d v = do
  case traverse asNat v of
    Just vnat -> return $ MDA.fromDimList $ V.toList vnat
    Nothing -> do
      let n = V.length v
      let bounds = MDA.asDimVectorN (fromIntegral n) d
      logFn 2 "Warning! A symbolic size was detected.  MSS does not currently support symbolic sizes."
      let go i b = do
            addAssertionM sym
                          (natLe sym i =<< natLit sym b)
                          (GenericSimError "Symbolic sizes must not grow array.")
      V.zipWithM_ go v bounds
      return d

type SymDim sym = V.Vector (SymNat sym)

symDimAsVecN :: IsExprBuilder sym
             => sym -- ^ Symbolic backend.
             -> SymDim sym -- ^ Vector of dimensions.
             -> Nat -- ^ Length of result vector
             -> IO (SymDim sym)
symDimAsVecN sym v (fromIntegral -> n)
    | l == n = return v
    | l < n  = do one <- natLit sym 1
                  return (v V.++ V.replicate (n-l) one)
    | True = do
      when (n == 0) $ fail "Cannot get 0 length vector from dimensions."
      -- TODO: Test this
      let unchanged_elts = V.take (n-1) v
          last_elt = v V.! (n-1)
          rest = V.drop n v
      new_last <- Fold.foldlM (natMul sym) last_elt rest
      return (unchanged_elts `V.snoc` new_last)
  where l = V.length v


symDimAt :: IsSymInterface sym
         => sym -- ^ Symbolic backend.
         -> SymDim sym -- ^ Vector of dimensions.
         -> Nat -- ^ Index to get at
         -> Nat -- ^ Length of vector

         -> IO (SymNat sym)
symDimAt sym v (fromIntegral -> i) (fromIntegral -> n)
    | i >= l = natLit sym 1
      -- Get last element in vector.
    | n < l && (i+1==n) = do
      let last_elt = v V.! i
          rest = V.drop (i+1) v
      new_last <- Fold.foldlM (natMul sym) last_elt rest
      return (new_last)
    | True = return (v V.! i)
  where l = V.length v

natIteM :: IsSymInterface sym
        => sym
        -> Pred sym
        -> IO (SymNat sym)
        -> IO (SymNat sym)
        -> IO (SymNat sym)
natIteM sym p tm fm = do
  case asConstantPred p of
    Just True  -> tm
    Just False -> fm
    Nothing -> do
      t <- tm
      f <- fm
      natIte sym p t f

-- | Returns number of dimensions in dim.  Dimensions after the count
-- all have value 1.
-- e.g. 2x3x4 returns 3 while 2x3x1 also returns 1.
symDimCount :: IsSymInterface sym
            => sym
            -> SymDim sym
            -> IO (SymNat sym)
symDimCount sym d = do
  one <- natLit sym 1
  let go i | i <= 2 = natLit sym 2
      go i = do
        let entry = d V.! (i-1)
        p <- natEq sym entry one
        natIteM sym p (go (i-1)) (natLit sym (fromIntegral i))
  go (V.length d)

-- | Returns true if dimensions contain a zero.
symDimNull :: IsSymInterface sym
           => sym
           -> SymDim sym
           -> IO (Pred sym)
symDimNull sym d = do
  z <- natLit sym 0
  let f e = natEq sym e z
  eqs <- traverse f d
  V.foldM' (orPred sym) (falsePred sym) eqs

withEquivWidths :: NatRepr m
                -> NatRepr n
                -> ((m :~: n) -> a)
                -> a
withEquivWidths wx wy f = do
  case testEquality wx wy of
    Just r -> f r
    Nothing -> error "internal: Given incompatible widths."

-- | Return predicate that holds if all array entries are real numbers.
cplxArrayIsReal :: IsSymInterface sym
                => sym
                -> MultiDimArray (SymCplx sym)
                -> IO (Pred sym)
cplxArrayIsReal sym a = do
  andAllOf sym folded =<< traverse (isReal sym) a

-- | Return predicate that holds if all array entries are non-negative numbers.
realArrayIsNonNeg :: IsSymInterface sym
                => sym
                -> MultiDimArray (SymReal sym)
                -> IO (Pred sym)
realArrayIsNonNeg sym a = do
  andAllOf sym folded =<< traverse (realIsNonNeg sym) a

dimBoundsN :: Nat -> MDA.ArrayDim -> [(Nat, Nat)]
dimBoundsN n d = (1,) <$> MDA.asDimListN (fromIntegral n) d


-- | Helper method for implementing 'indexSymbolic'
indexSymbolic' :: IsSymInterface sym
               => sym
               -> (Pred sym -> a -> a -> IO a)
                  -- ^ Function for merging valeus
               -> ([Nat] -> IO a) -- ^ Concrete index function.
               -> [Nat] -- ^ Values of processed indices (in reverse order)
               -> [(Nat,Nat)] -- ^ Bounds on remaining indices.
               -> [SymNat sym] -- ^ Remaining indices.
               -> IO a
indexSymbolic' _ _ f p [] _ = f (reverse p)
indexSymbolic' _ _ f p _ [] = f (reverse p)
indexSymbolic' sym iteFn f p ((l,h):nl) (si:il) = do
  let subIndex idx = indexSymbolic' sym iteFn f (idx:p) nl il
  case asNat si of
    Just i
      | l <= i && i <= h -> subIndex i
      | otherwise -> fail $ "Index exceeds matrix dimensions.\n" ++ show (l,i,h)
    Nothing -> do
      l_sym <- natLit sym l
      h_sym <- natLit sym h
      inRange <- join $ andPred sym <$> natLe sym l_sym si <*> natLe sym si h_sym
      addAssertion sym inRange (GenericSimError "Index exceeds matrix dimensions.")
      let predFn i = natEq sym si =<< natLit sym (fromInteger i)
      muxIntegerRange predFn iteFn (subIndex . fromInteger) (toInteger l) (toInteger h)

-- | Lookup a value in an array that may be at a symbolic offset.
--
-- This function takes a list of symbolic indices as natural numbers
-- along with a pair of lower and upper bounds for each index.
-- It assumes that the indices are all in range.
indexSymbolic :: IsSymInterface sym
              => sym
              -> (Pred sym -> a  -> a -> IO a)
                 -- ^ Function for combining results together.
              -> ([Nat] -> IO a) -- ^ Concrete index function.
              -> [(Nat,Nat)] -- ^ High and low bounds at the indices.
              -> [SymNat sym]
              -> IO a
indexSymbolic sym iteFn f = indexSymbolic' sym iteFn f []

-- | Lookup a value in an array that may be at a symbolic offset.
mda_symbolic_lookup :: IsSymInterface sym
                      => sym
                      -> (Pred sym -> a  -> a -> IO a)
                         -- ^ Function for combining results together.
                      -> MultiDimArray a
                         -- Concrete array to lookup
                      -> V.Vector (SymNat sym)
                         -- ^ Indices
                      -> IO a
mda_symbolic_lookup sym ite_fn a idx_v = indexSymbolic sym ite_fn elt_fn bounds idx_l
  where d = MDA.dim a

        elt_fn i = return r
          where Just r = a MDA.!? (MDA.indexFromList i)

        n = fromIntegral (V.length idx_v)
        bounds = dimBoundsN n d
        idx_l = V.toList idx_v

-- | Compute index of element in vector given bounds of array and indices to lookup.
getLastIndex :: Nat -- ^ Base offset
             -> Nat -- ^ What to multiply index by when adding to offset
             -> [Nat] -- ^ Bounds on dimensions of elements.
             -> [Nat]  -- ^ Indices to lookup
             -> Nat
getLastIndex o _ [] [] = o
getLastIndex o m (d:dl) (i:il) = seq o' $ seq d' $ getLastIndex o' d' dl il
  where o' = o + m * (i-1)
        d' = m * d
getLastIndex _ _ _ _ = error "getLastIndex given mismatched dimensions."

asIndexVectorN :: MDA.ArrayDim -> MDA.Index -> Nat -> V.Vector Nat
asIndexVectorN _ _  0 = error "Expected at least one index."
asIndexVectorN d i0 req
   | n < req = i V.++ V.replicate (fromIntegral (req - n)) 1
   | req < n =
       let toL v = V.toList (V.drop (fromIntegral (req-1)) v)
           last_idx = getLastIndex 1 1 (toL dv) (toL i)
        in V.take (fromIntegral (req-1)) i `V.snoc` last_idx
   | otherwise = i
  where i  = MDA.indexToVector i0
        n = fromIntegral (V.length i)
        dv = MDA.asDimVectorN n d

-- | Mux the dimensions of an array together.
matchConcreteArrayIndex :: IsExprBuilder sym
                              => sym
                              -> MDA.ArrayDim
                              -> MDA.Index
                              -> V.Vector (SymNat sym)
                              -> IO (Pred sym)
matchConcreteArrayIndex sym d x0 y =
    andAllOf sym folded =<< V.zipWithM eq x y
 where x = asIndexVectorN d x0 (fromIntegral (V.length y))
       eq u v = natEq sym v =<< natLit sym u

-- | Update the multi-dim array at the given index.
--
-- This function assumes that the index is in range, and does not
-- grow the array to accomodate it.
mda_symbolic_update
  :: IsExprBuilder sym
     => sym
     -> (Pred sym -> a  -> a -> IO a)
     -- ^ Function for combining results together.
     -> MultiDimArray a
     -> V.Vector (SymNat sym) -- ^ Index to update.
     -> a -- ^ Value to assign
     -> IO (MultiDimArray a)
mda_symbolic_update sym ite_fn a sym_idx v =
    MDA.generateM (MDA.dim a) $ \i -> do
      p <- matchConcreteArrayIndex sym (MDA.dim a) i sym_idx
      ite_fn p v (a MDA.! i)

cplxArrayAsPosNat :: IsSymInterface sym
                  => sym
                  -> MultiDimArray (SymCplx sym)
                  -> IO (PartExpr (Pred sym) (MultiDimArray (SymNat sym)))
cplxArrayAsPosNat sym a = do
  -- Collect assertions that numbers have no cplx part.
  p0 <- andAllOf sym folded =<< traverse (isReal sym) a
  -- Get just the real part of numbers.
  ra <- traverse (getRealPart sym) a
  -- Collect assertions that real numbers are integers.
  p1 <- andAllOf sym folded =<< traverse (isInteger sym) ra
  -- Get constant 1.
  c1 <- realLit sym 1
  -- Collect assertions that numbers are at least 1.
  p2 <- andAllOf sym folded =<< traverse (realLe sym c1) ra
  -- Conjoin predicates.
  p <- andPred sym p0 =<< andPred sym p1 p2
  -- Convert real numbers to naturals.
  na <- traverse (realToNat sym) ra
  -- Return result
  return (mkPE p na)

matlabIntArrayAsPosNat :: IsSymInterface sym
                       => sym
                       -> SomeBVArray (SymExpr sym)
                       -> IO (PartExpr (Pred sym) (MultiDimArray (SymNat sym)))
matlabIntArrayAsPosNat sym (SomeBVArray w a) = do
  -- Get constant 0.
  c0 <- bvLit sym w 0
  -- Check to ensure all values are greater than 0 with signed comparison.
  p <- andAllOf sym folded =<< traverse (bvSlt sym c0) a
  -- Convert bitvectors to natural numbers.
  r <- traverse (bvToNat sym) a
  return (mkPE p r)

matlabUIntArrayAsPosNat :: IsSymInterface sym
                        => sym
                        -> SomeBVArray (SymExpr sym)
                        -> IO (PartExpr (Pred sym) (MultiDimArray (SymNat sym)))
matlabUIntArrayAsPosNat sym (SomeBVArray _ a) = do
  r <- traverse (bvToNat sym) a
  p <- checkAtLeast1 sym r
  return (mkPE p r)

logicArrayToIndices :: IsExprBuilder sym
                    => sym
                    -> MultiDimArray (Pred sym)
                    -> IO (MultiDimArray (SymNat sym))
logicArrayToIndices sym a = do
  m <- failIfNothing "Logical indices may not be symbolic." $ do
         traverse asConstantPred a
  let d = MDA.dim m
  let vIndices = V.fromList $ selectedIndices (Fold.toList m)
  let fixedM | MDA.rowDim d == 1 && MDA.higherDims d == [] = MDA.rowVector vIndices
               -- Return indices on a single column.
             | otherwise = MDA.colVector vIndices
               -- Return indices on a single row.
  -- Create terms for indices.
  traverse (natLit sym) fixedM

charArrayAsPosNat :: IsSymInterface sym
                  => sym
                  -> CharArray
                  -> IO (PartExpr (Pred sym) (MultiDimArray (SymNat sym)))
charArrayAsPosNat sym a = do
  r <- traverse (natLit sym . fromIntegral . fromEnum) a
  p <- checkAtLeast1 sym r
  return (PE p r)

-- | Create a list of dimensions from an arraydim.
dimLit :: IsExprBuilder sym
       => sym
       -> ArrayDim
       -> IO (SymDim sym)
dimLit sym d = traverse (natLit sym) (V.fromList (MDA.asDimList d))

-- | Evaluate an indexTermterm to an index value.
evalBase :: sym
          -> (forall utp . f utp -> IO (RegValue sym utp))
          -> BaseTerm f vtp
          -> IO (SymExpr sym vtp)
evalBase _ evalSub (BaseTerm tp e) =
  case tp of
    BaseBoolRepr    -> evalSub e
    BaseBVRepr _    -> evalSub e
    BaseNatRepr     -> evalSub e
    BaseIntegerRepr -> evalSub e
    BaseRealRepr    -> evalSub e
    BaseComplexRepr -> evalSub e
    BaseStructRepr  _ -> evalSub e
    BaseArrayRepr _ _ -> evalSub e

-- | Get value stored in vector at a symbolic index.
indexVectorWithSymNat :: IsExprBuilder sym
                      => sym
                      -> (Pred sym -> a -> a -> IO a)
                         -- ^ Ite function
                      -> V.Vector a
                      -> SymNat sym
                      -> IO a
indexVectorWithSymNat sym iteFn v si = do
  let n = fromIntegral (V.length v)
  assert (n > 0) $ do
  case asNat si of
    Just i | 0 <= i && i <= n -> return (v V.! fromIntegral i)
           | otherwise -> error "indexVectorWithSymNat given bad value"
    Nothing -> do
      let predFn i = natEq sym si =<< natLit sym (fromInteger i)
      let getElt i = return (v V.! fromInteger i)
      muxIntegerRange predFn iteFn getElt 0 (toInteger (n-1))

-- | Update a vector at a given natural number index.
updateVectorWithSymNat :: IsExprBuilder sym
                       => sym
                          -- ^ Symbolic backend
                       -> (Pred sym -> a -> a -> IO a)
                          -- ^ Ite function
                       -> V.Vector a
                          -- ^ Vector to update
                       -> SymNat sym
                          -- ^ Index to update
                       -> a
                          -- ^ New value to assign
                       -> IO (V.Vector a)
updateVectorWithSymNat sym iteFn v si new_val = do
  let n = V.length v
  case asNat si of
    Just i | i < fromIntegral n -> do
             return $ v V.// [(fromIntegral i, new_val)]
           | otherwise -> fail $
               "internal: Illegal index " ++ show i ++ " given to updateVectorWithSymNat"
    Nothing -> do
      let setFn j = do
            -- Compare si and j.
            c <- natEq sym si =<< natLit sym (fromIntegral j)
            -- Select old value or new value
            iteFn c new_val (v V.! j)
      V.generateM n setFn

{-# INLINE evalApp #-}
-- | Evaluate the application.
evalApp :: forall sym f tp
         . IsSymInterface sym
        => sym
        -> IntrinsicTypes sym
        -> (Int -> String -> IO ())
           -- ^ Function for logging messages.
        -> (forall utp . f utp -> IO (RegValue sym utp))
           -- ^ Evaluation function for arguments.
        -> App f tp
        -> IO (RegValue sym tp)
evalApp sym itefns logFn evalSub a0 = do
  case a0 of

    ----------------------------------------------------------------------
    -- ()

    EmptyApp -> return ()

    ----------------------------------------------------------------------
    -- Any

    PackAny tp x -> do
      xv <- evalSub x
      return (AnyValue tp xv)

    UnpackAny tp x -> do
      xv <- evalSub x
      case xv of
        AnyValue tpv v
          | Just Refl <- testEquality tp tpv ->
               return $! PE (truePred sym) v
          | otherwise ->
               return $! Unassigned

    ----------------------------------------------------------------------
    -- Concrete

    ConcreteLit (TypeableValue x) -> return x

    ----------------------------------------------------------------------
    -- Bool

    BoolLit b -> return $ backendPred sym b
    Not x -> do
      r <- evalSub x
      notPred sym r
    And x y -> do
      xv <- evalSub x
      yv <- evalSub y
      andPred sym xv yv
    Or x y -> do
      xv <- evalSub x
      yv <- evalSub y
      orPred sym xv yv
    BoolXor x y -> do
      xv <- evalSub x
      yv <- evalSub y
      xorPred sym xv yv
    BoolIte ce x y -> do
      c <- evalSub ce
      case asConstantPred c of
        Just True  -> evalSub x
        Just False -> evalSub y
        Nothing -> do
          t <- evalSub x
          f <- evalSub y
          itePred sym c t f

    ----------------------------------------------------------------------
    -- Nat

    NatLit n -> natLit sym n
    NatEq xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natEq sym x y
    NatLt xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natLt sym x y
    NatLe x y -> do
      x' <- evalSub x
      y' <- evalSub y
      natLe sym x' y'
    NatAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natAdd sym x y
    NatSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natSub sym x y
    NatMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      natMul sym x y

    ----------------------------------------------------------------------
    -- Int

    IntLit n -> intLit sym n
    IntEq xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intEq sym x y
    IntLt xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intLt sym x y
    IntAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intAdd sym x y
    IntSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intSub sym x y
    IntMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      intMul sym x y

    --------------------------------------------------------------------
    -- Maybe

    JustValue _ e -> do
      r <- evalSub e
      return $! PE (truePred sym) r
    NothingValue _ -> do
      return $! Unassigned
    FromJustValue _ maybe_expr msg_expr -> do
      maybe_val <- evalSub maybe_expr
      case maybe_val of
        -- Special case to avoid forcing evaluation of msg.
        PE (asConstantPred -> Just True) v -> return v
        _ -> do
          msg <- evalSub msg_expr
          readPartExpr sym maybe_val (GenericSimError (Text.unpack msg))

    ----------------------------------------------------------------------
    -- Side conditions

    AddSideCondition _ pe rsn e -> do
      addAssertionM sym (evalSub pe) (AssertFailureSimError rsn)
      evalSub e

    ----------------------------------------------------------------------
    -- Recursive Types

    RollRecursive _ e   -> RolledType <$> evalSub e
    UnrollRecursive _ e -> unroll <$> evalSub e

    ----------------------------------------------------------------------
    -- Vector

    VectorLit _ v -> traverse evalSub v
    VectorReplicate _ n_expr e_expr -> do
      ne <- evalSub n_expr
      case asNat ne of
        Nothing -> fail $ "mss does not support symbolic length arrays."
        Just n -> do
          e <- evalSub e_expr
          return $ V.replicate (fromIntegral n) e
    VectorIsEmpty r -> do
      v <- evalSub r
      return $ backendPred sym (V.null v)
    VectorSize v_expr -> do
      v <- evalSub v_expr
      natLit sym (fromIntegral (V.length v))
    VectorGetEntry rtp v_expr i_expr -> do
      v <- evalSub v_expr
      i <- evalSub i_expr
      indexVectorWithSymNat sym (muxRegForType sym itefns rtp) v i
    VectorSetEntry rtp v_expr i_expr n_expr -> do
      v <- evalSub v_expr
      i <- evalSub i_expr
      n <- evalSub n_expr
      updateVectorWithSymNat sym (muxRegForType sym itefns rtp) v i n


    --------------------------------------------------------------------
    -- Symbolic Arrays

    SymArrayLookup _ a i -> do
      join $ arrayLookup sym <$> evalSub a <*> traverseFC (evalBase sym evalSub) i

    SymArrayUpdate  _ a i v -> do
      join $ arrayUpdate sym
        <$> evalSub a
        <*> traverseFC (evalBase sym evalSub) i
        <*> evalSub v

    --------------------------------------------------------------------
    -- Symbolic Multi-dimensional Arrays

    MatlabSymArrayDim ae -> do
      SMDA.symDim <$> evalSub ae

    MatlabSymArrayReplicate _bt de xe -> do
      d <- evalSub de
      x <- evalSub xe
      SMDA.replicate sym d x

    MatlabSymArrayLookup _bt ae ie -> do
      join $ SMDA.lookup sym
        <$> evalSub ae
        <*> evalSub ie

    MatlabSymArrayUpdate _ ae ie ve -> do
      join $ SMDA.update sym
        <$> evalSub  ae
        <*> evalSub  ie
        <*> evalSub  ve

    MatlabSymArrayAsSingleton _bt ae -> do
      a <- evalSub ae
      SMDA.asSingleton sym a

    MatlabSymArrayResize _bt a d def -> do
      join $ SMDA.resize sym <$> evalSub a <*> evalSub d <*> evalSub def

    MatlabSymIndexArray _bt ae idx_e -> do
      a <- evalSub ae
      idx <- evalSub idx_e
      let f is = SMDA.lookup sym a is
      traverse f idx

    MatlabSymArraySymIndex _bt ae idx_e -> do
      join $ SMDA.lookupArray sym <$> evalSub ae <*> traverse evalSub idx_e

    MatlabSymArrayExternalize _ ae -> do
      a <- evalSub ae
      SMDA.externalizeArray sym a

    MatlabArrayInternalize tp ae -> do
      a <- evalSub ae
      SMDA.internalizeArray sym tp a

    --------------------------------------------------------------------
    -- MultiDimArray

    ArrayEmpty _ -> return MDA.empty
    ArrayReplicate _ d_expr e_expr -> do
      d_sym <- evalSub d_expr
      e <- evalSub e_expr
      d <- asDimLit d_sym
      return $ MDA.replicate d e
    ArrayDim a_expr -> do
      a <- evalSub a_expr
      dimLit sym (MDA.dim a)
    ArrayResize _ a_expr d_expr v_expr -> do
      a <- evalSub a_expr
      d_sym <- evalSub d_expr
      d <- resizeDimLit sym logFn (MDA.dim a) d_sym
      if d == MDA.dim a then
        return a
       else do
        v <- evalSub v_expr
        return $ MDA.generate d $ \i -> fromMaybe v (a MDA.!? i)
    ArrayLookup rtp a_expr i_expr -> do
      let ite_fn = muxRegForType sym itefns rtp
      join $ mda_symbolic_lookup sym ite_fn
        <$> evalSub a_expr
        <*> evalSub i_expr
    ArrayUpdate rtp a_expr i_expr v_expr -> do
      let ite_fn = muxRegForType sym itefns rtp
      join $ mda_symbolic_update sym ite_fn
        <$> evalSub a_expr
        <*> evalSub i_expr
        <*> evalSub v_expr
    ArrayAsSingleton _ x_expr -> do
      x <- evalSub x_expr
      return $ maybePartExpr sym (MDA.asSingleton x)
    IndexArray rtp a_expr i_expr -> do
      a <- evalSub a_expr
      idx <- evalSub i_expr
      let iteFn = muxRegForType sym itefns rtp
      traverse (mda_symbolic_lookup sym iteFn a) idx
    ArrayEntry _ ae args -> do
      a <- evalSub ae
      -- Compute indices into array based on dimensions of a.
      sIndices <- evalSub args
      -- Get constants indices
      let noSymbolicMsg = "Simulator does not support symbolic indices in this context."
      cIndices <- failIfNothing noSymbolicMsg $
                    asConstantIndex sIndices
      -- By requirements in translation, index should be defined.
      let Just r = a MDA.!? cIndices
      return r
    ArrayProduct _ v_expr -> do
      v <- traverse evalSub (V.toList v_expr)
      return $ V.fromList <$> (MDA.arrayProduct v)
    MultiDimArrayToVec _ a_expr -> do
      a <- evalSub a_expr
      return $ MDA.mdVec a

    MatlabExtArraySymIndex rtp a_expr i_expr -> do
      a <- evalSub a_expr
      i_mda <- traverse (SMDA.externalizeArray sym <=< evalSub) i_expr
      let idx = V.fromList <$> MDA.arrayProduct (V.toList i_mda)
      let iteFn = muxRegForType sym itefns rtp
      traverse (mda_symbolic_lookup sym iteFn a) idx

    ----------------------------------------------------------------------
    -- Conversion to vector based indexing.

    CplxVecToNat v_expr -> do
      let cplxToNat = realToNat sym <=< getRealPart sym
      traverse cplxToNat =<< evalSub v_expr
    LogicVecToIndex v_expr -> do
      v <- evalSub v_expr
      let go :: [Nat] -> Int -> IO [Nat]
          go l i
            | i < V.length v =
              case asConstantPred (v V.! i) of
                Just True  -> (go $! (fromIntegral i:l)) (i+1)
                Just False -> go l (i+1)
                Nothing -> fail "Simulator does not support symbolic logical indexing."
            | otherwise = return $ reverse l
      l <- go [] 0
      -- Create natural number literals.
      traverse (\i -> natLit sym (i+1)) (V.fromList l)
    MatlabCharVecToNat v_expr -> do
      traverse (natLit sym . fromIntegral) =<< evalSub v_expr
    MatlabIntArrayToNat a_expr -> do
      SomeBVArray _ a <- evalSub a_expr
      traverse (bvToNat sym) (MDA.mdVec a)
    MatlabUIntArrayToNat a_expr -> do
      SomeBVArray _ a <- evalSub a_expr
      traverse (bvToNat sym) (MDA.mdVec a)

    ----------------------------------------------------------------------
    -- Handle

    HandleLit h -> return (HandleFnVal h)

    Closure _ _ h_expr tp v_expr -> do
      h <- evalSub h_expr
      v <- evalSub v_expr
      return $! ClosureFnVal h tp v

    ----------------------------------------------------------------------
    -- PosNat

    EnumTo e -> do
      ne <- evalSub e
      case asNat ne of
        Nothing -> fail "mss does not support symbolic length vectors."
        Just n ->
          fmap MDA.colVector $
            V.generateM (fromIntegral n) (\i ->  natLit sym (fromIntegral (i+1)))

    ----------------------------------------------------------------------
    -- RealVal

    RationalLit d -> realLit sym d
    RealAdd xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realAdd sym x y
    RealSub xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realSub sym x y
    RealMul xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      realMul sym x y
    RealIte ce te fe -> do
      c <- evalSub ce
      case asConstantPred c of
        Just True  -> evalSub te
        Just False -> evalSub fe
        Nothing -> do
          t <- evalSub te
          f <- evalSub fe
          realIte sym c t f
    RealEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      realEq sym x y
    RealLt x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      realLt sym x y
    RealIsInteger x_expr -> do
      x <- evalSub x_expr
      isInteger sym x

    ----------------------------------------------------------------------
    -- Conversions

    NatToInteger x_expr -> do
      x <- evalSub x_expr
      natToInteger sym x
    IntegerToReal x_expr -> do
      x <- evalSub x_expr
      integerToReal sym x
    RealToNat x_expr -> do
      x <- evalSub x_expr
      realToNat sym x

    ----------------------------------------------------------------------
    -- ComplexReal

    Complex r_expr i_expr -> do
      r <- evalSub r_expr
      i <- evalSub i_expr
      mkComplex sym (r :+ i)
    RealPart c_expr -> getRealPart sym =<< evalSub c_expr
    ImagPart c_expr -> getImagPart sym =<< evalSub c_expr

    ----------------------------------------------------------------------
    -- MatlabChar

    MatlabCharLit (MatlabChar w) -> return w
    MatlabCharEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      return $ backendPred sym (x == y)
    MatlabCharToNat x_expr -> do
      x <- evalSub x_expr
      natLit sym (fromIntegral x)

    --------------------------------------------------------------------
    -- CplxArrayType

    CplxArrayEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      if MDA.dim x == MDA.dim y then do
        eq <- MDA.zipWithM (cplxEq sym) x y
        andAllOf sym folded eq
       else
        return $ falsePred sym
    CplxArrayToRealArray x_expr -> do
      x <- evalSub x_expr
      r <- cplxArrayIsReal sym x
      addAssertion sym r (GenericSimError "Cannot coerce complex numbers to real numbers")
      traverse (getRealPart sym) x
    CplxArrayToIntegerArray x_expr -> do
      x <- evalSub x_expr
      r <- cplxArrayIsReal sym x
      addAssertion sym r (GenericSimError "Cannot coerce complex numbers to real numbers")
      let toint v = do
            a <- getRealPart sym v
            addAssertionM sym (isInteger sym a) (GenericSimError "Expected integer value")
            realFloor sym a
      traverse toint x
    RealArrayToIntegerArray x_expr -> do
      x <- evalSub x_expr
      traverse (realToInteger sym) x
    IntArrayToIntegerArray x_expr -> do
      SomeBVArray _w x <- evalSub x_expr
      traverse (sbvToInteger sym) x
    UIntArrayToIntegerArray x_expr -> do
      SomeBVArray _w x <- evalSub x_expr
      traverse (bvToInteger sym) x
    LogicArrayToIntegerArray x_expr -> do
      x <- evalSub x_expr
      z <- intLit sym 0
      o <- intLit sym 1
      traverse (\b -> intIte sym b o z) x
    CharArrayToIntegerArray e -> do
      a <- evalSub e
      let charToReal = intLit sym . fromIntegral
      traverse charToReal a
    CplxArrayIsReal x_expr -> do
      x <- evalSub x_expr
      cplxArrayIsReal sym x
    RealArrayToCplxArray e -> do
      a <- evalSub e
      traverse (cplxFromReal sym) a
    IntegerArrayToCplxArray e -> do
      a <- evalSub e
      traverse (cplxFromReal sym <=< integerToReal sym) a
    IntArrayToCplxArray e -> do
      SomeBVArray _ a <- evalSub e
      traverse (cplxFromReal sym <=< integerToReal sym <=< sbvToInteger sym) a
    UIntArrayToCplxArray e -> do
      SomeBVArray _ a <- evalSub e
      traverse (cplxFromReal sym <=< integerToReal sym <=< bvToInteger sym) a
    LogicArrayToCplxArray e -> do
      a <- evalSub e
      traverse (cplxFromReal sym <=< predToReal sym) a
    CharArrayToCplxArray e -> do
      a <- evalSub e
      let charToReal = mkRational sym . toRational
      traverse charToReal a
    CplxArrayAsPosNat e -> cplxArrayAsPosNat sym =<< evalSub e

    --------------------------------------------------------------------
    -- IntWidth

    IntArrayWidth e -> do
      SomeBVArray w _ <- evalSub e
      return $! IntWidth w

    --------------------------------------------------------------------
    -- MatlabInt

    MatlabIntLit w x -> do
      SomeInt w <$> bvLit sym w x
    MatlabIntEq xe ye -> do
      SomeInt wx x <- evalSub xe
      SomeInt wy y <- evalSub ye
      withEquivWidths wx wy $ \Refl -> do
        bvEq sym x y
    MatlabIntLt xe ye -> do
      SomeInt wx x <- evalSub xe
      SomeInt wy y <- evalSub ye
      withEquivWidths wx wy $ \Refl -> do
        bvSlt sym x y
    MatlabIntIsPos xe -> do
      SomeInt w x <- evalSub xe
      z <- bvLit sym w 0
      bvSgt sym x z
    MatlabIntToNat xe -> do
      SomeInt w x <- evalSub xe
      -- Check if x is less than zero.
      p <- bvSlt sym x =<< bvLit sym w 0
      -- If it is then return 0, else return nat.
      zero <- natLit sym 0
      natIte sym p zero =<< bvToNat sym x


    --------------------------------------------------------------------
    -- IntArrayType

    MatlabIntArrayEmpty e -> do
      IntWidth w <- evalSub e
      return $ SomeBVArray w MDA.empty
    MatlabIntArraySingleton e -> do
      SomeInt w n <- evalSub e
      return $ SomeBVArray w (MDA.singleton n)
    MatlabIntArrayLookup a_expr i_expr -> do
      SomeBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeInt w <$> mda_symbolic_lookup sym (bvIte sym) a i
    MatlabIntArrayUpdate a_expr i_expr v_expr -> do
      SomeBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeInt wn v <- evalSub v_expr
      case testEquality w wn of
        Nothing ->
          fail "Incompatiable widths given to MatlabIntArrayUpdate"
        Just Refl -> do
          let ite_fn = bvIte sym
          SomeBVArray w <$> mda_symbolic_update sym ite_fn a i v
    MatlabIntArrayDim a_sym -> do
      a <- evalSub a_sym
      dimLit sym (MDA.dim a)
    MatlabIntArrayResize a_expr d_expr -> do
      SomeBVArray w a <- evalSub a_expr
      d_sym <- evalSub d_expr
      d <- resizeDimLit sym logFn (MDA.dim a) d_sym
      if d == MDA.dim a then
        return (SomeBVArray w a)
       else do
        v <- bvLit sym w 0
        return $ SomeBVArray w $ MDA.generate d $ \i -> fromMaybe v (a MDA.!? i)
    MatlabIntArrayAsSingleton a_expr -> do
      SomeBVArray w a <- evalSub a_expr
      return $ maybePartExpr sym (SomeInt w <$> MDA.asSingleton a)
    MatlabIntArrayIndex f args -> do
      SomeBVArray w a <- evalSub f
      idx <- evalSub args
      let ite c x y = bvIte sym c x y
      SomeBVArray w <$> traverse (mda_symbolic_lookup sym ite a) idx
    MatlabIntArrayEq x_expr y_expr -> do
      SomeBVArray wx x <- evalSub x_expr
      SomeBVArray wy y <- evalSub y_expr
      case testEquality wx wy of
        Just Refl | MDA.dim x == MDA.dim y -> do
          eq <- MDA.zipWithM (bvEq sym) x y
          andAllOf sym folded eq
        _ -> return $ falsePred sym
    MatlabIntArrayAsPosNat a_expr -> matlabIntArrayAsPosNat sym =<< evalSub a_expr
    CplxArrayToMatlabInt a_exp w_exp -> do
      a <- evalSub a_exp
      IntWidth w <- evalSub w_exp
      let f c = do
            r <- getRealPart sym c
            realToInt sym r w
      SomeBVArray w <$> traverse f a
    MatlabIntArraySetWidth a_exp w_exp -> do
      SomeBVArray u a <- evalSub a_exp
      IntWidth w <- evalSub w_exp
      SomeBVArray w <$>
        case w `testEquality` u of
          Just Refl -> return a
          Nothing -> traverse (\e -> intSetWidth sym e w) a
    MatlabUIntArrayToInt a_exp w_exp -> do
      SomeBVArray _ a <- evalSub a_exp
      IntWidth w <- evalSub w_exp
      SomeBVArray w <$> traverse (\e -> uintToInt sym e w) a
    LogicArrayToMatlabInt a_exp w_exp -> do
      a <- evalSub a_exp
      IntWidth w <- evalSub w_exp
      SomeBVArray w <$> traverse (\v -> predToBV sym v w) a
    CharArrayToMatlabInt a_exp w_exp -> do
      a <- evalSub a_exp
      IntWidth w <- evalSub w_exp
      let charToInt = bvLit sym w . toInteger
      SomeBVArray w <$> traverse charToInt a

    --------------------------------------------------------------------
    -- UIntWidth

    UIntArrayWidth e -> do
      SomeBVArray w _ <- evalSub e
      return (UIntWidth w)

    --------------------------------------------------------------------
    -- BVs

    BVUndef w ->
      freshConstant sym emptySymbol (BaseBVRepr w)

    BVLit w x -> bvLit sym w x

    BVConcat _ _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvConcat sym x y
    -- FIXME: there are probably some worthwhile special cases to exploit in "BVSelect"
    BVSelect idx n _ xe -> do
      x <- evalSub xe
      bvSelect sym idx n x
    BVTrunc w' _ xe -> do
      x <- evalSub xe
      bvTrunc sym w' x
    BVZext w' _ xe -> do
      x <- evalSub xe
      bvZext sym w' x
    BVSext w' _ xe -> do
      x <- evalSub xe
      bvSext sym w' x
    BVEq _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvEq sym x y
    BVNot _ xe ->
      bvNotBits sym =<< evalSub xe
    BVAnd _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAndBits sym x y
    BVOr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvOrBits sym x y
    BVXor _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvXorBits sym x y
    BVAdd _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAdd sym x y
    BVSub _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSub sym x y
    BVMul _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvMul sym x y
    BVUdiv _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUdiv sym x y
    BVSdiv _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSdiv sym x y
    BVUrem _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUrem sym x y
    BVSrem _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSrem sym x y

    BvToNat _ xe -> do
      bvToNat sym =<< evalSub xe
    BVUlt _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUlt sym x y
    BVSlt _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSlt sym x y
    BoolToBV w xe -> do
      x <- evalSub xe
      one <- bvLit sym w 1
      zro <- bvLit sym w 0
      bvIte sym x one zro
    BVNonzero _ xe -> do
      x <- evalSub xe
      bvIsNonzero sym x
    BVShl _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvShl sym x y
    BVLshr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvLshr sym x y
    BVAshr _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvAshr sym x y
    BVCarry _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> addUnsignedOF sym x y
    BVSCarry _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> addSignedOF sym x y
    BVSBorrow _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      fst <$> subSignedOF sym x y
    BVUle _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvUle sym x y
    BVSle _ xe ye -> do
      x <- evalSub xe
      y <- evalSub ye
      bvSle sym x y
    BVIte ce _ xe ye -> do
      c <- evalSub ce
      x <- evalSub xe
      y <- evalSub ye
      bvIte sym c x y

    --------------------------------------------------------------------
    -- Symbolic (u)int arrays

    MatlabSymIntArrayResize ae de -> do
       SomeSymbolicBVArray w arr  <- evalSub ae
       newdims <- evalSub de
       def <- bvLit sym w 0
       SomeSymbolicBVArray w <$> SMDA.resize sym arr newdims def
    MatlabSymIntArrayLookup ae ie -> do
      SomeSymbolicBVArray w a <- evalSub ae
      i <- evalSub ie
      SomeInt w <$> SMDA.lookup sym a i
    MatlabSymIntArrayUpdate a_expr i_expr v_expr -> do
      SomeSymbolicBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeInt w' v <- evalSub v_expr
      case testEquality w w' of
        Just Refl ->
          SomeSymbolicBVArray w <$> SMDA.update sym a i v
        Nothing ->
          fail $ unwords ["MatlabSymIntArrayUpdate: width mismatch",show w, show w']

    SymIntArrayWidth e -> do
      SomeSymbolicBVArray w _ <- evalSub e
      return $! IntWidth w

    SymUIntArrayWidth e -> do
      SomeSymbolicBVArray w _ <- evalSub e
      return $! UIntWidth w

    MatlabSymbolicIntArrayDim ae -> do
      SomeSymbolicBVArray _ a <- evalSub ae
      return $! SMDA.symDim a

    MatlabSymbolicUIntArrayDim ae -> do
      SomeSymbolicBVArray _ a <- evalSub ae
      return $! SMDA.symDim a

    MatlabSymUIntArrayResize ae de -> do
       SomeSymbolicBVArray w arr  <- evalSub ae
       newdims <- evalSub de
       def <- bvLit sym w 0
       SomeSymbolicBVArray w <$> SMDA.resize sym arr newdims def

    MatlabSymUIntArrayLookup ae ie -> do
      SomeSymbolicBVArray w a <- evalSub ae
      i <- evalSub ie
      SomeUInt w <$> SMDA.lookup sym a i

    MatlabSymUIntArrayUpdate a_expr i_expr v_expr -> do
      SomeSymbolicBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeUInt w' v <- evalSub v_expr
      case testEquality w w' of
        Just Refl ->
          SomeSymbolicBVArray w <$> SMDA.update sym a i v
        Nothing ->
          fail $ unwords ["MatlabSymUIntArrayUpdate: width mismatch",show w, show w']
    MatlabSymIntArrayAsSingleton ae -> do
      SomeSymbolicBVArray w a <- evalSub ae
      fmap (SomeInt w) <$> SMDA.asSingleton sym a

    MatlabSymUIntArrayAsSingleton ae -> do
      SomeSymbolicBVArray w a <- evalSub ae
      fmap (SomeUInt w) <$> SMDA.asSingleton sym a

    SymIndexIntArray ae idx_e -> do
      SomeSymbolicBVArray w a <- evalSub ae
      idx <- evalSub idx_e
      let f is = SMDA.lookup sym a is
      SomeBVArray w <$> traverse f idx

    SymIndexUIntArray ae idx_e -> do
      SomeSymbolicBVArray w a <- evalSub ae
      idx <- evalSub idx_e
      let f is = SMDA.lookup sym a is
      SomeBVArray w <$> traverse f idx

    SymIntArrayExternalize ae -> do
      SomeSymbolicBVArray w a <- evalSub ae
      SomeBVArray w <$> SMDA.externalizeArray sym a

    SymUIntArrayExternalize ae -> do
      SomeSymbolicBVArray w a <- evalSub ae
      SomeBVArray w <$> SMDA.externalizeArray sym a

    --------------------------------------------------------------------
    -- Word Maps

    EmptyWordMap w tp -> do
      emptyWordMap sym w tp

    InsertWordMap w tp ie ve me -> do
      i <- evalSub ie
      v <- evalSub ve
      m <- evalSub me
      insertWordMap sym w tp i v m

    LookupWordMap tp ie me -> do
      i <- evalSub ie
      m <- evalSub me
      x <- lookupWordMap sym (bvWidth i) tp i m
      let msg = "WordMap: read an undefined index" ++
                case asUnsignedBV i of
                   Nothing  -> ""
                   Just idx -> " 0x" ++ showHex idx ""
      let ex = ReadBeforeWriteSimError msg
      readPartExpr sym x ex

    LookupWordMapWithDefault tp ie me de -> do
      i <- evalSub ie
      m <- evalSub me
      d <- evalSub de
      x <- lookupWordMap sym (bvWidth i) tp i m
      case x of
        Unassigned -> return d
        PE p v -> do
          muxRegForType sym itefns (baseToType tp) p v d

    --------------------------------------------------------------------
    -- LLVM Pointers

--    NullPointer -> nullLLVMPointer sym
--    UndefPointer -> undefLLVMPointer sym

    --------------------------------------------------------------------
    -- MatlabUInt

    MatlabUIntLit w x -> do
      SomeUInt w <$> bvLit sym w x
    MatlabUIntEq xe ye -> do
      SomeUInt wx x <- evalSub xe
      SomeUInt wy y <- evalSub ye
      withEquivWidths wx wy $ \Refl -> do
        bvEq sym x y
    MatlabUIntLt xe ye -> do
      SomeUInt wx x <- evalSub xe
      SomeUInt wy y <- evalSub ye
      withEquivWidths wx wy $ \Refl -> do
        bvUlt sym x y
    MatlabUIntIsPos xe -> do
      SomeUInt _ x <- evalSub xe
      bvIsNonzero sym x
    MatlabUIntToNat xe -> do
      SomeUInt _ x <- evalSub xe
      bvToNat sym x

    --------------------------------------------------------------------
    -- UIntArrayType

    MatlabUIntArrayEmpty e -> do
      UIntWidth w <- evalSub e
      return $ SomeBVArray w MDA.empty
    MatlabUIntArraySingleton e -> do
      SomeUInt w n <- evalSub e
      return $ SomeBVArray w (MDA.singleton n)
    MatlabUIntArrayLookup a_expr i_expr -> do
      SomeBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeUInt w <$> mda_symbolic_lookup sym (bvIte sym) a i
    MatlabUIntArrayUpdate  a_expr i_expr v_expr -> do
      SomeBVArray w a <- evalSub a_expr
      i <- evalSub i_expr
      SomeUInt wv v <- evalSub v_expr
      case testEquality w wv of
        Nothing -> fail "Incompatiable widths given to MatlabUIntArrayUpdate"
        Just Refl -> do
          let ite_fn = bvIte sym
          SomeBVArray w <$> mda_symbolic_update sym ite_fn a i v
    MatlabUIntArrayDim a_expr -> do
      a <- evalSub a_expr
      dimLit sym (MDA.dim a)
    MatlabUIntArrayResize a_expr d_expr -> do
      SomeBVArray w a <- evalSub a_expr
      d_sym <- evalSub d_expr
      d <- resizeDimLit sym logFn (MDA.dim a) d_sym
      if d == MDA.dim a then
        return (SomeBVArray w a)
       else do
        v <- bvLit sym w 0
        return $ SomeBVArray w $ MDA.generate d $ \i -> fromMaybe v (a MDA.!? i)
    MatlabUIntArrayAsSingleton a_expr -> do
      SomeBVArray w a <- evalSub a_expr
      return $ maybePartExpr sym (SomeUInt w <$> MDA.asSingleton a)
    MatlabUIntArrayIndex f args -> do
      SomeBVArray w a <- evalSub f
      idx <- evalSub args
      let ite = bvIte sym
      SomeBVArray w <$> traverse (mda_symbolic_lookup sym ite a) idx
    MatlabUIntArrayEq x_expr y_expr -> do
      SomeBVArray wx x <- evalSub x_expr
      SomeBVArray wy y <- evalSub y_expr
      case testEquality wx wy of
        Just Refl | MDA.dim x == MDA.dim y -> do
          eqs <- MDA.zipWithM (bvEq sym) x y
          andAllOf sym folded eqs
        _ -> return $ falsePred sym
    MatlabUIntArrayAsPosNat a_expr -> do
      matlabUIntArrayAsPosNat sym =<< evalSub a_expr

    CplxArrayToMatlabUInt a_exp w_exp -> do
      a <- evalSub a_exp
      UIntWidth w <- evalSub w_exp
      let f c = do
            r <- getRealPart sym c
            realToUInt sym r w
      SomeBVArray w <$> traverse f a
    MatlabIntArrayToUInt a_exp w_exp -> do
      SomeBVArray _ a <- evalSub a_exp
      UIntWidth w <- evalSub w_exp
      SomeBVArray w <$> traverse (\e -> intToUInt sym e w) a
    MatlabUIntArraySetWidth a_exp w_exp -> do
      SomeBVArray u a <- evalSub a_exp
      UIntWidth w <- evalSub w_exp
      SomeBVArray w <$>
        case w `testEquality` u of
          Just Refl -> return a
          Nothing -> traverse (\e -> uintSetWidth sym e w) a
    LogicArrayToMatlabUInt a_exp w_exp -> do
      a <- evalSub a_exp
      UIntWidth w <- evalSub w_exp
      SomeBVArray w <$> traverse (\v -> predToBV sym v w) a
    CharArrayToMatlabUInt a_exp w_exp -> do
      a <- evalSub a_exp
      UIntWidth w <- evalSub w_exp
      let charToUInt = bvLit sym w . toInteger
      SomeBVArray w <$> traverse charToUInt a

    --------------------------------------------------------------------
    -- LogicArrayType

    LogicArrayEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      if MDA.dim x == MDA.dim y then do
        andAllOf sym folded =<< MDA.zipWithM (eqPred sym) x y
       else
        return $ falsePred sym
    LogicArrayToIndices a_expr -> do
      a <- evalSub a_expr
      logicArrayToIndices sym a
    CplxArrayToLogic e -> do
      a <- evalSub e
      addAssertionM sym
                    (cplxArrayValuesAreReal sym a)
                    (GenericSimError "Complex numbers cannot be converted to logicals.")
      z <- mkRational sym 0
      traverse (\v -> cplxNe sym v z) a
    RealArrayToLogic e -> do
      a <- evalSub e
      z <- realLit sym 0
      traverse (\v -> realNe sym v z) a
    IntegerArrayToLogic e -> do
      a <- evalSub e
      z <- intLit sym 0
      traverse (\v -> notPred sym =<< intEq sym v z) a
    MatlabIntArrayToLogic e -> do
      SomeBVArray _ a <- evalSub e
      traverse (bvIsNonzero sym) a
    MatlabUIntArrayToLogic e -> do
      SomeBVArray _ a <- evalSub e
      traverse (bvIsNonzero sym) a
    AllEntriesAreTrue src -> do
      e <- evalSub src
      andAllOf sym folded e

    ----------------------------------------------------------------------
    -- CharArrayType

    CharVectorLit s_lit -> return $ MDA.rowVector $ CV.toVector s_lit
    CharArrayEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      return $ backendPred sym (x == y)
    CplxArrayToChar a_exp -> do
      a <- evalSub a_exp
      traverse complexRealAsChar a
    CharArrayAsPosNat a_expr -> charArrayAsPosNat sym =<< evalSub a_expr
    CharArrayToLogic e -> do
      a <- evalSub e
      return $ (\v -> backendPred sym (v /= 0)) <$> a

    --------------------------------------------------------------------
    -- CellArrayType

    UpdateCellEntry a_exp i_exp v_exp -> do
      v <- evalSub v_exp
      a <- evalSub a_exp
      i <- evalSub i_exp
      case asConstantIndex i of
        Just ic ->
          case MDA.set a emptyDoubleValue ic v of
            Just a' -> return a'
            Nothing -> fail "In assignments with a single index, the array cannot be resized."
        Nothing -> fail "Concrete indices required when assigning cell array values."
    GetVarArgs v_expr cnt -> do
      MDA.rowVector . V.drop (fromIntegral cnt) <$> evalSub v_expr

    --------------------------------------------------------------------
    -- StructFields

    EmptyStructFields -> return V.empty
    FieldsEq x y -> do
      xv <- evalSub x
      yv <- evalSub y
      return $ backendPred sym (xv == yv)
    HasField e s_expr -> do
      ev <- evalSub e
      sv <- evalSub s_expr
      return $ backendPred sym (ev `V.elem` sv)

    --------------------------------------------------------------------
    -- MatlabValue

    CplxArrayToMatlab e   -> RealArray      <$> evalSub e
    MatlabIntArrayToMatlab e  -> IntArray   <$> evalSub e
    MatlabUIntArrayToMatlab e -> UIntArray  <$> evalSub e
    LogicArrayToMatlab e  -> LogicArray     <$> evalSub e
    CharArrayToMatlab e   -> CharArray      <$> evalSub e
    CellArrayToMatlab e   -> CellArray      <$> evalSub e
    MatlabStructArrayToMatlab e -> MatlabStructArray <$> evalSub e
    MatlabObjectArrayToMatlab e -> MatlabObjectArray <$> evalSub e
    HandleToMatlab e -> FunctionHandle <$> evalSub e
    SymLogicArrayToMatlab e -> SymLogicArray <$> evalSub e
    SymRealArrayToMatlab e -> SymRealArray <$> evalSub e
    SymCplxArrayToMatlab e -> SymCplxArray <$> evalSub e
    SymIntArrayToMatlab e  -> SymIntArray <$> evalSub e
    SymUIntArrayToMatlab e -> SymUIntArray <$> evalSub e

    ---------------------------------------------------------------------
    -- Struct

    MkStruct _ exprs -> traverseFC (\x -> RV <$> evalSub x) exprs

    GetStruct st idx _ -> do
      struct <- evalSub st
      return $ unRV $ struct Ctx.! idx

    SetStruct _ st idx x -> do
      struct <- evalSub st
      v <- evalSub x
      return $ Ctx.update idx (RV v) struct

    ----------------------------------------------------------------------
    -- Variant

    InjectVariant ctx idx ve -> do
         v <- evalSub ve
         let voidVariant = Ctx.generate (Ctx.size ctx) (\_ -> VB $ Unassigned)
         return $ Ctx.update idx (VB (PE (truePred sym) v)) voidVariant

    ----------------------------------------------------------------------
    -- IdentValueMap

    EmptyStringMap _ -> return Map.empty
    LookupStringMapEntry _ m_expr i_expr -> do
      i <- evalSub i_expr
      m <- evalSub m_expr
      return $ joinMaybePE (Map.lookup i m)
    InsertStringMapEntry _ m_expr i_expr v_expr -> do
      m <- evalSub m_expr
      i <- evalSub i_expr
      v <- evalSub v_expr
      return $ Map.insert i v m

    ----------------------------------------------------
    -- Uncategorized
    RealArrayEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      if MDA.dim x == MDA.dim y then do
        eq <- MDA.zipWithM (realEq sym) x y
        andAllOf sym folded eq
       else
        return $ falsePred sym

    IntegerArrayEq x_expr y_expr -> do
      x <- evalSub x_expr
      y <- evalSub y_expr
      if MDA.dim x == MDA.dim y then do
        eq <- MDA.zipWithM (intEq sym) x y
        andAllOf sym folded eq
       else
        return $ falsePred sym

    --------------------------------------------------------------------
    -- Text

    TextLit txt -> return txt
    AssignmentText nm v -> do
      Text.pack . (++"\n") . show <$> (ppValue <$> (Text.unpack <$> evalSub nm) <*> evalSub v)
    ShowValue _bt x_expr -> do
      x <- evalSub x_expr
      return $! Text.pack (show (printSymExpr x))

    ---------------------------------------------------------------------
    -- Introspection

    IsConcrete b v -> do
      x <- baseIsConcrete sym b =<< evalSub v
      return $! if x then truePred sym else falsePred sym
