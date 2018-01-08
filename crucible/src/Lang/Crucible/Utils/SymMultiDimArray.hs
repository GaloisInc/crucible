{-|
Module     : Lang.Crucible.Utils.SymMultiDimArray
Copyright  : (c) Galois, Inc 2013-2016
License    : BSD3
Maintainer : Joe Hendrix <jhendrix@galois.com>

Define symbolic multidimensional arrays, and translations between
these and "concrete" multidimensional arrays.  The difference is that
symbolic arrays are directly backed by symbolic formulae inside solvers
that support a theory of arrays or a theory of uninterpreted functions.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}

module Lang.Crucible.Utils.SymMultiDimArray
  ( -- * SymMultiDimArray
    SymMultiDimArray(..)
  , totalSize
  , rowVector
  , freshSymArray
  , dim
  , symDimToVector
  , symDim
  , symDimN
  , mkSymDimN
  , checkSymbolicAndConcreteDimsMatch
  , dimsEq
  , symTerms
  , encoder
  , encoderFromValue
  , muxArray
  , Lang.Crucible.Utils.SymMultiDimArray.singleton
  , asSingleton
  , lookup
  , lookupConcrete
  , lookupArray
  , update
  , internalizeArray
  , internalizeArray'
  , externalizeArray
  , resize
  , zeroValue
  , Lang.Crucible.Utils.SymMultiDimArray.isEq
  , Lang.Crucible.Utils.SymMultiDimArray.map
  , mapBinToConstL
  , mapBinToConstR
  , arrayEntriesTrue
  , Lang.Crucible.Utils.SymMultiDimArray.replicate
    -- * NatExpr
  , NatExpr(..)
  , unwrapNatExpr
  , onlyNatTypeRepr
    -- * NonEmptyAssignment
  , NonEmptyAssignment(..)
  , concreteDimToSymbolic
  ) where

import           Control.Exception (assert)
import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.State.Strict
import           Data.Foldable
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern Empty, pattern (:>) )
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Numeric.Natural

import qualified Lang.MATLAB.MultiDimArray as MDA

import           Lang.Crucible.BaseTypes
import           Lang.Crucible.MATLAB.Intrinsics.Solver
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Utils.Complex
import           Lang.Crucible.Utils.OnlyNatRepr
import qualified Lang.Crucible.Utils.Hashable as Hash

import           Prelude hiding (lookup, map)

--------------------------------------------------------------------------------
-- General purpose utilities

-- | Returns some "zero" value for a given solver type.
zeroValue :: IsExprBuilder sym => sym -> BaseTypeRepr tp -> IO (SymExpr sym tp)
zeroValue sym tp0 =
  case tp0 of
    BaseBoolRepr -> return $! falsePred sym
    BaseBVRepr w -> bvLit sym w 0
    BaseNatRepr  -> natLit sym 0
    BaseIntegerRepr -> intLit sym 0
    BaseRealRepr    -> realLit sym 0
    BaseComplexRepr -> mkComplexLit sym (0 :+ 0)
    BaseStructRepr ctx -> mkStruct sym =<< traverseFC (zeroValue sym) ctx
    BaseArrayRepr idx tp -> constantArray sym idx =<< zeroValue sym tp

-- | Return predicate that holds if all dimensions are equal.
dimsEq :: IsExprBuilder sym
            => sym
            -> V.Vector (SymNat sym)
            -> V.Vector (SymNat sym)
            -> IO (Pred sym)
dimsEq sym x y
  | V.length x < V.length y = do
    p <- andAllOf sym folded =<< V.zipWithM (natEq sym) x y
    one <- natLit sym 1
    q <- allEqNat sym (V.drop (V.length x) y) one
    andPred sym p q
  | V.length y < V.length x = do
    p <- andAllOf sym folded =<< V.zipWithM (natEq sym) x y
    one <- natLit sym 1
    q <- allEqNat sym (V.drop (V.length y) x) one
    andPred sym p q
  | otherwise = do
    andAllOf sym folded =<< V.zipWithM (natEq sym) x y

-- | Convert a vector to some assignment
vectorToSomeAssignment :: (a -> Some f) ->  V.Vector a -> Some (Ctx.Assignment f)
vectorToSomeAssignment f v = Ctx.generateSome (V.length v) g
  where g i = f e
          where Just e = v V.!? i

--------------------------------------------------------------------------------
-- NatExpr

-- | A parameterized type that is a base type.
data NatExpr f tp = tp ~ BaseNatType => NatExpr (f BaseNatType)

-- | Extract the underyling nat type from a 'NatExpr'
unwrapNatExpr :: NatExpr f tp -> f BaseNatType
unwrapNatExpr (NatExpr v) = v

onlyNatTypeRepr :: NatExpr f tp
                -> OnlyNatRepr tp
onlyNatTypeRepr = (\(NatExpr _) -> OnlyNatRepr)

natTypeRepr :: NatExpr f c
            -> BaseTypeRepr c
natTypeRepr = \(NatExpr _) -> BaseNatRepr

--------------------------------------------------------------------------------
-- NonEmptyAssignment

-- | This denotes an assignment where the only non fact is the assignment is
-- nonempty.
data NonEmptyAssignment f
  = forall l r
  . NonEmptyAssignment !(Ctx.Assignment f (l Ctx.::> r))

--------------------------------------------------------------------------------
-- SymMultiDimArray

-- | A value of type 'SymMultiDimArray f tp' is a multidimensional Matlab
-- array.
--
-- Mathematically, we model the dimensions of an array 'a' as a function
-- 'dim(a)' from natural numbers to natural numbers.  The number of
-- dimensions in an array is the largest index 'i' such that 'dim(a)(i)'
-- is not '1'.
data SymMultiDimArray (f :: BaseType -> *) tp
   = forall idx itp
   . SymMultiDimArray !(Ctx.Assignment (NatExpr f) (idx Ctx.::> itp))
                      !(f (BaseArrayType (idx Ctx.::> itp) tp))

-- | Return the dimensions of a symbolic array as a non-empty assignment
dim :: SymMultiDimArray f tp -> NonEmptyAssignment (NatExpr f)
dim (SymMultiDimArray sizes _) = NonEmptyAssignment sizes

-- | Convert dimensions to a vector.
symDimToVector :: NonEmptyAssignment (NatExpr f) -> V.Vector (f BaseNatType)
symDimToVector (NonEmptyAssignment d) = d `Ctx.toVector` unwrapNatExpr

-- | Return the dimensions of a symbolic array as a vector.
symDim :: SymMultiDimArray f tp -> V.Vector (f BaseNatType)
symDim a = symDimToVector (dim a)

instance FunctorFC SymMultiDimArray where
  fmapFC = fmapFCDefault

instance FoldableFC SymMultiDimArray where
  foldMapFC = foldMapFCDefault

instance TraversableFC SymMultiDimArray where
  traverseFC f (SymMultiDimArray sd a) = do
    SymMultiDimArray <$> traverseFC (\(NatExpr e) -> NatExpr <$> f e) sd
                     <*> f a

-- | Return total number of elements in the array.
totalSize :: IsExprBuilder sym
          => sym
          -> SymMultiDimArray (SymExpr sym) tp
          -> IO (SymNat sym)
totalSize sym (SymMultiDimArray sizes _) = do
  foldrFC (\(NatExpr v) r -> natMul sym v =<< r) (natLit sym 1) sizes

-- | Get symbolic dimensions with given number of elements.
symDimN :: IsSymInterface sym
        => sym
        -> Natural
        -> SymMultiDimArray (SymExpr sym) tp
        -> IO (V.Vector (SymNat sym))
symDimN sym n0 a = mkSymDimN sym n0 (dim a)

-- | Get symbolic dimensions with given number of elements.
mkSymDimN :: IsSymInterface sym
          => sym
          -> Natural -- ^ Number of elements in vector
          -> NonEmptyAssignment (NatExpr (SymExpr sym))
          -> IO (V.Vector (SymNat sym))
mkSymDimN sym n0 (NonEmptyAssignment d)
  | n0 <= 0 =
      error "symDimN should be positive"
  | v_len == n =
      return $! v
  | v_len < n = do
      one <- natLit sym 1
      return $! v V.++ V.replicate (n - v_len) one
  | otherwise = assert (v_len > n) $ do
      -- Take elements before.
      let v_sub = V.take (n-1) v
      -- Multiply last elements together
      let Just e = v V.!? (n-1)
      v_last <- foldlM (natMul sym) e (V.drop n v)
      return $! V.snoc v_sub v_last
  where v = d `Ctx.toVector` unwrapNatExpr
        n = fromIntegral n0
        v_len = V.length v

-- | Create a row vector.
rowVector :: IsSymInterface sym
          => sym
          -> SymNat sym
          -> V.Vector (SymExpr sym tp)
          -- ^ Entries in the vector.
          -> SymExpr sym tp
          -- ^ Default value for other values.
          -> IO (SymMultiDimArray (SymExpr sym) tp)
rowVector sym sn v def = do
  one <- natLit sym 1
  -- Add default to beginning of list as indices are 1-based.
  let entry_fn i = Hash.mapInsert j e
        where j = Ctx.empty Ctx.:> NatIndexLit 1
                            Ctx.:> NatIndexLit (fromIntegral i)
              Just e = v V.!? (i-1)

  let tps = Ctx.empty Ctx.:> BaseNatRepr
                      Ctx.:> BaseNatRepr

  let entry_map = foldr' entry_fn Hash.mapEmpty [1..V.length v]
  a <-  arrayFromMap sym tps entry_map def

  let idxTypes = Ctx.empty Ctx.:> NatExpr one
                           Ctx.:> NatExpr sn
  return $! SymMultiDimArray idxTypes a

replicateInt :: Int -> f (tp :: k) -> Some (Ctx.Assignment f)
replicateInt n v
  | n <= 0 = Some Ctx.empty
  | otherwise =
      case replicateInt (n-1) v of
        Some a -> Some (a Ctx.:> v)

onlyNatToBaseRepr :: OnlyNatRepr tp -> BaseTypeRepr tp
onlyNatToBaseRepr OnlyNatRepr = BaseNatRepr

mkArrayType :: Ctx.Assignment OnlyNatRepr (idx Ctx.::> itp)
            -> BaseTypeRepr tp
            -> BaseTypeRepr (BaseArrayType (idx Ctx.::> itp) tp)
mkArrayType i r = BaseArrayRepr (fmapFC onlyNatToBaseRepr i) r

mkArrayType' :: Ctx.Assignment (NatExpr f) (idx Ctx.::> itp)
             -> BaseTypeRepr tp
             -> BaseTypeRepr (BaseArrayType (idx Ctx.::> itp) tp)
mkArrayType' i r = BaseArrayRepr (fmapFC (\(NatExpr _) -> BaseNatRepr) i) r

-- | Create the symbolic dimensions from a concrete dimensions
concreteDimToSymbolic :: IsExprBuilder sym
                      => sym
                      -> MDA.ArrayDim
                      -> IO (NonEmptyAssignment (NatExpr (SymExpr sym)))
concreteDimToSymbolic sym d = do
  dims <- traverse (natLit sym) (V.fromList (MDA.asDimList d))
  case vectorToSomeAssignment (\e -> Some (NatExpr e)) dims of
    Some a -> pure $!
      case Ctx.viewSize (Ctx.size a) of
        Ctx.ZeroSize -> error "concreteDimToSymbolic encountered illegal case."
        Ctx.IncSize{} -> NonEmptyAssignment a

-- | Create a symbolic multi-dim array with concrete dimensions.
freshSymArray :: IsSymInterface sym
              => sym
              -> SolverSymbol
              -> MDA.ArrayDim
              -> BaseTypeRepr tp
              -> IO (SymMultiDimArray (SymExpr sym) tp)
freshSymArray sym nm d btp = do
  NonEmptyAssignment d_ctx <- concreteDimToSymbolic sym d
  let tp = mkArrayType' d_ctx btp
  SymMultiDimArray d_ctx <$> freshConstant sym nm tp

symTerms :: SymMultiDimArray f tp -> Set.Set (Some f)
symTerms (SymMultiDimArray _ a) = Set.singleton (Some a)

smdaToExpr :: Ctx.Assignment OnlyNatRepr (idx Ctx.::> itp)
           -> SymMultiDimArray f tp
           -> IO (f (BaseArrayType (idx Ctx.::> itp) tp))
smdaToExpr idxTypes (SymMultiDimArray atp a) =
  case testEquality idxTypes (fmapFC onlyNatTypeRepr atp) of
    Just Refl -> return a
    Nothing -> fail "The simulator does not support remapping indices."

-- | Returns a encoder for a symbolic array with fixed dimensions.
encoder :: IsExprBuilder sym
        => MDA.ArrayDim
        -> BaseTypeRepr tp
        -> Some (SymEncoder sym (SymMultiDimArray (SymExpr sym) tp))
encoder d tp = do
  case replicateInt (MDA.dimCount d) OnlyNatRepr of
    Some idxTypes -> do
      let n = Ctx.size idxTypes
      case Ctx.viewSize n of
        Ctx.ZeroSize -> error $ "SMDA.encoder expected multiple dimensions"
        Ctx.IncSize _ -> do
          let fromExpr sym a = do
                let v = MDA.asDimVectorN (fromIntegral (Ctx.sizeInt n)) d
                sd <- Ctx.generateM n $ \i -> do
                        case idxTypes Ctx.! i of
                          OnlyNatRepr -> NatExpr <$> natLit sym e
                            where Just e = v V.!? Ctx.indexVal i
                return $! SymMultiDimArray sd a
          Some $ SymEncoder { symEncoderType = mkArrayType idxTypes tp
                            , symFromExpr    = fromExpr
                            , symToExpr      = \_ -> smdaToExpr idxTypes
                            }

-- | Returns a encoder for a symbolic array with the same dimensions as the
-- input.
encoderFromValue :: BaseTypeRepr tp
                 -> SymMultiDimArray (SymExpr sym) tp
                 -> Some (SymEncoder sym (SymMultiDimArray (SymExpr sym) tp))
encoderFromValue tp (SymMultiDimArray sd _) =
    Some $ SymEncoder { symEncoderType = array_tp
                      , symFromExpr    = fromExpr
                      , symToExpr      = \_ -> smdaToExpr idx_types
                      }
  where idx_types    = fmapFC onlyNatTypeRepr sd
        array_tp     = BaseArrayRepr (fmapFC onlyNatToBaseRepr idx_types) tp
        fromExpr _ a = return $! SymMultiDimArray sd a

-- | Create an where every element has the same value.
replicate :: IsSymInterface sym
          => sym
          -> V.Vector (SymNat sym) -- ^ Dimensions
          -> SymExpr sym bt
          -> IO (SymMultiDimArray (SymExpr sym) bt)
replicate sym d x = assert (V.length d > 0) $ do
  case vectorToSomeAssignment (\e -> Some (NatExpr e)) d of
    Some sd ->
      case Ctx.viewSize (Ctx.size sd) of
        Ctx.ZeroSize -> error $ "SymMultiDimArray.replicate given illegal dimensions."
        Ctx.IncSize{} -> do
          a <- constantArray sym (fmapFC natTypeRepr sd) x
          return $! SymMultiDimArray sd a

-- | Return true if all values in vector have the given value.
allEqNat :: IsExprBuilder sym
         => sym
         -> V.Vector (SymNat sym)
         -> SymNat sym -- ^ Value entries should have.
         -> IO (Pred sym)
allEqNat sym v n = andAllOf sym folded =<< traverse (natEq sym n) v

-- | Create a singleton array for the expression.
singleton :: IsExprBuilder sym
          => sym
          -> SymExpr sym tp
          -> IO (SymMultiDimArray (SymExpr sym) tp)
singleton sym e = do
  n1 <- NatExpr <$> natLit sym 1
  let sd  = Ctx.empty Ctx.:> n1 Ctx.:> n1
  let tps = Ctx.empty Ctx.:> BaseNatRepr Ctx.:> BaseNatRepr
  a <- constantArray sym tps e
  return $! SymMultiDimArray sd a

-- | Return partial expression containing the value stored in an array if this
-- is a singleton array
asSingleton :: IsExprBuilder sym
            => sym
            -> SymMultiDimArray (SymExpr sym) bt
            -> IO (PartExpr (Pred sym) (SymExpr sym bt))
asSingleton sym x@(SymMultiDimArray idxTypes a) = do
  one <- natLit sym 1
  p <- allEqNat sym (symDim x) one
  case asConstantPred p of
    Just False ->
      return Unassigned
    _ -> do
      let idx = fmapFC (\(NatExpr _) -> one) idxTypes
      PE p <$> arrayLookup sym a idx

-- | Add assertion checking that the symbolic and concrete array dimensions are
-- equal.
checkSymbolicAndConcreteDimsMatch :: IsSymInterface sym
                                  => sym
                                  -> String -- ^ Name of array
                                  -> NonEmptyAssignment (NatExpr (SymExpr sym))
                                  -- ^ The symbolic dimensions of array to compare.
                                  -> MDA.ArrayDim
                                  -- ^ The concrete dimensions of array to compare.
                                  -> IO ()
checkSymbolicAndConcreteDimsMatch sym nm sd d1 = do
  let sym_d = symDimToVector sd
  let expected = MDA.asDimVectorN (fromIntegral (V.length sym_d)) d1
  eqs <- V.zipWithM (\x y -> natEq sym x =<< natLit sym y) sym_d expected
  p <- andAllOf sym folded eqs
  addAssertion sym p $ GenericSimError $
    "Dimensions of " ++ nm ++ " does not match expected."

-- | Given one-based indices, and dimensions of the vector we are indexing, this
-- returns an equivalent vector of indices with at least as many indexes as
-- the sizes.
fixLength :: forall sym idx itp
           . IsExprBuilder sym
          => sym
          -> V.Vector (SymNat sym) -- Indices.
          -> Ctx.Assignment (NatExpr (SymExpr sym)) (idx Ctx.::> itp)
             -- ^ Sizes
          -> IO (Ctx.Assignment (SymExpr sym) (idx Ctx.::> itp))
fixLength sym idx sizes
    -- If th number of indices exceeds the dimensions, then we can
  | V.length idx >= Ctx.sizeInt (Ctx.size sizes) =
    return $! coerceIndex idx sizes
  | otherwise = assert (V.length idx > 0) $ do
    one <- natLit sym 1

    -- Get last index - 1.
    last_idx0 <- natSub sym (V.last idx) one

    flip evalStateT (V.init idx, last_idx0) $ do
      let n = Ctx.size sizes
      Ctx.generateM n $ \i -> do
        (idx_v,last_idx) <- get
        case sizes Ctx.! i of
          NatExpr sz
              -- If we are at end of list, then just get last element
            | Just _ <- testEquality i (Ctx.lastIndex n) -> do
                liftIO $ natAdd sym one last_idx

              -- If we are out of elements before but not at end of list.
            | V.null idx_v -> do
                last_idx'  <- liftIO $ natDiv sym last_idx sz
                put (idx_v, last_idx')
                liftIO $ natAdd sym one =<< natMod sym last_idx sz
            | otherwise -> do
                put (V.tail idx_v, last_idx)
                return (V.head idx_v)

-- | Given an index vector, and an assignment of nat repts where
-- the index vector is not shorter than the nat reprs.
coerceIndex :: V.Vector (f BaseNatType) -- Indices.
            -> Ctx.Assignment (NatExpr g) ctx
            -> Ctx.Assignment f ctx
coerceIndex v a = assert (V.length v >= Ctx.sizeInt (Ctx.size a)) $
  Ctx.generate (Ctx.size a) $ \i ->
    case a Ctx.! i of
      NatExpr{} -> e
        where j = Ctx.indexVal i
              Just e = v V.!? j

-- | This lookups into a symbolic array based on symbolic indices.
--
-- In the single dimension case, the result has the same shape as its input,
-- otherwise the ith dimension of the result has the same length as the
-- total number of entries in the ith array in the input.
lookupArray :: IsSymInterface sym
            => sym
            -> SymMultiDimArray (SymExpr sym) bt -- ^ Symbolic multi dim array.
            -> V.Vector (SymMultiDimArray (SymExpr sym) BaseNatType) -- ^ Indices
            -> IO (SymMultiDimArray (SymExpr sym) bt)
lookupArray sym a idx_vec
  | V.length idx_vec == 0 = error "lookupArray expects at least one index"
  | V.length idx_vec == 1 = do
      fn <- inlineDefineFun sym emptySymbol knownRepr $ \idx -> do
        lookup1 sym a idx
      let Just e = idx_vec V.!? 0
      map sym fn e
  | otherwise = do
    -- Create idx vector from indices
    let getExpr i = Some (NatExpr e)
          where Just e = idx_vec V.!? i
    case Ctx.generateSome (V.length idx_vec) getExpr of
      Some idx_vec' -> do
        case idx_vec' of
          Empty -> error "Internal: lookupArray given bad size"
          _ :> _ -> do
            sizes_ctx <- traverseFC (\(NatExpr i) -> NatExpr <$> totalSize sym i) idx_vec'

            -- Create bound variables used in array.
            idx_idx_vars <-
              traverseFC (\(NatExpr _) -> freshBoundVar sym emptySymbol knownRepr) idx_vec'
            let n = Ctx.size idx_vec'
            -- Lookup the index to use for each position.
            idx_exprs <- V.generateM (Ctx.sizeInt n) $ \i -> do
              case Ctx.intIndex i n of
                Nothing -> error "Internal: bad index given to lookupArray"
                Just (Some j) ->
                  case idx_vec' Ctx.! j of
                    NatExpr v -> lookup1 sym v idx
                      where idx = varExpr sym (idx_idx_vars Ctx.! j)
            -- Create symbolic array.
            res_val <- lookup sym a idx_exprs
            fn <- definedFn sym emptySymbol idx_idx_vars res_val (\_ -> True)
            result <- arrayFromFn sym fn
            return $! SymMultiDimArray sizes_ctx result

-- | Lookup a single entry in an array.
lookup ::  IsExprBuilder sym
       => sym
       -> SymMultiDimArray (SymExpr sym) bt -- ^ Multi dim array.
       -> V.Vector (SymNat sym) -- ^ Indices
       -> IO (SymExpr sym bt)
lookup sym (SymMultiDimArray idxTypes a) i = do
  i' <- fixLength sym i idxTypes
  arrayLookup sym a i'


-- | Lookup a single entry in an array.
lookup1 ::  IsExprBuilder sym
        => sym
        -> SymMultiDimArray (SymExpr sym) bt -- ^ Multi dim array.
        -> SymNat sym -- ^ Indices
        -> IO (SymExpr sym bt)
lookup1 sym (SymMultiDimArray idxTypes a) i = do
  i' <- fixLength sym (V.singleton i) idxTypes
  arrayLookup sym a i'

-- | Lookup a specific index in a symbolic array.
--
-- This function assumes that the indices are valid.
lookupConcrete :: IsExprBuilder sym
                  => sym
                  -> SymMultiDimArray (SymExpr sym) bt -- ^ Array to look up value in.
                  -> MDA.Index -- ^ Index to lookup
                  -> IO (SymExpr sym bt)
lookupConcrete sym (SymMultiDimArray idxTypes a) idx = do
  idx' <- traverse (natLit sym) (MDA.indexToVector idx)
  idx2 <- fixLength sym idx' idxTypes
  arrayLookup sym a idx2

-- | Update an array at the given index.
update :: IsSymInterface sym
       => sym
       -> SymMultiDimArray (SymExpr sym) bt
       -> V.Vector (SymNat sym)
       -> SymExpr sym bt
       -> IO (SymMultiDimArray (SymExpr sym) bt)
update sym (SymMultiDimArray idxTypes a) i v = do
  i' <- fixLength sym i idxTypes
  SymMultiDimArray idxTypes <$> arrayUpdate sym a i' v

-- | Resize a symbolic array.
--
-- Note: Currently we do not yet have support in the symbolic backend to support
-- resizing, so all this does is check that the dimensions haven't changed and
-- continue.
resize :: forall sym bt
        . IsSymInterface sym
       => sym
       -> SymMultiDimArray (SymExpr sym) bt
          -- ^ Symbolic array to resize.
       -> V.Vector (SymNat sym)
          -- ^ New dimensions (already asserted to be at least as large as previous).
       -> SymExpr sym bt
          -- ^ Default value for new entries.
       -> IO (SymMultiDimArray (SymExpr sym) bt)
resize sym x new_dims _ = do
  addAssertionM sym (dimsEq sym (symDim x) new_dims) $
          GenericSimError "Symbolic arrays cannot be resized."
  -- Return original.
  return $! x

muxSymDims :: forall sym c
           .  IsExprBuilder sym
           => sym
           -> Pred sym
           -> Ctx.Assignment (NatExpr (SymExpr sym)) c
           -> Ctx.Assignment (NatExpr (SymExpr sym)) c
           -> IO (Ctx.Assignment (NatExpr (SymExpr sym)) c)
muxSymDims sym p = Ctx.zipWithM f
  where f :: NatExpr (SymExpr sym) tp
          -> NatExpr (SymExpr sym) tp
          -> IO (NatExpr (SymExpr sym) tp)
        f (NatExpr x) (NatExpr y) = NatExpr <$> natIte sym p x y


muxArray :: IsExprBuilder sym
         => sym
         -> Pred sym
         -> SymMultiDimArray (SymExpr sym) tp
         -> SymMultiDimArray (SymExpr sym) tp
         -> IO (SymMultiDimArray (SymExpr sym) tp)
muxArray sym p (SymMultiDimArray dim_x x) (SymMultiDimArray dim_y y) =
  case testEquality (fmapFC natTypeRepr dim_x) (fmapFC natTypeRepr dim_y) of
    Just Refl -> do
      dim_z <- muxSymDims sym p dim_x dim_y
      SymMultiDimArray dim_z <$> arrayIte sym p x y
    Nothing -> do
      fail $ "Cannot mux symbolic arrays with dissimiliar numbers of indices."

-- | Convert a MDA index to an index lit assignment
mdaIndexToConcrete :: Ctx.Assignment OnlyNatRepr ctx
                      -- ^ Types used for index purposes.
                   -> MDA.Index
                   -> Ctx.Assignment IndexLit ctx
mdaIndexToConcrete tps idx = Ctx.generate (Ctx.size tps) $ \i ->
  let v = fromMaybe 1 $ idx MDA.!!? Ctx.indexVal i
   in case tps Ctx.! i of
        OnlyNatRepr -> NatIndexLit v

mdaIndexToSymbolic :: IsExprBuilder sym
                   => sym
                   -> Ctx.Assignment OnlyNatRepr ctx
                   -> MDA.Index
                   -> IO (Ctx.Assignment (SymExpr sym) ctx)
mdaIndexToSymbolic sym tps idx =
  traverseFC (indexLit sym) (mdaIndexToConcrete tps idx)


-- | Builds a hashmap with the concrete index assignments.
mdaToSymbolicIndexMap :: HashableF f
                      => Ctx.Assignment OnlyNatRepr idx
                         -- ^ Nat repr used for defining number of indices.
                      -> MDA.MultiDimArray (f tp)
                      -> Hash.Map IndexLit idx f tp
mdaToSymbolicIndexMap idxTypes a = fst $
  flip execState (Hash.mapEmpty,0) $ do
    let d = MDA.dim a
    let v = MDA.mdVec a
    MDA.forIndicesM_ d $ \i -> do
      let idx = mdaIndexToConcrete idxTypes i
      modify $ \(m,c) ->
        let Just e = v V.!? c
         in ((,) $! Hash.mapInsert idx e m) $! c+1


-- | Convert a multi-dimensional array to a symbolic array.
internalizeArray
  :: IsExprBuilder sym
  => sym
  -> BaseTypeRepr bt
     -- ^ Type repr used for getting default value when creating sym array.
  -> MDA.MultiDimArray (SymExpr sym bt)
     -- ^ Multi dimensional array
  -> IO (SymMultiDimArray (SymExpr sym) bt)
internalizeArray sym tp arr = do
  NonEmptyAssignment sd <- concreteDimToSymbolic sym (MDA.dim arr)
  fmap (SymMultiDimArray sd) $ internalizeArray' sym (fmapFC onlyNatTypeRepr sd) tp arr

-- | Internalize a multi-dimensional array into a symbolic array expression.
internalizeArray'
  :: IsExprBuilder sym
  => sym
  -> Ctx.Assignment OnlyNatRepr (idx Ctx.::> itp)
     -- ^ Index types (used for defining array)
  -> BaseTypeRepr bt
     -- ^ Default value to use for entries when creating sym array.
  -> MDA.MultiDimArray (SymExpr sym bt)
     -- ^ Multi dimensional array
  -> IO (SymExpr sym (BaseArrayType (idx Ctx.::> itp) bt))
internalizeArray' sym idxTypes tp arr = do
  let entryMap = mdaToSymbolicIndexMap idxTypes arr
  case Hash.mapMinView entryMap of
    Nothing -> do
      constantArray sym (fmapFC toBaseTypeRepr idxTypes) =<< zeroValue sym tp
    Just (c,m) -> do
      a <- constantArray sym (fmapFC toBaseTypeRepr idxTypes) c
      arrayUpdateAtIdxLits sym m a

-- | Convert a sym array to a concrete array.
externalizeArray
  :: IsExprBuilder sym
  => sym
  -> SymMultiDimArray (SymExpr sym) bt
  -> IO (MDA.MultiDimArray (SymExpr sym bt))
externalizeArray sym x@(SymMultiDimArray dims arr) = do
  case traverse asNat (symDim x) of
    Nothing -> do
      fail $ "Converting a symbolic array to a concrete array requires that the "
          ++ "dimensions are concrete."
    Just concrete_d -> do
      let d = MDA.fromDimList (V.toList concrete_d)
      MDA.generateM d $ \i -> do
        let idxTypes = fmapFC onlyNatTypeRepr dims
        idx <- mdaIndexToSymbolic sym idxTypes i
        arrayLookup sym arr idx

-- | Returns true if both arrays are equal.  This holds if their dimensions are
-- equal, and each element is equal.
--
-- This will first try to figure out concrete dimensions for one or both of the
-- arrays.  If it can, then it will check that all elements are equal.  Otherwise,
-- this will check that the arrays are equal on all index values using the 'arrayEq'
-- predicate.  This may result in arrays that are only equal on values outside their
-- range, which would lead to check_sat returning models that do not satisfy the
-- expected constraints.
isEq :: MatlabSymbolicArrayBuilder sym
        => sym
        -> SymFn sym (Ctx.EmptyCtx Ctx.::> bt Ctx.::> bt) BaseBoolType
        -> SymMultiDimArray (SymExpr sym) bt
        -> SymMultiDimArray (SymExpr sym) bt
        -> IO (Pred sym)
isEq sym elt_pred x@(SymMultiDimArray xi xs) y@(SymMultiDimArray yi ys) = do
  -- Get predicate asserting dimensions are equal.
  case fmapFC natTypeRepr xi `testEquality` fmapFC natTypeRepr yi of
    Nothing ->
      fail $ "Tool does not yet support coercisions between arrays with different types."
    Just Refl -> do
      dims_eq <- dimsEq sym (symDim x) (symDim y)
      case asConstantPred dims_eq of
        -- Return false if size predicate is false.
        Just False ->
          return $! falsePred sym
        _ -> do
          isIndex <- do
            let tps = fmapFC onlyNatTypeRepr xi
            let bnds = fmapFC (\(NatExpr v) -> v) xi
            mkMatlabSolverFn sym $ IndicesInRange tps bnds

          let args = Ctx.empty Ctx.:> ArrayResultWrapper xs
                               Ctx.:> ArrayResultWrapper ys
          eq_array <- arrayMap sym elt_pred args
          array_eq <- arrayTrueOnEntries sym isIndex eq_array
          andPred sym dims_eq array_eq

-- | Apply function to each element in array.
--
-- This satisfies the constraint that
--
--   '(map f a)[i] = f (a[i])'
map :: IsExprBuilder sym
    => sym
    -> SymFn sym (Ctx.EmptyCtx Ctx.::> tp) ret
    -> SymMultiDimArray (SymExpr sym) tp
    -> IO (SymMultiDimArray (SymExpr sym) ret)
map sym f (SymMultiDimArray idx a) =
  SymMultiDimArray idx <$> arrayMap sym f (Ctx.singleton (ArrayResultWrapper a))

-- | Apply a binary function to a constant and elements in an array.
--
-- This satisfies the constraint that
--
--   '(mapBinToConstL f c a)[i] = f c (a[i])'
mapBinToConstL :: IsExprBuilder sym
                 => sym
                 -> SymFn sym (Ctx.EmptyCtx Ctx.::> xtp Ctx.::> ytp) ztp
                 -> SymExpr sym xtp
                 -> SymMultiDimArray (SymExpr sym) ytp
                 -> IO (SymMultiDimArray (SymExpr sym) ztp)
mapBinToConstL sym f c (SymMultiDimArray sizes a) = do
  ca <- constantArray sym (fmapFC natTypeRepr sizes) c
  let args = Ctx.empty Ctx.:> ArrayResultWrapper ca
                       Ctx.:> ArrayResultWrapper a
  SymMultiDimArray sizes <$> arrayMap sym f args

-- | Apply a binary function to a constant and elements in an array.
--
-- This satisfies the constraint that
--
--   '(mapBinToConstL f a c)[i] = f (a[i]) c'
mapBinToConstR :: IsExprBuilder sym
                 => sym
                 -> SymFn sym (Ctx.EmptyCtx Ctx.::> xtp Ctx.::> ytp) ztp
                 -> SymMultiDimArray (SymExpr sym) xtp
                 -> SymExpr sym ytp
                 -> IO (SymMultiDimArray (SymExpr sym) ztp)
mapBinToConstR sym f (SymMultiDimArray idx a) c = do
  ca <- constantArray sym (fmapFC (\(NatExpr _) -> BaseNatRepr) idx) c
  let args = Ctx.empty Ctx.:> ArrayResultWrapper a
                       Ctx.:> ArrayResultWrapper ca
  SymMultiDimArray idx <$> arrayMap sym f args


-- | Return true if array if the given proposition holds on all elements in the array.
arrayEntriesTrue :: MatlabSymbolicArrayBuilder sym
                  => sym
                  -> SymMultiDimArray (SymExpr sym) BaseBoolType
                  -> IO (Pred sym)
arrayEntriesTrue sym (SymMultiDimArray dims a) = do
  let tps = fmapFC onlyNatTypeRepr dims
  let bnds = fmapFC (\(NatExpr v) -> v) dims
  isIndex <- mkMatlabSolverFn sym $ IndicesInRange tps bnds
  arrayTrueOnEntries sym isIndex a
