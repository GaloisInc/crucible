{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
module SemMC.Util
  ( -- * Misc
    groundValToExpr
  , exprToGroundVal
  , showGroundValue
  , showGroundValues
  , concreteToGVW
  , makeSymbol
  , mapFReverse
  , sequenceMaybes
  , allBoundVars
  , extractUsedLocs
  , mapFMapBothM
  , filterMapF
  , fromJust'
  , withRounding
  , roundingModeToBits
    -- * Async
  , asyncLinked
  , withAsyncLinked
    -- * Reexports
  , module SemMC.Log
  ) where

import           Control.Monad.ST ( runST )
import qualified Data.HashTable.Class as H
import           Data.Maybe ( fromMaybe )
import           Data.Parameterized.Context
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr (knownNat)
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Set as Set
import           Text.Printf ( printf )

import qualified Data.Map as Map
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC


import qualified UnliftIO as U
import qualified Control.Exception as E

import           What4.BaseTypes
import qualified What4.Expr.Builder as B
import qualified What4.Expr.GroundEval as GE
import qualified What4.Interface as S
import           What4.Symbol ( SolverSymbol, userSymbol )
import qualified What4.Utils.Hashable as Hash
import qualified What4.Concrete as W

import           SemMC.Log

----------------------------------------------------------------
-- * Async

-- | Fork an async action that is linked to the parent thread, but can
-- be safely 'U.cancel'd without also killing the parent thread.
--
-- Note that if your async doesn't return unit, then you probably want
-- to 'U.wait' for it instead, which eliminates the need for linking
-- it. Also, if you plan to cancel the async near where you fork it,
-- then 'withAsyncLinked' is a better choice than using this function
-- and subsequently canceling, since it ensures cancellation.
--
-- See https://github.com/simonmar/async/issues/25 for a perhaps more
-- robust, but also harder to use version of this. The linked version
-- is harder to use because it requires a special version of @cancel@.
asyncLinked :: (U.MonadUnliftIO m) => m () -> m (U.Async ())
asyncLinked action = do
  -- We use 'U.mask' to avoid a race condition between starting the
  -- async and running @action@. Without 'U.mask' here, an async
  -- exception (e.g. via 'U.cancel') could arrive after
  -- @handleUnliftIO@ starts to run but before @action@ starts.
  U.mask $ \restore -> do
  a <- U.async $ handleUnliftIO (\E.ThreadKilled -> return ()) (restore action)
  restore $ do
  U.link a
  return a

-- | A version of 'U.withAsync' that safely links the child. See
-- 'asyncLinked'.
withAsyncLinked :: (U.MonadUnliftIO m) => m () -> (U.Async () -> m a) -> m a
withAsyncLinked child parent = do
  U.mask $ \restore -> do
  U.withAsync (handleUnliftIO (\E.ThreadKilled -> return ()) $ restore child) $ \a -> restore $ do
  U.link a
  parent a

-- A 'U.MonadUnliftIO' version of 'Control.Exception.handle'.
--
-- The 'U.handle' doesn't catch async exceptions, because the
-- @unliftio@ library uses the @safe-execeptions@ library, not
-- @base@, for it exception handling primitives. This is very
-- confusing if you're not expecting it!
handleUnliftIO :: (U.MonadUnliftIO m, U.Exception e)
               => (e -> m a) -> m a -> m a
handleUnliftIO h a = U.withUnliftIO $ \u ->
  E.handle (U.unliftIO u . h) (U.unliftIO u a)

----------------------------------------------------------------
-- * Uncategorized

-- | Try converting any 'String' into a 'SolverSymbol'. If it is an invalid
-- symbol, then error.
makeSymbol :: String -> SolverSymbol
makeSymbol name = case userSymbol sanitizedName of
                    Right symbol -> symbol
                    Left _ -> error $ printf "tried to create symbol with bad name: %s (%s)"
                                             name sanitizedName
  where
    sanitizedName = map (\c -> case c of ' ' -> '_'; '.' -> '_'; _ -> c) name






-- | Convert a 'GroundValue' (a primitive type that represents the given
-- Crucible type) back into a symbolic expression, just as a literal.
groundValToExpr :: forall sym tp.
                   (S.IsSymExprBuilder sym)
                => sym
                -> [Integer]
                -- ^ A list of relevant indices into memory
                -> BaseTypeRepr tp
                -> GE.GroundValue tp
                -> IO (S.SymExpr sym tp)
groundValToExpr sym _ BaseBoolRepr True = return (S.truePred sym)
groundValToExpr sym _ BaseBoolRepr False = return (S.falsePred sym)
groundValToExpr sym _ (BaseBVRepr w) val = S.bvLit sym w val
groundValToExpr sym _ BaseNatRepr val = S.natLit sym val
groundValToExpr sym _ BaseIntegerRepr val = S.intLit sym val
groundValToExpr sym _ BaseRealRepr val = S.realLit sym val
groundValToExpr sym _ (BaseFloatRepr fpp@(FloatingPointPrecisionRepr eb sb)) val
  | LeqProof <- leqTrans (LeqProof @1 @2) (leqProof (knownNat @2) eb)
  , LeqProof <- leqTrans (LeqProof @1 @2) (leqProof (knownNat @2) sb)
  , LeqProof <- leqAddPos eb sb
  = S.floatFromBinary sym fpp =<< S.bvLit sym (addNat eb sb) val
groundValToExpr sym _        BaseComplexRepr val = S.mkComplexLit sym val
groundValToExpr sym indices (BaseArrayRepr idxTp elemTp) (GE.ArrayConcrete base m) = do
  base' <- groundValToExpr sym indices elemTp base
  entries <- Hash.mkMap <$> traverse (groundValToExpr sym indices elemTp) m
  S.arrayFromMap sym idxTp entries base'

groundValToExpr sym indices (BaseArrayRepr idxs r) (GE.ArrayMapping f) = do
    -- Construct a default value to populate the array
    defaultValue <- f $ defaultInput idxs
    defaultExpr  <- groundValToExpr sym indices r defaultValue

    let indexVals = allGroundAssign idxs indices
        indexLits = fmap (mkIndex idxs) indexVals

    resultVals <- mapM f indexVals
    resultExprs <- mapM (groundValToExpr sym indices r) resultVals

--      :: Map.Map (Assignment S.IndexLit idx) (S.SymExpr sym xs)
    let arrayMap' = Map.fromList $ zip indexLits resultExprs

    S.arrayFromMap sym idxs (Hash.mkMap arrayMap') defaultExpr


  where
    defaultInput :: forall idx. Assignment BaseTypeRepr idx -> Assignment GE.GroundValueWrapper idx
    defaultInput Empty = Empty
    defaultInput (idxs' :> r') = defaultInput idxs' :> GE.GVW (GE.defaultValueForType r')


    mkIndex :: Assignment BaseTypeRepr idx'
            -> Assignment GE.GroundValueWrapper idx'
            -> Assignment S.IndexLit idx'
    mkIndex Empty Empty = Empty
    mkIndex (idx' :> BaseBVRepr n) (vals :> GE.GVW i) = mkIndex idx' vals :> S.BVIndexLit n i
    mkIndex (idx' :> BaseNatRepr)  (vals :> GE.GVW i) = mkIndex idx' vals :> S.NatIndexLit i
    mkIndex _                      _                  = error "Error creating index literal into an array: unsupported types"



groundValToExpr _ _ (BaseStructRepr _) _ = error "groundValToExpr: struct type isn't handled yet"
groundValToExpr _ _ (BaseStringRepr _) _ = error "groundValToExpr: string base types are not supported yet"


showGroundValue :: BaseTypeRepr b -> GE.GroundValue b -> String
showGroundValue BaseBoolRepr b = show b
showGroundValue BaseNatRepr n = show n
showGroundValue BaseIntegerRepr i = show i
showGroundValue BaseRealRepr r = show r
showGroundValue (BaseBVRepr _w) i = show i
showGroundValue (BaseFloatRepr _fpp) f = show f
showGroundValue BaseComplexRepr i = show i
showGroundValue (BaseStringRepr _) s = show s
showGroundValue (BaseArrayRepr _idx _b) _i = "No show instance for BaseArrayRepr"
showGroundValue (BaseStructRepr _ctx) _i = "No show instance for BaseStructType"

showGroundValues :: Assignment BaseTypeRepr idx -> Assignment GE.GroundValueWrapper idx -> String
showGroundValues Empty Empty = "Empty"
showGroundValues (rs :> r) (bs :> GE.GVW b) = showGroundValues rs bs ++ " :> " ++ showGroundValue r b




-- | Given a list of integers representing memory accesses, produce a list of all
-- tuples of such integersin the shape of idx.
--
-- For example, if idx = [BVRepr 32, BVRepr 32], then allGroundAssign idx ls is
-- equivalent to [(i,j) | i <- ls, j <- ls].
--
-- If idx represents data that are not bit vectors, allGroundAssign will throw
-- an error. 
allGroundAssign :: Assignment BaseTypeRepr idx 
                -> [Integer]
                -> [Assignment GE.GroundValueWrapper idx]
allGroundAssign Empty                 _ = [Empty]
allGroundAssign (idx :> BaseBVRepr _) indices = do
  vs <- allGroundAssign idx indices
  i <- indices
  return $ vs :> GE.GVW i
allGroundAssign _ _ = error "allGroundAssign is only defined for bit vectors"



-- | Support for converting symbolic expressions to ground values. 
exprToGroundVal :: forall sym tp.
                   S.IsSymExprBuilder sym
                => BaseTypeRepr tp
                -> S.SymExpr sym tp
                -> Maybe (GE.GroundValue tp)
exprToGroundVal BaseBoolRepr                 e = S.asConstantPred e
exprToGroundVal (BaseBVRepr _w)              e = S.asSignedBV e
exprToGroundVal BaseNatRepr                  e = S.asNat e 
exprToGroundVal BaseIntegerRepr              e = S.asInteger e
exprToGroundVal BaseRealRepr                _e = Nothing
exprToGroundVal (BaseFloatRepr _fpp)        _e = Nothing
exprToGroundVal BaseComplexRepr              e = S.asComplex e
exprToGroundVal (BaseArrayRepr _iTp _elmTp) _e = Nothing
exprToGroundVal (BaseStructRepr _r)          e = do
    v <- S.asStruct e
    traverseFC (\e' -> GE.GVW <$> exprToGroundVal @sym (S.exprType e') e') v
exprToGroundVal (BaseStringRepr _)           e = S.asString e

concreteToGVW :: W.ConcreteVal tp -> GE.GroundValueWrapper tp
concreteToGVW = GE.GVW . concreteToGroundVal

-- | Convert concrete values to ground values
concreteToGroundVal :: W.ConcreteVal tp -> GE.GroundValue tp
concreteToGroundVal (W.ConcreteBool b) = b
concreteToGroundVal (W.ConcreteNat n) = n
concreteToGroundVal (W.ConcreteInteger n) = n
concreteToGroundVal (W.ConcreteReal r) = r
concreteToGroundVal (W.ConcreteString s) = s
concreteToGroundVal (W.ConcreteComplex c) = c
concreteToGroundVal (W.ConcreteBV _ i) = i
concreteToGroundVal (W.ConcreteStruct ctx) = fmapFC (GE.GVW . concreteToGroundVal) ctx
concreteToGroundVal (W.ConcreteArray _idx def m) = GE.ArrayConcrete (concreteToGroundVal def) $ 
                                                     Map.fromList (concToGV' <$> Map.toList m)
  where
    concToGV' :: (Assignment W.ConcreteVal idx, W.ConcreteVal tp) 
              -> (Assignment S.IndexLit idx, GE.GroundValue tp)
    concToGV' (args,v) = (fmapFC concreteToIndexLit args, concreteToGroundVal v)

concreteToIndexLit :: W.ConcreteVal tp -> S.IndexLit tp
concreteToIndexLit (W.ConcreteNat n) = S.NatIndexLit n
concreteToIndexLit (W.ConcreteBV r i) = S.BVIndexLit r i
concreteToIndexLit v = error $ "Cannot turn conrete value of type " ++ show (W.concreteType v) ++ " into an IndexLit"


-- | Reverse a MapF, so that the old keys are the new values and the old values
-- are the new keys.
mapFReverse :: (OrdF value) => MapF.MapF key value -> MapF.MapF value key
mapFReverse = MapF.foldrWithKey (flip MapF.insert) MapF.empty

-- | Run the monadic actions in order, returning the first 'Just' value.
sequenceMaybes :: (Monad m) => [m (Maybe a)] -> m (Maybe a)
sequenceMaybes [] = return Nothing
sequenceMaybes (x : xs) = x >>= maybe (sequenceMaybes xs) (return . Just)

-- | Find all the bound variables in a symbolic expression.
allBoundVars :: B.Expr t tp -> Set.Set (Some (B.ExprBoundVar t))
allBoundVars e = runST (B.boundVars e >>= H.foldM f Set.empty)
  where f s (_, v) = return (Set.union s v)

-- | Given a map from location to bound variable, return all of the locations
-- that are actually used in an expression (along with their corresponding
-- variables).
extractUsedLocs :: forall t loc tp
                 . (OrdF loc)
                => MapF.MapF loc (B.ExprBoundVar t)
                -> B.Expr t tp
                -> MapF.MapF loc (B.ExprBoundVar t)
extractUsedLocs locMapping expr = MapF.mapMaybe keepIfNeeded locMapping
  where
    keepIfNeeded :: forall tp' . B.ExprBoundVar t tp' -> Maybe (B.ExprBoundVar t tp')
    keepIfNeeded bv' =
      case Set.member (Some bv') bvs of
        False -> Nothing
        True -> Just bv'
    bvs = allBoundVars expr

-- | Monadically map both keys and values of a 'MapF.MapF'.
mapFMapBothM :: forall k1 v1 k2 v2 m.
                (OrdF k2, Monad m)
             => (forall tp. k1 tp -> v1 tp -> m (k2 tp, v2 tp))
             -> MapF.MapF k1 v1
             -> m (MapF.MapF k2 v2)
mapFMapBothM f = MapF.foldrWithKey f' (return MapF.empty)
  where f' :: forall tp. k1 tp -> v1 tp -> m (MapF.MapF k2 v2) -> m (MapF.MapF k2 v2)
        f' k v wrappedM = do
          (k', v') <- f k v
          m <- wrappedM
          return $ MapF.insert k' v' m

-- | Filter the elements of a 'MapF.MapF'.
filterMapF :: forall k v. (OrdF k) => (forall tp. k tp -> v tp -> Bool) -> MapF.MapF k v -> MapF.MapF k v
filterMapF f = MapF.foldrWithKey go MapF.empty
  where go :: forall tp. k tp -> v tp -> MapF.MapF k v -> MapF.MapF k v
        go key value m
          | f key value = MapF.insert key value m
          | otherwise   = m

-- | Traceback-friendly fromJust alternative.
fromJust' :: (HasCallStack) => String -> Maybe a -> a
fromJust' label x =
    let msg = "fromJust': got Nothing (" ++ label ++ ")"
    in fromMaybe (error msg) x

withRounding
  :: forall sym tp
   . S.IsExprBuilder sym
  => sym
  -> S.SymBV sym 2
  -> (S.RoundingMode -> IO (S.SymExpr sym tp))
  -> IO (S.SymExpr sym tp)
withRounding sym r action = do
  cRNE <- roundingCond S.RNE
  cRTZ <- roundingCond S.RTZ
  cRTP <- roundingCond S.RTP
  S.iteM S.baseTypeIte sym cRNE
    (action S.RNE) $
    S.iteM S.baseTypeIte sym cRTZ
      (action S.RTZ) $
      S.iteM S.baseTypeIte sym cRTP (action S.RTP) (action S.RTN)
 where
  roundingCond :: S.RoundingMode -> IO (S.Pred sym)
  roundingCond rm =
    S.bvEq sym r =<< S.bvLit sym knownNat (roundingModeToBits rm)

roundingModeToBits :: S.RoundingMode -> Integer
roundingModeToBits = \case
  S.RNE -> 0
  S.RTZ -> 1
  S.RTP -> 2
  S.RTN -> 3
  S.RNA -> error $ "unsupported rounding mode: " ++ show S.RNA
