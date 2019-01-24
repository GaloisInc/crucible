------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Partial
-- Description      : Partial values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- Many values created and manipulated by the memory model have some (symbolic)
-- safety assertions associated with them, often expressed as a What4 'Pred'
-- (e.g. a value read from an pointer might have an associated predicate
-- that expresses that the pointer pointed to a live allocation).
--
-- We would like to maintain precise error messages even as such values are
-- manipulated and combined. To this end, instead of storing one 'Pred' which
-- is really the @and@, @or@, and @ite@ of many component predicates, we prefer
-- to maintain a tree of such predicates, each with a human-readable description
-- of what they assert.
--
-- TODO: What is said above could be asserted just as fully about the Java
-- memory model. Could this interface (specifically, 'AssertionTree') be
-- generalized in a suitable way for inclusion into What4? See also the
-- comment on 'AndOrITE'.
--
-- More detail: There should be a type (family) of safety assertions keyed on
-- the syntax extension. Instead of strings, these assertions should be paired
-- with one of those values.
--
-- TODO: Better story for error messages for 'Unassigned' values
--
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.MemModel.Partial where
  -- ( AndOrITE(..)
  -- ) where

import           Prelude hiding (pred)

import           Control.Lens ((^.), view)
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (liftIO, MonadIO)
import           Control.Monad.State.Strict (State, get, put, runState)
import           Data.Data (Data)
import           Data.List.NonEmpty (NonEmpty((:|)))
import           Data.Maybe (catMaybes)
import           Data.Semigroup (sconcat)
import           Data.Text (Text, unpack)
import           Data.Vector (Vector)
import           Data.Word (Word64)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Data.Vector as V

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.Backend
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import qualified Lang.Crucible.LLVM.Bytes as Bytes
import           Lang.Crucible.LLVM.Bytes (Bytes)
import qualified Lang.Crucible.LLVM.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Type
import qualified Lang.Crucible.LLVM.MemModel.Value as Value
import           Lang.Crucible.LLVM.MemModel.Value (LLVMVal(..), PartLLVMVal)
import qualified What4.Interface as W4I
import           What4.Interface (Pred, IsExprBuilder)
import qualified What4.InterpretedFloatingPoint as W4IFP
import qualified What4.Partial as W4P
import           What4.Partial (PartExpr(..))

------------------------------------------------------------------------
-- ** AndOrITE
--

-- | A type representing an AST consisting of
--  * "atomic" predicates
--  * a list of predicates 'And'-ed together
--  * a list of predicates 'Or'-ed together
--  * the if-then-else of two predicates
--
-- This is essentially the 'BaseBoolType' fragment of "the free
-- 'IsExprBuilder'", i.e. an 'IsExprBuilder' that simply builds an AST, and can
-- be interpreted into any other 'IsExprBuilder'. One possibility for
-- formalizing this intuition would be to split out a subclass
-- 'IsPredExprBuilder' of 'IsExprBuilder', and make this into an instance.
--
-- NB: The semigroup instance isn't /actually/ associative, it is \"semantically\"
-- associative.
--
-- TODO: Consider constantly-true and constantly-false leaves ('returnLLVMVal'')
data AndOrITE a =
    Leaf a
  | And    [AndOrITE a] -- TODO: nonempty lists
  | Or     [AndOrITE a]
  | Ite  a (AndOrITE a) (AndOrITE a)
  deriving (Data, Eq, Functor, Foldable, Traversable, Ord, Show)

-- | Not really associative...
instance Semigroup (AndOrITE a) where
  a1 <> a2 = And [a1, a2]

-- | Also not really associative...
-- (<+>) :: AndOrITE a -> AndOrITE a -> AndOrITE a
-- a1 <+> a2 = Or [a1, a2]

-- | Catamorphisms for the 'AndOrITE' type
cataAOI :: (a -> b)           -- ^ 'Leaf' case
        -> ([b] -> b)         -- ^ 'And' case
        -> ([b] -> b)         -- ^ 'Or' case
        -> (a -> b -> b -> b) -- ^ 'Ite' case
        -> AndOrITE a
        -> b
cataAOI leaf and_ or_ ite val =
  case val of
    Leaf a      -> leaf a
    And  l      -> and_ (map r l)
    Or   l      -> or_  (map r l)
    Ite a t1 t2 -> ite a (r t1) (r t2)
  where r = cataAOI leaf and_ or_ ite

-- | Add an additional piece of information to an 'AndOrIte' tree
tagAOI :: (a   -> c)         -- ^ 'Leaf' case
       -> ([c] -> c)         -- ^ Summarize child tags ('And' case)
       -> ([c] -> c)         -- ^ Summarize child tags ('Or' case)
       -> (a -> c -> c -> c) -- ^ Summarize child tags ('Ite' case)
       -> AndOrITE a
       -> (AndOrITE (a, c), c)
tagAOI leaf summarizeAnd summarizeOr summarizeITE =
  cataAOI
    (\lf      ->
       let tag = leaf lf
       in (Leaf (lf, tag), tag))
    (\factors ->
       let tag = summarizeAnd (map snd factors)
       in (And (map fst factors), tag))
    (\summands ->
       let tag = summarizeOr (map snd summands)
       in (Or (map fst summands), tag))
    (\cond t1 t2 ->
       let tag = summarizeITE cond (snd t1) (snd t2)
       in (Ite (cond, tag) (fst t1) (fst t2), tag))

-- | Monadic catamorphisms for the 'AndOrITE' type
--
-- Essentially, this function just arbitrarily picks a serialization of effects.
cataMAOI :: Monad f
         => (a -> f b)           -- ^ 'Leaf' case
         -> ([b] -> f b)         -- ^ 'And' case
         -> ([b] -> f b)         -- ^ 'Or' case
         -> (a -> b -> b -> f b) -- ^ 'Ite' case
         -> AndOrITE a
         -> f b
cataMAOI leaf and_ or_ ite = cataAOI
  leaf             -- Leaf
  (\l -> sequence l >>= and_)
  (\l -> sequence l >>= or_)
  (\a t1 t2 -> do
    t1' <- t1
    t2' <- t2
    ite a t1' t2') -- Ite

-- | Simplify an tree with 'Pred' in it with 'asConstantPred'
--
-- The original tree is included with a 'Maybe Bool' that might summarize it's
-- (constant) value.
asConstAOI_ :: (IsExprBuilder sym) =>
  sym -> (a -> Pred sym) -> AndOrITE a -> (AndOrITE (a, Maybe Bool), Maybe Bool)
asConstAOI_ _sym f =
  tagAOI
    (W4I.asConstantPred . f)
    (\factors    ->
       let factors' = catMaybes factors
       in if any not factors'
          then Just False
          else if length factors' == length factors
               then Just True
               else Nothing)
    (\summands    ->
       let summands' = catMaybes summands
       in if or summands'
          then Just True
          else if length summands' == length summands
               then Just False
               else Nothing)
    (\_ t1 t2 ->
       case (t1, t2) of
         (Just True, Just True)   -> Just True
         (Just False, Just False) -> Just False
         _                        -> Nothing)

-- | Like 'asConstPred', but for assertion trees.
asConstAOI :: (IsExprBuilder sym)
           => sym
           -> (a -> Pred sym)
           -> AndOrITE a
           -> Maybe Bool
asConstAOI sym f = snd . asConstAOI_ sym f


------------------------------------------------------------------------
-- ** PartLLVMVal'
--
-- Specializing the above type to the case of LLVM values...

data LLVMValAssertion sym =
  LLVMValAssertion { _explanation       :: Text
                   , _undefinedBehavior :: Maybe UB.UndefinedBehavior
                   , _pred              :: Pred sym
                   }

-- | Make an assertion that isn't about undefined behavior
llvmAssert :: Text -> Pred sym -> LLVMValAssertion sym
llvmAssert = flip LLVMValAssertion Nothing

type AssertionTree sym = AndOrITE (LLVMValAssertion sym)

ppAssertionTree :: (IsExprBuilder sym) => sym -> AssertionTree sym -> Doc
ppAssertionTree sym tree =
  let (tree', _) = asConstAOI_ sym _pred tree
  in
    cataAOI
      (\(lf, mb) -> text' (_explanation lf) <+> mbToText mb) -- TODO(langston): UB
      (\factors ->
         text' "All of "
         <$$> indent 2 (vcat factors))
      (\summands ->
         text' "Any of "
         <$$> indent 2 (vcat summands))
      (\(cond, mb) doc1 doc2 ->
         text' "If " <+> text' (_explanation cond) <+> mbToText mb <$$>
         indent 2 (vcat [ "then " <+> doc1
                        , "else " <+> doc2
                        ]))
      tree'
  where mbToText (Just True)  = text "(known-true)"
        mbToText (Just False) = text "(known-false)"
        mbToText Nothing      = mempty
        text' = text . unpack

type PartLLVMVal' sym = PartExpr (AssertionTree sym) (LLVMVal sym)

-- | A monadic catamorphism, collapsing everything to one predicate.
collapseAssertionTree :: (IsExprBuilder sym)
                      => sym
                      -> AssertionTree sym
                      -> IO (Pred sym)
collapseAssertionTree sym = cataMAOI
  (pure . _pred)
  (foldM (W4I.andPred sym) (W4I.truePred sym))
  (foldM (W4I.orPred sym) (W4I.falsePred sym))
  (\a -> W4I.itePred sym (_pred a))

fromPart' :: PartLLVMVal sym -> Text -> PartLLVMVal' sym
fromPart' Unassigned   _   = Unassigned
fromPart' (W4P.PE p v) txt = W4P.PE (Leaf (LLVMValAssertion txt Nothing p)) v

-- fromPart :: PartLLVMVal sym -> PartLLVMVal' sym
-- fromPart = flip fromPart' "<fromPart>"

-- toPart :: (IsExprBuilder sym) => sym -> PartLLVMVal' sym -> IO (PartLLVMVal sym)
-- toPart _   Unassigned  = pure Unassigned
-- toPart sym (W4P.PE t v) = W4P.PE <$> (collapseAssertionTree sym t) <*> pure v

-- | An 'LLVMVal' which is always valid.
returnPartLLVMVal' :: (IsExprBuilder sym) => sym -> LLVMVal sym -> PartLLVMVal' sym
returnPartLLVMVal' sym v = fromPart' (W4P.PE (W4I.truePred sym) v) "<const true>"

explainPartLLVMVal' :: Pred sym -> Text -> LLVMVal sym -> PartLLVMVal' sym
explainPartLLVMVal' p txt v = fromPart' (W4P.PE p v) txt

assertPartLLVMVal' ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym ->
  PartLLVMVal' sym ->
  IO (Maybe (LLVMVal sym))
assertPartLLVMVal' _sym Unassigned    = pure Nothing
assertPartLLVMVal' sym  (PE tree val) = do
  collapsed <- collapseAssertionTree sym tree
  assert sym collapsed (AssertFailureSimError (show (ppAssertionTree sym tree)))
  pure (Just val)

------------------------------------------------------------------------
-- ** PartLLVMVal interface
--

-- | Convert a bitvector to a float, asserting that it is not a pointer
bvToFloatPartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)

bvToFloatPartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 4) _))) =
  PE p . LLVMValFloat Value.SingleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr =<<
       W4I.bvLit sym (knownNat @32) 0)

bvToFloatPartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @32) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0

      let exp_ = "While converting a bitvector to a float: " <>
                   "The bitvector is really an integer (not a pointer)"
      PE (And [p, Leaf (llvmAssert exp_ pz)]) .
        LLVMValFloat Value.SingleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr off

bvToFloatPartLLVMVal _ _ = return Unassigned


-- | Convert a bitvector to a double, asserting that it is not a pointer
bvToDoublePartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)

bvToDoublePartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 8) _))) =
  PE p . LLVMValFloat Value.DoubleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr =<<
       W4I.bvLit sym (knownNat @64) 0)

bvToDoublePartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @64) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0
      let exp_ = "While converting a bitvector to a double: " <>
                   "The bitvector is really an integer (not a pointer)"
      PE (And [p, Leaf (llvmAssert exp_ pz)]) .
        LLVMValFloat Value.DoubleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr off

bvToDoublePartLLVMVal _ _ = return Unassigned


-- | Convert a bitvector to an FP80 float, asserting that it is not a pointer
bvToX86_FP80PartLLVMVal ::
  IsSymInterface sym => sym ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)

bvToX86_FP80PartLLVMVal sym (PE p (LLVMValZero (StorageType (Bitvector 10) _))) =
  PE p . LLVMValFloat Value.X86_FP80Size <$>
    (W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr =<<
       W4I.bvLit sym (knownNat @80) 0)

bvToX86_FP80PartLLVMVal sym (PE p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @80) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0
      let exp_ = "While converting a bitvector to an FP80 float: " <>
                   "The bitvector is really an integer (not a pointer)"
      PE (And [p, Leaf (llvmAssert exp_ pz)]) . LLVMValFloat Value.X86_FP80Size <$>
        W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr off

bvToX86_FP80PartLLVMVal _ _ = return Unassigned

-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcatPartLLVMVal :: forall sym.
  IsSymInterface sym => sym ->
  PartLLVMVal' sym ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)
bvConcatPartLLVMVal _ Unassigned _ = return Unassigned
bvConcatPartLLVMVal _ _ Unassigned = return Unassigned

bvConcatPartLLVMVal sym (PE p1 v1) (PE p2 v2) =
    case (v1, v2) of
      (LLVMValInt blk_low low, LLVMValInt blk_high high) ->
        do go blk_low low blk_high high
      (LLVMValInt blk_low low, LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        Value.zeroInt sym high_bytes $ \case
          Nothing -> return Unassigned
          Just (blk_high, high) ->
            go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValInt blk_high high) ->
         Value.zeroInt sym low_bytes $ \case
           Nothing -> return Unassigned
           Just (blk_low, low) ->
             go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        pure $ returnPartLLVMVal' sym (LLVMValZero (bitvectorType (low_bytes + high_bytes)))
      _ -> return Unassigned

 where
  go :: forall l h. (1 <= l, 1 <= h) =>
    W4I.SymNat sym -> W4I.SymBV sym l -> W4I.SymNat sym -> W4I.SymBV sym h -> IO (PartLLVMVal' sym)
  go blk_low low blk_high high
    -- NB we check that the things we are concatenating are each an integral number of
    -- bytes.  This prevents us from concatenating together the partial-byte writes that
    -- result from e.g. writing an i1 or an i20 into memory.  This is consistent with LLVM
    -- documentation, which says that non-integral number of bytes loads will only succeed
    -- if the value was written orignally with the same type.
    | natValue low_w' `mod` 8 == 0
    , natValue high_w' `mod` 8 == 0 =
      do blk0   <- W4I.natLit sym 0
         -- TODO: Why won't this pattern match fail?
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         p_blk1 <- W4I.natEq sym blk_low blk0
         p_blk2 <- W4I.natEq sym blk_high blk0
         bv <- W4I.bvConcat sym high low
         return $ flip W4P.PE (LLVMValInt blk0 bv) $ sconcat $
           let
             expl s = "While concatenating bitvectors: " <> s
             exp1 = expl "The first bitvector is really an integer (not a pointer)"
             exp2 = expl "The second bitvector is really an integer (not a pointer)"
           in
             (Leaf (llvmAssert exp1 p_blk1) :|
               [ Leaf (llvmAssert exp2 p_blk2)
               , p1
               , p2
               ])
    | otherwise =
       return Unassigned

    where low_w' = W4I.bvWidth low
          high_w' = W4I.bvWidth high

-- | Cons an element onto a partial LLVM array value.
consArrayPartLLVMVal ::
  IsSymInterface sym =>
  PartLLVMVal' sym ->
  PartLLVMVal' sym ->
  PartLLVMVal' sym
consArrayPartLLVMVal (PE p1 (LLVMValZero tp)) (PE p2 (LLVMValZero (StorageType (Array m tp') _)))
  | tp == tp' =
      PE (And [p1, p2]) $ LLVMValZero (arrayType (m+1) tp')

consArrayPartLLVMVal (PE p1 hd) (PE p2 (LLVMValZero (StorageType (Array m tp) _)))
  | Value.llvmValStorableType hd == tp =
      PE (And [p1, p2]) $ LLVMValArray tp (V.cons hd (V.replicate (fromIntegral m) (LLVMValZero tp)))

consArrayPartLLVMVal (PE p1 hd) (PE p2 (LLVMValArray tp vec))
  | Value.llvmValStorableType hd == tp =
      PE (And [p1, p2]) $ LLVMValArray tp (V.cons hd vec)

consArrayPartLLVMVal _ _ = Unassigned

-- | Append two partial LLVM array values.
appendArrayPartLLVMVal ::
  IsSymInterface sym =>
  PartLLVMVal' sym ->
  PartLLVMVal' sym ->
  PartLLVMVal' sym
appendArrayPartLLVMVal
  (PE p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PE p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 = PE (And [p1, p2]) $ LLVMValZero (arrayType (n1+n2) tp1)

appendArrayPartLLVMVal
  (PE p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PE p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      let v1 = V.replicate (fromIntegral n1) (LLVMValZero tp1)
      in PE (And [p1, p2]) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal
  (PE p1 (LLVMValArray tp1 v1))
  (PE p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
      let v2 = V.replicate (fromIntegral n2) (LLVMValZero tp1)
      in PE (And [p1, p2]) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal
  (PE p1 (LLVMValArray tp1 v1))
  (PE p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      PE (And [p1, p2]) $ LLVMValArray tp1 (v1 V.++ v2)

appendArrayPartLLVMVal _ _ = Unassigned


-- | Make a partial LLVM array value.
--
-- It returns 'Unassigned' if any of the elements of the vector are
-- 'Unassigned'. Otherwise, the 'AssertionTree' on the returned value
-- is the 'And' of all the assertions on the values.
mkArrayPartLLVMVal :: forall sym. IsSymInterface sym =>
  StorageType ->
  Vector (PartLLVMVal' sym) ->
  PartLLVMVal' sym
mkArrayPartLLVMVal tp vec =
  let f :: PartLLVMVal' sym -> State [AssertionTree sym] (Maybe (LLVMVal sym))
      f Unassigned = pure Nothing
      f (PE p x) = do
        ps_ <- get     -- Current predicates
        put (p:ps_)    -- Append this one
        pure (Just x)
      (vecMay, ps) = flip runState [] $ (traverse f vec)
  in case sequence vecMay of
       Nothing  -> Unassigned
       Just vec' -> PE (And ps) $ LLVMValArray tp vec'


-- | Make a partial LLVM struct value.
--
-- It returns 'Unassigned' if any of the struct fields are 'Unassigned'.
-- Otherwise, the 'AssertionTree' on the returned value is the 'And' of all the
-- assertions on the values.
mkStructPartLLVMVal :: forall sym .
  Vector (Field StorageType, PartLLVMVal' sym) ->
  (PartLLVMVal' sym)
mkStructPartLLVMVal vec =
  let f :: (Field StorageType, PartLLVMVal' sym)
        -> State [AssertionTree sym] (Maybe (Field StorageType, LLVMVal sym))
      f (_fld, Unassigned) = pure Nothing
      f (fld, PE p x) = do
        ps_ <- get
        put (p:ps_)
        pure (Just (fld, x))
      (vecMay, ps) = flip runState [] $ (traverse f vec)
  in case sequence vecMay of
       Nothing   -> Unassigned
       Just vec' -> PE (And ps) $ LLVMValStruct vec'


-- | Select some of the least significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectLowBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)

selectLowBvPartLLVMVal _sym low hi (PE p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PE p $ LLVMValZero (bitvectorType low)

selectLowBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof       <- isPosNat low_w
  , Just Refl           <- testEquality (addNat low_w hi_w) w
  , Just LeqProof       <- testLeq low_w w = do
      let expl = ("When selecting the least-significant bytes of a bitvector: " <>)
      let exp0 = expl "The bitvector is really an integer (not a pointer)"
      pz  <- W4I.natEq sym blk =<< W4I.natLit sym 0
      bv' <- W4I.bvSelect sym (knownNat :: NatRepr 0) low_w bv
      return $ PE (And [Leaf (llvmAssert exp0 pz), p]) (LLVMValInt blk bv')
  where w = W4I.bvWidth bv
selectLowBvPartLLVMVal _ _ _ _ = return Unassigned

-- | Select some of the most significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectHighBvPartLLVMVal ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)

selectHighBvPartLLVMVal _sym low hi (PE p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PE p $ LLVMValZero (bitvectorType hi)

selectHighBvPartLLVMVal sym low hi (PE p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do let expl = ("When selecting the most-significant bytes of a bitvector: " <>)
       let exp0 = expl "The bitvector is really an integer (not a pointer)"
       pz <-  W4I.natEq sym blk =<< W4I.natLit sym 0
       bv' <- W4I.bvSelect sym low_w hi_w bv
       return $ PE (And [Leaf (llvmAssert exp0 pz), p]) $ LLVMValInt blk bv'
  where w = W4I.bvWidth bv
selectHighBvPartLLVMVal _ _ _ _ = return Unassigned


-- | Look up an element in a partial LLVM array value.
arrayEltPartLLVMVal ::
  Word64 ->
  StorageType ->
  Word64 ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)
arrayEltPartLLVMVal sz tp idx (PE p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < sz =
    return $ PE p (LLVMValZero tp)

arrayEltPartLLVMVal sz tp idx (PE p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ PE p (vec V.! fromIntegral idx)

arrayEltPartLLVMVal _ _ _ _ = return Unassigned

-- | Look up a field in a partial LLVM struct value.
fieldValPartLLVMVal ::
  (Vector (Field StorageType)) ->
  Int ->
  PartLLVMVal' sym ->
  IO (PartLLVMVal' sym)
fieldValPartLLVMVal flds idx (PE p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < V.length flds =
      return $ PE p $ LLVMValZero $ view fieldVal $ flds V.! idx

fieldValPartLLVMVal flds idx (PE p (LLVMValStruct vec))
  | flds == fmap fst vec
  , 0 <= idx
  , idx < V.length vec =
    return $ PE p $ snd $ (vec V.! idx)

fieldValPartLLVMVal _ _ _ = return Unassigned

------------------------------------------------------------------------
-- ** Merging and muxing
--

-- | If-then-else on partial expressions.
mergePartial :: (IsExprBuilder sym, MonadIO m) =>
  sym ->
  (Pred sym -> LLVMVal sym -> LLVMVal sym -> m (PartLLVMVal' sym))
    {- ^ Operation to combine inner values. The 'Pred' parameter is the
         if/then/else condition -} ->
  Pred sym {- ^ condition to merge on -} ->
  PartLLVMVal' sym {- ^ 'if' value -}  ->
  PartLLVMVal' sym {- ^ 'then' value -} ->
  m (PartLLVMVal' sym)

{-# SPECIALIZE mergePartial ::
      IsExprBuilder sym =>
      sym ->
      (Pred sym -> LLVMVal sym -> LLVMVal sym -> IO (PartLLVMVal' sym)) ->
      Pred sym ->
      PartLLVMVal' sym ->
      PartLLVMVal' sym ->
      IO (PartLLVMVal' sym)   #-}

mergePartial _ _ _ Unassigned Unassigned  = return Unassigned
mergePartial _ _ c (PE px x) Unassigned = do
  let expl = "If-then-else of partial LLVM values, second was 'Unassigned'"
  return $ PE (And [Leaf (llvmAssert expl c), px]) x
mergePartial sym _ c Unassigned (PE py y) = do
  p <- liftIO $ W4I.notPred sym c
  let expl = "If-then-else of partial LLVM values, first was 'Unassigned'"
  return $! PE (And [Leaf (llvmAssert expl p), py]) y
mergePartial _ f c (PE px x) (PE py y) = do
  let expl    = "If-then-else of partial LLVM values"
  z0 <- f c x y
  pure $
    case z0 of
      Unassigned -> Unassigned
      PE pz z    -> PE (And [Ite (llvmAssert expl c) px py, pz]) z

{-
-- | Merge a collection of partial values in an if-then-else tree.
--   For example, if we merge a list like @[(xp,x),(yp,y),(zp,z)]@,
--   we get a value that is morally equivalant to:
--   @if xp then x else (if yp then y else (if zp then z else undefined))@.
mergePartials :: (IsExprBuilder sym, MonadIO m) =>
  sym ->
  (Pred sym -> a -> a -> W4P.PartialT sym m a)
    {- ^ Operation to combine inner values.
         The 'Pred' parameter is the if/then/else condition
     -} ->
  [(Pred sym, PartExpr (Pred sym) a)]      {- ^ values to merge -} ->
  m (PartExpr (Pred sym) a)
mergePartials sym f = go
  where
  go [] = return Unassigned
  go ((c,x):xs) =
    do y <- go xs
       mergePartial sym f c x y
-}

-- | Mux partial LLVM values.
muxLLVMVal :: forall sym
    . IsSymInterface sym
   => sym
   -> Pred sym
   -> PartLLVMVal' sym
   -> PartLLVMVal' sym
   -> IO (PartLLVMVal' sym)
muxLLVMVal sym = mergePartial sym muxval
  where

    muxzero :: Pred sym -> StorageType -> LLVMVal sym -> IO (LLVMVal sym)
    muxzero cond tpz val = case val of
      LLVMValZero tp -> return $ LLVMValZero tp
      LLVMValUndef tpu ->
        -- TODO: Is this the right behavior?
        panic "Cannot mux zero and undef" [ "Zero type: " ++ show tpz
                                          , "Undef type: " ++ show tpu
                                          ]
      LLVMValInt base off ->
        do zbase <- W4I.natLit sym 0
           zoff  <- W4I.bvLit sym (W4I.bvWidth off) 0
           base' <- W4I.natIte sym cond zbase base
           off'  <- W4I.bvIte sym cond zoff off
           return $ LLVMValInt base' off'
      LLVMValFloat Value.SingleSize x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.SingleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.SingleFloat sym cond zerof x)
           return $ LLVMValFloat Value.SingleSize x'
      LLVMValFloat Value.DoubleSize x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.DoubleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.DoubleFloat sym cond zerof x)
           return $ LLVMValFloat Value.DoubleSize x'
      LLVMValFloat Value.X86_FP80Size x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.X86_80FloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.X86_80Float sym cond zerof x)
           return $ LLVMValFloat Value.X86_FP80Size x'

      LLVMValArray tp vec ->
        LLVMValArray tp <$> traverse (muxzero cond tp) vec

      LLVMValStruct flds ->
        LLVMValStruct <$> traverse (\(fld, v) -> (fld,) <$> muxzero cond (fld^.fieldVal) v) flds


    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> IO (PartLLVMVal' sym)
    muxval cond (LLVMValZero tp) v = returnPartLLVMVal' sym <$> muxzero cond tp v
    muxval cond v (LLVMValZero tp) = do cond' <- W4I.notPred sym cond
                                        returnPartLLVMVal' sym <$> muxzero cond' tp v

    muxval cond (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (W4I.bvWidth off1) (W4I.bvWidth off2)
      = do base <- liftIO $ W4I.natIte sym cond base1 base2
           off  <- liftIO $ W4I.bvIte sym cond off1 off2
           pure $ returnPartLLVMVal' sym $ LLVMValInt base off

    muxval cond (LLVMValFloat (xsz :: Value.FloatSize fi) x) (LLVMValFloat ysz y)
      | Just Refl <- testEquality xsz ysz
      = returnPartLLVMVal' sym .  LLVMValFloat xsz <$>
          (liftIO $ W4IFP.iFloatIte @_ @fi sym cond x y)

    muxval cond (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 =
          mkStructPartLLVMVal <$>
            V.zipWithM (\(f, x) (_, y) -> (f,) <$> muxval cond x y) fls1 fls2

    muxval cond (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          mkArrayPartLLVMVal tp1 <$> V.zipWithM (muxval cond) v1 v2

    muxval _ v1@(LLVMValUndef tp1) (LLVMValUndef tp2)
      | tp1 == tp2 = pure (returnPartLLVMVal' sym v1)

    muxval _ _ _ = pure Unassigned
