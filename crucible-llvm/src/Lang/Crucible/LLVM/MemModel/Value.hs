------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Value
-- Description      : Representation of values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.Value
  ( -- * LLVM Value representation
    LLVMVal(..)
  , ppLLVMValWithGlobals
  , FloatSize(..)
  , Field
  , ptrToPtrVal
  , zeroInt

  , llvmValStorableType
  , isZero
  , testEqual
  ) where

import           Control.Lens (view)
import           Control.Monad (foldM, join)
import           Data.Map (Map)
import           Data.Coerce (coerce)
import           Data.Foldable (toList)
import           Data.Functor.Identity (Identity(..))
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.List (intersperse)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           What4.Interface
import           What4.InterpretedFloatingPoint

import           Lang.Crucible.Backend
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.Panic (panic)

data FloatSize (fi :: FloatInfo) where
  SingleSize :: FloatSize SingleFloat
  DoubleSize :: FloatSize DoubleFloat
  X86_FP80Size :: FloatSize X86_80Float

deriving instance Eq (FloatSize fi)
deriving instance Ord (FloatSize fi)
deriving instance Show (FloatSize fi)
instance TestEquality FloatSize where
  testEquality SingleSize SingleSize = Just Refl
  testEquality DoubleSize DoubleSize = Just Refl
  testEquality X86_FP80Size X86_FP80Size = Just Refl
  testEquality _ _ = Nothing

-- | This datatype describes the variety of values that can be stored in
--   the LLVM heap.
data LLVMVal sym where
  -- | NOTE! The ValInt constructor uniformly represents both pointers and
  -- raw bitvector values.  The 'SymNat' value is an allocation block number
  -- that identifies specific allocations.  The block number '0' is special,
  -- and indicates that this value is actually a bitvector.  Non-zero block
  -- numbers correspond to pointer values, where the 'SymBV' value is an
  -- offset from the base pointer of the allocation.
  LLVMValInt :: (1 <= w) => SymNat sym -> SymBV sym w -> LLVMVal sym
  LLVMValFloat :: FloatSize fi -> SymInterpretedFloat sym fi -> LLVMVal sym
  LLVMValStruct :: Vector (Field StorageType, LLVMVal sym) -> LLVMVal sym
  LLVMValArray :: StorageType -> Vector (LLVMVal sym) -> LLVMVal sym

  -- | The zero value exists at all storage types, and represents the the value
  -- which is obtained by loading the approprite number of all zero bytes.
  -- It is useful for compactly representing large zero-initialized data structures.
  LLVMValZero :: StorageType -> LLVMVal sym

  -- | The @undef@ value exists at all storage types.
  LLVMValUndef :: StorageType -> LLVMVal sym


llvmValStorableType :: IsExprBuilder sym => LLVMVal sym -> StorageType
llvmValStorableType v =
  case v of
    LLVMValInt _ bv -> bitvectorType (bitsToBytes (natValue (bvWidth bv)))
    LLVMValFloat SingleSize _ -> floatType
    LLVMValFloat DoubleSize _ -> doubleType
    LLVMValFloat X86_FP80Size _ -> x86_fp80Type
    LLVMValStruct fs -> structType (fmap fst fs)
    LLVMValArray tp vs -> arrayType (fromIntegral (V.length vs)) tp
    LLVMValZero tp -> tp
    LLVMValUndef tp -> tp

-- | Coerce an 'LLVMPtr' value into a memory-storable 'LLVMVal'.
ptrToPtrVal :: (1 <= w) => LLVMPtr sym w -> LLVMVal sym
ptrToPtrVal (LLVMPointer blk off) = LLVMValInt blk off

zeroInt ::
  IsSymInterface sym =>
  sym ->
  Bytes ->
  (forall w. (1 <= w) => Maybe (SymNat sym, SymBV sym w) -> IO a) ->
  IO a
zeroInt sym bytes k
   | Some w <- mkNatRepr (bytesToBits bytes)
   , Just LeqProof <- isPosNat w
   =   do blk <- natLit sym 0
          bv  <- bvLit sym w (BV.zero w)
          k (Just (blk, bv))
zeroInt _ _ k = k @1 Nothing

-- | Pretty-print an 'LLVMVal'.
--
-- This is parameterized over how to display pointers, see
-- 'ppLLVMValWithGlobals'.
ppLLVMVal ::
  (Applicative f, IsExpr (SymExpr sym)) =>
  (forall w. SymNat sym -> SymBV sym w -> f (Maybe PP.Doc))
    {- ^ Printing of pointers -} ->
  LLVMVal sym ->
  f PP.Doc
ppLLVMVal ppInt =
  let typed doc tp = PP.text doc PP.<+> PP.text ":" PP.<+> PP.text (show tp)
      pp = ppLLVMVal ppInt
  in
    \case
      (LLVMValZero tp) -> pure $ PP.angles (typed "zero" tp)
      (LLVMValUndef tp) -> pure $ PP.angles (typed "undef" tp)
      (LLVMValInt blk w) -> fromMaybe otherDoc <$> ppInt blk w
        where
          otherDoc =
            case asNat blk of
              Just 0 ->
                case (asBV w) of
                  (Just (BV.BV unsigned)) -> PP.text $ unwords $
                    [ "literal integer:"
                    , "unsigned value = " ++ show unsigned ++ ","
                    , unwords [ "signed value = "
                              , show (toSigned (bvWidth w) unsigned) ++ ","
                              ]
                    , "width = " ++ show (bvWidth w)
                    ]
                  Nothing -> PP.text $ unwords $
                    [ "symbolic integer: "
                    , "width = " ++ show (bvWidth w)
                    ]
              Just n ->
                case asBV w of
                  Just (BV.BV offset) -> PP.text $ unwords $
                    [ "concrete pointer:"
                    , "allocation = " ++ show n ++ ","
                    , "offset = " ++ show offset
                    ]
                  Nothing -> PP.text $ unwords $
                    [ "pointer with concrete allocation and symbolic offset:"
                    , "allocation = " ++ show n
                    ]

              Nothing ->
                case asBV w of
                  Just (BV.BV offset) -> PP.text $
                    "pointer with concrete offset " ++ show offset
                  Nothing -> PP.text "pointer with symbolic offset"

      (LLVMValFloat SingleSize _) -> pure $ PP.text "symbolic float"
      (LLVMValFloat DoubleSize _) -> pure $ PP.text "symbolic double"
      (LLVMValFloat X86_FP80Size _) -> pure $ PP.text "symbolic long double"
      (LLVMValStruct xs) -> PP.semiBraces <$> traverse (pp . snd) (V.toList xs)
      (LLVMValArray _ xs) -> PP.list <$> traverse pp (V.toList xs)

-- | Pretty-print an 'LLVMVal', but replace pointers to globals with the name of
--   the global when possible. Probably pretty slow on big structures.
ppLLVMValWithGlobals :: forall sym.
  (IsSymInterface sym) =>
  sym ->
  Map L.Symbol (SomePointer sym) {-^ c.f. 'memImplGlobalMap' -} ->
  LLVMVal sym ->
  IO PP.Doc
ppLLVMValWithGlobals sym globalMap = ppLLVMVal $ \allocNum offset ->
  isGlobalPointer' sym globalMap (LLVMPointer allocNum offset) <&&>
    \(L.Symbol symb) -> PP.text ('@':symb)
  where x <&&> f = (fmap . fmap) f x -- map under IO and Maybe

-- | This instance tries to make things as concrete as possible.
instance IsExpr (SymExpr sym) => PP.Pretty (LLVMVal sym) where
  pretty = coerce $ ppLLVMVal (\_ _ -> Identity Nothing)

instance IsExpr (SymExpr sym) => Show (LLVMVal sym) where
  show (LLVMValZero _tp) = "0"
  show (LLVMValUndef tp) = "<undef : " ++ show tp ++ ">"
  show (LLVMValInt blk w)
    | Just 0 <- asNat blk = "<int" ++ show (bvWidth w) ++ ">"
    | otherwise = "<ptr " ++ show (bvWidth w) ++ ">"
  show (LLVMValFloat SingleSize _) = "<float>"
  show (LLVMValFloat DoubleSize _) = "<double>"
  show (LLVMValFloat X86_FP80Size _) = "<long double>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]

-- | An efficient n-way @and@: it quits early if it finds any concretely false
-- values, rather than chaining a bunch of 'andPred's.
allOf :: (IsExprBuilder sym)
      => sym
      -> [Pred sym]
      -> IO (Pred sym)
allOf sym xs =
  if and (mapMaybe asConstantPred xs)
  then foldM (andPred sym) (truePred sym) xs
  else pure (falsePred sym)

{-
-- | An efficient n-way @or@: it quits early if it finds any concretely false
-- values, rather than chaining a bunch of 'orPred's.
oneOf :: (IsExprBuilder sym)
      => sym
      -> [Pred sym]
      -> IO (Pred sym)
oneOf sym xs =
  if or (mapMaybe asConstantPred xs)
  then pure (truePred sym)
  else foldM (orPred sym) (falsePred sym) xs
-}

-- | Commute an applicative with Maybe
commuteMaybe :: Applicative n => Maybe (n a) -> n (Maybe a)
commuteMaybe (Just val) = Just <$> val
commuteMaybe Nothing    = pure Nothing

-- | This should be used with caution: it is very inefficient to expand zeroes,
-- especially to large data structures (e.g. long arrays).
zeroExpandLLVMVal :: (IsExprBuilder sym, IsInterpretedFloatExprBuilder sym)
                  => sym -> StorageType -> IO (LLVMVal sym)
zeroExpandLLVMVal sym (StorageType tpf _sz) =
  case tpf of
    Bitvector bytes ->
      case mkNatRepr (bytesToBits bytes) of
        Some (repr :: NatRepr w) ->
          case testNatCases (knownNat @0) repr of
            NatCaseLT (LeqProof :: LeqProof 1 w) ->
              LLVMValInt <$> natLit sym 0 <*> bvLit sym repr (BV.zero repr)
            NatCaseEQ -> panic "zeroExpandLLVMVal" ["Zero value inside Bytes"]
            NatCaseGT (LeqProof :: LeqProof (w + 1) 0) ->
              panic "zeroExpandLLVMVal" ["Impossible: (w + 1) </= 0"]
    Float    -> LLVMValFloat SingleSize <$> iFloatPZero sym SingleFloatRepr
    Double   -> LLVMValFloat DoubleSize <$> iFloatPZero sym DoubleFloatRepr
    X86_FP80 -> LLVMValFloat X86_FP80Size <$> iFloatPZero sym X86_80FloatRepr
    Array n ty ->
      LLVMValArray ty . V.replicate (fromIntegral (bytesToInteger n)) <$>
        zeroExpandLLVMVal sym ty
    Struct vec ->
      LLVMValStruct <$>
        V.zipWithM (\f t -> (f,) <$> zeroExpandLLVMVal sym t) vec (fmap (view fieldVal) vec)

-- | A special case for comparing values to the distinguished zero value.
--
-- Should be faster than using 'testEqual' with 'zeroExpandLLVMVal' for compound
-- values, because we 'traverse' subcomponents of vectors and structs, quitting
-- early on a constantly false answer or 'LLVMValUndef'.
--
-- Returns 'Nothing' for 'LLVMValUndef'.
isZero :: forall sym. (IsExprBuilder sym, IsInterpretedFloatExprBuilder sym)
       => sym -> LLVMVal sym -> IO (Maybe (Pred sym))
isZero sym v =
  case v of
    LLVMValStruct fs  -> areZero' (fmap snd fs)
    LLVMValArray _ vs -> areZero' vs
    LLVMValZero _     -> pure (Just $ truePred sym)
    LLVMValUndef _    -> pure Nothing
    _                 ->
      -- For atomic types, we simply expand and compare.
      testEqual sym v =<< zeroExpandLLVMVal sym (llvmValStorableType v)
  where
    areZero :: Traversable t => t (LLVMVal sym) -> IO (Maybe (t (Pred sym)))
    areZero = fmap sequence . traverse (isZero sym)
    areZero' :: Traversable t => t (LLVMVal sym) -> IO (Maybe (Pred sym))
    areZero' vs =
      -- This could probably be simplified with a well-placed =<<...
      join $ fmap commuteMaybe $ fmap (fmap (allOf sym . toList)) $ areZero vs

-- | A predicate denoting the equality of two LLVMVals.
--
-- Returns 'Nothing' in the event that one of the values contains 'LLVMValUndef'.
testEqual :: forall sym. (IsExprBuilder sym, IsInterpretedFloatExprBuilder sym)
          => sym -> LLVMVal sym -> LLVMVal sym -> IO (Maybe (Pred sym))
testEqual sym v1 v2 =
  case (v1, v2) of
    (LLVMValInt blk1 off1, LLVMValInt blk2 off2) ->
      case testEquality (bvWidth off1) (bvWidth off2) of
        Nothing   -> false
        Just Refl ->
          natEq sym blk1 blk2 >>= \p1 ->
            Just <$> (andPred sym p1 =<< bvEq sym off1 off2)
    (LLVMValFloat (sz1 :: FloatSize fi1) flt1, LLVMValFloat sz2 flt2) ->
      case testEquality sz1 sz2 of
        Nothing   -> false
        Just Refl -> Just <$> iFloatEq @_ @fi1 sym flt1 flt2
    (LLVMValArray tp1 vec1, LLVMValArray tp2 vec2) ->
      andAlso (tp1 == tp2) (allEqual vec1 vec2)
    (LLVMValStruct vec1, LLVMValStruct vec2) ->
      let (si1, si2) = (fmap fst vec1, fmap fst vec2)
          (fd1, fd2) = (fmap snd vec1, fmap snd vec2)
      in andAlso (V.and (V.zipWith (==) si1 si2))
                 (allEqual fd1 fd2)
    (LLVMValZero tp1, LLVMValZero tp2) -> if tp1 == tp2 then true else false
    (LLVMValZero tp, other) -> compareZero tp other
    (other, LLVMValZero tp) -> compareZero tp other
    (LLVMValUndef _, _) -> pure Nothing
    (_, LLVMValUndef _) -> pure Nothing
    (_, _) -> false -- type mismatch
  where true = pure (Just $ truePred sym)
        false = pure (Just $ falsePred sym)

        andAlso b x = if b then x else false

        allEqual vs1 vs2 =
          foldM (\x y -> commuteMaybe (andPred sym <$> x <*> y)) (Just $ truePred sym) =<<
            V.zipWithM (testEqual sym) vs1 vs2

        -- This is probably inefficient:
        compareZero tp other =
          andAlso (llvmValStorableType other == tp) $ isZero sym other
