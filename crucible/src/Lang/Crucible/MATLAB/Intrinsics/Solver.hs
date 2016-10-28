{-|
Module     : Lang.Crucible.MATLAB.Intrinsics.Solver
Copyright  : (c) Galois, Inc, 2016
Maintainer : Joe Hendrix <jhendrix@galois.com>
License    : BSD3

This module provides an interface that a symbolic backend should
implement to support MATLAB intrinsics.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.MATLAB.Intrinsics.Solver
  ( MatlabSolverFn(..)
  , matlabSolverArgTypes
  , matlabSolverReturnType
  , ppMatlabSolverFn
  , evalMatlabSolverFn
  , testSolverFnEq
  , traverseMatlabSolverFn
  , MatlabSymbolicArrayBuilder(..)
  ) where

import           Control.Monad (join)
import           Data.Hashable
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.TraversableFC
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))


import           Lang.Crucible.BaseTypes
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Utils.OnlyNatRepr


-- | Data type that lists solver functions that need to be generated during
-- symbolic ex
data MatlabSolverFn (f :: BaseType -> *) args ret where
  -- Returns true if the real value is an integer.
  IsIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseBoolType

  -- Returns true if the imaginary part of complex number is zero.
  CplxIsRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseBoolType

  -- Return true if first nat is less than or equal to second.
  NatLeFn :: MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseBoolType

  -- Return true if first value is less than or equal to second.
  IntLeFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType ::> BaseIntegerType) BaseBoolType

  -- A function for mapping a unsigned bitvector to a natural number.
  BVToNatFn :: (1 <= w)
            => !(NatRepr w)
            ->  MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseNatType
  -- A function for mapping a signed bitvector to a integer.
  SBVToIntegerFn :: (1 <= w)
                 => !(NatRepr w)
                 -> MatlabSolverFn f (EmptyCtx ::> BaseBVType w) BaseIntegerType

  -- A function for mapping a natural number to an integer.
  NatToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseNatType) BaseIntegerType

  -- A function for mapping an integer to equivalent nat.
  --
  -- Function may return any value if input is negative.
  IntegerToNatFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType) BaseNatType

  -- A function for mapping an integer to equivalent real.
  IntegerToRealFn :: MatlabSolverFn f (EmptyCtx ::> BaseIntegerType) BaseRealType

  -- A function for mapping a real to equivalent integer.
  --
  -- Function may return any value if input is not an integer.
  RealToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseIntegerType

  -- A function for mapping a real to equivalent complex.
  RealToComplexFn :: MatlabSolverFn f (EmptyCtx ::> BaseRealType) BaseComplexType

  -- A function for mapping a real to equivalent complex.
  RealPartOfCplxFn :: MatlabSolverFn f (EmptyCtx ::> BaseComplexType) BaseRealType

  -- A function that maps Booleans logical value to an integer
  -- (either 0 for false, or 1 for true)
  PredToIntegerFn :: MatlabSolverFn f (EmptyCtx ::> BaseBoolType) BaseIntegerType

  -- 'NatSeqFn base c' denotes the function '\i _ -> base + c*i
  NatSeqFn :: !(f BaseNatType)
           -> !(f BaseNatType)
             -> MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseNatType

  -- 'RealSeqFn base c' denotes the function '\_ i -> base + c*i
  RealSeqFn :: !(f BaseRealType)
             -> !(f BaseRealType)
             -> MatlabSolverFn f (EmptyCtx ::> BaseNatType ::> BaseNatType) BaseRealType

  -- 'IndicesInRange tps upper_bounds' returns a predicate that is true if all the arguments
  -- (which must be natural numbers) are between 1 and the given upper bounds (inclusive).
  IndicesInRange :: !(Ctx.Assignment OnlyNatRepr (idx ::> itp))
                 -> !(Ctx.Assignment f (idx ::> itp))
                    -- ^ Upper bounds on indices
                 -> MatlabSolverFn f (idx ::> itp) BaseBoolType

  IsEqFn :: !(BaseTypeRepr tp)
         -> MatlabSolverFn f (EmptyCtx ::> tp ::> tp) BaseBoolType

-- Dummy declaration splice to bring App into template haskell scope.
$(return [])

traverseMatlabSolverFn :: Applicative m
                       => (forall tp . e tp -> m (f tp))
                       -> MatlabSolverFn e a r
                       -> m (MatlabSolverFn f a r)
traverseMatlabSolverFn f fn_id =
  case fn_id of
    IsIntegerFn          -> pure $ IsIntegerFn
    CplxIsRealFn         -> pure $ CplxIsRealFn
    NatLeFn              -> pure $ NatLeFn
    IntLeFn              -> pure $ IntLeFn
    BVToNatFn w          -> pure $ BVToNatFn w
    SBVToIntegerFn w     -> pure $ SBVToIntegerFn w
    NatToIntegerFn       -> pure $ NatToIntegerFn
    IntegerToNatFn       -> pure $ IntegerToNatFn
    IntegerToRealFn      -> pure $ IntegerToRealFn
    RealToIntegerFn      -> pure $ RealToIntegerFn
    RealToComplexFn      -> pure $ RealToComplexFn
    RealPartOfCplxFn     -> pure $ RealPartOfCplxFn
    PredToIntegerFn      -> pure $ PredToIntegerFn
    NatSeqFn  b i        -> NatSeqFn <$> f b <*> f i
    RealSeqFn b i        -> RealSeqFn <$> f b <*> f i
    IndicesInRange tps a -> IndicesInRange tps <$> traverseFC f a
    IsEqFn tp            -> pure $ IsEqFn tp

-- | Get arg tpyes of solver fn.
matlabSolverArgTypes :: MatlabSolverFn f args ret -> Ctx.Assignment BaseTypeRepr args
matlabSolverArgTypes f =
  case f of
    IsIntegerFn          -> knownRepr
    CplxIsRealFn         -> knownRepr
    NatLeFn              -> knownRepr
    IntLeFn              -> knownRepr
    BVToNatFn w          -> Ctx.singleton (BaseBVRepr w)
    SBVToIntegerFn w     -> Ctx.singleton (BaseBVRepr w)
    NatToIntegerFn       -> knownRepr
    IntegerToNatFn       -> knownRepr
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    PredToIntegerFn      -> knownRepr
    NatSeqFn{}           -> knownRepr
    IndicesInRange tps _ -> fmapFC toBaseTypeRepr tps
    RealSeqFn _ _        -> knownRepr
    IsEqFn tp            -> Ctx.empty Ctx.%> tp Ctx.%> tp

-- | Get return type of solver fn.
matlabSolverReturnType :: MatlabSolverFn f args ret -> BaseTypeRepr ret
matlabSolverReturnType f =
  case f of
    IsIntegerFn          -> knownRepr
    CplxIsRealFn         -> knownRepr
    NatLeFn              -> knownRepr
    IntLeFn              -> knownRepr
    BVToNatFn{}          -> knownRepr
    SBVToIntegerFn{}     -> knownRepr
    NatToIntegerFn       -> knownRepr
    IntegerToNatFn       -> knownRepr
    IntegerToRealFn      -> knownRepr
    RealToIntegerFn      -> knownRepr
    RealToComplexFn      -> knownRepr
    RealPartOfCplxFn     -> knownRepr
    PredToIntegerFn      -> knownRepr
    NatSeqFn{}           -> knownRepr
    IndicesInRange{}     -> knownRepr
    RealSeqFn _ _        -> knownRepr
    IsEqFn{}             -> knownRepr

ppMatlabSolverFn :: IsExpr f => MatlabSolverFn f a r -> Doc
ppMatlabSolverFn f =
  case f of
    IsIntegerFn          -> text "is_integer"
    CplxIsRealFn         -> text "cplx_is_real"
    NatLeFn              -> text "nat_le"
    IntLeFn              -> text "int_le"
    BVToNatFn w          -> parens $ text "bv_to_nat" <+> text (show w)
    SBVToIntegerFn w     -> parens $ text "sbv_to_int" <+> text (show w)
    NatToIntegerFn       -> text "nat_to_integer"
    IntegerToNatFn       -> text "integer_to_nat"
    IntegerToRealFn      -> text "integer_to_real"
    RealToIntegerFn      -> text "real_to_integer"
    RealToComplexFn      -> text "real_to_complex"
    RealPartOfCplxFn     -> text "real_part_of_complex"
    PredToIntegerFn      -> text "pred_to_integer"
    NatSeqFn  b i        -> parens $ text "nat_seq"  <+> printSymExpr b <+> printSymExpr i
    RealSeqFn b i        -> parens $ text "real_seq" <+> printSymExpr b <+> printSymExpr i
    IndicesInRange _ bnds ->
      parens (text "indices_in_range" <+> sep (toListFC printSymExpr bnds))
    IsEqFn{}             -> text "is_eq"


-- | Test 'MatlabSolverFn' values for equality.
testSolverFnEq :: TestEquality f
               => MatlabSolverFn f ax rx
               -> MatlabSolverFn f ay ry
               -> Maybe ((ax ::> rx) :~: (ay ::> ry))
testSolverFnEq = $(structuralTypeEquality [t|MatlabSolverFn|]
                   [ ( DataArg 0 `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|NatRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|Ctx.Assignment|] `TypeApp` AnyType `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   , ( ConType [t|BaseTypeRepr|] `TypeApp` AnyType
                     , [|testEquality|]
                     )
                   ]
                  )

instance ( Hashable (f BaseNatType)
         , Hashable (f BaseRealType)
         , HashableF f
         )
         => Hashable (MatlabSolverFn f args tp) where
  hashWithSalt = $(structuralHash [t|MatlabSolverFn|])

evalMatlabSolverFn :: forall sym args ret
                   .  IsExprBuilder sym
                   => MatlabSolverFn (SymExpr sym) args ret
                   -> sym
                   -> Ctx.Assignment (SymExpr sym) args
                   -> IO (SymExpr sym ret)
evalMatlabSolverFn f sym =
  case f of
    IsIntegerFn      -> Ctx.uncurryAssignment $ isInteger sym
    CplxIsRealFn     -> Ctx.uncurryAssignment $ isReal sym
    NatLeFn          -> Ctx.uncurryAssignment $ natLe sym
    IntLeFn          -> Ctx.uncurryAssignment $ intLe sym
    BVToNatFn{}      -> Ctx.uncurryAssignment $ bvToNat sym
    SBVToIntegerFn{} -> Ctx.uncurryAssignment $ sbvToInteger sym
    NatToIntegerFn   -> Ctx.uncurryAssignment $ natToInteger sym
    IntegerToNatFn   -> Ctx.uncurryAssignment $ integerToNat sym
    IntegerToRealFn  -> Ctx.uncurryAssignment $ integerToReal sym
    RealToIntegerFn  -> Ctx.uncurryAssignment $ realToInteger sym
    RealToComplexFn  -> Ctx.uncurryAssignment $ cplxFromReal sym
    RealPartOfCplxFn -> Ctx.uncurryAssignment $ getRealPart sym
    PredToIntegerFn  -> Ctx.uncurryAssignment $ \p ->
      iteM intIte sym p (intLit sym 1) (intLit sym 0)
    NatSeqFn base inc   -> Ctx.uncurryAssignment $ \idx _ -> do
      natAdd sym base =<< natMul sym inc idx
    RealSeqFn base inc -> Ctx.uncurryAssignment $ \_ idx -> do
      realAdd sym base =<< realMul sym inc =<< natToReal sym idx
    IndicesInRange tps0 bnds0 -> \args ->
        Ctx.forIndex (Ctx.size tps0) (g tps0 bnds0 args) (pure (truePred sym))
      where g :: Ctx.Assignment OnlyNatRepr ctx
              -> Ctx.Assignment (SymExpr sym) ctx
              -> Ctx.Assignment (SymExpr sym) ctx
              -> IO (Pred sym)
              -> Ctx.Index ctx tp
              -> IO (Pred sym)
            g tps bnds args m i = do
              case tps Ctx.! i of
                OnlyNatRepr -> do
                  let v = args Ctx.! i
                  let bnd = bnds Ctx.! i
                  one <- natLit sym 1
                  p <- join $ andPred sym <$> natLe sym one v <*> natLe sym v bnd
                  andPred sym p =<< m
    IsEqFn{} -> Ctx.uncurryAssignment $ \x y -> do
      isEq sym x y

-- | This class is provides functions needed to implement the symbolic
-- array intrinsic functions
class IsSymInterface sym => MatlabSymbolicArrayBuilder sym where

  -- | Create a Matlab solver function from its prototype.
  mkMatlabSolverFn :: sym
                   -> MatlabSolverFn (SymExpr sym) args ret
                   -> IO (SymFn sym args ret)
