{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | A parser for an s-expression representation of formulas
module SemMC.Formula.Parser
  ( operandVarPrefix
  , literalVarPrefix
  , argumentVarPrefix
  , readFormula
  , readFormulaFromFile
  , readDefinedFunction
  , readDefinedFunctionFromFile
  ) where

import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.Reader as MR
import           Control.Monad ( when )
import           Data.Foldable ( foldrM )
import           Data.Kind
import qualified Data.Map as Map
import qualified Data.SCargot.Repr as SC
import           Data.Semigroup
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Text.Printf ( printf )
import qualified Data.Set as Set
import           GHC.TypeLits ( Symbol )
import           Data.Proxy ( Proxy(..) )

import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..), mapSome, viewSome )
import qualified Data.Parameterized.List as SL
import           Data.Parameterized.TraversableFC ( traverseFC, allFC )
import qualified Data.Parameterized.Map as MapF
import           What4.BaseTypes
import qualified Lang.Crucible.Backend as S
import qualified What4.Interface as S
import           What4.Symbol ( userSymbol )

import qualified Data.Type.List as TL -- in this package
import qualified SemMC.Architecture as A
import qualified SemMC.Architecture.Location as L
import qualified SemMC.BoundVar as BV
import           SemMC.Formula.Env ( FormulaEnv(..), SomeSome(..) )
import           SemMC.Formula.Formula
import           SemMC.Formula.SETokens
import qualified SemMC.Util as U

import           Prelude

data OperandTypeWrapper (arch :: Type) :: TL.TyFun Symbol BaseType -> Type
type instance TL.Apply (OperandTypeWrapper arch) s = A.OperandType arch s
type OperandTypes arch sh = TL.Map (OperandTypeWrapper arch) sh

-- | A counterpart to 'SemMC.Formula.Parameter' for use in the parser, where we
-- might know only a parameter's base type (such as when parsing a defined
-- function).
data ParsedParameter arch (tps :: [BaseType]) (tp :: BaseType) where
  ParsedOperandParameter :: BaseTypeRepr tp -> SL.Index tps tp
                         -> ParsedParameter arch tps tp
  ParsedLiteralParameter :: L.Location arch tp -> ParsedParameter arch tps tp

-- Translating from 'SL.Index' on 'BaseType' to 'SL.Index' on 'Symbol' is
-- tricky.  Need this view to show that when we translate some @SL.Index tps tp@
-- to an @SL.Index sh s@, the symbol @s@ maps to the base type @tp@ (assuming
-- that @tps ~ OperandTypes arch sh@).
data IndexByArchType arch sh tp where
  IndexByArchType :: A.OperandType arch s ~ tp => SL.Index sh s -> IndexByArchType arch sh tp

-- TODO This is all very silly. It's an expensive identity function.
indexByArchType :: proxy arch
                -> A.ShapeRepr arch sh
                -> SL.Index (OperandTypes arch sh) tp
                -> IndexByArchType arch sh tp
indexByArchType _ SL.Nil _ = error "impossible"
indexByArchType _ (_ SL.:< _) SL.IndexHere = IndexByArchType SL.IndexHere
indexByArchType p (_ SL.:< shapeRepr) (SL.IndexThere ix) =
  case indexByArchType p shapeRepr ix of
    IndexByArchType ix' -> IndexByArchType (SL.IndexThere ix')

toParameter :: forall arch sh tp
             . A.ShapeRepr arch sh
            -> ParsedParameter arch (OperandTypes arch sh) tp
            -> Parameter arch sh tp
toParameter shapeRepr (ParsedOperandParameter tpRepr ix) =
  case indexByArchType (Proxy @arch) shapeRepr ix of
    IndexByArchType ix' -> OperandParameter tpRepr ix'
toParameter _ (ParsedLiteralParameter loc) =
  LiteralParameter loc

-- * First pass of parsing turns the raw text into s-expressions.
--   This pass is handled by the code in SemMC.Formula.SELang

-- * Second pass of parsing: turning the s-expressions into symbolic expressions
-- and the overall templated formula

-- ** Utility functions

-- | Utility function for contextualizing errors. Prepends the given prefix
-- whenever an error is thrown.
prefixError :: (Monoid e, E.MonadError e m) => e -> m a -> m a
prefixError prefix act = E.catchError act (E.throwError . mappend prefix)

-- | Utility function for lifting a 'Maybe' into a 'MonadError'
fromMaybeError :: (E.MonadError e m) => e -> Maybe a -> m a
fromMaybeError err = maybe (E.throwError err) return

-- ** Parsing operands

-- | Data about the operands pertinent after parsing: their name and their type.
data OpData (tp :: BaseType) where
  OpData :: String -> BaseTypeRepr tp -> OpData tp

buildOperandList' :: forall m proxy arch tps
                   . (E.MonadError String m, A.Architecture arch)
                  => proxy arch
                  -> A.ShapeRepr arch tps
                  -> SC.SExpr FAtom
                  -> m (SL.List OpData (OperandTypes arch tps))
buildOperandList' proxy rep atm =
  case rep of
    SL.Nil ->
      case atm of
        SC.SNil -> return SL.Nil
        _ -> E.throwError $ "Expected Nil but got " ++ show atm
    r SL.:< rep' ->
      case atm of
        SC.SNil -> E.throwError $ "Expected entry but got Nil"
        SC.SAtom _ -> E.throwError $ "Expected SCons but got SAtom: " ++ show atm
        SC.SCons s rest -> do
          let SC.SCons (SC.SAtom (AIdent operand)) (SC.SAtom (AQuoted ty)) = s
          when (A.operandTypeReprSymbol proxy r /= ty) $
            E.throwError $ "unknown reference: " ++ show ty
          rest' <- buildOperandList' proxy rep' rest
          let tyRepr = A.shapeReprToTypeRepr proxy r
          return $ (OpData operand tyRepr) SL.:< rest'

buildArgumentList' :: forall m
                    . (E.MonadError String m)
                   => SC.SExpr FAtom
                   -> m (Some (SL.List OpData))
buildArgumentList' sexpr =
  case sexpr of
    SC.SNil -> return $ Some (SL.Nil)
    SC.SAtom _ -> E.throwError $ "Expected SNil or SCons but got SAtom: " ++ show sexpr
    SC.SCons s rest -> do
      (operand, tyRaw) <- case s of
        SC.SCons (SC.SAtom (AIdent operand)) (SC.SCons ty SC.SNil)
          -> return (operand, ty)
        _ -> E.throwError $ "Expected (operand . 'type) pair: " ++ show s
      Some tp <- readBaseType tyRaw
      Some rest' <- buildArgumentList' rest
      return $ Some ((OpData operand tp) SL.:< rest')

readBaseType :: forall m
              . (E.MonadError String m)
             => SC.SExpr FAtom
             -> m (Some BaseTypeRepr)
readBaseType sexpr =
  case sexpr of
    SC.SAtom (AQuoted atom) ->
      case atom of
        "bool" -> return $ Some BaseBoolRepr
        "nat" -> return $ Some BaseNatRepr
        "int" -> return $ Some BaseIntegerRepr
        "real" -> return $ Some BaseRealRepr
        "string" -> return $ Some (BaseStringRepr UnicodeRepr)
        "complex" -> return $ Some BaseComplexRepr
        _ -> panic
    SC.SCons (SC.SAtom (AQuoted "bv")) (SC.SCons (SC.SAtom (AInt w)) SC.SNil)
      | Just (Some wRepr) <- someNat w
      , Just LeqProof <- testLeq (knownNat @1) wRepr
        -> return $ Some (BaseBVRepr wRepr)
      | otherwise
        -> panic
    SC.SCons (SC.SAtom (AQuoted "struct")) (SC.SCons args SC.SNil) -> do
      Some tps <- readBaseTypes args
      return $ Some (BaseStructRepr tps)
    SC.SCons (SC.SAtom (AQuoted "array"))
             (SC.SCons ixArgs (SC.SCons tpArg SC.SNil)) -> do
      Some ixs <- readBaseTypes ixArgs
      Some tp <- readBaseType tpArg
      case Ctx.viewAssign ixs of
        Ctx.AssignEmpty -> E.throwError $ "array type has no indices: " ++ show sexpr
        Ctx.AssignExtend _ _ -> return $ Some (BaseArrayRepr ixs tp)
    _ -> panic
  where
    panic = E.throwError $ "unknown base type: " ++ show sexpr

readBaseTypes :: forall m
              . (E.MonadError String m)
              => SC.SExpr FAtom
              -> m (Some (Ctx.Assignment BaseTypeRepr))
readBaseTypes sexpr0 =
  go sexpr0 Ctx.empty
  where
    -- Be tail recursive to reverse list
    go :: SC.SExpr FAtom
       -> Ctx.Assignment BaseTypeRepr sh
       -> m (Some (Ctx.Assignment BaseTypeRepr))
    go sexpr acc =
      case sexpr of
        SC.SNil -> return (Some acc)
        SC.SCons s rest -> do
          Some tp <- readBaseType s
          go rest (Ctx.extend acc tp)
        SC.SAtom _ -> E.throwError $
          "expected list of base types: " ++ show sexpr

-- ** Parsing parameters
--
-- By which I mean, handling occurrences in expressions of either operands or
-- literals.

-- | Low-level representation of a parameter: no checking done yet on whether
-- they're valid yet or not.
data RawParameter = RawOperand String
                  | RawLiteral String
                  deriving (Show, Eq, Ord)

operandVarPrefix :: String
operandVarPrefix = "op_"

literalVarPrefix :: String
literalVarPrefix = "lit_"

argumentVarPrefix :: String
argumentVarPrefix = "arg_"

-- | Parses the name of a parameter and whether it's an operand or a literal.
readRawParameter :: (E.MonadError String m) => FAtom -> m RawParameter
readRawParameter (AIdent name)
  | Right _ <- userSymbol (operandVarPrefix ++ name) = return (RawOperand name)
  | otherwise = E.throwError $ printf "%s is not a valid parameter name" name
readRawParameter (AQuoted name)
  | Right _ <- userSymbol (literalVarPrefix ++ name) = return (RawLiteral name)
  | otherwise = E.throwError $ printf "%s is not a valid parameter name" name
readRawParameter a = E.throwError $ printf "expected parameter, found %s" (show a)

-- | Short-lived type that just stores an index with its corresponding type
-- representation, with the type parameter ensuring they correspond to one another.
data IndexWithType (sh :: [BaseType]) (tp :: BaseType) where
  IndexWithType :: BaseTypeRepr tp -> SL.Index sh tp -> IndexWithType sh tp

-- | Look up a name in the given operand list, returning its index and type if found.
findOpListIndex :: String -> SL.List OpData sh -> Maybe (Some (IndexWithType sh))
findOpListIndex _ SL.Nil = Nothing
findOpListIndex x ((OpData name tpRepr) SL.:< rest)
  | x == name = Just $ Some (IndexWithType tpRepr SL.IndexHere)
  | otherwise = mapSome incrIndex <$> findOpListIndex x rest
      where incrIndex (IndexWithType tpRepr' idx) = IndexWithType tpRepr' (SL.IndexThere idx)

-- | Parse a single parameter, given the list of operands to use as a lookup.
readParameter :: (E.MonadError String m, A.Architecture arch) => proxy arch -> SL.List OpData tps -> FAtom -> m (Some (ParsedParameter arch tps))
readParameter _ oplist atom =
  readRawParameter atom >>= \case
    RawOperand op ->
      maybe (E.throwError $ printf "couldn't find operand %s" op)
            (viewSome (\(IndexWithType tpRepr idx) -> return $ Some (ParsedOperandParameter tpRepr idx)))
            (findOpListIndex op oplist)
    RawLiteral lit ->
      maybe (E.throwError $ printf "%s is an invalid literal for this arch" lit)
            (return . viewSome (Some . ParsedLiteralParameter))
            (A.readLocation lit)

-- | Parses the input list, e.g., @(ra rb 'ca)@
readInputs :: forall m (arch :: Type) (tps :: [BaseType])
            . (E.MonadError String m,
               A.Architecture arch)
           => SL.List OpData tps
           -> SC.SExpr FAtom
           -> m [Some (ParsedParameter arch tps)]
readInputs _ SC.SNil = return []
readInputs oplist (SC.SCons (SC.SAtom p) rest) = do
  p' <- readParameter Proxy oplist p
  rest' <- readInputs oplist rest
  return $ p' : rest'
readInputs _ i = E.throwError $ "malformed input list: " <> show i

-- ** Parsing definitions

-- | "Global" data stored in the Reader monad throughout parsing the definitions.
data DefsInfo sym arch tps = DefsInfo
                             { getSym :: sym
                             -- ^ SymInterface/ExprBuilder used to build up symbolic
                             -- expressions while parsing the definitions.
                             , getEnv :: FormulaEnv sym arch
                             -- ^ Global formula environment
                             , getLitLookup :: forall tp. A.Location arch tp -> Maybe (S.SymExpr sym tp)
                             -- ^ Function used to retrieve the expression
                             -- corresponding to a given literal.
                             , getOpVarList :: SL.List (S.BoundVar sym) tps
                             -- ^ ShapedList used to retrieve the variable
                             -- corresponding to a given literal.
                             , getOpNameList :: SL.List OpData tps
                             -- ^ ShapedList used to look up the index given an
                             -- operand's name.
                             , getBindings :: Map.Map FAtom (Some (S.SymExpr sym))
                             -- ^ Mapping of currently in-scope let-bound variables
                             --- to their parsed bindings.
                             }

-- | Stores a NatRepr along with proof that its type parameter is a bitvector of
-- that length. Used for easy pattern matching on the LHS of a binding in a
-- do-expression to extract the proof.
data BVProof tp where
  BVProof :: forall n. (1 <= n) => NatRepr n -> BVProof (BaseBVType n)

-- | Given an expression, monadically either returns proof that it is a
-- bitvector or throws an error.
getBVProof :: (S.IsExpr ex, E.MonadError String m) => ex tp -> m (BVProof tp)
getBVProof expr =
  case S.exprType expr of
    BaseBVRepr n -> return $ BVProof n
    t -> E.throwError $ printf "expected BV, found %s" (show t)


-- | Operator type descriptions for parsing s-expression of
-- the form @(operator operands ...)@.
data Op sym where
  -- | Generic unary operator description.
    Op1 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1)
        -> (sym ->
            S.SymExpr sym arg1 ->
            IO (S.SymExpr sym ret))
        -> Op sym
  -- | Generic dyadic operator description.
    Op2 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2)
        -> (sym ->
            S.SymExpr sym arg1 ->
            S.SymExpr sym arg2 ->
            IO (S.SymExpr sym ret))
        -> Op sym
  -- | Generic triadic operator description.
    Op3 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3)
        -> (sym ->
            S.SymExpr sym arg1 ->
            S.SymExpr sym arg2 ->
            S.SymExpr sym arg3 ->
            IO (S.SymExpr sym ret)
           )
        -> Op sym
    -- | Generic tetradic operator description.
    Op4 :: Ctx.Assignment
           BaseTypeRepr
           (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3 Ctx.::> arg4)
        -> ( sym ->
             S.SymExpr sym arg1 ->
             S.SymExpr sym arg2 ->
             S.SymExpr sym arg3 ->
             S.SymExpr sym arg4 ->
             IO (S.SymExpr sym ret)
           )
        -> Op sym
    -- | Encapsulating type for a unary operation that takes one bitvector and
    -- returns another (in IO).
    BVOp1 :: (forall w . (1 <= w) =>
               sym ->
               S.SymBV sym w ->
               IO (S.SymBV sym w))
          -> Op sym
    -- | Binop with a bitvector return type, e.g., addition or bitwise operations.
    BVOp2 :: (forall w . (1 <= w) =>
               sym ->
               S.SymBV sym w ->
               S.SymBV sym w ->
               IO (S.SymBV sym w))
          -> Op sym
    -- | Bitvector binop with a boolean return type, i.e., comparison operators.
    BVComp2 :: (forall w . (1 <= w) =>
                    sym ->
                    S.SymBV sym w ->
                    S.SymBV sym w ->
                    IO (S.Pred sym))
                -> Op sym

-- | Lookup mapping operators to their Op definitions (if they exist)
lookupOp :: forall sym . S.IsSymExprBuilder sym => String -> Maybe (Op sym)
lookupOp = \case
  -- -- -- Boolean ops -- -- --
  "andp" -> Just $ Op2 knownRepr $ S.andPred
  "orp"  -> Just $ Op2 knownRepr $ S.orPred
  "xorp" -> Just $ Op2 knownRepr $ S.xorPred
  "notp" -> Just $ Op1 knownRepr $ S.notPred
  -- -- -- Natural ops -- -- --
  "natmul" -> Just $ Op2 knownRepr $ S.natMul
  "natadd" -> Just $ Op2 knownRepr $ S.natAdd
  "natle"  -> Just $ Op2 knownRepr $ S.natLe
  -- -- -- Integer ops -- -- --
  "intmul" -> Just $ Op2 knownRepr $ S.intMul
  "intadd" -> Just $ Op2 knownRepr $ S.intAdd
  "intmod" -> Just $ Op2 knownRepr $ S.intMod
  "intdiv" -> Just $ Op2 knownRepr $ S.intDiv
  "intle"  -> Just $ Op2 knownRepr $ S.intLe
  -- -- -- Bitvector ops -- -- --
  "bvand" -> Just $ BVOp2 S.bvAndBits
  "bvor" -> Just $ BVOp2 S.bvOrBits
  "bvadd" -> Just $ BVOp2 S.bvAdd
  "bvmul" -> Just $ BVOp2 S.bvMul
  "bvudiv" -> Just $ BVOp2 S.bvUdiv
  "bvurem" -> Just $ BVOp2 S.bvUrem
  "bvshl" -> Just $ BVOp2 S.bvShl
  "bvlshr" -> Just $ BVOp2 S.bvLshr
  "bvnand" -> Just $ BVOp2 $ \sym arg1 arg2 -> S.bvNotBits sym =<< S.bvAndBits sym arg1 arg2
  "bvnor" -> Just $ BVOp2 $ \sym arg1 arg2 -> S.bvNotBits sym =<< S.bvOrBits sym arg1 arg2
  "bvxor" -> Just $ BVOp2 S.bvXorBits
  "bvxnor" -> Just $ BVOp2 $ \sym arg1 arg2 -> S.bvNotBits sym =<< S.bvXorBits sym arg1 arg2
  "bvsub" -> Just $ BVOp2 S.bvSub
  "bvsdiv" -> Just $ BVOp2 S.bvSdiv
  "bvsrem" -> Just $ BVOp2 S.bvSrem
  "bvsmod" -> error "bvsmod is not implemented"
  "bvashr" -> Just $ BVOp2 S.bvAshr
  "bvult" -> Just $ BVComp2 S.bvUlt
  "bvule" -> Just $ BVComp2 S.bvUle
  "bvugt" -> Just $ BVComp2 S.bvUgt
  "bvuge" -> Just $ BVComp2 S.bvUge
  "bvslt" -> Just $ BVComp2 S.bvSlt
  "bvsle" -> Just $ BVComp2 S.bvSle
  "bvsgt" -> Just $ BVComp2 S.bvSgt
  "bvsge" -> Just $ BVComp2 S.bvSge
  "bveq" -> Just $ BVComp2 S.bvEq
  "bvne" -> Just $ BVComp2 S.bvNe
  "bvneg" -> Just $ BVOp1 S.bvNeg
  "bvnot" -> Just $ BVOp1 S.bvNotBits
  -- -- -- Floating point ops -- -- --
  "fnegd" -> Just $ Op1 knownRepr $ S.floatNeg @_ @Prec64
  "fnegs" -> Just $ Op1 knownRepr $ S.floatNeg @_ @Prec32
  "fabsd" -> Just $ Op1 knownRepr $ S.floatAbs @_ @Prec64
  "fabss" -> Just $ Op1 knownRepr $ S.floatAbs @_ @Prec32
  "fsqrt" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatSqrt @_ @Prec64 sym rm x
  "fsqrts" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatSqrt @_ @Prec32 sym rm x
  "fnand" -> Just $ Op1 knownRepr $ S.floatIsNaN @_ @Prec64
  "fnans" -> Just $ Op1 knownRepr $ S.floatIsNaN @_ @Prec32
  "frsp" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatCast @_ @Prec32 @Prec64 sym knownRepr rm x
  "fp_single_to_double" -> Just $ Op1 knownRepr $ \sym ->
    S.floatCast @_ @Prec64 @Prec32 sym knownRepr S.RNE
  "fp_binary_to_double" ->
    Just $ Op1 knownRepr $ \sym -> S.floatFromBinary @_ @11 @53 sym knownRepr
  "fp_binary_to_single" ->
    Just $ Op1 knownRepr $ \sym -> S.floatFromBinary @_ @8 @24 sym knownRepr
  "fp_double_to_binary" -> Just $ Op1 knownRepr $ S.floatToBinary @_ @11 @53
  "fp_single_to_binary" -> Just $ Op1 knownRepr $ S.floatToBinary @_ @8 @24
  "fctid" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatToSBV @_ @64 @Prec64 sym knownRepr rm x
  "fctidu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatToBV @_ @64 @Prec64 sym knownRepr rm x
  "fctiw" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatToSBV @_ @32 @Prec64 sym knownRepr rm x
  "fctiwu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatToBV @_ @32 @Prec64 sym knownRepr rm x
  "fcfid" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.sbvToFloat @_ @64 @Prec64 sym knownRepr rm x
  "fcfids" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.sbvToFloat @_ @64 @Prec32 sym knownRepr rm x
  "fcfidu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.bvToFloat @_ @64 @Prec64 sym knownRepr rm x
  "fcfidus" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.bvToFloat @_ @64 @Prec32 sym knownRepr rm x
  "frti" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatRound @_ @Prec64 sym rm x
  "frtis" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    S.floatRound @_ @Prec32 sym rm x
  "fadd" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatAdd @_ @Prec64 sym rm x y
  "fadds" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatAdd @_ @Prec32 sym rm x y
  "fsub" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatSub @_ @Prec64 sym rm x y
  "fsubs" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatSub @_ @Prec32 sym rm x y
  "fmul" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatMul @_ @Prec64 sym rm x y
  "fmuls" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatMul @_ @Prec32 sym rm x y
  "fdiv" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatDiv @_ @Prec64 sym rm x y
  "fdivs" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    S.floatDiv @_ @Prec32 sym rm x y
  "fltd" -> Just $ Op2 knownRepr $ S.floatLt @_ @Prec64
  "flts" -> Just $ Op2 knownRepr $ S.floatLt @_ @Prec32
  "feqd" -> Just $ Op2 knownRepr $ S.floatFpEq @_ @Prec64
  "feqs" -> Just $ Op2 knownRepr $ S.floatFpEq @_ @Prec32
  "fled" -> Just $ Op2 knownRepr $ S.floatLe @_ @Prec64
  "fles" -> Just $ Op2 knownRepr $ S.floatLe @_ @Prec32
  "ffma" -> Just $ Op4 knownRepr $ \sym r x y z -> U.withRounding sym r $ \rm ->
    S.floatFMA @_ @Prec64 sym rm x y z
  "ffmas" -> Just $ Op4 knownRepr $ \sym r x y z ->
    U.withRounding sym r $ \rm -> S.floatFMA @_ @Prec32 sym rm x y z
  _ -> Nothing

-- | Verify a list of arguments has a single argument and
-- return it, else raise an error.
readOneArg ::
  (S.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym arch sh) m,
    A.Architecture arch,
    MonadIO m)
  => SC.SExpr FAtom
  -> m (Some (S.SymExpr sym))
readOneArg operands = do
  args <- readExprs operands
  when (length args /= 1)
    (E.throwError $ printf "expecting 1 argument, got %d" (length args))
  return $ args !! 0

-- | Verify a list of arguments has two arguments and return
-- it, else raise an error.
readTwoArgs ::
  (S.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym arch sh) m,
    A.Architecture arch,
    MonadIO m)
  => SC.SExpr FAtom
  -> m (Some (S.SymExpr sym), Some (S.SymExpr sym))
readTwoArgs operands = do
  args <- readExprs operands
  when (length args /= 2)
    (E.throwError $ printf "expecting 2 arguments, got %d" (length args))
  return $ (args !! 0, args !! 1)

-- | Verify a list of arguments has three arguments and
-- return it, else raise an error.
readThreeArgs ::
  (S.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym arch sh) m,
    A.Architecture arch,
    MonadIO m)
  => SC.SExpr FAtom
  -> m (Some (S.SymExpr sym), Some (S.SymExpr sym), Some (S.SymExpr sym))
readThreeArgs operands = do
  args <- readExprs operands
  when (length args /= 3)
    (E.throwError $ printf "expecting 3 arguments, got %d" (length args))
  return $ (args !! 0, args !! 1, args !! 2)


-- | Reads an "application" form, i.e. @(operator operands ...)@.
readApp ::
  forall sym m arch sh .
  (S.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym arch sh) m,
    A.Architecture arch,
    MonadIO m)
  => SC.SExpr FAtom
  -> SC.SExpr FAtom
  -> m (Some (S.SymExpr sym))
readApp opRaw@(SC.SAtom (AIdent operator)) operands = do
  sym <- MR.reader getSym
  prefixError ("in reading expression:\n"
              -- ++(show $ SC.SCons opRaw operands)++"\n") $ -- the raw display version
               ++(T.unpack $ printTokens mempty $ SC.SCons opRaw operands)++"\n") $
  -- Parse an expression of the form @(fnname operands ...)@
    case lookupOp operator of
      Just (Op1 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 ->
            liftIO (Some <$> fn sym arg1)
          _ -> error "Unable to unpack Op1 arg in Formula.Parser readApp"
      Just (Op2 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 ->
              liftIO (Some <$> fn sym arg1 arg2)
          _ -> error "Unable to unpack Op2 arg in Formula.Parser readApp"
      Just (Op3 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3)
          _ -> error "Unable to unpack Op3 arg in Formula.Parser readApp"
      Just (Op4 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 Ctx.:> arg4 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3 arg4)
          _ -> error "Unable to unpack Op4 arg in Formula.Parser readApp"
      Just (BVOp1 op) -> do
        Some expr <- readOneArg operands
        BVProof _ <- getBVProof expr
        liftIO $ Some <$> op sym expr
      Just (BVOp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Just (BVComp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Nothing ->
        -- Operators/syntactic-forms with types too
        -- complicated to nicely fit in the Op type
        case operator of
          "concat" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            BVProof _ <- prefixError "in arg 1: " $ getBVProof arg1
            BVProof _ <- prefixError "in arg 2: " $ getBVProof arg2
            liftIO (Some <$> S.bvConcat sym arg1 arg2)
          "=" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            case testEquality (S.exprType arg1) (S.exprType arg2) of
              Just Refl -> liftIO (Some <$> S.isEq sym arg1 arg2)
              Nothing -> E.throwError $
                printf "arguments must have same types, \
                       \but arg 1 has type %s \
                       \and arg 2 has type %s"
                (show (S.exprType arg1))
                (show (S.exprType arg2))
          "ite" -> do
            (Some test, Some then_, Some else_)  <- readThreeArgs operands
            case S.exprType test of
              BaseBoolRepr ->
                case testEquality (S.exprType then_) (S.exprType else_) of
                  Just Refl -> liftIO (Some <$> S.baseTypeIte sym test then_ else_)
                  Nothing -> E.throwError $
                    printf "then and else branches must have same type, \
                           \but then has type %s \
                           \and else has type %s"
                    (show (S.exprType then_))
                    (show (S.exprType else_))
              tp -> E.throwError $ printf "test expression must be a boolean; got %s" (show tp)
          "select" -> do
            (Some arr, Some idx)  <- readTwoArgs operands
            ArraySingleDim _ <- expectArrayWithIndex (S.exprType idx) (S.exprType arr)
            let idx' = Ctx.empty Ctx.:> idx
            liftIO (Some <$> S.arrayLookup sym arr idx')
          "store" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (S.exprType idx) (S.exprType arr)
            case testEquality resRepr (S.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> S.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (S.exprType expr))
          "updateArray" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (S.exprType idx) (S.exprType arr)
            case testEquality resRepr (S.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> S.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (S.exprType expr))
          "field" -> do
            case operands of
              SC.SCons rawStruct (SC.SCons (SC.SAtom (AInt rawIdx)) SC.SNil) -> do
                Some struct  <- readExpr rawStruct
                case S.exprType struct of
                  (BaseStructRepr fldTpReprs) ->
                    case Ctx.intIndex (fromInteger rawIdx) (Ctx.size fldTpReprs) of
                      Just (Some i) -> liftIO (Some <$> S.structField sym struct i)
                      Nothing -> E.throwError $
                        unwords ["invalid struct index, got", show fldTpReprs, "and", show rawIdx]
                  srepr -> E.throwError $ unwords ["expected a struct, got", show srepr]
              _ -> E.throwError $ unwords ["expected an arg and an Int, got", show operands]
          "struct" -> do
            case operands of
              SC.SCons rawFldExprs SC.SNil -> do
                Some flds <- readExprsAsAssignment rawFldExprs
                liftIO (Some <$> S.mkStruct sym flds)
              _ -> E.throwError $ unwords ["struct expects a single operand, got", show operands]
          "sbvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> S.sbvToInteger sym arg
          "bvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> S.bvToInteger sym arg
          "integerToBV" -> do
            case operands of
              SC.SCons (SC.SAtom (ANat width)) (SC.SCons rawValExpr SC.SNil) -> do
                Some x <- readExpr rawValExpr
                case (mkNatRepr width, S.exprType x) of
                  (Some w, BaseIntegerRepr)
                    | Just LeqProof <- isPosNat w -> do
                    liftIO (Some <$> S.integerToBV sym x w)
                  srepr -> E.throwError $ unwords ["expected a non-zero natural and an integer, got", show srepr]
              _ -> E.throwError $ unwords ["integerToBV expects two operands, the first of which is a nat, got", show operands]
          _ -> E.throwError $ printf "couldn't parse application of %s" (printTokens mempty opRaw)
-- Parse an expression of the form @((_ extract i j) x)@.
readApp (SC.SCons (SC.SAtom (AIdent "_"))
             (SC.SCons (SC.SAtom (AIdent "extract"))
              (SC.SCons (SC.SAtom (AInt iInt))
               (SC.SCons (SC.SAtom (AInt jInt))
                SC.SNil))))
  args = prefixError "in reading extract expression: " $ do
  sym <- MR.reader getSym
  (Some arg) <- readOneArg args
  -- The SMT-LIB spec represents extracts differently than Crucible does. Per
  -- SMT: "extraction of bits i down to j from a bitvector of size m to yield a
  -- new bitvector of size n, where n = i - j + 1". Per Crucible:
  --
  -- > -- | Select a subsequence from a bitvector.
  -- > bvSelect :: (1 <= n, idx + n <= w)
  -- >          => sym
  -- >          -> NatRepr idx  -- ^ Starting index, from 0 as least significant bit
  -- >          -> NatRepr n    -- ^ Number of bits to take
  -- >          -> SymBV sym w  -- ^ Bitvector to select from
  -- >          -> IO (SymBV sym n)
  --
  -- The "starting index" seems to be from the bottom, so that (in slightly
  -- pseudocode)
  --
  -- > > bvSelect sym 0 8 (0x01020304:[32])
  -- > 0x4:[8]
  -- > > bvSelect sym 24 8 (0x01020304:[32])
  -- > 0x1:[8]
  --
  -- Thus, n = i - j + 1, and idx = j.
  let nInt = iInt - jInt + 1
      idxInt = jInt
  Some nNat <- prefixError "in calculating extract length: " $ intToNatM nInt
  Some idxNat <- prefixError "in extract lower bound: " $ intToNatM idxInt
  LeqProof <- fromMaybeError "extract length must be positive" $ isPosNat nNat
  BVProof lenNat <- getBVProof arg
  LeqProof <- fromMaybeError "invalid extract for given bitvector" $
    testLeq (addNat idxNat nNat) lenNat
  liftIO (Some <$> S.bvSelect sym idxNat nNat arg)
-- Parse an expression of the form @((_ zero_extend i) x)@ or @((_ sign_extend i) x)@.
readApp (SC.SCons (SC.SAtom (AIdent "_"))
             (SC.SCons (SC.SAtom (AIdent extend))
               (SC.SCons (SC.SAtom (AInt iInt))
                SC.SNil)))
  args
  | extend == "zero_extend" ||
    extend == "sign_extend" = prefixError (printf "in reading %s expression: " extend) $ do
      sym <- MR.reader getSym
      Some arg <- readOneArg args
      Some iNat <- intToNatM iInt
      iPositive <- fromMaybeError "must extend by a positive length" $ isPosNat iNat
      BVProof lenNat <- getBVProof arg
      let newLen = addNat lenNat iNat
      liftIO $ withLeqProof (leqAdd2 (leqRefl lenNat) iPositive) $
        let op = if extend == "zero_extend" then S.bvZext else S.bvSext
        in Some <$> op sym newLen arg
-- | Parse an expression of the form:
--
-- > ((_ call "undefined") "bv" size)
--
-- This has to be separate from the normal uninterpreted functions because the
-- type is determined by the arguments.
readApp (SC.SCons (SC.SAtom (AIdent "_"))
                (SC.SCons (SC.SAtom (AIdent "call"))
                  (SC.SCons (SC.SAtom (AString "uf.undefined"))
                    SC.SNil)))
  operands = do
  (Some ex) <- readOneArg operands
  case S.exprType ex of
    BaseBVRepr {}
      | Just size <- S.asUnsignedBV ex -> do
          sym <- MR.reader getSym
          case NR.someNat ((fromIntegral size) :: Integer) of
            Just (Some nr) -> mkUndefined nr sym
            Nothing -> E.throwError $ printf "Invalid size for undefined value: %d" size
    ety -> E.throwError $ printf "Invalid expr type: %s" (show ety)
  where
    mkUndefined :: NR.NatRepr n -> sym -> m (Some (S.SymExpr sym))
    mkUndefined nr sym = do
      case NR.testLeq (knownNat @1) nr of
        Just NR.LeqProof -> do
          let rty = BaseBVRepr nr
          fn <- liftIO (S.freshTotalUninterpFn sym (U.makeSymbol "uf.undefined") Ctx.empty rty)
          assn <- exprAssignment (S.fnArgTypes fn) []
          Some <$> liftIO (S.applySymFn sym fn assn)
        Nothing -> E.throwError $ printf "Invalid size for undefined value: %d" (NR.widthVal nr)
-- Parse an expression of the form @((_ call "foo") x y ...)@
readApp (SC.SCons (SC.SAtom (AIdent "_"))
            (SC.SCons (SC.SAtom (AIdent "call"))
               (SC.SCons (SC.SAtom (AString fnName))
                  SC.SNil)))
  operands =
  prefixError ("in reading call '" <> fnName <> "' expression: ") $ do
    sym <- MR.reader getSym
    fns <- MR.reader (envFunctions . getEnv)
    SomeSome fn <- case Map.lookup fnName fns of
      Just (fn, _) -> return fn
      Nothing ->
        let template = case take 3 fnName of
              "uf." -> "uninterpreted function '%s' is not defined"
              "df." -> "library function '%s' is not defined"
              _     -> "unrecognized function prefix: '%s'"
        in E.throwError $ printf template fnName
    args <- readExprs operands
    assn <- exprAssignment (S.fnArgTypes fn) (reverse args)
    liftIO (Some <$> S.applySymFn sym fn assn)
readApp opRaw _ = E.throwError $ printf "couldn't parse application of %s" (printTokens mempty opRaw)



-- | Try converting an 'Integer' to a 'NatRepr' or throw an error if not
-- possible.
intToNatM :: (E.MonadError String m) => Integer -> m (Some NatRepr)
intToNatM = fromMaybeError "integer must be non-negative to be a nat" . someNat



data ArrayJudgment :: BaseType -> BaseType -> Type where
  ArraySingleDim :: forall idx res.
                    BaseTypeRepr res
                 -> ArrayJudgment idx (BaseArrayType (Ctx.SingleCtx idx) res)

expectArrayWithIndex :: (E.MonadError String m) => BaseTypeRepr tp1 -> BaseTypeRepr tp2 -> m (ArrayJudgment tp1 tp2)
expectArrayWithIndex dimRepr (BaseArrayRepr idxTpReprs resRepr) =
  case Ctx.viewAssign idxTpReprs of
    Ctx.AssignExtend rest idxTpRepr ->
      case Ctx.viewAssign rest of
        Ctx.AssignEmpty ->
          case testEquality idxTpRepr dimRepr of
            Just Refl -> return $ ArraySingleDim resRepr
            Nothing -> E.throwError $ unwords ["Array index type", show idxTpRepr,
                                               "does not match", show dimRepr]
        _ -> E.throwError "multidimensional arrays are not supported"
expectArrayWithIndex _ repr = E.throwError $ unwords ["expected an array, got", show repr]


exprAssignment' :: (E.MonadError String m,
                    S.IsExpr ex)
                => Ctx.Assignment BaseTypeRepr ctx
                -> [Some ex]
                -> Int
                -> Int
                -> m (Ctx.Assignment ex ctx)
exprAssignment' (Ctx.viewAssign -> Ctx.AssignEmpty) [] _ _ = return Ctx.empty
exprAssignment' (Ctx.viewAssign -> Ctx.AssignExtend restTps tp) (Some e : restExprs) idx len = do
  Refl <- case testEquality tp (S.exprType e) of
            Just pf -> return pf
            Nothing -> E.throwError ("unexpected type in index " ++ (show idx) ++ " (total length " ++ (show len)
                                     ++ "), assigning to: " ++ show tp ++ " from expr: " ++ show (S.exprType e))
  restAssn <- exprAssignment' restTps restExprs (idx + 1) len
  return $ restAssn Ctx.:> e
exprAssignment' _ _ _  _ = E.throwError "mismatching numbers of arguments"

exprAssignment :: (E.MonadError String m,
                   S.IsExpr ex)
               => Ctx.Assignment BaseTypeRepr ctx
               -> [Some ex]
               -> m (Ctx.Assignment ex ctx)
exprAssignment tpAssn exs = exprAssignment' tpAssn (reverse exs) 0 (Ctx.sizeInt $ Ctx.size tpAssn)

-- | Given the s-expressions for the bindings and body of a
-- let, parse the bindings into the Reader monad's state and
-- then parse the body with those newly bound variables.
readLetExpr ::
  forall sym m arch sh
  . (S.IsSymExprBuilder sym,
      Monad m,
      E.MonadError String m,
      A.Architecture arch,
      MR.MonadReader (DefsInfo sym arch sh) m,
      MonadIO m)
  => SC.SExpr FAtom
  -- ^ Bindings in a let-expression.
  -> SC.SExpr FAtom
  -- ^ Body of the let-expression.
  -> m (Some (S.SymExpr sym))
readLetExpr SC.SNil body = readExpr body
readLetExpr (SC.SCons (SC.SCons (SC.SAtom x@(AIdent _)) (SC.SCons e SC.SNil)) rst) body = do
  v <- readExpr e
  MR.local (\r -> r {getBindings = (Map.insert x v) $ getBindings r}) $
    readLetExpr rst body
readLetExpr bindings _body = E.throwError $
  "invalid s-expression for let-bindings: " ++ (show bindings)


-- | Parse an arbitrary expression.
readExpr :: forall sym m arch sh
          . (S.IsSymExprBuilder sym,
             Monad m,
             E.MonadError String m,
             A.Architecture arch,
             MR.MonadReader (DefsInfo sym arch sh) m,
             MonadIO m)
         => SC.SExpr FAtom
         -> m (Some (S.SymExpr sym))
readExpr SC.SNil = E.throwError "found nil where expected an expression"
readExpr (SC.SAtom (AInt n)) = do
  sym <- MR.reader getSym
  liftIO $ (Some <$> S.intLit sym n)
readExpr (SC.SAtom (ANat n)) = do
  sym <- MR.reader getSym
  liftIO $ (Some <$> S.natLit sym n)
readExpr (SC.SAtom (ABool b)) = do
  sym <- MR.reader getSym
  liftIO $ return $ Some $ S.backendPred sym b
readExpr (SC.SAtom (AString op)) = do
  -- This is an uninterpreted function.
  sym <- MR.reader getSym
  case userSymbol op of
    Right opSym -> do
      e <- liftIO $ S.freshTotalUninterpFn sym opSym Ctx.empty (BaseStructRepr Ctx.empty)
      f <- liftIO $ S.applySymFn sym e Ctx.empty
      return $ Some f
    Left _ -> E.throwError $ printf "couldn't parse string expression %s" (show op)
readExpr (SC.SAtom (ABV len val)) = do
  -- This is a bitvector literal.
  sym <- MR.reader getSym
  -- The following two patterns should never fail, given that during parsing we
  -- can only construct BVs with positive length.
  case someNat (toInteger len) of
    Just (Some lenRepr) ->
        let Just pf = isPosNat lenRepr
        in liftIO $ withLeqProof pf (Some <$> S.bvLit sym lenRepr val)
    Nothing -> error "SemMC.Formula.Parser.readExpr someNat failure"
  -- Just (Some lenRepr) <- return $ someNat (toInteger len)
  -- let Just pf = isPosNat lenRepr
  -- liftIO $ withLeqProof pf (Some <$> S.bvLit sym lenRepr val)
readExpr (SC.SAtom paramRaw) = do
  maybeBinding <- MR.asks $ (Map.lookup paramRaw) . getBindings
  case maybeBinding of
    -- if this is actually a let-bound variable, simply return it's binding
    Just binding -> return binding
    Nothing -> do
      -- Otherwise this is a standard parameter (i.e., variable).
      DefsInfo { getOpNameList = opNames
               , getSym = sym
               , getOpVarList = opVars
               , getLitLookup = litLookup
               } <- MR.ask
      param <- readParameter (Proxy @arch) opNames paramRaw
      case param of
        Some (ParsedOperandParameter _ idx) ->
          return . Some . S.varExpr sym $ (opVars SL.!! idx)
        Some (ParsedLiteralParameter lit) ->
          maybe (E.throwError ("not declared as input but saw unknown literal param: " ++ showF lit))
                                   (return . Some) $ litLookup lit
readExpr (SC.SCons (SC.SAtom (AIdent "let")) rhs) =
  case rhs of
    (SC.SCons bindings (SC.SCons body SC.SNil)) -> readLetExpr bindings body
    _ -> E.throwError "ill-formed let s-expression"
readExpr (SC.SCons operator operands) = do
  readApp operator operands


-- | Parse multiple expressions in a list.
readExprs :: (S.IsSymExprBuilder sym,
              Monad m,
              E.MonadError String m,
              A.Architecture arch,
              MR.MonadReader (DefsInfo sym arch sh) m,
              MonadIO m)
          => SC.SExpr FAtom
          -> m [Some (S.SymExpr sym)]
readExprs SC.SNil = return []
readExprs (SC.SAtom _) = E.throwError "found atom where expected a list of expressions"
readExprs (SC.SCons e rest) = do
  e' <- readExpr e
  rest' <- readExprs rest
  return $ e' : rest'

readExprsAsAssignment ::
  forall sym m arch sh .
  (S.IsSymExprBuilder sym,
    Monad m,
    E.MonadError String m,
    A.Architecture arch,
    MR.MonadReader (DefsInfo sym arch sh) m,
    MonadIO m)
  => SC.SExpr FAtom
  -> m (Some (Ctx.Assignment (S.SymExpr sym)))
readExprsAsAssignment SC.SNil = return $ Some Ctx.empty
readExprsAsAssignment (SC.SCons s rest) = do
  Some e <- readExpr s
  Some ss <- readExprsAsAssignment rest
  return $ Some (Ctx.extend ss e)
readExprsAsAssignment sexpr = E.throwError $ "expected list of expressions: " ++ show sexpr


-- | Parse the whole definitions expression, e.g.:
--
-- > ((rt . (bvadd ra rb))
-- >  ('ca . #b1))
--
readDefs :: forall sym m arch sh
          . (S.IsSymExprBuilder sym,
             Monad m,
             E.MonadError String m,
             A.Architecture arch,
             MR.MonadReader (DefsInfo sym arch (OperandTypes arch sh)) m,
             MonadIO m,
             ShowF (S.SymExpr sym))
         => A.ShapeRepr arch sh
         -> SC.SExpr FAtom
         -> m (MapF.MapF (Parameter arch sh) (S.SymExpr sym))
readDefs _ SC.SNil = return MapF.empty
readDefs shapeRepr (SC.SCons (SC.SCons (SC.SAtom p) (SC.SCons defRaw SC.SNil)) rest) = do
  oplist <- MR.reader getOpNameList
  Some param <- mapSome (toParameter shapeRepr) <$> readParameter (Proxy @arch) oplist p
  Some def <- readExpr defRaw
  Refl <- fromMaybeError ("mismatching types of parameter and expression for " ++ showF param) $
            testEquality (paramType param) (S.exprType def)
  rest' <- prefixError (", defining " <> showF def <> " ... ") $ readDefs shapeRepr rest
  return $ MapF.insert param def rest'
readDefs shapeRepr (SC.SCons (SC.SCons (SC.SCons mUF (SC.SCons (SC.SAtom p) SC.SNil)) (SC.SCons defRaw SC.SNil)) rest)
  | Just funcName <- matchUF mUF = prefixError (", processing uninterpreted function " <> show funcName <> " ... ") $ do
    oplist <- MR.reader getOpNameList
    Some param <- mapSome (toParameter shapeRepr) <$> readParameter (Proxy @arch) oplist p
    fns <- MR.reader (envFunctions . getEnv)
    case Map.lookup funcName fns of
      Just (_, Some rep) -> do
        Some def <- readExpr defRaw
        Refl <- fromMaybeError ("mismatching types of parameter and expression for " ++ showF param) $
                  testEquality rep (S.exprType def)
        rest' <- readDefs shapeRepr rest
        case param of
          LiteralParameter {} -> E.throwError "Literals are not allowed as arguments to parameter functions"
          FunctionParameter {} -> E.throwError "Nested parameter functions are not allowed"
          OperandParameter orep oix ->
            return $ MapF.insert (FunctionParameter funcName (WrappedOperand orep oix) rep) def rest'
      _ -> E.throwError ("Missing type repr for uninterpreted function " ++ show funcName)
readDefs _ _ = E.throwError "invalid defs structure"

matchUF :: SC.SExpr FAtom -> Maybe String
matchUF se =
  case se of
    SC.SCons (SC.SAtom (AIdent "_"))
             (SC.SCons (SC.SAtom (AIdent "call"))
                       (SC.SCons (SC.SAtom (AString fnName))
                                 SC.SNil)) -> Just fnName
    _ -> Nothing

-- | Parse the whole definition of a templated formula, inside an appropriate
-- monad.
readFormula' :: forall sym arch (sh :: [Symbol]) m.
                (S.IsSymExprBuilder sym,
                 E.MonadError String m,
                 MonadIO m,
                 A.Architecture arch,
                 ShowF (S.SymExpr sym),
                 U.HasLogCfg)
             => sym
             -> FormulaEnv sym arch
             -> A.ShapeRepr arch sh
             -> T.Text
             -> m (ParameterizedFormula sym arch sh)
readFormula' sym env repr text = do
  sexpr <- case parseLL text of
             Left err -> E.throwError err
             Right res -> return res
  let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
  liftIO $ U.logIO U.Info $ "readFormula' of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
  liftIO $ U.logIO U.Debug $ "readFormula' shaperepr " ++ (A.showShapeRepr (Proxy @arch) repr)
  -- Extract the raw s-expressions for the three components.
  (opsRaw, inputsRaw, defsRaw) <- case sexpr of
    SC.SCons (SC.SCons (SC.SAtom (AIdent "operands")) (SC.SCons ops SC.SNil))
      (SC.SCons (SC.SCons (SC.SAtom (AIdent "in")) (SC.SCons inputs SC.SNil))
       (SC.SCons (SC.SCons (SC.SAtom (AIdent "defs")) (SC.SCons defs SC.SNil))
         SC.SNil))
      -> return (ops, inputs, defs)
    _ -> E.throwError "invalid top-level structure"

  -- Most of the following bindings have type annotations not because inference
  -- fails, but because with all the type-level hackery we have going on, it
  -- greatly helps human comprehension.

  -- Build the operand list from the given s-expression, validating that it
  -- matches the correct shape as we go.
  let strShape = A.showShapeRepr (Proxy @arch) repr
  operands :: SL.List OpData (OperandTypes arch sh)
    <- prefixError ("invalid operand structure (expected " ++ strShape ++
                    ") from " ++ show opsRaw) $
       buildOperandList' (Proxy @arch) repr opsRaw

  inputs :: [Some (ParsedParameter arch (OperandTypes arch sh))]
    <- readInputs @m @arch @(OperandTypes arch sh) operands inputsRaw

  let mkOperandVar :: forall tp. OpData tp -> m (S.BoundVar sym tp)
      mkOperandVar (OpData name tpRepr) =
        let symbol = U.makeSymbol (operandVarPrefix ++ name)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

  opVarList :: SL.List (S.BoundVar sym) (OperandTypes arch sh)
    <- traverseFC mkOperandVar @(OperandTypes arch sh) operands

  -- NOTE: At the moment, we just trust that the semantics definition declares
  -- the correct input operands; instead of validating it, we generate BoundVars
  -- for *all* inputs (partially because it is unclear how to treat immediates
  -- -- do they count as inputs?).

  let mkLiteralVar :: forall tp. BaseTypeRepr tp -> A.Location arch tp -> m (S.BoundVar sym tp)
      mkLiteralVar tpRepr loc =
        let symbol = U.makeSymbol (literalVarPrefix ++ showF loc)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

      buildLitVarMap :: Some (ParsedParameter arch (OperandTypes arch sh))
                     -> MapF.MapF (A.Location arch) (S.BoundVar sym)
                     -> m (MapF.MapF (A.Location arch) (S.BoundVar sym))
      buildLitVarMap (Some (ParsedLiteralParameter loc)) m = (\v -> MapF.insert loc v m) <$> mkLiteralVar (A.locationType loc) loc
      buildLitVarMap (Some (ParsedOperandParameter _ _))        m = return m

  litVars :: MapF.MapF (A.Location arch) (S.BoundVar sym)
    <- foldrM buildLitVarMap MapF.empty inputs

  defs <- MR.runReaderT (readDefs repr defsRaw) $
            (DefsInfo { getSym = sym
                      , getEnv = env
                      , getLitLookup = \loc -> S.varExpr sym <$> flip MapF.lookup litVars loc
                      , getOpVarList = opVarList
                      , getOpNameList = operands
                      , getBindings = Map.empty
                      })

  let finalInputs :: [Some (Parameter arch sh)]
      finalInputs = mapSome (toParameter repr) <$> inputs
      finalOpVarList :: SL.List (BV.BoundVar sym arch) sh
      finalOpVarList =
        -- Wrap each operand variable using 'BV.BoundVar'
        TL.mapFromMapped (Proxy @(OperandTypeWrapper arch)) BV.BoundVar repr opVarList

  return $
    ParameterizedFormula { pfUses = Set.fromList finalInputs
                         , pfOperandVars = finalOpVarList
                         , pfLiteralVars = litVars
                         , pfDefs = defs
                         }

-- | Parse the definition of a templated formula.
readFormula :: (S.IsSymExprBuilder sym,
                A.Architecture arch,
                ShowF (S.SymExpr sym),
                U.HasLogCfg)
            => sym
            -> FormulaEnv sym arch
            -> A.ShapeRepr arch sh
            -> T.Text
            -> IO (Either String (ParameterizedFormula sym arch sh))
readFormula sym env repr text = E.runExceptT $ readFormula' sym env repr text

-- | Read a templated formula definition from file, then parse it.
readFormulaFromFile :: (S.IsSymExprBuilder sym,
                        A.Architecture arch,
                        ShowF (S.SymExpr sym),
                        U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> A.ShapeRepr arch sh
                    -> FilePath
                    -> IO (Either String (ParameterizedFormula sym arch sh))
readFormulaFromFile sym env repr fp = do
  liftIO $ U.logIO U.Info $ "readFormulaFromFile " ++ fp
  readFormula sym env repr =<< T.readFile fp

-- | Parse the whole definition of a defined function, inside an appropriate
-- monad.
readDefinedFunction' :: forall sym arch m.
                        (S.IsExprBuilder sym,
                         S.IsSymInterface sym,
                         E.MonadError String m,
                         MonadIO m,
                         A.Architecture arch,
                         ShowF (S.SymExpr sym),
                         U.HasLogCfg)
                     => sym
                     -> FormulaEnv sym arch
                     -> T.Text
                     -> m (Some (FunctionFormula sym))
readDefinedFunction' sym env text = do
  sexpr <- case parseLL text of
             Left err -> E.throwError err
             Right res -> return res
  let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
  liftIO $ U.logIO U.Info $
    "readDefinedFunction' of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
  -- Extract the raw s-expressions for the four components.
  (name, argsRaw, retTypeRaw, bodyRaw) <- case sexpr of
    SC.SCons (SC.SCons (SC.SAtom (AIdent "function"))
              (SC.SCons (SC.SAtom (AIdent name)) SC.SNil))
      (SC.SCons (SC.SCons (SC.SAtom (AIdent "arguments")) (SC.SCons args SC.SNil))
       (SC.SCons (SC.SCons (SC.SAtom (AIdent "return")) (SC.SCons retType SC.SNil))
         (SC.SCons (SC.SCons (SC.SAtom (AIdent "body")) (SC.SCons body SC.SNil))
           SC.SNil)))
      -> return (name, args, retType, body)
    _ -> E.throwError "invalid top-level structure"

  -- Most of the following bindings have type annotations not because inference
  -- fails, but because with all the type-level hackery we have going on, it
  -- greatly helps human comprehension.

  -- Build the argument list from the given s-expression. Unlike with a formula,
  -- we don't know the arguments' types beforehand.
  Some (arguments :: SL.List OpData sh)
    <- buildArgumentList' argsRaw

  Some (retTypeRepr :: BaseTypeRepr retType)
    <- readBaseType retTypeRaw

  let mkArgumentVar :: forall tp. OpData tp -> m (S.BoundVar sym tp)
      mkArgumentVar (OpData varName tpRepr) =
        let symbol = U.makeSymbol (argumentVarPrefix ++ varName)
        in liftIO $ S.freshBoundVar sym symbol tpRepr

  argVarList :: SL.List (S.BoundVar sym) sh
    <- traverseFC mkArgumentVar arguments

  argTypeReprs :: SL.List BaseTypeRepr sh
    <- traverseFC (\(OpData _ tpRepr) -> return tpRepr) arguments
  
  Some body <- MR.runReaderT (readExpr bodyRaw) $
    DefsInfo { getSym = sym
             , getEnv = env
             , getLitLookup = const Nothing
             , getOpVarList = argVarList
             , getOpNameList = arguments
             , getBindings = Map.empty
             }

  let actualTypeRepr = S.exprType body
  Refl <- case testEquality retTypeRepr actualTypeRepr of
    Just r -> return r
    Nothing -> E.throwError $
      "Body has wrong type: expected " ++ show retTypeRepr ++
      " but found " ++ show actualTypeRepr

  let symbol = U.makeSymbol name
      argVarAssignment = TL.toAssignmentFwd argVarList
      expand args = allFC S.baseIsConcrete args

  symFn <- liftIO $ S.definedFn sym symbol argVarAssignment body expand
  return $ Some (FunctionFormula { ffName = name
                                 , ffArgTypes = argTypeReprs
                                 , ffArgVars = argVarList
                                 , ffRetType = retTypeRepr
                                 , ffDef = symFn })

-- | Parse the definition of a templated formula.
readDefinedFunction :: (S.IsExprBuilder sym,
                        S.IsSymInterface sym,
                        A.Architecture arch,
                        ShowF (S.SymExpr sym),
                        U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> T.Text
                    -> IO (Either String (Some (FunctionFormula sym)))
readDefinedFunction sym env text = E.runExceptT $ readDefinedFunction' sym env text

-- | Read a defined function definition from a file, then parse it.
readDefinedFunctionFromFile :: (S.IsExprBuilder sym,
                                S.IsSymInterface sym,
                                A.Architecture arch,
                                ShowF (S.SymExpr sym),
                                U.HasLogCfg)
                    => sym
                    -> FormulaEnv sym arch
                    -> FilePath
                    -> IO (Either String (Some (FunctionFormula sym)))
readDefinedFunctionFromFile sym env fp = do
  liftIO $ U.logIO U.Info $ "readDefinedFunctionFromFile " ++ fp
  readDefinedFunction sym env =<< T.readFile fp
