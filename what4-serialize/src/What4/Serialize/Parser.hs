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
{-# LANGUAGE MultiWayIf #-}

-- | A parser for an s-expression representation of what4 expressions
module What4.Serialize.Parser
  ( readSymFn
  , readSymFnFromFile
  , readSymFnEnv
  , readSymFnEnvFromFile
  , ParserConfig(..)
  , defaultParserConfig
  , SymFnEnv
  ) where

import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.Reader as MR
import           Control.Monad ( when )
import           Data.Kind
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.SCargot.Repr as SC
import           Data.Semigroup
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Text.Printf ( printf )

import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.TraversableFC ( traverseFC, allFC )
import           What4.BaseTypes

import qualified What4.Interface as S
import           What4.Symbol ( userSymbol )

import           What4.Serialize.SETokens ( FAtom(..), printTokens, parseNoLet)
import qualified What4.Utils.Log as U
import           What4.Utils.Util ( SomeSome(..) )
import qualified What4.Utils.Util as U

import           Prelude



-- * First pass of parsing turns the raw text into s-expressions.
--   This pass is handled by the code in What4.Serialize.SETokens

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


data ParsedVariable sym (tps :: Ctx.Ctx BaseType) (tp :: BaseType) where
  ParsedArgument :: BaseTypeRepr tp -> Ctx.Index tps tp
                 -> ParsedVariable sym tps tp
  ParsedGlobal :: S.SymExpr sym tp -> ParsedVariable sym tps tp

-- | Data about the argument pertinent after parsing: their name and their type.
data ArgData (tp :: BaseType) where
  ArgData :: String -> BaseTypeRepr tp -> ArgData tp


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

-- | Short-lived type that just stores an index with its corresponding type
-- representation, with the type parameter ensuring they correspond to one another.
data IndexWithType (sh :: Ctx.Ctx BaseType) (tp :: BaseType) where
  IndexWithType :: BaseTypeRepr tp -> Ctx.Index sh tp -> IndexWithType sh tp

-- | Look up a name in the given operand list, returning its index and type if found.
findArgListIndex :: forall sh. String -> Ctx.Assignment ArgData sh -> Maybe (Some (IndexWithType sh))
findArgListIndex x args = Ctx.forIndex (Ctx.size args) getArg Nothing
  where
    getArg :: forall tp
            . Maybe (Some (IndexWithType sh))
           -> Ctx.Index sh tp
           -> Maybe (Some (IndexWithType sh))
    getArg Nothing idx = case args Ctx.! idx of
      ArgData name tpRepr
        | name == x -> Just $ Some (IndexWithType tpRepr idx)
      _ -> Nothing
    getArg (Just iwt) _ = Just iwt
          

-- | Parse a single parameter, given the list of operands to use as a lookup.
readVariable :: forall sym tps m. (E.MonadError String m) => (T.Text -> m (Maybe (Some (S.SymExpr sym)))) -> Ctx.Assignment ArgData tps -> FAtom -> m (Some (ParsedVariable sym tps))
readVariable lookupGlobal arglist atom = case atom of
  AIdent name -> do
    lookupGlobal (T.pack name) >>= \case
      Just (Some glb) -> return $ Some (ParsedGlobal glb)
      Nothing
        | Just (Some (IndexWithType tpRepr idx)) <- findArgListIndex name arglist ->
          return $ Some (ParsedArgument tpRepr idx)
      _ -> E.throwError $ printf "couldn't find binding for variable %s" name
  _ -> E.throwError $ printf "expected variable, found %s" (show atom)

-- ** Parsing definitions

-- | "Global" data stored in the Reader monad throughout parsing the definitions.
data DefsInfo sym tps = DefsInfo
                        { getSym :: sym
                        -- ^ SymInterface/ExprBuilder used to build up symbolic
                        -- expressions while parsing the definitions.
                        , getEnv :: SymFnEnv sym
                        -- ^ Global formula environment
                        , getGlobalLookup :: T.Text -> IO (Maybe (Some (S.SymExpr sym)))
                        -- ^ Function to retrieve the expression corresponding to the
                        -- given global
                        , getArgVarList :: Ctx.Assignment (S.BoundVar sym) tps
                        -- ^ ShapedList used to retrieve the variable
                        -- corresponding to a given argument.
                        , getArgNameList :: Ctx.Assignment ArgData tps
                        -- ^ ShapedList used to look up the index given an
                        -- argument's name.
                        , getBindings :: Map.Map FAtom (Some (S.SymExpr sym))
                        -- ^ Mapping of currently in-scope let-bound variables
                        --- to their parsed bindings.
                        , getOverrides :: String -> Maybe ([Some (S.SymExpr sym)] -> IO (Either String (Some (S.SymExpr sym))))
                        -- ^ Ad-hoc overrides
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
  "intabs" -> Just $ Op1 knownRepr $ S.intAbs
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
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (S.SymExpr sym),
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
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (S.SymExpr sym),
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
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (S.SymExpr sym),
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
  forall sym m sh.
  (S.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (S.SymExpr sym),
    MonadIO m)
  => SC.SExpr FAtom
  -> SC.SExpr FAtom
  -> m (Some (S.SymExpr sym))
readApp opRaw@(SC.SAtom (AIdent operator)) operands = do
  sym <- MR.reader getSym
  ov <- MR.reader getOverrides
  prefixError ("in reading expression:\n"
              -- ++(show $ SC.SCons opRaw operands)++"\n") $ -- the raw display version
               ++(T.unpack $ printTokens mempty $ SC.SCons opRaw operands)++"\n") $
  -- Parse an expression of the form @(fnname operands ...)@
    case lookupOp operator of
      _ | Just f <- ov operator -> do
            args <- readExprs operands
            liftIO (f args) >>= \case
              Left err -> E.throwError err
              Right result -> return result

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
    fns <- MR.reader getEnv
    SomeSome fn <- case Map.lookup (T.pack fnName) fns of
      Just fn -> return fn
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
  forall sym m sh
  . (S.IsSymExprBuilder sym,
      Monad m,
      E.MonadError String m,
      MR.MonadReader (DefsInfo sym sh) m,
      ShowF (S.SymExpr sym),
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
readExpr :: forall sym m sh
          . (S.IsSymExprBuilder sym,
             Monad m,
             E.MonadError String m,
             MR.MonadReader (DefsInfo sym sh) m,
             ShowF (S.SymExpr sym),
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
readExpr (SC.SAtom varRaw) = do
  maybeBinding <- MR.asks $ (Map.lookup varRaw) . getBindings
  case maybeBinding of
    -- if this is actually a let-bound variable, simply return it's binding
    Just binding -> return binding
    Nothing -> do
      -- Otherwise this is a standard parameter (i.e., variable).
      DefsInfo { getArgNameList = argNames
               , getSym = sym
               , getArgVarList = argVars
               , getGlobalLookup = globalLookup
               } <- MR.ask
      var <- readVariable @sym (\nm -> liftIO $ globalLookup nm) argNames varRaw
      case var of
        Some (ParsedArgument _ idx) ->
          return . Some . S.varExpr sym $ (argVars Ctx.! idx)
        Some (ParsedGlobal expr) -> return $ Some expr
readExpr (SC.SCons (SC.SAtom (AIdent "let")) rhs) =
  case rhs of
    (SC.SCons bindings (SC.SCons body SC.SNil)) -> do
      readLetExpr bindings body
    _ -> E.throwError "ill-formed let s-expression"
readExpr (SC.SCons operator operands) = do
  readApp operator operands


-- | Parse multiple expressions in a list.
readExprs :: (S.IsSymExprBuilder sym,
              Monad m,
              E.MonadError String m,
              MR.MonadReader (DefsInfo sym sh) m,
              ShowF (S.SymExpr sym),
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
  forall sym m sh .
  (S.IsSymExprBuilder sym,
    Monad m,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (S.SymExpr sym),
    MonadIO m)
  => SC.SExpr FAtom
  -> m (Some (Ctx.Assignment (S.SymExpr sym)))
readExprsAsAssignment SC.SNil = return $ Some Ctx.empty
readExprsAsAssignment (SC.SCons s rest) = do
  Some e <- readExpr s
  Some ss <- readExprsAsAssignment rest
  return $ Some (Ctx.extend ss e)
readExprsAsAssignment sexpr = E.throwError $ "expected list of expressions: " ++ show sexpr


buildArgumentList :: forall m
                    . (E.MonadError String m)
                   => SC.SExpr FAtom
                   -> m (Some (Ctx.Assignment ArgData))
buildArgumentList sexpr =
  case sexpr of
    SC.SNil -> return $ Some (Ctx.empty)
    SC.SAtom _ -> E.throwError $ "Expected SNil or SCons but got SAtom: " ++ show sexpr
    SC.SCons s rest -> do
      (operand, tyRaw) <- case s of
        SC.SCons (SC.SAtom (AIdent arg)) (SC.SCons ty SC.SNil)
          -> return (arg, ty)
        _ -> E.throwError $ "Expected (operand . 'type) pair: " ++ show s
      Some tp <- readBaseType tyRaw
      Some rest' <- buildArgumentList rest
      return $ Some (rest' Ctx.:> (ArgData operand tp))

readSymFn' :: forall sym m
           . (S.IsExprBuilder sym,
              S.IsSymExprBuilder sym,
              E.MonadError String m,
              MonadIO m,
              ShowF (S.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> SC.SExpr FAtom
          -> m (SomeSome (S.SymFn sym))
readSymFn' cfg sexpr =
  let
    sym = pSym cfg
    env = pSymFnEnv cfg
    globalLookup = pGlobalLookup cfg
  in do
  (name, symFnInfoRaw) <- case sexpr of
    SC.SCons (SC.SAtom (AIdent "symfn"))
      (SC.SCons (SC.SAtom (AString name))
        (SC.SCons symFnInfoRaw
          SC.SNil))
      -> return (name, symFnInfoRaw)
    _ -> E.throwError ("invalid top-level function definition structure:\n" ++ show sexpr)

  let symbol = U.makeSymbol name
  case symFnInfoRaw of
    SC.SCons (SC.SAtom (AIdent "definedfn"))
      (SC.SCons argTsRaw
        (SC.SCons retTRaw
          (SC.SCons argVarsRaw
            (SC.SCons exprRaw
               SC.SNil))))
      -> do
        Some argTs <- readBaseTypes argTsRaw
        Some retT <- readBaseType retTRaw
        let ufname = T.pack ("uf." ++ name)
        -- For recursive calls, we may need an uninterpreted variant of this function
        env' <- case Map.lookup ufname env of
          Just (U.SomeSome ufsymFn) ->
            if | Just Refl <- testEquality argTs (S.fnArgTypes ufsymFn)
               , Just Refl <- testEquality retT (S.fnReturnType ufsymFn) -> return env
               | otherwise -> E.throwError $ "Bad signature for existing function: " ++ show name
          Nothing -> do
            symFn <- liftIO $ S.freshTotalUninterpFn sym symbol argTs retT
            return $ Map.insert ufname (U.SomeSome symFn) env

        Some argNameList <- buildArgumentList @m argVarsRaw
        argVarList <- traverseFC mkArgumentVar argNameList
        Some expr <- MR.runReaderT (readExpr exprRaw) $
          DefsInfo { getSym = sym
                   , getEnv = env'
                   , getGlobalLookup = globalLookup
                   , getArgVarList = argVarList
                   , getArgNameList = argNameList
                   , getBindings = Map.empty
                   , getOverrides = pOverrides cfg
                   }
        let expand args = allFC S.baseIsConcrete args
        symFn <- liftIO $ S.definedFn sym symbol argVarList expr expand
        return $ SomeSome symFn
    SC.SCons (SC.SAtom (AIdent "uninterpfn"))
      (SC.SCons argTsRaw
        (SC.SCons retTRaw
          SC.SNil))
      -> do
        Some argTs <- readBaseTypes argTsRaw
        Some retT <- readBaseType retTRaw
        case Map.lookup (T.pack ("uf." ++ name)) env of
          Just (SomeSome symFn) -> do
            let argTs' = S.fnArgTypes symFn
            let retT' = S.fnReturnType symFn
            if | Just Refl <- testEquality argTs argTs'
               , Just Refl <- testEquality retT retT' -> do
                 return $ SomeSome symFn
               | otherwise -> E.throwError "invalid function signature in environment"
          _ -> do
            symFn <- liftIO $ S.freshTotalUninterpFn sym symbol argTs retT
            return $ SomeSome symFn
    _ -> E.throwError "invalid function definition info structure"
        
  where    
    mkArgumentVar :: forall tp. ArgData tp -> m (S.BoundVar sym tp)
    mkArgumentVar (ArgData varName tpRepr) =
      let symbol = U.makeSymbol varName
      in liftIO $ S.freshBoundVar (pSym cfg) symbol tpRepr

genRead :: forall a
         . U.HasLogCfg
        => String
        -> (SC.SExpr FAtom -> E.ExceptT String IO a)
        -> T.Text
        -> IO (Either String a)
genRead callnm m text = E.runExceptT $ go
  where
    go = do
      sexpr <- case parseNoLet text of
                 Left err -> E.throwError err
                 Right res -> return res
      let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
      liftIO $ U.logIO U.Info $
        callnm ++ " of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
      m sexpr

data ParserConfig t = ParserConfig
  { pSymFnEnv :: SymFnEnv t
  , pGlobalLookup :: T.Text -> IO (Maybe (Some (S.SymExpr t)))
  , pOverrides :: String -> Maybe ([Some (S.SymExpr t)] -> IO (Either String (Some (S.SymExpr t))))
  , pSym :: t
  }

defaultParserConfig :: t -> ParserConfig t
defaultParserConfig t =
  ParserConfig { pSymFnEnv = Map.empty
               , pGlobalLookup = \_ -> return Nothing
               , pOverrides = \_ -> Nothing
               , pSym = t }

type SymFnEnv t = Map T.Text (SomeSome (S.SymFn t))

readSymFn :: forall sym
           . (S.IsExprBuilder sym,
              S.IsSymExprBuilder sym,
              ShowF (S.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> T.Text
          -> IO (Either String (SomeSome (S.SymFn sym)))
readSymFn cfg = genRead "readSymFn" (readSymFn' cfg)

readSymFnFromFile :: forall sym
                   . (S.IsExprBuilder sym,
                      S.IsSymExprBuilder sym,
                      ShowF (S.SymExpr sym),
                      U.HasLogCfg)
                  => ParserConfig sym
                  -> FilePath
                  -> IO (Either String (SomeSome (S.SymFn sym)))
readSymFnFromFile cfg fp = do
  liftIO $ U.logIO U.Info $ "readSymFnFromFile " ++ fp
  readSymFn cfg =<< T.readFile fp

readSymFnEnv' :: forall sym m
               . (S.IsExprBuilder sym,
                  S.IsSymExprBuilder sym,
                  E.MonadError String m,
                  MonadIO m,
                  ShowF (S.SymExpr sym),
                  U.HasLogCfg)
              => ParserConfig sym
              -> SC.SExpr FAtom
              -> m (SymFnEnv sym)
readSymFnEnv' cfg sexpr = do
  symFnEnvRaw <- case sexpr of
    SC.SCons (SC.SAtom (AIdent "symfnenv"))
      (SC.SCons symFnEnvRaw
        SC.SNil)
      -> return symFnEnvRaw
    _ -> E.throwError "invalid top-level function environment structure"
  readSymFns (pSymFnEnv cfg) symFnEnvRaw
  where
    readSymFns :: SymFnEnv sym -> SC.SExpr FAtom -> m (SymFnEnv sym)
    readSymFns env sexpr' = case sexpr' of
      SC.SNil -> return env
      SC.SAtom _ -> E.throwError $ "Expected SNil or SCons but got SAtom: " ++ show sexpr
      SC.SCons s rest -> do
        (nm, symFn) <- readSomeSymFn env s
        let env' = Map.insert nm symFn env
        readSymFns env' rest
      
    readSomeSymFn :: SymFnEnv sym -> SC.SExpr FAtom -> m (T.Text, (SomeSome (S.SymFn sym)))
    readSomeSymFn env sexpr' = do
      (name, rawSymFn) <- case sexpr' of
        SC.SCons (SC.SAtom (AString name))
          (SC.SCons rawSymFn
            SC.SNil)
          -> return (T.pack name, rawSymFn)
        _ -> E.throwError $ "invalid function environment structure: " ++ show sexpr'
      ssymFn <- readSymFn' (cfg { pSymFnEnv = env }) rawSymFn
      return (name, ssymFn)

readSymFnEnv :: forall sym
           . (S.IsExprBuilder sym,
              S.IsSymExprBuilder sym,
              ShowF (S.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> T.Text
          -> IO (Either String (SymFnEnv sym))
readSymFnEnv cfg = genRead "readSymFnEnv" (readSymFnEnv' cfg)

readSymFnEnvFromFile :: forall sym
                   . (S.IsExprBuilder sym,
                      S.IsSymExprBuilder sym,
                      ShowF (S.SymExpr sym),
                      U.HasLogCfg)
                  => ParserConfig sym
                  -> FilePath
                  -> IO (Either String (SymFnEnv sym))
readSymFnEnvFromFile cfg fp = do
  liftIO $ U.logIO U.Info $ "readSymFnEnvFromFile " ++ fp
  readSymFnEnv cfg =<< T.readFile fp
