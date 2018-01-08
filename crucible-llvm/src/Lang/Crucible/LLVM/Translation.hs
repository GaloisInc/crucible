-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation
-- Description      : Translation of LLVM AST into Crucible control-flow graph
-- Copyright        : (c) Galois, Inc 2014-2015
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module translates an LLVM 'Module' into a collection of Crucible
-- control-flow graphs, one per function.  The tricky parts of this translation
-- are 1) mapping LLVM types onto Crucible types in a sensible way and 2)
-- translating the phi-instructions of LLVM's SSA form.
--
-- To handle the translation of phi-functions, we first perform a
-- pre-pass over all the LLVM basic blocks looking for phi-functions
-- and build a datastructure that tells us what assignments to make
-- when jumping from block l to block l'.  We then emit instructions
-- to make these assignments in a separate Crucible basic block (see
-- 'definePhiBlock').  Thus, the translated CFG will generally have
-- more basic blocks than the original LLVM.
--
-- Points of note:
--
--  * Immediate (i.e., not in memory) structs and packed structs are translated the same.
--  * Undefined values generate special Crucible expressions (e.g., BVUndef) to
--     represent arbitrary bitpatterns.
--  * All floating point operations are abstracted into operations on the real numbers.
--     Thus, answers returned by solvers might not be bit-exact, and might not even be expressible
--     in the original floating-point representation.  Moreover, trying to directly
--     examine the bit-patterns of floating-point values will not work, and weird bit-level
--     tricks on floating-point values will not work properly.  Additionally, @NaN@, @+INF@ and @-INF@
--     are never generated, but instead assertions (e.g. about division by zero) will fail.
--
-- Some notes on undefined/poison values: (outcome of discussions between JHx and RWD)
--
-- * Continue to add Crucible expressions for undefined values as
-- required (e.g. for floating-point values).  Crucible itself is
-- currently treating undefined values as fresh symbolic inputs; it
-- should instead invent a new category of "arbitrary" values that get
-- passed down into the solvers in a way that is dependent on the task
-- at hand.  For example, in verification tasks, it is appropriate to
-- treat the arbitrary values the same as symbolic inputs.  However,
-- for preimage-finding tasks, the arbitrary values must be treated as
-- universally-quantified, unlike the symbolic inputs which are
-- existentially-quantified.
--
-- * For poison values, our implementation strategy is to assert
-- side conditions onto values that may create poison.  As opposed
-- to assertions (which must be satisfied because you passed through
-- a control-flow point) side conditions are intended to mean that
-- a condition must hold when a value is used (i.e., side conditions
-- follow data-flow).  So if a poison value is created but not examined
-- (e.g., because we later do a test to determine if the value is safe),
-- that should be allowed.
--
-- A (probably) partial list of things we intend to support, but do not yet:
--
--  * Some floating-point operations (FDiv, FRem, FpToUi, FpToSi)
--  * Checking of alignment constraints on load, store, alloca, etc.
--  * Various vector instructions.  This includes 'shufflevector' as well
--      as a variety of other instructions that LLVM allows to take vector
--      arguments, but are currently only defined on scalar (nonvector) arguments.
--
-- A list of things that are unsupported and may never be:
--
--  * Computed jumps and blockaddress expressions
--  * Multithreading primitives
--  * Alternate calling conventions
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.Translation
  ( ModuleTranslation(..)
  , ModuleCFGMap
  , LLVMContext(..)
  , LLVMHandleInfo(..)
  , SymbolHandleMap
  , symbolMap
  , translateModule
  , llvmIntrinsicTypes
  , llvmIntrinsics
  , initializeMemory
  , toStorableType

  , module Lang.Crucible.LLVM.Translation.Types
  ) where

import Control.Monad.State.Strict
import Control.Lens hiding (op, (:>) )
import Control.Monad.ST
import Data.Foldable (toList)
import Data.Int
import qualified Data.List as List
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.String
import qualified Data.Text as Text
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>) )

import Data.Parameterized.Some
import Text.PrettyPrint.ANSI.Leijen (pretty)

import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion( toSSA )
import           Lang.Crucible.FunctionName
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Intrinsics
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Bytes as G
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.Translation.Types

import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Solver.Interface( IsSymInterface )
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- Translation results

type ModuleCFGMap = Map L.Symbol (C.AnyCFG LLVM)

-- | The result of translating an LLVM module into Crucible CFGs.
data ModuleTranslation
   = ModuleTranslation
      { cfgMap :: ModuleCFGMap
      , initMemoryCFG :: C.SomeCFG LLVM EmptyCtx UnitType
      }

-------------------------------------------------------------------------
-- LLVMExpr

-- | An intermediate form of LLVM expressions that retains some structure
--   that would otherwise be more difficult to retain if we translated directly
--   into crucible expressions.
data LLVMExpr s where
   BaseExpr   :: TypeRepr tp -> Expr LLVM s tp -> LLVMExpr s
   ZeroExpr   :: MemType -> LLVMExpr s
   UndefExpr  :: MemType -> LLVMExpr s
   VecExpr    :: MemType -> Seq (LLVMExpr s) -> LLVMExpr s
   StructExpr :: Seq (MemType, LLVMExpr s) -> LLVMExpr s

instance Show (LLVMExpr s) where
  show (BaseExpr _ x)   = C.showF x
  show (ZeroExpr mt)    = "<zero :" ++ show mt ++ ">"
  show (UndefExpr mt)   = "<undef :" ++ show mt ++ ">"
  show (VecExpr _mt xs) = "[" ++ concat (List.intersperse ", " (map show (toList xs))) ++ "]"
  show (StructExpr xs)  = "{" ++ concat (List.intersperse ", " (map f (toList xs))) ++ "}"
    where f (_mt,x) = show x


data ScalarView s where
  Scalar    :: TypeRepr tp -> Expr LLVM s tp -> ScalarView s
  NotScalar :: ScalarView s

-- | Examine an LLVM expression and return the corresponding
--   crucible expression, if it is a scalar.
asScalar :: (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr)
         => LLVMExpr s
         -> ScalarView s
asScalar (BaseExpr tp xs)
  = Scalar tp xs
asScalar (ZeroExpr llvmtp)
  = let ?err = error
     in zeroExpand llvmtp $ \tpr ex -> Scalar tpr ex
asScalar (UndefExpr llvmtp)
  = let ?err = error
     in undefExpand llvmtp $ \tpr ex -> Scalar tpr ex
asScalar _ = NotScalar

-- | Given an LLVM type and a type context and a register assignment,
--   peel off the rightmost register from the assignment, which is
--   expected to match the given LLVM type.  Pass the register and
--   the remaining type and register context to the given continuation.
--
--   This procedure is used to set up the initial state of the
--   registers at the entry point of a function.
packType :: (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr)
         => MemType
         -> CtxRepr ctx
         -> Ctx.Assignment (Atom s) ctx
         -> (forall ctx'. Some (Atom s) -> CtxRepr ctx' -> Ctx.Assignment (Atom s) ctx' -> a)
         -> a
packType tp ctx asgn k =
   llvmTypeAsRepr tp $ \repr ->
     packBase repr ctx asgn k

packBase
    :: TypeRepr tp
    -> CtxRepr ctx
    -> Ctx.Assignment (Atom s) ctx
    -> (forall ctx'. Some (Atom s) -> CtxRepr ctx' -> Ctx.Assignment (Atom s) ctx' -> a)
    -> a
packBase ctp ctx0 asgn k =
  case ctx0 of
    ctx' Ctx.:> ctp' ->
      case testEquality ctp ctp' of
        Nothing -> error $ unwords ["crucible type mismatch",show ctp,show ctp']
        Just Refl ->
          let asgn' = Ctx.init asgn
              idx   = Ctx.nextIndex (Ctx.size asgn')
           in k (Some (asgn Ctx.! idx))
                ctx'
                asgn'
    _ -> error "packType: ran out of actual arguments!"

typeToRegExpr :: MemType -> LLVMEnd h s wptr ret (Some (Reg s))
typeToRegExpr tp = do
  llvmTypeAsRepr tp $ \tpr ->
    Some <$> newUnassignedReg' tpr


instrResultType :: L.Instr -> L.Type
instrResultType instr =
  case instr of
    L.Arith _ x _ -> L.typedType x
    L.Bit _ x _   -> L.typedType x
    L.Conv _ _ ty -> ty
    L.Call _ (L.PtrTo (L.FunTy ty _ _)) _ _ -> ty
    L.Call _ ty _ _ -> error $ unwords ["unexpected function type in call:", show ty]
    L.Invoke (L.FunTy ty _ _) _ _ _ _ -> ty
    L.Invoke ty _ _ _ _ -> error $ unwords ["unexpected function type in invoke:", show ty]
    L.Alloca ty _ _ -> L.PtrTo ty
    L.Load x _ _ -> case L.typedType x of
                   L.PtrTo ty -> ty
                   _ -> error $ unwords ["load through non-pointer type", show (L.typedType x)]
    L.ICmp _ _ _ -> L.PrimType (L.Integer 1)
    L.FCmp _ _ _ -> L.PrimType (L.Integer 1)
    L.Phi tp _   -> tp
    L.GEP _ _ _  -> L.PtrTo (L.PrimType (L.Integer 8))
    L.Select _ x _ -> L.typedType x

    L.ExtractValue x idxes -> go (L.typedType x) idxes
         where go tp [] = tp
               go (L.Array n tp') (i:is)
                   | i < n = go tp' is
                   | otherwise = error $ unwords ["invalid index into array type", showInstr instr]
               go (L.Struct tps) (i:is) =
                      case drop (fromIntegral i) tps of
                        (tp':_) -> go tp' is
                        [] -> error $ unwords ["invalid index into struct type", showInstr instr]
               go _ _ = error $ unwords ["invalid type in extract value instruction", showInstr instr]

    L.InsertValue x _ _ -> L.typedType x
    L.ExtractElt x _ -> case L.typedType x of
                        L.Vector _ tp -> tp
                        _ -> error $ unwords ["extract element of non-vector type", showInstr instr]
    L.InsertElt x _ _ -> L.typedType x
    L.ShuffleVector x _ _ -> L.typedType x

    L.LandingPad x _ _ _ -> x

    _ -> error $ unwords ["instrResultType, unsupported instruction:", showInstr instr]

------------------------------------------------------------------------
-- LLVMState

-- | Maps identifiers to an associated register or defined expression.
type IdentMap s = Map L.Ident (Either (Some (Reg s)) (Some (Atom s)))

data LLVMState wptr s
   = LLVMState
   { -- | Map from identifiers to associated register shape
     _identMap :: !(IdentMap s)
   , _blockInfoMap :: !(Map L.BlockLabel (LLVMBlockInfo s))
   , llvmContext :: LLVMContext wptr
   }

identMap :: Simple Lens (LLVMState wptr s) (IdentMap s)
identMap = lens _identMap (\s v -> s { _identMap = v })

blockInfoMap :: Simple Lens (LLVMState wptr s) (Map L.BlockLabel (LLVMBlockInfo s))
blockInfoMap = lens _blockInfoMap (\s v -> s { _blockInfoMap = v })

-- Given a list of LLVM formal parameters and a corresponding crucible
-- register assignment, build an IdentMap mapping LLVM identifiers to
-- corresponding crucible registers.
buildIdentMap :: (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr)
              => [L.Typed L.Ident]
              -> Bool -- ^ varargs
              -> CtxRepr ctx
              -> Ctx.Assignment (Atom s) ctx
              -> IdentMap s
              -> IdentMap s
buildIdentMap ts True ctx asgn m =
  -- Vararg functions are translated as taking a vector of extra arguments
  packBase (VectorRepr AnyRepr) ctx asgn $ \_x ctx' asgn' ->
    buildIdentMap ts False ctx' asgn' m
buildIdentMap [] _ ctx _ m
  | Ctx.null ctx = m
  | otherwise =
      error "buildIdentMap: passed arguments do not match LLVM input signature"
buildIdentMap (ti:ts) _ ctx asgn m = do
  -- ?? FIXME, irrefutable pattern...
  let Just ty = TyCtx.liftMemType (L.typedType ti)
  packType ty ctx asgn $ \x ctx' asgn' ->
     buildIdentMap ts False ctx' asgn' (Map.insert (L.typedValue ti) (Right x) m)

-- | Build the initial LLVM generator state upon entry to to the entry point of a function.
initialState :: (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr)
             => L.Define
             -> LLVMContext wptr
             -> CtxRepr args
             -> Ctx.Assignment (Atom s) args
             -> LLVMState wptr s
initialState d llvmctx args asgn =
   let m = buildIdentMap (reverse (L.defArgs d)) (L.defVarArgs d) args asgn Map.empty in
     LLVMState { _identMap = m, _blockInfoMap = Map.empty, llvmContext = llvmctx }

type LLVMGenerator h s wptr ret a =
  (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr) => Generator LLVM h s (LLVMState wptr) ret a
type LLVMEnd h s wptr ret a =
  (?lc :: TyCtx.LLVMContext, HasPtrWidth wptr) => End LLVM h s (LLVMState wptr) ret a

-- | Information about an LLVM basic block
data LLVMBlockInfo s
  = LLVMBlockInfo
    {
      -- The crucible block label corresponding to this LLVM block
      block_label    :: Label s

      -- map from labels to assignments that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map    :: !(Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value)))
    }

buildBlockInfoMap :: L.Define -> LLVMEnd h s wptr ret (Map L.BlockLabel (LLVMBlockInfo s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: L.BasicBlock -> LLVMEnd h s wptr ret (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let Just blk_lbl = L.bbLabel bb
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_label = lab
                                })

-- Given the statements in a basic block, find all the phi instructions and
-- compute the list of assignments that must be made for each predicessor block.
buildPhiMap :: [L.Stmt] -> Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value))
buildPhiMap ss = go ss Map.empty
 where go (L.Result ident (L.Phi tp xs) _ : stmts) m = go stmts (go' ident tp xs m)
       go _ m = m

       f x mseq = Just (fromMaybe Seq.empty mseq Seq.|> x)

       go' ident tp ((v, lbl) : xs) m = go' ident tp xs (Map.alter (f (ident,tp,v)) lbl m)
       go' _ _ [] m = m

-- | This function pre-computes the types of all the crucible registers by scanning
--   through each basic block and finding the place where that register is assigned.
--   Because LLVM programs are in SSA form, this will occur in exactly one place.
--   The type of the register is infered from the instruction that assigns to it
--   and is recorded in the ident map.
buildRegMap :: IdentMap s -> L.Define -> LLVMEnd h s wptr reg (IdentMap s)
buildRegMap m d = foldM buildRegTypeMap m $ L.defBody d

buildRegTypeMap :: IdentMap s
                -> L.BasicBlock
                -> LLVMEnd h s wptr ret (IdentMap s)
buildRegTypeMap m0 bb = foldM stmt m0 (L.bbStmts bb)
 where stmt m (L.Effect _ _) = return m
       stmt m (L.Result ident instr _) = do
         ty <- liftMemType $ instrResultType instr
         ex <- typeToRegExpr ty
         case Map.lookup ident m of
           Just _ -> fail $ unwords ["register not used in SSA fasion:", show ident]
           Nothing -> return $ Map.insert ident (Left ex) m


---------------------------------------------------------------------------
-- Translations
transTypedValue :: L.Typed L.Value
                -> LLVMGenerator h s wptr ret (LLVMExpr s)
transTypedValue v = do
   tp <- liftMemType $ L.typedType v
   transValue tp (L.typedValue v)

-- | Translate an LLVM Value into an expression.
transValue :: forall h s wptr ret.
              MemType
           -> L.Value
           -> LLVMGenerator h s wptr ret (LLVMExpr s)

transValue ty L.ValZeroInit =
  return $ ZeroExpr ty

transValue ty@(PtrType _) L.ValNull =
  return $ ZeroExpr ty

transValue ty@(IntType _) L.ValNull =
  return $ ZeroExpr ty

transValue ty L.ValUndef =
  return $ UndefExpr ty

transValue _ (L.ValString str) = do
  let eight = knownNat :: NatRepr 8
  let bv8   = BVRepr eight
  let chars = V.fromList $ map (App . BVLit eight . toInteger . fromEnum) $ str
  return $ BaseExpr (VectorRepr bv8) (App $ VectorLit bv8 $ chars)

transValue _ (L.ValIdent i) = do
  m <- use identMap
  case Map.lookup i m of
    Nothing -> do
      reportError $ fromString $ "Could not find identifier " ++ show i ++ "."
    Just (Left (Some r)) -> do
      e <- readReg r
      return $ BaseExpr (typeOfReg r) e
    Just (Right (Some a)) -> do
      return $ BaseExpr (typeOfAtom a) (AtomExpr a)

transValue (IntType w) (L.ValInteger i) =
  case someNat (fromIntegral w) of
    Just (Some w') | Just LeqProof <- isPosNat w' ->
      return $ BaseExpr (LLVMPointerRepr w') (BitvectorAsPointerExpr w' (App (BVLit w' i)))
    _ -> fail $ unwords ["invalid integer type", show w]

transValue (IntType 1) (L.ValBool b) =
  return $ BaseExpr (LLVMPointerRepr (knownNat :: NatRepr 1))
                    (BitvectorAsPointerExpr knownRepr (App (BoolToBV knownNat (litExpr b))))

transValue FloatType (L.ValFloat f) =
  return $ BaseExpr RealValRepr (App (RationalLit (toRational f)))

transValue DoubleType (L.ValDouble d) =
  return $ BaseExpr RealValRepr (App (RationalLit (toRational d)))

transValue (StructType _) (L.ValStruct vs) = do
     vs' <- mapM transTypedValue vs
     xs <- mapM (liftMemType . L.typedType) vs
     return (StructExpr $ Seq.fromList $ zip xs vs')

transValue (StructType _) (L.ValPackedStruct vs) =  do
     vs' <- mapM transTypedValue vs
     xs <- mapM (liftMemType . L.typedType) vs
     return (StructExpr $ Seq.fromList $ zip xs vs')

transValue (ArrayType _ tp) (L.ValArray _ vs) = do
     vs' <- mapM (transValue tp) vs
     return (VecExpr tp $ Seq.fromList vs')

transValue (VecType _ tp) (L.ValVector _ vs) = do
     vs' <- mapM (transValue tp) vs
     return (VecExpr tp $ Seq.fromList vs')

transValue _ (L.ValSymbol symbol) = do
     memVar <- llvmMemVar . memModelOps . llvmContext <$> get
     resolveGlobal <- litExpr . llvmResolveGlobal . memModelOps . llvmContext <$> get
     mem <- readGlobal memVar
     let symbol' = app $ ConcreteLit $ TypeableValue $ GlobalSymbol symbol
     ptr <- call resolveGlobal (Ctx.Empty :> mem :> symbol')
     return (BaseExpr PtrRepr ptr)

transValue _ (L.ValConstExpr cexp) =
  case cexp of
    L.ConstConv op x outty ->
      translateConversion Nothing op x outty
    L.ConstGEP _inBounds _resType [] ->
      fail "empty getelementpointer expression"
    L.ConstGEP _inBounds _resType (base:elts) -> do
      base' <- transTypedValue base
      elts' <- mapM transTypedValue elts
      typ <- liftMemType (L.typedType base)
      BaseExpr PtrRepr <$> calcGEP typ base' elts'
    L.ConstSelect b x y -> do
      b' <- transTypedValue b
      x' <- transTypedValue x
      y' <- transTypedValue y
      mty <- liftMemType (L.typedType x)

      let constSelect :: (1 <= w) => NatRepr w -> Expr LLVM s (BVType w) -> LLVMGenerator h s wptr ret (LLVMExpr s)
          constSelect w bv =
                llvmTypeAsRepr mty $ \tpr -> do
                   b_e <- mkAtom (App $ BVNonzero w bv)
                   BaseExpr tpr <$> (endNow $ \c -> do
                     r <- newUnassignedReg' tpr
                     t_id <- newLabel
                     f_id <- newLabel
                     c_id <- newLambdaLabel' tpr

                     endCurrentBlock (Br b_e t_id f_id)
                     defineBlock t_id $ do
                        doAssign (Some r) x'
                        jumpToLambda c_id =<< readReg r
                     defineBlock t_id $ do
                        doAssign (Some r) y'
                        jumpToLambda c_id =<< readReg r
                     resume c_id c)
      case asScalar b' of
          Scalar (LLVMPointerRepr w) ptr ->
             constSelect w =<< pointerAsBitvectorExpr w ptr
          _ -> fail "expected boolean value in select expression"

    L.ConstBlockAddr _funSymbol _blockLabel ->
      reportError "'blockaddress' expressions not supported."

    L.ConstFCmp _ _ _ -> reportError "constant comparisons not currently supported"
    L.ConstICmp _ _ _ -> reportError "constant comparisons not currently supported"
    L.ConstArith _ _ _ -> reportError "constant arithmetic not currently supported"
    L.ConstBit _ _ _ -> reportError "constant bit operations not currently supported"

transValue ty v =
  reportError $ fromString $ unwords ["unsupported LLVM value:", show v, "of type", show ty]


-- | Assign a packed LLVM expression into the named LLVM register.
assignLLVMReg
        :: L.Ident
        -> LLVMExpr s
        -> LLVMGenerator h s wptr ret ()
assignLLVMReg ident rhs = do
  st <- get
  let idMap = st^.identMap
  case Map.lookup ident idMap of
    Just (Left lhs) -> do
      doAssign lhs rhs
    Just (Right _) -> fail $ "internal: Value cannot be assigned to."
    Nothing  -> fail $ unwords ["register not found in register map:", show ident]

-- | Given a register and an expression shape, assign the expressions in the right-hand-side
--   into the register left-hand side.
doAssign :: forall h s wptr ret.
      Some (Reg s)
   -> LLVMExpr s  -- ^ the RHS values to assign
   -> LLVMGenerator h s wptr ret ()
doAssign (Some r) (BaseExpr tpr ex) =
   case testEquality (typeOfReg r) tpr of
     Just Refl -> assignReg r ex
     Nothing -> reportError $ fromString $ unwords ["type mismatch when assigning register", show r, show (typeOfReg r) , show tpr]
doAssign (Some r) (StructExpr vs) = do
   let ?err = fail
   unpackArgs (map snd $ toList vs) $ \ctx asgn ->
     case testEquality (typeOfReg r) (StructRepr ctx) of
       Just Refl -> assignReg r (mkStruct ctx asgn)
       Nothing -> reportError $ fromString $ unwords ["type mismatch when assigning structure to register", show r, show (StructRepr ctx)]
doAssign (Some r) (ZeroExpr tp) = do
  let ?err = fail
  zeroExpand tp $ \(tpr :: TypeRepr t) (ex :: Expr LLVM s t) ->
    case testEquality (typeOfReg r) tpr of
      Just Refl -> assignReg r ex
      Nothing -> reportError $ fromString $ "type mismatch when assigning zero value"
doAssign (Some r) (UndefExpr tp) = do
  let ?err = fail
  undefExpand tp $ \(tpr :: TypeRepr t) (ex :: Expr LLVM s t) ->
    case testEquality (typeOfReg r) tpr of
      Just Refl -> assignReg r ex
      Nothing -> reportError $ fromString $ "type mismatch when assigning undef value"
doAssign (Some r) (VecExpr tp vs) = do
  let ?err = fail
  llvmTypeAsRepr tp $ \tpr ->
    unpackVec tpr (toList vs) $ \ex ->
      case testEquality (typeOfReg r) (VectorRepr tpr) of
        Just Refl -> assignReg r ex
        Nothing -> reportError $ fromString $ "type mismatch when assigning vector value"

-- | Given a list of LLVMExpressions, "unpack" them into an assignment
--   of crucible expressions.
unpackArgs :: forall s a wptr
    . (?lc :: TyCtx.LLVMContext
      ,?err :: String -> a
      , HasPtrWidth wptr
      )
   => [LLVMExpr s]
   -> (forall ctx. CtxRepr ctx -> Ctx.Assignment (Expr LLVM s) ctx -> a)
   -> a
unpackArgs = go Ctx.Empty Ctx.Empty
 where go :: CtxRepr ctx
          -> Ctx.Assignment (Expr LLVM s) ctx
          -> [LLVMExpr s]
          -> (forall ctx'. CtxRepr ctx' -> Ctx.Assignment (Expr LLVM s) ctx' -> a)
          -> a
       go ctx asgn [] k = k ctx asgn
       go ctx asgn (v:vs) k = unpackOne v (\tyr ex -> go (ctx :> tyr) (asgn :> ex) vs k)

unpackOne
   :: (?lc :: TyCtx.LLVMContext, ?err :: String -> a, HasPtrWidth wptr)
   => LLVMExpr s
   -> (forall tpr. TypeRepr tpr -> Expr LLVM s tpr -> a)
   -> a
unpackOne (BaseExpr tyr ex) k = k tyr ex
unpackOne (UndefExpr tp) k = undefExpand tp k
unpackOne (ZeroExpr tp) k = zeroExpand tp k
unpackOne (StructExpr vs) k =
  unpackArgs (map snd $ toList vs) $ \struct_ctx struct_asgn ->
      k (StructRepr struct_ctx) (mkStruct struct_ctx struct_asgn)
unpackOne (VecExpr tp vs) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (toList (Seq.reverse vs)) $ k (VectorRepr tpr)

unpackVec :: forall tpr s wptr a
    . (?lc :: TyCtx.LLVMContext, ?err :: String -> a, HasPtrWidth wptr)
   => TypeRepr tpr
   -> [LLVMExpr s]
   -> (Expr LLVM s (VectorType tpr) -> a)
   -> a
unpackVec tpr = go []
  where go :: [Expr LLVM s tpr] -> [LLVMExpr s] -> (Expr LLVM s (VectorType tpr) -> a) -> a
        go vs [] k = k (vectorLit tpr $ V.fromList vs)
        go vs (x:xs) k = unpackOne x $ \tpr' v ->
                           case testEquality tpr tpr' of
                             Just Refl -> go (v:vs) xs k
                             Nothing -> ?err $ unwords ["type mismatch in array value", show tpr, show tpr']

zeroExpand :: forall s wptr a
            . (?lc :: TyCtx.LLVMContext, ?err :: String -> a, HasPtrWidth wptr)
           => MemType
           -> (forall tp. TypeRepr tp -> Expr LLVM s tp -> a)
           -> a
zeroExpand (IntType w) k =
  case someNat (fromIntegral w) of
    Just (Some w') | Just LeqProof <- isPosNat w' ->
      k (LLVMPointerRepr w') $
         BitvectorAsPointerExpr w' $
         App $ BVLit w' 0

    _ -> ?err $ unwords ["illegal integer size", show w]

zeroExpand (StructType si) k =
   unpackArgs (map ZeroExpr tps) $ \ctx asgn -> k (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
zeroExpand (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k (VectorRepr tpr)
zeroExpand (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k (VectorRepr tpr)
zeroExpand (PtrType _tp) k = k PtrRepr nullPointer
zeroExpand FloatType   k  = k RealValRepr (App (RationalLit 0))
zeroExpand DoubleType  k  = k RealValRepr (App (RationalLit 0))
zeroExpand MetadataType _ = ?err "Cannot zero expand metadata"

nullPointer :: (IsExpr e, HasPtrWidth wptr)
            => e (LLVMPointerType wptr)
nullPointer = app $ RollRecursive knownSymbol (Ctx.Empty Ctx.:> BVRepr PtrWidth)  $
  app $ MkStruct
          (Ctx.Empty :> NatRepr :> BVRepr PtrWidth)
          (Ctx.Empty :> litExpr 0 :> app (BVLit PtrWidth 0))

undefExpand :: (?lc :: TyCtx.LLVMContext, ?err :: String -> a, HasPtrWidth wptr)
            => MemType
            -> (forall tp. TypeRepr tp -> Expr LLVM s tp -> a)
            -> a
undefExpand (IntType w) k =
  case someNat (fromIntegral w) of
    Just (Some w') | Just LeqProof <- isPosNat w' ->
      k (LLVMPointerRepr w') $
         BitvectorAsPointerExpr w' $
         App $ BVUndef w'

    _ -> ?err $ unwords ["illegal integer size", show w]
undefExpand (PtrType _tp) k =
   k PtrRepr $ BitvectorAsPointerExpr PtrWidth $ App $ BVUndef PtrWidth
undefExpand (StructType si) k =
   unpackArgs (map UndefExpr tps) $ \ctx asgn -> k (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
undefExpand (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k (VectorRepr tpr)
undefExpand (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k (VectorRepr tpr)
undefExpand tp _ = ?err $ unwords ["cannot undef expand type:", show tp]

--undefExpand (L.PrimType (L.FloatType _ft)) _k = error "FIXME undefExpand: float types"

unpackVarArgs :: forall h s wptr ret a
    . (?err :: String -> a)
   => [LLVMExpr s]
   -> LLVMGenerator h s wptr ret (Expr LLVM s (VectorType AnyType))
unpackVarArgs xs = App . VectorLit AnyRepr . V.fromList <$> xs'
 where xs' = let ?err = fail in
             mapM (\x -> unpackOne x (\tp x' -> return $ App (PackAny tp x'))) xs

-- | Implement the phi-functions along the edge from one LLVM Basic block to another.
definePhiBlock :: L.BlockLabel      -- ^ The LLVM source basic block
               -> L.BlockLabel      -- ^ The LLVM target basic block
               -> LLVMGenerator h s wptr ret ()
definePhiBlock l l' = do
  bim <- use blockInfoMap
  case Map.lookup l' bim of
    Nothing -> fail $ unwords ["label not found in label map:", show l']
    Just bi' -> do
      -- Collect all the relevant phi functions to evaluate
      let phi_funcs = maybe [] toList $ Map.lookup l (block_phi_map bi')

      -- NOTE: We evaluate all the right-hand sides of the phi nodes BEFORE
      --   we assign the values to their associated registers.  This preserves
      --   the expected semantics that phi functions are evaluated in the context
      --   of the previous basic block, and prevents unintended register shadowing.
      --   Otherwise loop-carried dependencies will sometimes end up with the wrong
      --   values.
      phiVals <- mapM evalPhi phi_funcs
      mapM_ assignPhi phiVals

      -- Now jump to the target code block
      jump (block_label bi')

 where evalPhi (ident,tp,v) = do
           t_v <- transTypedValue (L.Typed tp v)
           return (ident,t_v)
       assignPhi (ident,t_v) = do
           assignLLVMReg ident t_v

pattern PointerExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s NatType
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s (LLVMPointerType w)
pattern PointerExpr w blk off <-
   App (RollRecursive _ (Ctx.Empty :> BVRepr w)
  (App (MkStruct _ (Ctx.Empty :> blk :> off))))
 where PointerExpr w blk off =
          App (RollRecursive knownRepr (Ctx.Empty :> BVRepr w)
          (App (MkStruct (Ctx.Empty :> NatRepr :> BVRepr w)
                    (Ctx.Empty :> blk :> off))))

pattern BitvectorAsPointerExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s (LLVMPointerType w)
pattern BitvectorAsPointerExpr w ex <-
   App (RollRecursive _ (Ctx.Empty :> BVRepr w)
  (App (MkStruct _ (Ctx.Empty :> (App (NatLit 0)) :> ex))))

 where BitvectorAsPointerExpr w ex =
          App (RollRecursive knownRepr (Ctx.Empty :> BVRepr w)
          (App (MkStruct (Ctx.Empty :> NatRepr :> BVRepr w)
                    (Ctx.Empty :> (App (NatLit 0)) :> ex))))

pointerAsBitvectorExpr
    :: (1 <= w)
    => NatRepr w
    -> Expr LLVM s (LLVMPointerType w)
    -> LLVMGenerator h s wptr ret (Expr LLVM s (BVType w))
pointerAsBitvectorExpr _ (BitvectorAsPointerExpr _ ex) =
     return ex
pointerAsBitvectorExpr w ex =
  do ex' <- forceEvaluation (App (UnrollRecursive knownRepr (Ctx.Empty :> BVRepr w) ex))
     let blk = App (GetStruct ex' (Ctx.natIndex @0) NatRepr)
     let off = App (GetStruct ex' (Ctx.natIndex @1) (BVRepr w))
     assertExpr (blk .== litExpr 0)
                (litExpr "Expected bitvector, but found pointer")
     return off

-- | Given an LLVM expression of vector type, select out the ith element.
extractElt
    :: forall h s wptr ret.
       L.Instr
    -> MemType    -- ^ type contained in the vector
    -> Integer   -- ^ size of the vector
    -> LLVMExpr s -- ^ vector expression
    -> LLVMExpr s -- ^ index expression
    -> LLVMGenerator h s wptr ret (LLVMExpr s)
extractElt _ ty _ _ (UndefExpr _)  =
   return $ UndefExpr ty
extractElt instr ty n v (ZeroExpr zty) = do
   let ?err = fail
   zeroExpand zty $ \tyr ex -> extractElt instr ty n v (BaseExpr tyr ex)
extractElt instr ty n (UndefExpr _) i  = do
   let ?err = fail
   undefExpand ty $ \tyr ex -> extractElt instr ty n (BaseExpr tyr ex) i
extractElt instr ty n (ZeroExpr _) i   = do
   let ?err = fail
   zeroExpand ty  $ \tyr ex -> extractElt instr ty n (BaseExpr tyr ex) i
extractElt instr _ n (VecExpr _ vs) i
  | Scalar (LLVMPointerRepr _) (BitvectorAsPointerExpr _ x) <- asScalar i
  , App (BVLit _ x') <- x
  = constantExtract x'

 where
 constantExtract :: Integer -> LLVMGenerator h s wptr ret (LLVMExpr s)
 constantExtract idx =
    if (fromInteger idx < Seq.length vs) && (fromInteger idx < n)
        then return $ Seq.index vs (fromInteger idx)
        else fail (unlines ["invalid extractelement instruction (index out of bounds)", showInstr instr])

extractElt instr ty n (VecExpr _ vs) i = do
   let ?err = fail
   llvmTypeAsRepr ty $ \tyr -> unpackVec tyr (toList vs) $
      \ex -> extractElt instr ty n (BaseExpr (VectorRepr tyr) ex) i
extractElt instr _ n (BaseExpr (VectorRepr tyr) v) i =
  do idx <- case asScalar i of
                   Scalar (LLVMPointerRepr w) x ->
                     do bv <- pointerAsBitvectorExpr w x
                        assertExpr (App (BVUlt w bv (App (BVLit w n)))) "extract element index out of bounds!"
                        return $ App (BvToNat w bv)
                   _ ->
                     fail (unlines ["invalid extractelement instruction", showInstr instr])
     return $ BaseExpr tyr (App (VectorGetEntry tyr v idx))

extractElt instr _ _ _ _ = fail (unlines ["invalid extractelement instruction", showInstr instr])


-- | Given an LLVM expression of vector type, insert a new element at location ith element.
insertElt :: forall h s wptr ret.
       L.Instr            -- ^ Actual instruction
    -> MemType            -- ^ type contained in the vector
    -> Integer            -- ^ size of the vector
    -> LLVMExpr s    -- ^ vector expression
    -> LLVMExpr s    -- ^ element to insert
    -> LLVMExpr s    -- ^ index expression
    -> LLVMGenerator h s wptr ret (LLVMExpr s)
insertElt _ ty _ _ _ (UndefExpr _) = do
   return $ UndefExpr ty
insertElt instr ty n v a (ZeroExpr zty) = do
   let ?err = fail
   zeroExpand zty $ \tyr ex -> insertElt instr ty n v a (BaseExpr tyr ex)

insertElt instr ty n (UndefExpr _) a i  = do
  insertElt instr ty n (VecExpr ty (Seq.replicate (fromInteger n) (UndefExpr ty))) a i
insertElt instr ty n (ZeroExpr _) a i   = do
  insertElt instr ty n (VecExpr ty (Seq.replicate (fromInteger n) (ZeroExpr ty))) a i

insertElt instr _ n (VecExpr ty vs) a i
  | Scalar (LLVMPointerRepr _) (BitvectorAsPointerExpr _ x) <- asScalar i
  , App (BVLit _ x') <- x
  = constantInsert x'
 where
 constantInsert :: Integer -> LLVMGenerator h s wptr ret (LLVMExpr s)
 constantInsert idx =
     if (fromInteger idx < Seq.length vs) && (fromInteger idx < n)
       then return $ VecExpr ty $ Seq.adjust (\_ -> a) (fromIntegral idx) vs
       else fail (unlines ["invalid insertelement instruction (index out of bounds)", showInstr instr])

insertElt instr ty n (VecExpr _ vs) a i = do
   let ?err = fail
   llvmTypeAsRepr ty $ \tyr -> unpackVec tyr (toList vs) $
        \ex -> insertElt instr ty n (BaseExpr (VectorRepr tyr) ex) a i

insertElt instr _ n (BaseExpr (VectorRepr tyr) v) a i =
  do (idx :: Expr LLVM s NatType)
         <- case asScalar i of
                   Scalar (LLVMPointerRepr w) x ->
                     do bv <- pointerAsBitvectorExpr w x
                        assertExpr (App (BVUlt w bv (App (BVLit w n)))) "insert element index out of bounds!"
                        return $ App (BvToNat w bv)
                   _ ->
                     fail (unlines ["invalid insertelement instruction", showInstr instr, show i])
     let ?err = fail
     unpackOne a $ \tyra a' ->
      case testEquality tyr tyra of
        Just Refl ->
          return $ BaseExpr (VectorRepr tyr) (App (VectorSetEntry tyr v idx a'))
        Nothing -> fail (unlines ["type mismatch in insertelement instruction", showInstr instr])
insertElt instr _tp n v a i = fail (unlines ["invalid insertelement instruction", showInstr instr, show n, show v, show a, show i])

-- Given an LLVM expression of vector or structure type, select out the
-- element indicated by the sequence of given concrete indices.
extractValue
    :: LLVMExpr s  -- ^ aggregate expression
    -> [Int32]     -- ^ sequence of indices
    -> LLVMGenerator h s wptr ret (LLVMExpr s)
extractValue v [] = return v
extractValue (UndefExpr (StructType si)) is =
   extractValue (StructExpr $ Seq.fromList $ map (\tp -> (tp, UndefExpr tp)) tps) is
 where tps = map fiType $ toList $ siFields si
extractValue (UndefExpr (ArrayType n tp)) is =
   extractValue (VecExpr tp $ Seq.replicate (fromIntegral n) (UndefExpr tp)) is
extractValue (ZeroExpr (StructType si)) is =
   extractValue (StructExpr $ Seq.fromList $ map (\tp -> (tp, ZeroExpr tp)) tps) is
 where tps = map fiType $ toList $ siFields si
extractValue (ZeroExpr (ArrayType n tp)) is =
   extractValue (VecExpr tp $ Seq.replicate (fromIntegral n) (ZeroExpr tp)) is
extractValue (BaseExpr (StructRepr ctx) x) (i:is)
   | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
           let tpr = ctx Ctx.! idx
           extractValue (BaseExpr tpr (getStruct idx x)) is
extractValue (StructExpr vs) (i:is)
   | fromIntegral i < Seq.length vs = extractValue (snd $ Seq.index vs $ fromIntegral i) is
extractValue (VecExpr _ vs) (i:is)
   | fromIntegral i < Seq.length vs = extractValue (Seq.index vs $ fromIntegral i) is
extractValue _ _ = fail "invalid extractValue instruction"


-- Given an LLVM expression of vector or structure type, insert a new element in the posistion
-- given by the concrete indices.
insertValue
    :: LLVMExpr s  -- ^ aggregate expression
    -> LLVMExpr s  -- ^ element to insert
    -> [Int32]     -- ^ sequence of concrete indices
    -> LLVMGenerator h s wptr ret (LLVMExpr s)
insertValue _ v [] = return v
insertValue (UndefExpr (StructType si)) v is =
   insertValue (StructExpr $ Seq.fromList $ map (\tp -> (tp, UndefExpr tp)) tps) v is
 where tps = map fiType $ toList $ siFields si
insertValue (UndefExpr (ArrayType n tp)) v is =
   insertValue (VecExpr tp $ Seq.replicate (fromIntegral n) (UndefExpr tp)) v is
insertValue (ZeroExpr (StructType si)) v is =
   insertValue (StructExpr $ Seq.fromList $ map (\tp -> (tp, ZeroExpr tp)) tps) v is
 where tps = map fiType $ toList $ siFields si
insertValue (ZeroExpr (ArrayType n tp)) v is =
   insertValue (VecExpr tp $ Seq.replicate (fromIntegral n) (ZeroExpr tp)) v is
insertValue (BaseExpr (StructRepr ctx) x) v (i:is)
   | Just (Some idx) <- Ctx.intIndex (fromIntegral i) (Ctx.size ctx) = do
           let tpr = ctx Ctx.! idx
           x' <- insertValue (BaseExpr tpr (getStruct idx x)) v is
           case x' of
             BaseExpr tpr' x''
               | Just Refl <- testEquality tpr tpr' ->
                    return $ BaseExpr (StructRepr ctx) (setStruct ctx x idx x'')
             _ -> fail "insertValue was expected to return base value of same type"
insertValue (StructExpr vs) v (i:is)
   | fromIntegral i < Seq.length vs = do
        let (xtp, x) = Seq.index vs (fromIntegral i)
        x' <- insertValue x v is
        return (StructExpr (Seq.adjust (\_ -> (xtp,x')) (fromIntegral i) vs))
insertValue (VecExpr tp vs) v (i:is)
   | fromIntegral i < Seq.length vs = do
        let x = Seq.index vs (fromIntegral i)
        x' <- insertValue x v is
        return (VecExpr tp (Seq.adjust (\_ -> x') (fromIntegral i) vs))
insertValue _ _ _ = fail "invalid insertValue instruction"


callIsNull
   :: (1 <= w)
   => NatRepr w
   -> Expr LLVM s (LLVMPointerType w)
   -> LLVMGenerator h s wptr ret (Expr LLVM s BoolType)
callIsNull w (BitvectorAsPointerExpr _ bv) =
  case bv of
    App (BVLit _ 0) -> return true
    _ -> return (App (BVEq w bv (App (BVLit w 0))))
callIsNull w ex =
   do ex' <- forceEvaluation (App (UnrollRecursive knownRepr (Ctx.Empty :> BVRepr w) ex))
      let blk = App (GetStruct ex' (Ctx.natIndex @0) NatRepr)
      let off = App (GetStruct ex' (Ctx.natIndex @1) (BVRepr w))
      return (blk .== litExpr 0 .&& (App (BVEq w off (App (BVLit w 0)))))

callAlloca
   :: Expr LLVM s (BVType wptr)
   -> LLVMGenerator h s wptr ret (Expr LLVM s (LLVMPointerType wptr))
callAlloca sz = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   alloca <- litExpr . llvmMemAlloca . memModelOps . llvmContext <$> get
   mem <- readGlobal memVar
   loc <- litExpr . Text.pack . show <$> getPosition
   res <- call alloca (Ctx.Empty :> mem :> sz :> loc)
   let mem' = getStruct (Ctx.natIndex @0) res
   let p    = getStruct (Ctx.natIndex @1) res
   writeGlobal memVar mem'
   return p

callPushFrame :: LLVMGenerator h s wptr ret ()
callPushFrame = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   pushFrame <- litExpr . llvmMemPushFrame . memModelOps . llvmContext <$> get
   mem  <- readGlobal memVar
   mem' <- call pushFrame (Ctx.Empty :> mem)
   writeGlobal memVar mem'

callPopFrame :: LLVMGenerator h s wptr ret ()
callPopFrame = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   popFrame <- litExpr . llvmMemPopFrame . memModelOps . llvmContext <$> get
   mem  <- readGlobal memVar
   mem' <- call popFrame (Ctx.Empty :> mem)
   writeGlobal memVar mem'


toStorableType :: (Monad m, HasPtrWidth wptr)
               => MemType
               -> m G.Type
toStorableType mt =
  case mt of
    IntType n -> return $ G.bitvectorType (G.bitsToBytes n)
    PtrType _ -> return $ G.bitvectorType (G.bitsToBytes (natValue PtrWidth))
    FloatType -> return $ G.floatType
    DoubleType -> return $ G.doubleType
    ArrayType n x -> G.arrayType (fromIntegral n) <$> toStorableType x
    VecType n x -> G.arrayType (fromIntegral n) <$> toStorableType x
    MetadataType -> fail "toStorableType: Cannot store metadata values"
    StructType si -> G.mkStruct <$> traverse transField (siFields si)
      where transField :: Monad m => FieldInfo -> m (G.Type, G.Size)
            transField fi = do
               t <- toStorableType $ fiType fi
               return (t, fiPadding fi)

callPtrAddOffset ::
       Expr LLVM s (LLVMPointerType wptr)
    -> Expr LLVM s (BVType wptr)
    -> LLVMGenerator h s wptr ret (Expr LLVM s (LLVMPointerType wptr))
callPtrAddOffset base off = do
    memVar <- llvmMemVar . memModelOps . llvmContext <$> get
    mem  <- readGlobal memVar
    ptrAddOff <- litExpr . llvmPtrAddOffset . memModelOps . llvmContext <$> get
    call ptrAddOff (Ctx.Empty :> mem :> base :> off)

callPtrSubtract ::
       Expr LLVM s (LLVMPointerType wptr)
    -> Expr LLVM s (LLVMPointerType wptr)
    -> LLVMGenerator h s wptr ret (Expr LLVM s (BVType wptr))
callPtrSubtract x y = do
    memVar <- llvmMemVar . memModelOps . llvmContext <$> get
    mem  <- readGlobal memVar
    pSub <- litExpr . llvmPtrSubtract . memModelOps . llvmContext <$> get
    call pSub (Ctx.Empty :> mem :> x :> y)


callLoad :: MemType
         -> TypeRepr tp
         -> LLVMExpr s
         -> Alignment
         -> LLVMGenerator h s wptr ret (LLVMExpr s)
callLoad typ expectTy (asScalar -> Scalar PtrRepr ptr) align =
   do memVar <- llvmMemVar . memModelOps . llvmContext <$> get
      memLoad <- litExpr . llvmMemLoad . memModelOps . llvmContext <$> get
      mem  <- readGlobal memVar
      typ' <- app . ConcreteLit . TypeableValue <$> toStorableType typ
      let align' = litExpr align
      v <- call memLoad (Ctx.Empty :> mem :> ptr :> typ' :> align')
      let msg = litExpr (Text.pack ("Expected load to return value of type " ++ show expectTy))
      let v' = app $ FromJustValue expectTy (app $ UnpackAny expectTy v) msg
      return (BaseExpr expectTy v')
callLoad _ _ _ _ =
  fail $ unwords ["Unexpected argument type in callLoad"]

callStore :: MemType
          -> LLVMExpr s
          -> LLVMExpr s
          -> LLVMGenerator h s wptr ret ()
callStore typ (asScalar -> Scalar PtrRepr ptr) v =
 do let ?err = fail
    unpackOne v $ \vtpr vexpr -> do
      memVar <- llvmMemVar . memModelOps . llvmContext <$> get
      memStore <- litExpr . llvmMemStore . memModelOps . llvmContext <$> get
      mem  <- readGlobal memVar
      let v' = app (PackAny vtpr vexpr)
      typ' <- app . ConcreteLit . TypeableValue <$> toStorableType typ
      mem' <- call memStore (Ctx.Empty :> mem :> ptr :> typ' :> v')
      writeGlobal memVar mem'

callStore _ _ _ =
  fail $ unwords ["Unexpected argument type in callStore"]


calcGEP :: MemType
        -> LLVMExpr s
        -> [LLVMExpr s]
        -> LLVMGenerator h s wptr ret (Expr LLVM s (LLVMPointerType wptr))
calcGEP typ@(PtrType _) (asScalar -> Scalar PtrRepr base) xs@(_ : _) =
   calcGEP' typ base xs

-- FIXME: support for vector base arguments
calcGEP typ _base _xs = do
   fail $ unwords ["Invalid base argument type in GEP", show typ]


calcGEP' :: forall h s wptr ret.
            MemType
         -> Expr LLVM s (LLVMPointerType wptr)
         -> [LLVMExpr s]
         -> LLVMGenerator h s wptr ret (Expr LLVM s (LLVMPointerType wptr))

calcGEP' _typ base [] = return base

calcGEP' (PtrType (Alias ident)) base xs =
  case TyCtx.lookupAlias ident of
    Just ty -> calcGEP' (PtrType ty) base xs
    Nothing -> fail $ unwords ["Unable to resolve type alias", show ident]

calcGEP' (ArrayType bound typ') base (idx : xs) = do
    idx' <- case asScalar idx of
              Scalar (LLVMPointerRepr w) x
                 | Just Refl <- testEquality w PtrWidth ->
                      pointerAsBitvectorExpr PtrWidth x
                 | Just LeqProof <- testLeq (incNat w) PtrWidth ->
                   do x' <- pointerAsBitvectorExpr w x
                      AtomExpr <$> mkAtom (app (BVSext PtrWidth w x'))
              Scalar tp x ->
                   fail $ unwords ["Invalid index value in GEP", show tp, show x]
              _ -> fail $ unwords ["Invalid index value in GEP", show idx]

    -- assert that 0 <= idx' <= bound
    --   (yes, <= and not < because of the 1-past-the-end rule)
    let zero      = App $ BVLit PtrWidth 0
    let bound'    = App $ BVLit PtrWidth $ toInteger bound
    let geZero    = App $ BVSle PtrWidth zero idx'
    let leBound   = App $ BVSle PtrWidth idx' bound'
    let boundTest = App $ And geZero leBound
    assertExpr boundTest
      (App $ TextLit $ Text.pack "Array index out of bounds when calculating getelementpointer")

    let dl  = TyCtx.llvmDataLayout ?lc

    -- Calculate the size of the element memtype and check that it fits
    -- in the pointer width
    let isz = G.bytesToInteger $ memTypeSize dl typ'
    unless (isz <= maxSigned PtrWidth)
      (fail $ unwords ["Type size too large for pointer width:", show typ'])

    let sz :: Expr LLVM s (BVType wptr)
        sz  = app $ BVLit PtrWidth $ isz

    -- Perform a signed wide multiply and check for overflow
    Just LeqProof <- return (testLeq (knownNat @1) (addNat PtrWidth PtrWidth))
    Just LeqProof <- return (testLeq (addNat PtrWidth (knownNat @1)) (addNat PtrWidth PtrWidth))
    let wideMul  = app $ BVMul (addNat PtrWidth PtrWidth)
                           (app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth sz)
                           (app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth idx')
    let off      = app $ BVTrunc PtrWidth (addNat PtrWidth PtrWidth) wideMul
    let wideMul' = app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth off
    assertExpr (app $ BVEq (addNat PtrWidth PtrWidth) wideMul wideMul')
      (App $ TextLit $ Text.pack "Multiplication overflow in getelementpointer")

    -- Perform the pointer arithmetic and continue
    base' <- callPtrAddOffset base off
    calcGEP' typ' base' xs

calcGEP' (PtrType (MemType typ')) base (idx : xs) = do
    (idx' :: Expr LLVM s (BVType wptr))
       <- case asScalar idx of
              Scalar (LLVMPointerRepr w) x
                 | Just Refl <- testEquality w PtrWidth ->
                      pointerAsBitvectorExpr PtrWidth x
                 | Just LeqProof <- testLeq (incNat w) PtrWidth ->
                   do x' <- pointerAsBitvectorExpr w x
                      return $ app (BVSext PtrWidth w x')
              _ -> fail $ unwords ["Invalid index value in GEP", show idx]
    let dl  = TyCtx.llvmDataLayout ?lc

    -- Calculate the size of the elemement memtype and check that it fits
    -- in the pointer width
    let isz = G.bytesToInteger $ memTypeSize dl typ'
    unless (isz <= maxSigned PtrWidth)
      (fail $ unwords ["Type size too large for pointer width:", show typ'])
    let sz :: Expr LLVM s (BVType wptr)
        sz  = app $ BVLit PtrWidth $ isz

    -- Perform a signed wide multiply and check for overflow
    Just LeqProof <- return (testLeq (knownNat @1) (addNat PtrWidth PtrWidth))
    Just LeqProof <- return (testLeq (addNat PtrWidth (knownNat @1)) (addNat PtrWidth PtrWidth))
    let wideMul = app $ BVMul (addNat PtrWidth PtrWidth)
                           (app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth sz)
                           (app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth idx')
    let off      = app $ BVTrunc PtrWidth (addNat PtrWidth PtrWidth) wideMul
    let wideMul' = app $ BVSext (addNat PtrWidth PtrWidth) PtrWidth off
    assertExpr (app $ BVEq (addNat PtrWidth PtrWidth) wideMul wideMul')
      (App $ TextLit $ Text.pack "Multiplication overflow in getelementpointer")

    -- Perform the pointer arithmetic and continue
    base' <- callPtrAddOffset base off
    calcGEP' typ' base' xs

calcGEP' (StructType si) base (idx : xs) = do
    idx' <- case asScalar idx of
              Scalar (LLVMPointerRepr _w) (BitvectorAsPointerExpr _ (asApp -> Just (BVLit _ x))) -> return x
              _ -> fail $ unwords ["Expected constant value when indexing fields in GEP"]
    case siFieldInfo si (fromInteger idx') of
      Just fi -> do
        -- Get the field offset and check that it fits
        -- in the pointer width
        let ioff = G.bytesToInteger $ fiOffset fi
        unless (ioff <= maxSigned PtrWidth)
          (fail $ unwords ["Field offset too large for pointer width in structure:"
                          , show (ppMemType (StructType si))])
        let off  = app $ BVLit PtrWidth $ ioff

        -- Perform the pointer arithmetic and continue
        base' <- callPtrAddOffset base off
        let typ' = fiType fi
        calcGEP' typ' base' xs
      Nothing ->
        fail $ unwords ["Invalid field index", show idx', "for structure", show (ppMemType (StructType si))]

calcGEP' tp _ _ =
    fail $ unwords ["calcGEP': invalid arguments", show tp]


translateConversion
  :: Maybe L.Instr
  -> L.ConvOp
  -> L.Typed L.Value
  -> L.Type
  -> LLVMGenerator h s wptr ret (LLVMExpr s)
translateConversion instr op x outty =
 let showI = maybe "" showInstr instr in
 case op of
    L.IntToPtr -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) _, LLVMPointerRepr w')
              | Just Refl <- testEquality w PtrWidth
              , Just Refl <- testEquality w' PtrWidth -> return x'
           (Scalar t v, a)   ->
               fail (unlines ["integer-to-pointer conversion failed: "
                             , showI
                             , show v ++ " : " ++ show (pretty t) ++ " -to- " ++ show (pretty a)
                             ])
           (NotScalar, _) -> fail (unlines ["integer-to-pointer conversion failed: non scalar", showI])

    L.PtrToInt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) _, LLVMPointerRepr w')
              | Just Refl <- testEquality w PtrWidth
              , Just Refl <- testEquality w' PtrWidth -> return x'
           _ -> fail (unlines ["pointer-to-integer conversion failed", showI])

    L.Trunc -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) x'', (LLVMPointerRepr w'))
             | Just LeqProof <- isPosNat w'
             , Just LeqProof <- testLeq (incNat w') w ->
                 do x_bv <- pointerAsBitvectorExpr w x''
                    let bv' = App (BVTrunc w' w x_bv)
                    return (BaseExpr outty'' (BitvectorAsPointerExpr w' bv'))
           _ -> fail (unlines [unwords ["invalid truncation:", show x, show outty], showI])

    L.ZExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) x'', (LLVMPointerRepr w'))
             | Just LeqProof <- isPosNat w
             , Just LeqProof <- testLeq (incNat w) w' ->
                 do x_bv <- pointerAsBitvectorExpr w x''
                    let bv' = App (BVZext w' w x_bv)
                    return (BaseExpr outty'' (BitvectorAsPointerExpr w' bv'))
           _ -> fail (unlines [unwords ["invalid zero extension:", show x, show outty], showI])

    L.SExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) x'', (LLVMPointerRepr w'))
             | Just LeqProof <- isPosNat w
             , Just LeqProof <- testLeq (incNat w) w' -> do
                 do x_bv <- pointerAsBitvectorExpr w x''
                    let bv' = App (BVSext w' w x_bv)
                    return (BaseExpr outty'' (BitvectorAsPointerExpr w' bv'))
           _ -> fail (unlines [unwords ["invalid sign extension", show x, show outty], showI])

    L.BitCast -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case asScalar x' of
           Scalar tyx _ | Just Refl <- testEquality tyx outty'' ->
             return x'
           _ -> fail (unlines ["invalid bitcast", showI, show x, show outty, show outty''])

    L.UiToFp -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       let promoteToFp :: (1 <= w) => NatRepr w -> Expr LLVM s (BVType w) -> LLVMExpr s
           promoteToFp w bv = BaseExpr RealValRepr (App $ IntegerToReal $ App $ NatToInteger $ App $ BvToNat w bv)
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) x'', RealValRepr) -> do
             promoteToFp w <$> pointerAsBitvectorExpr w x''

           _ -> fail (unlines [unwords ["Invalid uitofp:", show op, show x, show outty], showI])

    L.SiToFp -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       let promoteToFp :: (1 <= w) => NatRepr w -> Expr LLVM s (BVType w) -> LLVMGenerator h s wptr ret (LLVMExpr s)
           promoteToFp w bv =
             do -- is the value negative?
                t <- AtomExpr <$> mkAtom (App $ BVSlt w bv $ App $ BVLit w 0)
                -- unsigned value of the bitvector as a real
                v <- AtomExpr <$> mkAtom (App $ IntegerToReal $ App $ NatToInteger $ App $ BvToNat w bv)
                -- MAXINT as a real
                maxint <- AtomExpr <$> mkAtom (App $ RationalLit $ fromInteger $ maxUnsigned w)
                -- z = if neg then (v - MAXINT) else v
                let z = App $ RealIte t (App $ RealSub v maxint) v
                return $ BaseExpr RealValRepr z

       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (LLVMPointerRepr w) x'', RealValRepr) ->
             promoteToFp w =<< pointerAsBitvectorExpr w x''
           _ -> fail (unlines [unwords ["Invalid uitofp:", show op, show x, show outty], showI])

    L.FpToUi -> do
       reportError "Not Yet Implemented: FpToUi"
    L.FpToSi -> do
       reportError "Not Yet Implemented: FpToSi"

    L.FpTrunc -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar RealValRepr x'', RealValRepr) -> do
             return $ BaseExpr RealValRepr x''
           _ -> fail (unlines [unwords ["Invalid fptrunc:", show op, show x, show outty], showI])

    L.FpExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar RealValRepr x'', RealValRepr) -> do
             return $ BaseExpr RealValRepr x''
           _ -> fail (unlines [unwords ["Invalid fpext:", show op, show x, show outty], showI])


intop :: (1 <= w)
      => L.ArithOp
      -> NatRepr w
      -> Expr LLVM s (BVType w)
      -> Expr LLVM s (BVType w)
      -> LLVMGenerator h s wptr ret (Expr LLVM s (BVType w))
intop op w a b =
      case op of
             L.Add nuw nsw -> do
                let nuwCond expr
                     | nuw = return $ App $ AddSideCondition (BaseBVRepr w)
                                (notExpr (App (BVCarry w a b)))
                                "unsigned overflow on addition"
                                expr
                     | otherwise = return expr

                let nswCond expr
                     | nsw = return $ App $ AddSideCondition (BaseBVRepr w)
                                (notExpr (App (BVSCarry w a b)))
                                "signed overflow on addition"
                                expr
                     | otherwise = return expr

                nuwCond =<< nswCond (App (BVAdd w a b))

             L.Sub nuw nsw -> do
                let nuwCond expr
                     | nuw = return $ App $ AddSideCondition (BaseBVRepr w)
                                (notExpr (App (BVUlt w a b)))
                                "unsigned overflow on subtraction"
                                expr
                     | otherwise = return expr

                let nusCond expr
                     | nsw = return $ App $ AddSideCondition (BaseBVRepr w)
                                (notExpr (App (BVSBorrow w a b)))
                                "signed overflow on subtraction"
                                expr
                     | otherwise = return expr

                nuwCond =<< nusCond (App (BVSub w a b))

             L.Mul nuw nsw -> do
                let w' = addNat w w
                Just LeqProof <- return $ isPosNat w'
                Just LeqProof <- return $ testLeq (incNat w) w'

                prod <- AtomExpr <$> mkAtom (App (BVMul w a b))
                let nuwCond expr
                     | nuw = do
                         az <- AtomExpr <$> mkAtom (App (BVZext w' w a))
                         bz <- AtomExpr <$> mkAtom (App (BVZext w' w b))
                         wideprod <- AtomExpr <$> mkAtom (App (BVMul w' az bz))
                         prodz <- AtomExpr <$> mkAtom (App (BVZext w' w prod))
                         return $ App $ AddSideCondition (BaseBVRepr w)
                                (App (BVEq w' wideprod prodz))
                                "unsigned overflow on multiplication"
                                expr
                     | otherwise = return expr

                let nswCond expr
                     | nsw = do
                         as <- AtomExpr <$> mkAtom (App (BVSext w' w a))
                         bs <- AtomExpr <$> mkAtom (App (BVSext w' w b))
                         wideprod <- AtomExpr <$> mkAtom (App (BVMul w' as bs))
                         prods <- AtomExpr <$> mkAtom (App (BVSext w' w prod))
                         return $ App $ AddSideCondition (BaseBVRepr w)
                                (App (BVEq w' wideprod prods))
                                "signed overflow on multiplication"
                                expr
                     | otherwise = return expr

                nuwCond =<< nswCond prod

             L.UDiv exact -> do
                let z = App (BVLit w 0)
                assertExpr (notExpr (App (BVEq w z b)))
                           (litExpr "unsigned division-by-0")

                q <- AtomExpr <$> mkAtom (App (BVUdiv w a b))

                let exactCond expr
                     | exact = do
                         m <- AtomExpr <$> mkAtom (App (BVMul w q b))
                         return $ App $ AddSideCondition (BaseBVRepr w)
                                (App (BVEq w a m))
                                "inexact result of unsigned division"
                                expr
                     | otherwise = return expr

                exactCond q

             L.SDiv exact
               | Just LeqProof <- isPosNat w -> do
                  let z      = App (BVLit w 0)
                  let neg1   = App (BVLit w (-1))
                  let minInt = App (BVLit w (minSigned w))
                  assertExpr (notExpr (App (BVEq w z b)))
                             (litExpr "signed division-by-0")
                  assertExpr (notExpr ((App (BVEq w neg1 b))
                                       .&&
                                       (App (BVEq w minInt a)) ))
                             (litExpr "signed division overflow (yes, really)")

                  q <- AtomExpr <$> mkAtom (App (BVSdiv w a b))

                  let exactCond expr
                       | exact = do
                           m <- AtomExpr <$> mkAtom (App (BVMul w q b))
                           return $ App $ AddSideCondition (BaseBVRepr w)
                                  (App (BVEq w a m))
                                  "inexact result of signed division"
                                  expr
                       | otherwise = return expr

                  exactCond q

               | otherwise -> fail "cannot take the signed quotient of a 0-width bitvector"

             L.URem -> do
                  let z = App (BVLit w 0)
                  assertExpr (notExpr (App (BVEq w z b)))
                             (litExpr "unsigned division-by-0 in urem")
                  return $ App (BVUrem w a b)

             L.SRem
               | Just LeqProof <- isPosNat w -> do
                  let z      = App (BVLit w 0)
                  let neg1   = App (BVLit w (-1))
                  let minInt = App (BVLit w (minSigned w))
                  assertExpr (notExpr (App (BVEq w z b)))
                             (litExpr "signed division-by-0 in srem")
                  assertExpr (notExpr ((App (BVEq w neg1 b))
                                       .&&
                                       (App (BVEq w minInt a)) ))
                             (litExpr "signed division overflow in srem (yes, really)")

                  return $ App (BVSrem w a b)

               | otherwise -> fail "cannot take the signed remainder of a 0-width bitvector"

             _ -> fail $ unwords ["unsupported integer arith operation", show op]

caseptr
  :: (1 <= w)
  => NatRepr w
  -> TypeRepr a
  -> (Expr LLVM s (BVType w) ->
      LLVMGenerator h s wptr ret (Expr LLVM s a))
  -> (Expr LLVM s NatType -> Expr LLVM s (BVType w) ->
      LLVMGenerator h s wptr ret (Expr LLVM s a))
  -> Expr LLVM s (LLVMPointerType w)
  -> LLVMGenerator h s wptr ret (Expr LLVM s a)

caseptr w tpr bvCase ptrCase x =
  case x of
    PointerExpr _ blk off ->
      case asApp blk of
        Just (NatLit 0) -> bvCase off
        Just (NatLit _) -> ptrCase blk off
        _               -> ptrSwitch blk off

    _ -> do a_x <- forceEvaluation (app (UnrollRecursive knownRepr (Ctx.Empty :> BVRepr w) x))
            blk <- forceEvaluation (app (GetStruct a_x (Ctx.natIndex @0) NatRepr))
            off <- forceEvaluation (app (GetStruct a_x (Ctx.natIndex @1) (BVRepr w)))
            ptrSwitch blk off
  where
  ptrSwitch blk off =
    do cond <- mkAtom (blk .== litExpr 0)
       endNow $ \c ->
         do bv_label  <- newLabel
            ptr_label <- newLabel
            c_label   <- newLambdaLabel' tpr
            endCurrentBlock (Br cond bv_label ptr_label)

            defineBlock bv_label  (bvCase off >>= jumpToLambda c_label)
            defineBlock ptr_label (ptrCase blk off >>= jumpToLambda c_label)
            resume c_label c

intcmp :: (1 <= w)
    => NatRepr w
    -> L.ICmpOp
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s (BVType w)
    -> Expr LLVM s BoolType
intcmp w op a b =
   case op of
      L.Ieq  -> App (BVEq w a b)
      L.Ine  -> App (Not (App (BVEq w a b)))
      L.Iult -> App (BVUlt w a b)
      L.Iule -> App (BVUle w a b)
      L.Iugt -> App (BVUlt w b a)
      L.Iuge -> App (BVUle w b a)
      L.Islt -> App (BVSlt w a b)
      L.Isle -> App (BVSle w a b)
      L.Isgt -> App (BVSlt w b a)
      L.Isge -> App (BVSle w b a)

pointerCmp
   :: L.ICmpOp
   -> Expr LLVM s (LLVMPointerType wptr)
   -> Expr LLVM s (LLVMPointerType wptr)
   -> LLVMGenerator h s wptr ret (Expr LLVM s BoolType)
pointerCmp op x y =
  caseptr PtrWidth knownRepr
    (\x_bv ->
      caseptr PtrWidth knownRepr
        (\y_bv   -> return $ intcmp PtrWidth op x_bv y_bv)
        (\_ _ -> ptr_bv_compare x_bv y)
        y)
    (\_ _ ->
      caseptr PtrWidth knownRepr
        (\y_bv   -> ptr_bv_compare y_bv x)
        (\_ _    -> ptrOp)
        y)
    x
 where

  -- Special case: a pointer can be compared for equality with an integer, as long as
  -- that integer is 0, representing the null pointer.
  ptr_bv_compare bv ptr =
    do assertExpr (App (BVEq PtrWidth bv (App (BVLit PtrWidth 0))))
                  "Attempted to compare a pointer to a non-0 integer value"
       case op of
         L.Ieq  -> do
            res <- callIsNull PtrWidth ptr
            return res
         L.Ine  -> do
            res <- callIsNull PtrWidth ptr
            return (App (Not res))
         _ -> reportError $ litExpr $ Text.pack $ unwords ["arithmetic comparison on incompatible values", show op, show x, show y]

  ptrOp =
    do pEq <- litExpr . llvmPtrEq . memModelOps . llvmContext <$> get
       pLe <- litExpr . llvmPtrLe . memModelOps . llvmContext <$> get
       memVar <- llvmMemVar . memModelOps . llvmContext <$> get
       mem <- readGlobal memVar
       case op of
         L.Ieq -> do
           isEq <- call pEq (Ctx.Empty :> mem :> x :> y)
           return $ isEq
         L.Ine -> do
           isEq <- call pEq (Ctx.Empty :> mem :> x :> y)
           return $ App (Not isEq)
         L.Iule -> do
           isLe <- call pLe (Ctx.Empty :> mem :> x :> y)
           return $ isLe
         L.Iult -> do
           isGe <- call pLe (Ctx.Empty :> mem :> y :> x)
           return $ App (Not isGe)
         L.Iuge -> do
           isGe <- call pLe (Ctx.Empty :> mem :> y :> x)
           return $ isGe
         L.Iugt -> do
           isLe <- call pLe (Ctx.Empty :> mem :> x :> y)
           return $ App (Not isLe)
         _ -> reportError $ litExpr $ Text.pack $ unwords ["signed comparison on pointer values", show op, show x, show y]

pointerOp
   :: L.ArithOp
   -> Expr LLVM s (LLVMPointerType wptr)
   -> Expr LLVM s (LLVMPointerType wptr)
   -> LLVMGenerator h s wptr ret (Expr LLVM s (LLVMPointerType wptr))
pointerOp op x y =
  caseptr PtrWidth PtrRepr
    (\x_bv  ->
      caseptr PtrWidth PtrRepr
        (\y_bv  -> BitvectorAsPointerExpr PtrWidth <$> intop op PtrWidth x_bv y_bv)
        (\_ _   -> bv_ptr_op x_bv)
        y)
    (\_ _ ->
      caseptr PtrWidth PtrRepr
        (\y_bv  -> ptr_bv_op y_bv)
        (\_ _   -> ptr_ptr_op)
      y)
    x
 where
  ptr_bv_op y_bv =
    case op of
      L.Add _ _ ->
           callPtrAddOffset x y_bv
      L.Sub _ _ ->
        do let off = App (BVSub PtrWidth (App $ BVLit PtrWidth 0) y_bv)
           callPtrAddOffset x off
      _ -> err

  bv_ptr_op x_bv =
    case op of
      L.Add _ _ -> callPtrAddOffset y x_bv
      _ -> err

  ptr_ptr_op =
    case op of
      L.Sub _ _ -> BitvectorAsPointerExpr PtrWidth <$> callPtrSubtract x y
      _ -> err

  err = reportError $ litExpr $ Text.pack $ unwords ["Invalid pointer operation", show op, show x, show y]

-- | Do the heavy lifting of translating LLVM instructions to crucible code.
generateInstr :: forall h s wptr ret
         . TypeRepr ret     -- ^ Type of the function return value
        -> L.BlockLabel     -- ^ The label of the current LLVM basic block
        -> L.Instr          -- ^ The instruction to translate
        -> (LLVMExpr s -> LLVMGenerator h s wptr ret ())
                            -- ^ A continuation to assign the produced value of this instruction to a register
        -> LLVMGenerator h s wptr ret ()  -- ^ A continuation for translating the remaining statements in this function.
                                   --   Straightline instructions should enter this continuation,
                                   --   but block-terminating instructions should not.
        -> LLVMGenerator h s wptr ret ()
generateInstr retType lab instr assign_f k =
  case instr of
    -- skip phi instructions, they are handled in definePhiBlock
    L.Phi _ _ -> k
    L.Comment _ -> k
    L.Unreachable -> reportError "LLVM unreachable code"

    L.ExtractValue x is -> do
        x' <- transTypedValue x
        v <- extractValue x' is
        assign_f v
        k

    L.InsertValue x v is -> do
        x' <- transTypedValue x
        v' <- transTypedValue v
        y <- insertValue x' v' is
        assign_f y
        k

    L.ExtractElt x i ->
        case x of
          L.Typed (L.Vector n ty) x' -> do
            ty' <- liftMemType ty
            x'' <- transValue (VecType (fromIntegral n) ty') x'
            i'  <- transValue (IntType 64) i               -- FIXME? this is a bit of a hack, since the llvm-pretty
                                                           -- AST doesn't track the size of the index value
            y <- extractElt instr ty' (fromIntegral n) x'' i'
            assign_f y
            k

          _ -> fail $ unwords ["expected vector type in extractelement instruction:", show x]

    L.InsertElt x v i ->
        case x of
          L.Typed (L.Vector n ty) x' -> do
            ty' <- liftMemType ty
            x'' <- transValue (VecType (fromIntegral n) ty') x'
            v'  <- transTypedValue v
            i'  <- transValue (IntType 64) i                -- FIXME? this is a bit of a hack, since the llvm-pretty
                                                            -- AST doesn't track the size of the index value
            y <- insertElt instr ty' (fromIntegral n) x'' v' i'
            assign_f y
            k

          _ -> fail $ unwords ["expected vector type in insertelement instruction:", show x]

    L.ShuffleVector _ _ _ ->
      reportError "FIXME shuffleVector not implemented"

    L.LandingPad _ _ _ _ ->
      reportError "FIXME landingPad not implemented"

    L.Alloca tp num _align -> do
      -- ?? FIXME assert that the alignment value is appropriate...
      tp' <- liftMemType tp
      let dl = TyCtx.llvmDataLayout ?lc
      let tp_sz = memTypeSize dl tp'
      let tp_sz' = app $ BVLit PtrWidth $ G.bytesToInteger tp_sz
      sz <- case num of
               Nothing -> return $ tp_sz'
               Just num' -> do
                  n <- transTypedValue num'
                  case n of
                     ZeroExpr _ -> return $ app $ BVLit PtrWidth 0
                     BaseExpr (LLVMPointerRepr w) x
                        | Just Refl <- testEquality w PtrWidth ->
                            do x' <- pointerAsBitvectorExpr w x
                               return $ app $ BVMul PtrWidth x' tp_sz'
                     _ -> fail $ "Invalid alloca argument: " ++ show num
      p <- callAlloca sz
      assign_f (BaseExpr (LLVMPointerRepr PtrWidth) p)
      k

    L.Load ptr _atomic align -> do
      tp'  <- liftMemType (L.typedType ptr)
      ptr' <- transValue tp' (L.typedValue ptr)
      case tp' of
        PtrType (MemType resTy) ->
          llvmTypeAsRepr resTy $ \expectTy -> do
            let a0 = memTypeAlign (TyCtx.llvmDataLayout ?lc) resTy
            let align' = fromMaybe a0 (toAlignment . G.toBytes =<< align)
            res <- callLoad resTy expectTy ptr' align'
            assign_f res
            k
        _ ->
          fail $ unwords ["Invalid argument type on load", show ptr]

    L.Store v ptr _align -> do
      -- ?? FIXME assert that the alignment value is appropriate...
      tp'  <- liftMemType (L.typedType ptr)
      ptr' <- transValue tp' (L.typedValue ptr)
      vTp <- liftMemType (L.typedType v)
      v' <- transValue vTp (L.typedValue v)
      unless (tp' == PtrType (MemType vTp))
           (fail "Pointer type does not match value type in store instruction")
      callStore vTp ptr' v'
      k

    -- NB We treat every GEP as though it has the "inbounds" flag set;
    --    thus, the calculation of out-of-bounds pointers results in
    --    a runtime error.
    L.GEP _inbounds base elts -> do
      base' <- transTypedValue base
      elts' <- mapM transTypedValue elts
      typ <- liftMemType (L.typedType base)
      p <- calcGEP typ base' elts'
      assign_f (BaseExpr (LLVMPointerRepr PtrWidth) p)
      k

    L.Conv op x outty -> do
      v <- translateConversion (Just instr) op x outty
      assign_f v
      k

    L.Call _tailCall (L.PtrTo fnTy) fn args ->
        callFunctionWithCont fnTy fn args assign_f k

    L.Invoke fnTy fn args normLabel _unwindLabel -> do
        callFunctionWithCont fnTy fn args assign_f $ definePhiBlock lab normLabel

    L.Bit op x y -> do
           let bitop :: (1 <= w)
                     => NatRepr w
                     -> Expr LLVM s (BVType w)
                     -> Expr LLVM s (BVType w)
                     -> LLVMGenerator h s wptr ret (Expr LLVM s (BVType w))
               bitop w a b =
                     case op of
                         L.And -> return $ App (BVAnd w a b)
                         L.Or  -> return $ App (BVOr w a b)
                         L.Xor -> return $ App (BVXor w a b)

                         L.Shl nuw nsw -> do
                           let wlit = App (BVLit w (natValue w))
                           assertExpr (App (BVUlt w b wlit))
                                      (litExpr "shift amount too large in shl")

                           res <- AtomExpr <$> mkAtom (App (BVShl w a b))

                           let nuwCond expr
                                | nuw = do
                                    m <- AtomExpr <$> mkAtom (App (BVLshr w res b))
                                    return $ App $ AddSideCondition (BaseBVRepr w)
                                       (App (BVEq w a m))
                                       "unsigned overflow on shl"
                                       expr
                                | otherwise = return expr

                           let nswCond expr
                                | nsw = do
                                    m <- AtomExpr <$> mkAtom (App (BVAshr w res b))
                                    return $ App $ AddSideCondition (BaseBVRepr w)
                                       (App (BVEq w a m))
                                       "signed overflow on shl"
                                       expr
                                | otherwise = return expr

                           nuwCond =<< nswCond =<< return res

                         L.Lshr exact -> do
                           let wlit = App (BVLit w (natValue w))
                           assertExpr (App (BVUlt w b wlit))
                                      (litExpr "shift amount too large in lshr")

                           res <- AtomExpr <$> mkAtom (App (BVLshr w a b))

                           let exactCond expr
                                | exact = do
                                    m <- AtomExpr <$> mkAtom (App (BVShl w res b))
                                    return $ App $ AddSideCondition (BaseBVRepr w)
                                       (App (BVEq w a m))
                                       "inexact logical right shift"
                                       expr
                                | otherwise = return expr

                           exactCond res

                         L.Ashr exact
                           | Just LeqProof <- isPosNat w -> do
                              let wlit = App (BVLit w (natValue w))
                              assertExpr (App (BVUlt w b wlit))
                                         (litExpr "shift amount too large in ashr")

                              res <- AtomExpr <$> mkAtom (App (BVAshr w a b))

                              let exactCond expr
                                   | exact = do
                                       m <- AtomExpr <$> mkAtom (App (BVShl w res b))
                                       return $ App $ AddSideCondition (BaseBVRepr w)
                                          (App (BVEq w a m))
                                          "inexact arithmetic right shift"
                                          expr
                                   | otherwise = return expr

                              exactCond res

                           | otherwise -> fail "cannot arithmetic right shift a 0-width integer"

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar (LLVMPointerRepr w) x'',
              Scalar (LLVMPointerRepr w') y'')
               | Just Refl <- testEquality w w'
               , Just LeqProof <- isPosNat w -> do
                  xbv <- pointerAsBitvectorExpr w x''
                  ybv <- pointerAsBitvectorExpr w y''
                  ex  <- bitop w xbv ybv
                  assign_f (BaseExpr (LLVMPointerRepr w) (BitvectorAsPointerExpr w ex))
                  k

             _ -> fail $ unwords ["bitwise operation on unsupported values", show x, show y]

    L.Arith op x y -> do
           let fop :: Expr LLVM s RealValType
                   -> Expr LLVM s RealValType
                   -> LLVMGenerator h s wptr ret (Expr LLVM s RealValType)
               fop a b =
                     case op of
                        L.FAdd -> do
                          return $ App (RealAdd a b)
                        L.FSub -> do
                          return $ App (RealSub a b)
                        L.FMul -> do
                          return $ App (RealMul a b)
                        L.FDiv -> do
                          return $ App (RealDiv a b)
                        L.FRem -> do
                          return $ App (RealMod a b)
                        _ -> reportError $ fromString $ unwords [ "unsupported floating-point arith operation"
                                                                , show op, show x, show y
                                                                ]

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar ty@(LLVMPointerRepr w)  x'',
              Scalar    (LLVMPointerRepr w') y'')
               | Just Refl <- testEquality w PtrWidth
               , Just Refl <- testEquality w w' ->
                 do z <- pointerOp op x'' y''
                    assign_f (BaseExpr ty z)
                    k

               | Just Refl <- testEquality w w' ->
                 do xbv <- pointerAsBitvectorExpr w x''
                    ybv <- pointerAsBitvectorExpr w y''
                    z   <- intop op w xbv ybv
                    assign_f (BaseExpr (LLVMPointerRepr w) (BitvectorAsPointerExpr w z))
                    k

             (Scalar RealValRepr x'',
              Scalar RealValRepr y'') -> do
                 ex <- fop x'' y''
                 assign_f (BaseExpr RealValRepr ex)
                 k

             _ -> reportError $ fromString $ unwords ["arithmetic operation on unsupported values", show x, show y]

    L.FCmp op x y -> do
           let cmpf :: Expr LLVM s RealValType
                    -> Expr LLVM s RealValType
                    -> Expr LLVM s BoolType
               cmpf a b =
                  -- We assume that values are never NaN, so the ordered and unordered
                  -- operations are the same.
                  case op of
                    L.Ftrue  -> App (BoolLit True)
                    L.Ffalse -> App (BoolLit False)
                    L.Foeq   -> App (RealEq a b)
                    L.Fueq   -> App (RealEq a b)
                    L.Fone   -> App $ Not $ App (RealEq a b)
                    L.Fune   -> App $ Not $ App (RealEq a b)
                    L.Folt   -> App (RealLt a b)
                    L.Fult   -> App (RealLt a b)
                    L.Fogt   -> App (RealLt b a)
                    L.Fugt   -> App (RealLt b a)
                    L.Fole   -> App $ Not $ App (RealLt b a)
                    L.Fule   -> App $ Not $ App (RealLt b a)
                    L.Foge   -> App $ Not $ App (RealLt a b)
                    L.Fuge   -> App $ Not $ App (RealLt a b)
                    L.Ford   -> App (BoolLit True)  -- True if a <> QNAN and b <> QNAN
                    L.Funo   -> App (BoolLit False) -- True if a == QNNA or b == QNAN

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar RealValRepr x'',
              Scalar RealValRepr y'') -> do
                assign_f (BaseExpr (LLVMPointerRepr (knownNat :: NatRepr 1))
                                   (BitvectorAsPointerExpr knownNat (App (BoolToBV knownNat (cmpf  x'' y'')))))
                k

             _ -> fail $ unwords ["Floating point comparison on incompatible values", show x, show y]

    L.ICmp op x y -> do
           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar (LLVMPointerRepr w) x'', Scalar (LLVMPointerRepr w') y'')
                | Just Refl <- testEquality w w'
                , Just Refl <- testEquality w PtrWidth
                -> do b <- pointerCmp op x'' y''
                      assign_f (BaseExpr (LLVMPointerRepr (knownNat :: NatRepr 1))
                                         (BitvectorAsPointerExpr knownNat (App (BoolToBV knownNat b))))
                      k
                | Just Refl <- testEquality w w'
                -> do xbv <- pointerAsBitvectorExpr w x''
                      ybv <- pointerAsBitvectorExpr w y''
                      let b = intcmp w op xbv ybv
                      assign_f (BaseExpr (LLVMPointerRepr (knownNat :: NatRepr 1))
                                         (BitvectorAsPointerExpr knownNat (App (BoolToBV knownNat b))))
                      k

             _ -> fail $ unwords ["arithmetic comparison on incompatible values", show x, show y]

    -- FIXME? reimplement the select operation using expression if/then/else rather than branching...
    L.Select c x y -> do
         c' <- transTypedValue c
         x' <- transTypedValue x
         y' <- transTypedValue (L.Typed (L.typedType x) y)
         e' <- case asScalar c' of
                 Scalar (LLVMPointerRepr w) e -> notExpr <$> callIsNull w e
                 _ -> fail "expected boolean condition on select"

         e_a <- mkAtom e'
         endNow $ \cont -> do
             l1 <- newLabel
             l2 <- newLabel
             c_lab <- newLabel

             endCurrentBlock (Br e_a l1 l2)
             defineBlock l1 (assign_f x' >> jump c_lab)
             defineBlock l2 (assign_f y' >> jump c_lab)
             resume_ c_lab cont
         k

    L.Jump l' -> definePhiBlock lab l'

    L.Br v l1 l2 -> do
        v' <- transTypedValue v
        e' <- case asScalar v' of
                 Scalar (LLVMPointerRepr w) e -> notExpr <$> callIsNull w e
                 _ -> fail "expected boolean condition on branch"

        a' <- mkAtom e'
        endNow $ \_ -> do
          phi1 <- newLabel
          phi2 <- newLabel
          endCurrentBlock (Br a' phi1 phi2)

          defineBlock phi1 (definePhiBlock lab l1)
          defineBlock phi2 (definePhiBlock lab l2)

    L.Switch x def branches -> do
        x' <- transTypedValue x
        case asScalar x' of
          Scalar (LLVMPointerRepr w) x'' ->
            do bv <- pointerAsBitvectorExpr w x''
               buildSwitch w bv lab def branches
          _ -> fail $ unwords ["expected integer value in switch", showInstr instr]

    L.Ret v -> do v' <- transTypedValue v
                  let ?err = fail
                  unpackOne v' $ \retType' ex ->
                     case testEquality retType retType' of
                        Just Refl -> do
                           callPopFrame
                           returnFromFunction ex
                        Nothing -> fail $ unwords ["unexpected return type", show retType, show retType']

    L.RetVoid -> case testEquality retType UnitRepr of
                    Just Refl -> do
                       callPopFrame
                       returnFromFunction (App EmptyApp)
                    Nothing -> fail $ unwords ["tried to void return from non-void function", show retType]

    _ -> reportError $ App $ TextLit $ Text.pack $ unwords ["unsupported instruction", showInstr instr]

showInstr :: L.Instr -> String
showInstr i = show (L.ppLLVM38 (L.ppInstr i))

callFunctionWithCont :: forall h s wptr ret.
                        L.Type -> L.Value -> [L.Typed L.Value]
                     -> (LLVMExpr s -> LLVMGenerator h s wptr ret ())
                     -> LLVMGenerator h s wptr ret ()
                     -> LLVMGenerator h s wptr ret ()
callFunctionWithCont fnTy@(L.FunTy lretTy largTys varargs) fn args assign_f k
     -- Skip calls to debugging intrinsics.  We might want to support these in some way
     -- in the future.  However, they take metadata values as arguments, which
     -- would require some work to support.
     | L.ValSymbol nm <- fn
     , nm `elem` [ "llvm.dbg.declare"
                 , "llvm.dbg.value"
                 ] = k

     -- For varargs functions, any arguments beyond the ones found in the function
     -- declaration are gathered into a vector of 'ANY' type, which is then passed
     -- as an additional final argument to the underlying Crucible function.  The
     -- called function is expected to know the types of these additional arguments,
     -- which it can unpack from the ANY values when it knows those types.
     | varargs = do
           fnTy' <- liftMemType (L.PtrTo fnTy)
           retTy' <- liftRetType lretTy
           fn' <- transValue fnTy' fn
           args' <- mapM transTypedValue args
           let ?err = fail
           let (mainArgs, varArgs) = splitAt (length largTys) args'
           varArgs' <- unpackVarArgs varArgs
           unpackArgs mainArgs $ \argTypes mainArgs' ->
             case asScalar fn' of
                Scalar PtrRepr ptr ->
                  do memVar <- llvmMemVar . memModelOps . llvmContext <$> get
                     memLoadHandle <- litExpr . llvmMemLoadHandle . memModelOps . llvmContext <$> get
                     mem <- readGlobal memVar
                     v <- call memLoadHandle (Ctx.Empty :> mem :> ptr)
                     llvmRetTypeAsRepr retTy' $ \retTy ->
                       do let expectTy = FunctionHandleRepr (argTypes :> varArgsRepr) retTy
                          let msg = litExpr (Text.pack ("Expected function of type " ++ show expectTy))
                          let v' = app $ FromJustValue expectTy (app $ UnpackAny expectTy v) msg
                          ret <- call v' (mainArgs' :> varArgs')
                          assign_f (BaseExpr retTy ret)
                          k
                _ -> fail $ unwords ["unsupported function value", show fn]

     -- Ordinary (non varargs) function call
     | otherwise = do
           fnTy' <- liftMemType (L.PtrTo fnTy)
           retTy' <- liftRetType lretTy
           fn' <- transValue fnTy' fn
           args' <- mapM transTypedValue args
           let ?err = fail
           unpackArgs args' $ \argTypes args'' ->
              case asScalar fn' of
                Scalar PtrRepr ptr ->
                  do memVar <- llvmMemVar . memModelOps . llvmContext <$> get
                     memLoadHandle <- litExpr . llvmMemLoadHandle . memModelOps . llvmContext <$> get
                     mem <- readGlobal memVar
                     v <- call memLoadHandle (Ctx.Empty :> mem :> ptr)
                     llvmRetTypeAsRepr retTy' $ \retTy ->
                       do let expectTy = FunctionHandleRepr argTypes retTy
                          let msg = litExpr (Text.pack ("Expected function of type " ++ show expectTy))
                          let v' = app $ FromJustValue expectTy (app $ UnpackAny expectTy v) msg
                          ret <- call v' args''
                          assign_f (BaseExpr retTy ret)
                          k
                _ -> fail $ unwords ["unsupported function value", show fn]
callFunctionWithCont fnTy _fn _args _assign_f _k =
    reportError $ App $ TextLit $ Text.pack $ unwords ["unsupported function type", show fnTy]

-- | Build a switch statement by decomposing it into a linear sequence of branches.
--   FIXME? this could be more efficient if we sort the list and do binary search instead...
buildSwitch :: (1 <= w)
            => NatRepr w
            -> Expr LLVM s (BVType w) -- ^ The expression to switch on
            -> L.BlockLabel        -- ^ The label of the current basic block
            -> L.BlockLabel        -- ^ The label of the default basic block if no other branch applies
            -> [(Integer, L.BlockLabel)] -- ^ The switch labels
            -> LLVMGenerator h s wptr ret ()
buildSwitch _ _  curr_lab def [] =
   definePhiBlock curr_lab def
buildSwitch w ex curr_lab def ((i,l):bs) = do
   let test = App $ BVEq w ex $ App $ BVLit w i
   test_a <- mkAtom test
   endNow $ \_ -> do
     t_id <- newLabel
     f_id <- newLabel
     endCurrentBlock $! Br test_a t_id f_id
     defineBlock t_id (definePhiBlock curr_lab l)
     defineBlock f_id (buildSwitch w ex curr_lab def bs)

-- | Generate crucible code for each LLVM statement in turn.
generateStmts
        :: TypeRepr ret
        -> L.BlockLabel
        -> [L.Stmt]
        -> LLVMGenerator h s wptr ret ()
generateStmts retType lab stmts = go (processDbgDeclare stmts)
 where go [] = fail "LLVM basic block ended without a terminating instruction"
       go (x:xs) =
         case x of
           -- a result statement assigns the result of the instruction into a register
           L.Result ident instr md -> do
                 setLocation md
                 generateInstr retType lab instr (assignLLVMReg ident) (go xs)

           -- an effect statement simply executes the instruction for its effects and discards the result
           L.Effect instr md -> do
                 setLocation md
                 generateInstr retType lab instr (\_ -> return ()) (go xs)

-- | Search for calls to intrinsic 'llvm.dbg.declare' and copy the
-- metadata onto the corresponding 'alloca' statement.  Also copy
-- metadata backwards from 'bitcast' statements toward 'alloca'.
processDbgDeclare :: [L.Stmt] -> [L.Stmt]
processDbgDeclare = snd . go
  where
    go :: [L.Stmt] -> (Map L.Ident [(String, L.ValMd)] , [L.Stmt])
    go [] = (Map.empty, [])
    go (stmt : stmts) =
      let (m, stmts') = go stmts in
      case stmt of
        L.Result x instr@L.Alloca{} md ->
          case Map.lookup x m of
            Just md' -> (m, L.Result x instr (md' ++ md) : stmts')
            Nothing -> (m, stmt : stmts')
              --error $ "Identifier not found: " ++ show x ++ "\nPossible identifiers: " ++ show (Map.keys m)

        L.Result x (L.Conv L.BitCast (L.Typed _ (L.ValIdent y)) _) md ->
          let md' = md ++ fromMaybe [] (Map.lookup x m)
              m'  = Map.alter (Just . maybe md' (md'++)) y m
           in (m', stmt:stmts)

        L.Effect (L.Call _ _ (L.ValSymbol "llvm.dbg.declare") (L.Typed _ (L.ValMd (L.ValMdValue (L.Typed _ (L.ValIdent x)))) : _)) md ->
          (Map.insert x md m, stmt : stmts')

        -- This is needlessly fragile. Let's just ignore debug declarations we don't understand.
        -- L.Effect (L.Call _ _ (L.ValSymbol "llvm.dbg.declare") args) md ->
        --  error $ "Ill-formed arguments to llvm.dbg.declare: " ++ show (args, md)

        _ -> (m, stmt : stmts')

setLocation
  :: [(String,L.ValMd)]
  -> LLVMGenerator h s wptr ret ()
setLocation [] = return ()
setLocation (("dbg",L.ValMdLoc dl):_) = do
   let ln   = fromIntegral $ L.dlLine dl
       col  = fromIntegral $ L.dlCol dl
       file = Text.pack $ findFile $ L.dlScope dl
    in setPosition (SourcePos file ln col)
setLocation (("dbg",L.ValMdDebugInfo (L.DebugInfoSubprogram subp)) :_)
  | Just file' <- L.dispFile subp
  = do let ln = fromIntegral $ L.dispLine subp
       let file = Text.pack $ findFile file'
       setPosition (SourcePos file ln 0)
setLocation (_:xs) = setLocation xs

findFile :: (?lc :: TyCtx.LLVMContext) => L.ValMd -> String
findFile (L.ValMdRef x) =
  case TyCtx.lookupMetadata x of
    Just (L.ValMdNode (_:Just (L.ValMdRef y):_)) ->
      case TyCtx.lookupMetadata y of
        Just (L.ValMdNode [Just (L.ValMdString fname), Just (L.ValMdString _fpath)]) -> fname
        _ -> ""
    Just (L.ValMdDebugInfo di) ->
      case di of
        L.DebugInfoLexicalBlock (L.dilbFile -> Just (L.ValMdDebugInfo (L.DebugInfoFile dif))) ->
          L.difFilename dif
        L.DebugInfoSubprogram (L.dispFile -> Just (L.ValMdDebugInfo (L.DebugInfoFile dif))) ->
          L.difFilename dif
        _ -> ""
    _ -> ""
findFile _ = ""

-- | Lookup the block info for the given LLVM block and then define a new crucible block
--   by translating the given LLVM statements.
defineLLVMBlock
        :: TypeRepr ret
        -> Map L.BlockLabel (LLVMBlockInfo s)
        -> L.BasicBlock
        -> LLVMEnd h s wptr ret ()
defineLLVMBlock retType lm L.BasicBlock{ L.bbLabel = Just lab, L.bbStmts = stmts } = do
  case Map.lookup lab lm of
    Just bi -> defineBlock (block_label bi) (generateStmts retType lab stmts)
    Nothing -> fail $ unwords ["LLVM basic block not found in block info map", show lab]

defineLLVMBlock _ _ _ = fail "LLVM basic block has no label!"

-- | Do some initial preprocessing to find all the phi nodes in the program
--   and to preallocate all the crucible registers we will need based on the LLVM
--   types of all the LLVM registers.  Then translate each LLVM basic block in turn.
--
--   This step introduces a new dummy entry point that simply jumps to the LLVM entry
--   point.  It is inconvenient to avoid doing this when using the Generator interface.
genDefn :: L.Define
        -> TypeRepr ret
        -> LLVMGenerator h s wptr ret (Expr LLVM s ret)
genDefn defn retType =
  case L.defBody defn of
    [] -> fail "LLVM define with no blocks!"
    ( L.BasicBlock{ L.bbLabel = Nothing } : _ ) -> fail $ unwords ["entry block has no label"]
    ( L.BasicBlock{ L.bbLabel = Just entry_lab } : _ ) -> do
      callPushFrame
      setLocation $ Map.toList (L.defMetadata defn)
      endNow $ \_ -> do
        bim <- buildBlockInfoMap defn
        blockInfoMap .= bim

        im <- use identMap
        im' <- buildRegMap im defn
        identMap .= im'

        case Map.lookup entry_lab bim of
           Nothing -> fail $ unwords ["entry label not found in label map:", show entry_lab]
           Just entry_bi ->
              endCurrentBlock (Jump (block_label entry_bi))

        mapM_ (defineLLVMBlock retType bim) (L.defBody defn)

------------------------------------------------------------------------
-- transDefine
--
-- | Translate a single LLVM function definition into a crucible CFG.
transDefine :: forall h wptr.
               (HasPtrWidth wptr)
            => LLVMContext wptr
            -> L.Define
            -> ST h (L.Symbol, C.AnyCFG LLVM)
transDefine ctx d = do
  let sym = L.defName d
  let ?lc = ctx^.llvmTypeCtx
  case ctx^.symbolMap^.at sym of
    Nothing -> fail "internal error: Could not find symbol"
    Just (LLVMHandleInfo _ (h :: FnHandle args ret)) -> do
      let argTypes = handleArgTypes h
      let retType  = handleReturnType h
      let def :: FunctionDef LLVM h (LLVMState wptr) args ret
          def inputs = (s, f)
            where s = initialState d ctx argTypes inputs
                  f = genDefn d retType
      (SomeCFG g,[]) <- defineFunction InternalPos h def
      case toSSA g of
        C.SomeCFG g_ssa -> return (sym, C.AnyCFG g_ssa)

------------------------------------------------------------------------
-- initMemProc

genGlobalInit
            :: (L.Symbol, MemType, Maybe L.Value)
            -> LLVMGenerator h s wptr ret ()
genGlobalInit (_sym,_ty,Nothing) =
  return ()
genGlobalInit (sym,ty,Just v) = do
  ptr <- transValue ty (L.ValSymbol sym)
  v'  <- transValue ty v
  callStore ty ptr v'


initMemProc :: forall s wptr.
               HasPtrWidth wptr
            => HandleAllocator s
            -> LLVMContext wptr
            -> L.Module
            -> ST s (C.SomeCFG LLVM EmptyCtx UnitType)
initMemProc halloc ctx m = do
   let gs = L.modGlobals m
   let ?lc = ctx^.llvmTypeCtx
   h <- mkHandle halloc "_llvm_mem_init"
   gs_alloc <- mapM (\g -> do
                        ty <- liftMemType $ L.globalType g
                        return (L.globalSym g, ty, L.globalValue g))
                    gs
   let def :: FunctionDef LLVM s (LLVMState wptr) EmptyCtx UnitType
       def _inputs = (st, f)
              where st = LLVMState
                         { _identMap = Map.empty
                         , _blockInfoMap = Map.empty
                         , llvmContext = ctx
                         }
                    f = do mapM_ genGlobalInit gs_alloc
                           return (App EmptyApp)

   (SomeCFG g,[]) <- defineFunction InternalPos h def
   return $! toSSA g

------------------------------------------------------------------------
-- translateModule

-- | Insert a declaration into the symbol handleMap if a handle for that
--   symbol does not already exist.
insDeclareHandle :: HasPtrWidth wptr
                 => HandleAllocator s
                 -> LLVMContext wptr
                 -> L.Declare
                 -> ST s (LLVMContext wptr)
insDeclareHandle halloc ctx decl = do
   let s@(L.Symbol sbl) = L.decName decl
   case Map.lookup s (ctx^.symbolMap) of
     Just (LLVMHandleInfo _decl' _) ->
       -- FIXME check that decl and decl' are compatible...
       return ctx
     Nothing -> do
       let ?lc = ctx^.llvmTypeCtx
       args <- traverse liftMemType (L.decArgs decl)
       ret  <- liftRetType (L.decRetType decl)
       let fn_name = functionNameFromText $ Text.pack sbl
       let decl' = FunDecl
                   { fdRetType  = ret
                   , fdArgTypes = args
                   , fdVarArgs  = L.decVarArgs decl
                   }
       llvmDeclToFunHandleRepr decl' $ \argTypes retType -> do
         h <- mkHandle' halloc fn_name argTypes retType
         let hinfo = LLVMHandleInfo decl h
         return (symbolMap %~ (Map.insert s hinfo) $ ctx)

-- | Translate a module into Crucible control-flow graphs.
-- Note: We may want to add a map from symbols to existing function handles
-- if we want to support dynamic loading.
translateModule :: HandleAllocator s -- ^ Generator for nonces.
                -> L.Module          -- ^ Module to translate
                -> ST s (Some LLVMContext, ModuleTranslation)
translateModule halloc m = do
  Some ctx0 <- mkLLVMContext halloc m
  llvmPtrWidth ctx0 $ \wptr -> withPtrWidth wptr $
    do -- Add handles for all functions declared in module.
       ctx <- foldM (insDeclareHandle halloc) ctx0 (allModuleDeclares m)
       -- Translate definitions
       pairs <- mapM (transDefine ctx) (L.modDefines m)
       -- Return result.
       initMem <- initMemProc halloc ctx m
       return (Some ctx, ModuleTranslation { cfgMap = Map.fromList pairs
                                           , initMemoryCFG = initMem
                                           })

-------------------------------------------------------------------------
-- initializeMemory

-- | Build the initial memory for an LLVM program.  Note, this process
-- allocates space for global variables, but does not set their
-- initial values.  Run the `initMemoryCFG` procedure of the
-- `ModuleTranslation` produced by `translateModule` to set
-- the values of global variables.
initializeMemory
   :: (IsSymInterface sym, HasPtrWidth wptr)
   => sym
   -> LLVMContext wptr
   -> L.Module
   -> IO (MemImpl sym)
initializeMemory sym llvm_ctx m = do
   -- Allocate function handles
   let handles = Map.assocs (_symbolMap llvm_ctx)
   mem0 <- emptyMem
   mem <- foldM (allocLLVMHandleInfo sym) mem0 handles
   -- Allocate global values
   let gs = L.modGlobals m
   let ?lc = llvm_ctx^.llvmTypeCtx
   let dl = TyCtx.llvmDataLayout ?lc
   gs_alloc <- mapM (\g -> do
                        ty <- liftMemType $ L.globalType g
                        let sz = memTypeSize dl ty
                        return (L.globalSym g, sz))
                    gs
   allocGlobals sym gs_alloc mem

allocLLVMHandleInfo :: (IsSymInterface sym, HasPtrWidth wptr)
                    => sym
                    -> MemImpl sym
                    -> (L.Symbol, LLVMHandleInfo)
                    -> IO (MemImpl sym)
allocLLVMHandleInfo sym mem (symbol@(L.Symbol sym_str), LLVMHandleInfo _ h) =
  do (ptr, mem') <- doMallocHandle sym G.GlobalAlloc sym_str mem (SomeFnHandle h)
     return (registerGlobal mem' symbol ptr)
