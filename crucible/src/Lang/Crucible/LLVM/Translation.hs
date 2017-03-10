-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation
-- Description      : This module performs the work of tranlating LLVM AST
--                    into a Cucible control-flow graph.
-- Copyright        : (c) Galois, Inc 2014-2015
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module translates an LLVM Module into a collection of Crucible
-- control-flow graphs, one per function.  The tricky parts of this translation
-- are 1) mapping LLVM types onto Crucible types in a sensible way and 2)
-- translating the phi-instructions of LLVM's SSA form.
--
-- The translation of the LLVM types themeselves is not so difficult;
-- however, navigating the fact that Crucible expressions are strongly
-- typed at the Haskell level, whereas the LLVM types are not makes for
-- some slightly strange programming idioms.  In particular, all the
-- functions that do the type translation are written in a polymorphic
-- continuation-passing style.
--
-- To handle the translation of phi-functions, we first perform a
-- pre-pass over all the LLVM basic blocks looking for phi-functions
-- and build a datastructure that tells us what assignments to make
-- when jumping from block l to block l'.  We then emit instructions
-- to make these assignements in a separate Crucible basic block (see
-- 'definePhiBlock').  Thus, the translated CFG will generally have
-- more basic blocks than the original LLVM.
--
-- Points of note:
--
--  * Immediate (i.e., not in memory) structs and packed structs are translated the same.
--  * Undefined values generate special Crucible expressions (e.g., BVUndef) to
--     represent arbitratry bitpatterns
--  * All floating point operations are abstracted into operations on the real numbers.
--     Thus, answers returned by solvers might not be bit-exact, and might not even be expressible
--     in the orignal floating-point representation.  Moreover, trying to directly
--     examine the bit-patterns of floating-point values will not work, and wierd bit-level
--     tricks on floating-point values will not work properly.  Additionally, NaN, +INF and -INF
--     are never generated, but instead assertions (e.g. about division by zero) will fail.
--
-- Some notes on undefined/posion values: (outcome of discussions between JHx and RWD)
--
-- Continue to add Crucible expressions for undefined values as
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
-- For poison values, our implementation strategy is to assert
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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.Translation
( ModuleTranslation(..)
, LLVMContext(..)
, LLVMHandleInfo(..)
, SymbolHandleMap
, symbolMap
, ModuleCFGMap
, translateModule
, llvmIntrinsicTypes
, llvmIntrinsics
, initalizeMemory
, LLVMInt
, toStorableType
) where


import Control.Monad.State.Strict
import Control.Lens hiding (op)
import Control.Monad.ST
import Data.Foldable (toList)
import Data.Int
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import Data.Parameterized.Some

import           Lang.Crucible.Core (AnyCFG(..))
import qualified Lang.Crucible.Core as C
import           Lang.Crucible.FunctionName
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Intrinsics
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Common as G

import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Generator
import           Lang.Crucible.Solver.Interface( IsSymInterface )
import           Lang.Crucible.SSAConversion( toSSA )
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types

type LLVMInt w = BVType w
type VarArgs   = VectorType AnyType

varArgsRepr :: TypeRepr VarArgs
varArgsRepr = VectorRepr AnyRepr

------------------------------------------------------------------------
-- LLVM AST utilities

declareFromDefine :: L.Define -> L.Declare
declareFromDefine d =
  L.Declare { L.decRetType = L.defRetType d
            , L.decName = L.defName d
            , L.decArgs = L.typedType <$> L.defArgs d
            , L.decVarArgs = L.defVarArgs d
            }

-- | Return all declarations derived from both external symbols and
-- internal definitions.
allModuleDeclares :: L.Module -> [L.Declare]
allModuleDeclares m = L.modDeclares m ++ def_decls
  where def_decls = declareFromDefine <$> L.modDefines m

------------------------------------------------------------------------
-- Translation results

type ModuleCFGMap = Map L.Symbol AnyCFG

-- | The result of translating an LLVM module into Crucible CFGs.
data ModuleTranslation
   = ModuleTranslation
      { cfgMap :: ModuleCFGMap
      , initMemoryCFG :: C.SomeCFG EmptyCtx UnitType
      }

-------------------------------------------------------------------------
-- LLVMExpr

-- | An intermediate form of LLVM expressions that retains some structure
--   that would otherwise be more difficult to retain if we translated directly
--   into crucible expressions.
data LLVMExpr s f where
   BaseExpr   :: TypeRepr tp -> f s tp -> LLVMExpr s f
   ZeroExpr   :: MemType -> LLVMExpr s f
   UndefExpr  :: MemType -> LLVMExpr s f
   VecExpr    :: MemType -> Seq (LLVMExpr s f) -> LLVMExpr s f
   StructExpr :: Seq (MemType, LLVMExpr s f) -> LLVMExpr s f

-----------------------------------------------------------------------------------------
-- Type translations

data ScalarView s where
  Scalar    :: TypeRepr tp -> Expr s tp -> ScalarView s
  NotScalar :: ScalarView s

-- | Examine an LLVM expression and return the corresponding
--   crucible expression, if it is a scalar.
asScalar :: (?lc :: TyCtx.LLVMContext)
         => LLVMExpr s Expr
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

-- | Translate a list of LLVM expressions into a crucible type context,
--   which is passed into the given continuation.
llvmTypesAsCtx :: forall a
                . (?lc :: TyCtx.LLVMContext)
               => [MemType]
               -> (forall ctx. CtxRepr ctx -> a)
               -> a
llvmTypesAsCtx xs f = go (concatMap llvmTypeToRepr xs) Ctx.empty
 where go :: forall ctx. [Some TypeRepr] -> CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.%> tp)

-- | Translate an LLVM type into a crucible type, which is passed into
--   the given continuation
llvmTypeAsRepr :: forall a
                . (?lc :: TyCtx.LLVMContext)
               => MemType
               -> (forall tp. TypeRepr tp -> a)
               -> a
llvmTypeAsRepr xs f = go (llvmTypeToRepr xs)
 where go :: [Some TypeRepr] -> a
       go []       = f UnitRepr
       go [Some x] = f x

       go _ = error $ unwords ["llvmTypesAsRepr: expected a single value type", show xs]

-- | Translate an LLVM return type into a crucible type, which is passed into
--   the given continuation
llvmRetTypeAsRepr :: forall a
                   . (?lc :: TyCtx.LLVMContext)
                  => Maybe MemType
                  -> (forall tp. TypeRepr tp -> a)
                  -> a
llvmRetTypeAsRepr Nothing   f = f UnitRepr
llvmRetTypeAsRepr (Just tp) f = llvmTypeAsRepr tp f

-- | Actually perform the type translation
llvmTypeToRepr :: (?lc :: TyCtx.LLVMContext) => MemType -> [Some TypeRepr]
llvmTypeToRepr (ArrayType _ tp)  = [llvmTypeAsRepr tp (\t -> Some (VectorRepr t))]
llvmTypeToRepr (VecType _ tp)    = [llvmTypeAsRepr tp (\t-> Some (VectorRepr t))]
llvmTypeToRepr (StructType si)   = [llvmTypesAsCtx tps (\ts -> Some (StructRepr ts))]
  where tps = map fiType $ toList $ siFields si
llvmTypeToRepr (PtrType pty) = llvmPtrTypeToRepr pty
llvmTypeToRepr FloatType     = [Some RealValRepr]
llvmTypeToRepr DoubleType    = [Some RealValRepr]
--llvmTypeToRepr FloatType   = [Some (FloatRepr SingleFloatRepr)]
--llvmTypeToRepr DoubleType  = [Some (FloatRepr DoubleFloatRepr)]
llvmTypeToRepr MetadataType = []
llvmTypeToRepr (IntType n) =
   case someNat (fromIntegral n) of
      Just (Some w) | Just LeqProof <- isPosNat w -> [Some (BVRepr w)]
      _ -> error $ unwords ["invalid integer width",show n]

llvmPtrTypeToRepr :: (?lc :: TyCtx.LLVMContext)
                  => SymType
                  -> [Some TypeRepr]
llvmPtrTypeToRepr (Alias ident) =
  case TyCtx.lookupAlias ident of
    Just tp -> llvmPtrTypeToRepr tp
    Nothing -> error $ unwords ["Unable to resolve type alias", show ident]
llvmPtrTypeToRepr (FunType decl) =
  llvmDeclToFunHandleRepr decl $ \args ret -> [Some (FunctionHandleRepr args ret)]
llvmPtrTypeToRepr _ = [Some llvmPointerRepr]

llvmDeclToFunHandleRepr
   :: (?lc :: TyCtx.LLVMContext)
   => FunDecl
   -> (forall args ret. CtxRepr args -> TypeRepr ret -> a)
   -> a
llvmDeclToFunHandleRepr decl k =
  llvmTypesAsCtx (fdArgTypes decl) $ \args ->
    llvmRetTypeAsRepr (fdRetType decl) $ \ret ->
      if fdVarArgs decl then
        k (args Ctx.%> varArgsRepr) ret
      else
        k args ret

-- | Given an LLVM type and a type context and a register assignment,
--   peel off the rightmost register from the assignement, which is
--   expected to match the given LLVM type.  Pass the register and
--   the remaining type and register context to the given continuation.
--
--   This procedure is used to set up the initial state of the
--   registers at the entry point of a function.
packType :: (?lc :: TyCtx.LLVMContext)
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
  case Ctx.view ctx0 of
    Ctx.AssignEmpty -> error "packType: ran out of actual arguments!"
    Ctx.AssignExtend ctx' ctp' ->
      case testEquality ctp ctp' of
        Nothing -> error $ unwords ["crucible type mismatch",show ctp,show ctp']
        Just Refl ->
          let asgn' = Ctx.init asgn
              idx   = Ctx.nextIndex (Ctx.size asgn')
           in k (Some (asgn Ctx.! idx))
                ctx'
                asgn'

typeToRegExpr :: (?lc :: TyCtx.LLVMContext)
              => MemType
              -> End h s LLVMState init ret (Some (Reg s))
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
    L.Alloca ty _ _ -> L.PtrTo ty
    L.Load x _ -> case L.typedType x of
                   L.PtrTo ty -> ty
                   _ -> error $ unwords ["load through non-pointer type", show (L.typedType x)]
    L.ICmp _ _ _ -> L.PrimType (L.Integer 1)
    L.FCmp _ _ _ -> L.PrimType (L.Integer 1)
    L.Phi tp _   -> tp
    L.GEP _ _ _  -> L.PtrTo (L.PrimType (L.Integer 8)) -- FIXME? Is this OK?
    L.Select _ x _ -> L.typedType x

    L.ExtractValue x idxes -> go (L.typedType x) idxes
         where go tp [] = tp
               go (L.Array n tp') (i:is)
                   | i < n = go tp' is
                   | otherwise = error $ unwords ["invalid index into array type", show instr]
               go (L.Struct tps) (i:is) =
                      case drop (fromIntegral i) tps of
                        (tp':_) -> go tp' is
                        [] -> error $ unwords ["invalid index into struct type", show instr]
               go _ _ = error $ unwords ["invalid type in extract value instruction", show instr]

    L.InsertValue x _ _ -> L.typedType x
    L.ExtractElt x _ -> case L.typedType x of
                        L.Vector _ tp -> tp
                        _ -> error $ unwords ["extract element of non-vector type", show instr]
    L.InsertElt x _ _ -> L.typedType x
    L.ShuffleVector x _ _ -> L.typedType x

    _ -> error $ unwords ["instrResultType, unsupported instruction:", show instr]

------------------------------------------------------------------------
-- LLVMState

-- | Maps identifiers to an associated register or defined expression.
type IdentMap s = Map L.Ident (Either (Some (Reg s)) (Some (Atom s)))

data LLVMState s
   = LLVMState
   { -- | Map from identifiers to associated register shape
     _identMap :: !(IdentMap s)
   , _blockInfoMap :: !(Map L.BlockLabel (LLVMBlockInfo s))
   , llvmContext :: LLVMContext
   }

identMap :: Simple Lens (LLVMState s) (IdentMap s)
identMap = lens _identMap (\s v -> s { _identMap = v })

blockInfoMap :: Simple Lens (LLVMState s) (Map L.BlockLabel (LLVMBlockInfo s))
blockInfoMap = lens _blockInfoMap (\s v -> s { _blockInfoMap = v })

-- Given a list of LLVM formal parameters and a corresponding crucible
-- register assignment, build an IdentMap mapping LLVM identifiers to
-- corresponding crucible registers.
buildIdentMap :: (?lc :: TyCtx.LLVMContext)
              => [L.Typed L.Ident]
              -> CtxRepr ctx
              -> Ctx.Assignment (Atom s) ctx
              -> IdentMap s
              -> IdentMap s
buildIdentMap [] ctx _ m
  | Ctx.null ctx = m
  | otherwise =
      error "buildIdentMap: passed arguments do not match LLVM input signature"
buildIdentMap (ti:ts) ctx asgn m = do
  -- ?? FIXME, irrefutable pattern...
  let Just ty = TyCtx.liftMemType (L.typedType ti)
  packType ty ctx asgn $ \x ctx' asgn' ->
     buildIdentMap ts ctx' asgn' (Map.insert (L.typedValue ti) (Right x) m)

-- | Build the initial LLVM generator state upon entry to to the entry point of a function.
initialState :: L.Define
             -> LLVMContext
             -> CtxRepr args
             -> Ctx.Assignment (Atom s) args
             -> LLVMState s
initialState d llvmctx args asgn =
   let ?lc = llvmTypeCtx llvmctx in
   let m = buildIdentMap (reverse (L.defArgs d)) args asgn Map.empty in
     LLVMState { _identMap = m, _blockInfoMap = Map.empty, llvmContext = llvmctx }

type LLVMGenerator h s ret = Generator h s LLVMState ret
type LLVMEnd h s init ret  = End h s LLVMState init ret

-- | Information about an LLVM basic block
data LLVMBlockInfo s
  = LLVMBlockInfo
    {
      -- The crucible block label corresponding to this LLVM block
      block_label    :: Label s

      -- map from labels to assignemnts that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map    :: !(Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value)))
    }

buildBlockInfoMap :: L.Define -> End h s LLVMState init ret (Map L.BlockLabel (LLVMBlockInfo s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: L.BasicBlock -> End h s LLVMState init ret (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let Just blk_lbl = L.bbLabel bb
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_label = lab
                                })

-- Given the statements in a basic block, find all the phi instructions and
-- compute the list of assignements that must be made for each predicessor block.
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
buildRegMap :: (?lc :: TyCtx.LLVMContext) => IdentMap s -> L.Define -> End h s LLVMState init reg (IdentMap s)
buildRegMap m d = foldM buildRegTypeMap m $ L.defBody d

buildRegTypeMap :: (?lc :: TyCtx.LLVMContext)
                => IdentMap s
                -> L.BasicBlock
                -> End h s LLVMState init ret (IdentMap s)
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

liftRetType :: (?lc :: TyCtx.LLVMContext, Monad m)
            => L.Type
            -> m (Maybe MemType)
liftRetType t =
  case TyCtx.liftRetType t of
    Just mt -> return mt
    Nothing -> fail $ unwords ["Expected return type: ", show t]


liftMemType :: (?lc :: TyCtx.LLVMContext, Monad m)
            => L.Type
            -> m MemType
liftMemType t =
  case TyCtx.liftMemType t of
    Just mt -> return mt
    Nothing -> fail $ unwords ["Expected memory type: ", show t]

transTypedValue :: (?lc :: TyCtx.LLVMContext)
                => L.Typed L.Value
                -> LLVMGenerator h s ret (LLVMExpr s Expr)
transTypedValue v = do
   tp <- liftMemType $ L.typedType v
   transValue tp (L.typedValue v)

-- | Translate an LLVM Value into an expression.
transValue :: (?lc :: TyCtx.LLVMContext)
           => MemType
           -> L.Value
           -> LLVMGenerator h s ret (LLVMExpr s Expr)

transValue ty L.ValZeroInit =
  return $ ZeroExpr ty

transValue ty@(PtrType _) L.ValNull =
  return $ ZeroExpr ty

transValue ty L.ValUndef =
  return $ UndefExpr ty

transValue _ (L.ValString str) = do
  let eight = knownNat :: NatRepr 8
  let bv8   = BVRepr eight
  let chars = V.fromList $ map (App . C.BVLit eight . toInteger . fromEnum) $ str
  return $ BaseExpr (VectorRepr bv8) (App $ C.VectorLit bv8 $ chars)

transValue _ (L.ValIdent i) = do
  m <- use identMap
  case Map.lookup i m of
    Nothing -> do
      fail $ "Could not find identifier " ++ show i ++ "."
    Just (Left (Some r)) -> do
      e <- readReg r
      return $ BaseExpr (typeOfReg r) e
    Just (Right (Some a)) -> do
      return $ BaseExpr (typeOfAtom a) (AtomExpr a)

transValue (PtrType (FunType _)) (L.ValSymbol sym) = do
  symmap <- (_symbolMap . llvmContext)  <$> get
  case Map.lookup sym symmap of
     Nothing -> fail $ unwords ["symbol not found:", show sym]
     Just (LLVMHandleInfo _ h) -> do
        let argTypes = handleArgTypes h
        let retType  = handleReturnType h
        return $ BaseExpr (FunctionHandleRepr argTypes retType) (litExpr h)

transValue (IntType w) (L.ValInteger i) =
  case someNat (fromIntegral w) of
    Just (Some w') | Just LeqProof <- isPosNat w' ->
      return $ BaseExpr (BVRepr w') (App (C.BVLit w' i))
    _ -> fail $ unwords ["invalid integer type", show w]

transValue (IntType 1) (L.ValBool b) =
  return $ BaseExpr (BVRepr (knownNat :: NatRepr 1))
                    (App (C.BoolToBV knownNat (litExpr b)))

transValue FloatType (L.ValFloat f) =
  return $ BaseExpr RealValRepr (App (C.RationalLit (toRational f)))

transValue DoubleType (L.ValDouble d) =
  return $ BaseExpr RealValRepr (App (C.RationalLit (toRational d)))

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
     let symbol' = app $ C.ConcreteLit $ TypeableValue $ GlobalSymbol symbol
     ptr <- call resolveGlobal (Ctx.empty Ctx.%> mem Ctx.%> symbol')
     return (BaseExpr llvmPointerRepr ptr)

transValue _ (L.ValConstExpr cexp) =
  case cexp of
    L.ConstConv op x outty ->
      translateConversion op x outty
    L.ConstGEP _inBounds _resType [] ->
      fail "empty getelementpointer expression"
    L.ConstGEP _inBounds _resType (base:elts) -> do
      base' <- transTypedValue base
      elts' <- mapM transTypedValue elts
      typ <- liftMemType (L.typedType base)
      BaseExpr llvmPointerRepr <$> calcGEP typ base' elts'
    L.ConstSelect b x y -> do
      b' <- transTypedValue b
      x' <- transTypedValue x
      y' <- transTypedValue y
      mty <- liftMemType (L.typedType x)
      case asScalar b' of
        Scalar (BVRepr w) b'' ->
          llvmTypeAsRepr mty $ \tpr -> do
            b_e <- mkAtom (App $ C.BVNonzero w b'')
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

        _ -> fail "expected boolean value in select expression"

    L.ConstBlockAddr _funSymbol _blockLabel ->
      fail "'blockaddress' expressions not supported."

    L.ConstFCmp _ _ _ -> fail "constant comparisons not currently supported"
    L.ConstICmp _ _ _ -> fail "constant comparisons not currently supported"
    L.ConstArith _ _ _ -> fail "constant arithmetic not currently supported"
    L.ConstBit _ _ _ -> fail "constant bit operations not currently supported"

transValue ty v =
  fail $ unwords ["unsupported LLVM value:", show v, "of type", show ty]


-- | Assign a packed LLVM expression into the named LLVM register.
assignLLVMReg
        :: (?lc :: TyCtx.LLVMContext)
        => L.Ident
        -> LLVMExpr s Expr
        -> LLVMGenerator h s ret ()
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
doAssign :: forall h s ret
    . (?lc :: TyCtx.LLVMContext)
   => Some (Reg s)
   -> LLVMExpr s Expr  -- ^ the RHS values to assign
   -> LLVMGenerator h s ret ()
doAssign (Some r) (BaseExpr tpr ex) =
   case testEquality (typeOfReg r) tpr of
     Just Refl -> assignReg r ex
     Nothing -> fail $ unwords ["type mismatch when assigning register", show r, show (typeOfReg r) , show tpr]
doAssign (Some r) (StructExpr vs) = do
   let ?err = fail
   unpackArgs (map snd $ toList vs) $ \ctx asgn ->
     case testEquality (typeOfReg r) (StructRepr ctx) of
       Just Refl -> assignReg r (mkStruct ctx asgn)
       Nothing -> fail $ unwords ["type mismatch when assigning structure to register", show r, show (StructRepr ctx)]
doAssign (Some r) (ZeroExpr tp) = do
  let ?err = fail
  zeroExpand tp $ \(tpr :: TypeRepr t) (ex :: Expr s t) ->
    case testEquality (typeOfReg r) tpr of
      Just Refl -> assignReg r ex
      Nothing -> fail $ "type mismatch when assigning zero value"
doAssign (Some r) (UndefExpr tp) = do
  let ?err = fail
  undefExpand tp $ \(tpr :: TypeRepr t) (ex :: Expr s t) ->
    case testEquality (typeOfReg r) tpr of
      Just Refl -> assignReg r ex
      Nothing -> fail $ "type mismatch when assigning undef value"
doAssign (Some r) (VecExpr tp vs) = do
  let ?err = fail
  llvmTypeAsRepr tp $ \tpr ->
    unpackVec tpr (toList vs) $ \ex ->
      case testEquality (typeOfReg r) (VectorRepr tpr) of
        Just Refl -> assignReg r ex
        Nothing -> fail $ "type mismatch when assigning vector value"

-- | Given a list of LLVMExpressions, "unpack" them into an assignement
--   of crucible expressions.
unpackArgs :: forall s a
    . (?lc :: TyCtx.LLVMContext
      ,?err :: String -> a
      )
   => [LLVMExpr s Expr]
   -> (forall ctx. CtxRepr ctx -> Ctx.Assignment (Expr s) ctx -> a)
   -> a
unpackArgs = go Ctx.empty Ctx.empty
 where go :: CtxRepr ctx
          -> Ctx.Assignment (Expr s) ctx
          -> [LLVMExpr s Expr]
          -> (forall ctx'. CtxRepr ctx' -> Ctx.Assignment (Expr s) ctx' -> a)
          -> a
       go ctx asgn [] k = k ctx asgn
       go ctx asgn (v:vs) k = unpackOne v (\tyr ex -> go (ctx Ctx.%> tyr) (asgn Ctx.%> ex) vs k)

unpackOne
   :: (?lc :: TyCtx.LLVMContext, ?err :: String -> a)
   => LLVMExpr s Expr
   -> (forall tpr. TypeRepr tpr -> Expr s tpr -> a)
   -> a
unpackOne (BaseExpr tyr ex) k = k tyr ex
unpackOne (UndefExpr tp) k = undefExpand tp k
unpackOne (ZeroExpr tp) k = zeroExpand tp k
unpackOne (StructExpr vs) k =
  unpackArgs (map snd $ toList vs) $ \struct_ctx struct_asgn ->
      k (StructRepr struct_ctx) (mkStruct struct_ctx struct_asgn)
unpackOne (VecExpr tp vs) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (toList (Seq.reverse vs)) $ k (VectorRepr tpr)

unpackVec :: forall tpr s a
    . (?lc :: TyCtx.LLVMContext, ?err :: String -> a)
   => TypeRepr tpr
   -> [LLVMExpr s Expr]
   -> (Expr s (VectorType tpr) -> a)
   -> a
unpackVec tpr = go []
  where go :: [Expr s tpr] -> [LLVMExpr s Expr] -> (Expr s (VectorType tpr) -> a) -> a
        go vs [] k = k (vectorLit tpr $ V.fromList vs)
        go vs (x:xs) k = unpackOne x $ \tpr' v ->
                           case testEquality tpr tpr' of
                             Just Refl -> go (v:vs) xs k
                             Nothing -> ?err $ unwords ["type mismatch in array value", show tpr, show tpr']

zeroExpand :: forall s a
            . (?lc :: TyCtx.LLVMContext, ?err :: String -> a)
           => MemType
           -> (forall tp. TypeRepr tp -> Expr s tp -> a)
           -> a
zeroExpand (IntType n) k =
   case someNat (fromIntegral n) of
     Just (Some w) | Just LeqProof <- isPosNat w -> do
       k (BVRepr w) (App (C.BVLit w 0))
     _ -> ?err $ unwords ["illegal integer size", show n]
zeroExpand (StructType si) k =
   unpackArgs (map ZeroExpr tps) $ \ctx asgn -> k (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
zeroExpand (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k (VectorRepr tpr)
zeroExpand (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (ZeroExpr tp)) $ k (VectorRepr tpr)
zeroExpand (PtrType _tp) k = k llvmPointerRepr nullPointer
zeroExpand FloatType   k  = k RealValRepr (App (C.RationalLit 0))
zeroExpand DoubleType  k  = k RealValRepr (App (C.RationalLit 0))
zeroExpand MetadataType _ = ?err "Cannot zero expand metadata"

undefExpand :: (?lc :: TyCtx.LLVMContext, ?err :: String -> a)
            => MemType
            -> (forall tp. TypeRepr tp -> Expr s tp -> a)
            -> a
undefExpand (IntType n) k =
   case someNat (fromIntegral n) of
     Just (Some w) | Just LeqProof <- isPosNat w ->
       k (BVRepr w) (App (C.BVUndef w))
     _ -> error $ unwords ["illegal integer size", show n]
undefExpand (StructType si) k =
   unpackArgs (map UndefExpr tps) $ \ctx asgn -> k (StructRepr ctx) (mkStruct ctx asgn)
 where tps = map fiType $ toList $ siFields si
undefExpand (ArrayType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k (VectorRepr tpr)
undefExpand (VecType n tp) k =
  llvmTypeAsRepr tp $ \tpr -> unpackVec tpr (replicate (fromIntegral n) (UndefExpr tp)) $ k (VectorRepr tpr)
undefExpand tp _ = ?err $ unwords ["cannot undef expand type:", show tp]

--undefExpand (L.PtrTo _tp) k = k llvmPointerRepr (App C.UndefPointer) FIXME?
--undefExpand (L.PrimType (L.FloatType _ft)) _k = error "FIXME undefExpand: float types"

unpackVarArgs :: forall h s ret a
    . (?lc :: TyCtx.LLVMContext
      ,?err :: String -> a
      )
   => [LLVMExpr s Expr]
   -> LLVMGenerator h s ret (Expr s (VectorType AnyType))
unpackVarArgs xs = App . C.VectorLit AnyRepr . V.fromList <$> xs'
 where xs' = let ?err = fail in
             mapM (\x -> unpackOne x (\tp x' -> return $ App (C.PackAny tp x'))) xs

-- | Implement the phi-functions along the edge from one LLVM Basic block to another.
definePhiBlock :: (?lc :: TyCtx.LLVMContext)
               => L.BlockLabel      -- ^ The LLVM source basic block
               -> L.BlockLabel      -- ^ The LLVM target basic block
               -> LLVMGenerator h s ret ()
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

-- Given an LLVM expression of vector type, select out the ith element.
extractElt
    :: (?lc :: TyCtx.LLVMContext)
    => MemType    -- ^ type contained in the vector
    -> Integer   -- ^ size of the vector
    -> LLVMExpr s Expr -- ^ vector expression
    -> LLVMExpr s Expr -- ^ index expression
    -> LLVMGenerator h s ret (LLVMExpr s Expr)
extractElt ty _ _ (UndefExpr _)  =
   return $ UndefExpr ty
extractElt ty n v (ZeroExpr zty) = do
   let ?err = fail
   zeroExpand zty $ \tyr ex -> extractElt ty n v (BaseExpr tyr ex)
extractElt ty n (UndefExpr _) i  = do
   let ?err = fail
   undefExpand ty $ \tyr ex -> extractElt ty n (BaseExpr tyr ex) i
extractElt ty n (ZeroExpr _) i   = do
   let ?err = fail
   zeroExpand ty  $ \tyr ex -> extractElt ty n (BaseExpr tyr ex) i
extractElt _ n (VecExpr _ vs) i
  | Scalar (BVRepr _) (App (C.BVLit _ idx)) <- asScalar i
       = do if (fromInteger idx < Seq.length vs) && (fromInteger idx < n)
              then return $ Seq.index vs (fromInteger idx)
              else fail "invalid extractelement instruction (index out of bounds)"
extractElt ty n (VecExpr _ vs) i = do
   let ?err = fail
   llvmTypeAsRepr ty $ \tyr -> unpackVec tyr (toList vs) $
      \ex -> extractElt ty n (BaseExpr (VectorRepr tyr) ex) i
extractElt _ n (BaseExpr (VectorRepr tyr) v) i
  | Scalar (BVRepr w) idx <- asScalar i
  , Just LeqProof <- isPosNat w = do
      assertExpr (App (C.BVUlt w idx (App (C.BVLit w n)))) "extract element index out of bounds!"
      return $ BaseExpr tyr (App (C.VectorGetEntry tyr v (App (C.BvToNat w idx))))
extractElt _ _ _ _ = fail $ "invalid extractelement instruction"


-- Given an LLVM expression of vector type, insert a new element at location ith element.
insertElt
    :: (?lc :: TyCtx.LLVMContext)

    => MemType            -- ^ type contained in the vector
    -> Integer            -- ^ size of the vector
    -> LLVMExpr s Expr    -- ^ vector expression
    -> LLVMExpr s Expr    -- ^ element to insert
    -> LLVMExpr s Expr    -- ^ index expression
    -> LLVMGenerator h s ret (LLVMExpr s Expr)
insertElt ty _ _ _ (UndefExpr _)  = do
   return $ UndefExpr ty
insertElt ty n v a (ZeroExpr zty) = do
   let ?err = fail
   zeroExpand zty $ \tyr ex -> insertElt ty n v a (BaseExpr tyr ex)
insertElt ty n (UndefExpr _) a i  = do
  let ?err = fail
  undefExpand ty $ \tyr ex -> insertElt ty n (BaseExpr tyr ex) a i
insertElt ty n (ZeroExpr _) a i   = do
  let ?err = fail
  zeroExpand ty  $ \tyr ex -> insertElt ty n (BaseExpr tyr ex) a i
insertElt _ n (VecExpr ty vs) a i
  | Scalar (BVRepr _) (App (C.BVLit _ idx)) <- asScalar i
       = do if (fromInteger idx < Seq.length vs) && (fromInteger idx < n)
              then return $ VecExpr ty $ Seq.adjust (\_ -> a) (fromIntegral idx) vs
              else fail "invalid insertelement instruction (index out of bounds)"
insertElt ty n (VecExpr _ vs) a i = do
   let ?err = fail
   llvmTypeAsRepr ty $ \tyr -> unpackVec tyr (toList vs) $
        \ex -> insertElt ty n (BaseExpr (VectorRepr tyr) ex) a i
insertElt _ n (BaseExpr (VectorRepr tyr) v) a i
  | Scalar (BVRepr w) idx <- asScalar i
  , Just LeqProof <- isPosNat w = do
    assertExpr (App (C.BVUlt w idx (App (C.BVLit w n)))) "insert element index out of bounds!"
    let ?err = fail
    unpackOne a $ \tyra a' ->
      case testEquality tyr tyra of
        Just Refl ->
          return $ BaseExpr (VectorRepr tyr) (App (C.VectorSetEntry tyr v (App (C.BvToNat w idx)) a'))
        Nothing -> fail $ "type mismatch in insertelement instruction"
insertElt _ _ _ _ _ = fail $ "invalid insertelement instruction"

-- Given an LLVM expression of vector or structure type, select out the
-- element indicated by the sequence of given concrete indices.
extractValue
    :: (?lc :: TyCtx.LLVMContext)
    => LLVMExpr s Expr  -- ^ aggregate expression
    -> [Int32]          -- ^ sequence of indices
    -> LLVMGenerator h s ret (LLVMExpr s Expr)
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
           extractValue (BaseExpr tpr (getStruct idx x tpr)) is
extractValue (StructExpr vs) (i:is)
   | fromIntegral i < Seq.length vs = extractValue (snd $ Seq.index vs $ fromIntegral i) is
extractValue (VecExpr _ vs) (i:is)
   | fromIntegral i < Seq.length vs = extractValue (Seq.index vs $ fromIntegral i) is
extractValue _ _ = fail "invalid extractValue instruction"


-- Given an LLVM expression of vector or structure type, insert a new element in the posistion
-- given by the concrete indices.
insertValue
    :: (?lc :: TyCtx.LLVMContext)
    => LLVMExpr s Expr  -- ^ aggregate expression
    -> LLVMExpr s Expr  -- ^ element to insert
    -> [Int32]          -- ^ sequence of concrete indices
    -> LLVMGenerator h s ret (LLVMExpr s Expr)
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
           x' <- insertValue (BaseExpr tpr (getStruct idx x tpr)) v is
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


callAlloca
   :: Expr s (BVType PtrWidth)
   -> LLVMGenerator h s ret (Expr s LLVMPointerType)
callAlloca sz = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   alloca <- litExpr . llvmMemAlloca . memModelOps . llvmContext <$> get
   mem <- readGlobal memVar
   res <- call alloca (Ctx.empty Ctx.%> mem Ctx.%> sz)
   let mem' = getStruct (Ctx.skip $ Ctx.nextIndex $ Ctx.zeroSize)    res knownRepr
   let p    = getStruct (Ctx.nextIndex $ Ctx.incSize $ Ctx.zeroSize) res knownRepr
   writeGlobal memVar mem'
   return p

callPushFrame :: LLVMGenerator h s ret ()
callPushFrame = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   pushFrame <- litExpr . llvmMemPushFrame . memModelOps . llvmContext <$> get
   mem  <- readGlobal memVar
   mem' <- call pushFrame (Ctx.empty Ctx.%> mem)
   writeGlobal memVar mem'

callPopFrame :: LLVMGenerator h s ret ()
callPopFrame = do
   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
   popFrame <- litExpr . llvmMemPopFrame . memModelOps . llvmContext <$> get
   mem  <- readGlobal memVar
   mem' <- call popFrame (Ctx.empty Ctx.%> mem)
   writeGlobal memVar mem'


-- RWD: This translation is really pretty dumb.  Why do both of these
-- different type representations exist, and do we actually need
-- them both?
toStorableType :: Monad m
               => MemType
               -> m G.Type
toStorableType mt =
  case mt of
    IntType n -> return $ G.bitvectorType ((fromIntegral n+7) `div` 8)
    PtrType _ -> return $ G.bitvectorType ((fromIntegral (natValue ptrWidth)) `div` 8)
    FloatType -> return $ G.floatType
    DoubleType -> return $ G.doubleType
    ArrayType n x -> G.arrayType (fromIntegral n) <$> toStorableType x
    VecType _ _ -> fail "Cannot directly store vector types (FIXME?)"
    MetadataType -> fail "toStorableType: Cannot store metadata values"
    StructType si -> G.mkStruct <$> traverse transField (siFields si)
      where transField :: Monad m => FieldInfo -> m (G.Type, G.Size)
            transField fi = do
               t <- toStorableType $ fiType fi
               return (t, fiPadding fi)

callPtrAddOffset ::
    (?lc :: TyCtx.LLVMContext)
    => Expr s LLVMPointerType
    -> Expr s (BVType PtrWidth)
    -> LLVMGenerator h s ret (Expr s LLVMPointerType)
callPtrAddOffset base off = do
    ptrAddOff <- litExpr . llvmPtrAddOffset . memModelOps . llvmContext <$> get
    call ptrAddOff (Ctx.empty Ctx.%> base Ctx.%> off)


callPtrSubtract ::
    (?lc :: TyCtx.LLVMContext)
    => Expr s LLVMPointerType
    -> Expr s LLVMPointerType
    -> LLVMGenerator h s ret (Expr s (BVType PtrWidth))
callPtrSubtract x y = do
    ptrSub <- litExpr . llvmPtrSubtract . memModelOps . llvmContext <$> get
    call ptrSub (Ctx.empty Ctx.%> x Ctx.%> y)


callLoad :: (?lc :: TyCtx.LLVMContext)
         => MemType
         -> TypeRepr tp
         -> LLVMExpr s Expr
         -> LLVMGenerator h s ret (LLVMExpr s Expr)
callLoad typ expectTy (asScalar -> Scalar (RecursiveRepr nm) ptr)
  | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") = do
      memVar <- llvmMemVar . memModelOps . llvmContext <$> get
      memLoad <- litExpr . llvmMemLoad . memModelOps . llvmContext <$> get
      mem  <- readGlobal memVar
      typ' <- app . C.ConcreteLit . TypeableValue <$> toStorableType typ
      v <- call memLoad (Ctx.empty Ctx.%> mem Ctx.%> ptr Ctx.%> typ')
      let msg = litExpr (Text.pack ("Expected load to return value of type " ++ show expectTy))
      let v' = app $ C.FromJustValue expectTy (app $ C.UnpackAny expectTy v) msg
      return (BaseExpr expectTy v')
callLoad _ _ _ =
  fail $ unwords ["Unexpected argument type in callStore"]

callStore :: (?lc :: TyCtx.LLVMContext)
          => MemType
          -> LLVMExpr s Expr
          -> LLVMExpr s Expr
          -> LLVMGenerator h s ret ()
callStore typ (asScalar -> Scalar (RecursiveRepr nm) ptr) v
  | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") = do

    let ?err = fail
    unpackOne v $ \vtpr vexpr -> do
      memVar <- llvmMemVar . memModelOps . llvmContext <$> get
      memStore <- litExpr . llvmMemStore . memModelOps . llvmContext <$> get
      mem  <- readGlobal memVar
      let v' = app (C.PackAny vtpr vexpr)
      typ' <- app . C.ConcreteLit . TypeableValue <$> toStorableType typ
      mem' <- call memStore (Ctx.empty Ctx.%> mem Ctx.%> ptr Ctx.%> typ' Ctx.%> v')
      writeGlobal memVar mem'

callStore _ _ _ =
  fail $ unwords ["Unexpected argument type in callStore"]


calcGEP :: (?lc :: TyCtx.LLVMContext)
        => MemType
        -> LLVMExpr s Expr
        -> [LLVMExpr s Expr]
        -> LLVMGenerator h s ret (Expr s LLVMPointerType)
calcGEP typ@(PtrType _) (asScalar -> Scalar (RecursiveRepr nm) base) xs@(_ : _)
   | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") =
        calcGEP' typ base xs
-- FIXME: support for vector base arguments
calcGEP typ _base _xs = do
   fail $ unwords ["Invalid base argument type in GEP", show typ]


calcGEP' :: (?lc :: TyCtx.LLVMContext)
         => MemType
         -> Expr s LLVMPointerType
         -> [LLVMExpr s Expr]
         -> LLVMGenerator h s ret (Expr s LLVMPointerType)

calcGEP' _typ base [] = return base

calcGEP' (PtrType (Alias ident)) base xs =
  case TyCtx.lookupAlias ident of
    Just ty -> calcGEP' (PtrType ty) base xs
    Nothing -> fail $ unwords ["Unable to resolve type alias", show ident]

calcGEP' (ArrayType bound typ') base (idx : xs) = do
    idx' <- case asScalar idx of
              Scalar (BVRepr w) x
                 | Just Refl <- testEquality w ptrWidth ->
                      return x
                 | Just LeqProof <- testLeq (incNat w) ptrWidth ->
                      return $ app (C.BVSext ptrWidth w x)
              _ -> fail $ unwords ["Invalid index value in GEP"]

    -- assert that 0 <= idx' <= bound
    --   (yes, <= and not < because of the 1-past-the-end rule)
    let zero      = App $ C.BVLit ptrWidth 0
    let bound'    = App $ C.BVLit ptrWidth $ toInteger bound
    let geZero    = App $ C.BVSle ptrWidth zero idx'
    let leBound   = App $ C.BVSle ptrWidth idx' bound'
    let boundTest = App $ C.And geZero leBound
    assertExpr boundTest
      (App $ C.TextLit $ Text.pack "Array index out of bounds when calculating getelementpointer")

    let dl  = TyCtx.llvmDataLayout ?lc

    -- Calculate the size of the elemement memtype and check that it fits
    -- in the pointer width
    let isz = fromIntegral $ memTypeSize dl typ'
    unless (isz <= maxSigned ptrWidth)
      (fail $ unwords ["Type size too large for pointer width:", show typ'])
    let sz  = app $ C.BVLit ptrWidth $ isz

    -- Perform a signed wide multiply and check for overflow
    let wideMul  = app $ C.BVMul (addNat ptrWidth ptrWidth)
                           (app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth sz)
                           (app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth idx')
    let off      = app $ C.BVTrunc ptrWidth (addNat ptrWidth ptrWidth) wideMul
    let wideMul' = app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth off
    assertExpr (app $ C.BVEq (addNat ptrWidth ptrWidth) wideMul wideMul')
      (App $ C.TextLit $ Text.pack "Multiplication overflow in getelementpointer")

    -- Perform the pointer arithmetic and continue
    base' <- callPtrAddOffset base off
    calcGEP' typ' base' xs

calcGEP' (PtrType (MemType typ')) base (idx : xs) = do
    idx' <- case asScalar idx of
              Scalar (BVRepr w) x
                 | Just Refl <- testEquality w ptrWidth ->
                      return x
                 | Just LeqProof <- testLeq (incNat w) ptrWidth ->
                      return $ app (C.BVSext ptrWidth w x)
              _ -> fail $ unwords ["Invalid index value in GEP"]
    let dl  = TyCtx.llvmDataLayout ?lc

    -- Calculate the size of the elemement memtype and check that it fits
    -- in the pointer width
    let isz = fromIntegral $ memTypeSize dl typ'
    unless (isz <= maxSigned ptrWidth)
      (fail $ unwords ["Type size too large for pointer width:", show typ'])
    let sz  = app $ C.BVLit ptrWidth $ isz

    -- Perform a signed wide multiply and check for overflow
    let wideMul = app $ C.BVMul (addNat ptrWidth ptrWidth)
                           (app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth sz)
                           (app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth idx')
    let off      = app $ C.BVTrunc ptrWidth (addNat ptrWidth ptrWidth) wideMul
    let wideMul' = app $ C.BVSext (addNat ptrWidth ptrWidth) ptrWidth off
    assertExpr (app $ C.BVEq (addNat ptrWidth ptrWidth) wideMul wideMul')
      (App $ C.TextLit $ Text.pack "Multiplication overflow in getelementpointer")

    -- Perform the pointer arithmetic and continue
    base' <- callPtrAddOffset base off
    calcGEP' typ' base' xs

calcGEP' (StructType si) base (idx : xs) = do
    idx' <- case asScalar idx of
              Scalar (BVRepr _w) (asApp -> Just (C.BVLit _ x)) -> return x
              _ -> fail $ unwords ["Expected constant value when indexing fields in GEP"]
    case siFieldInfo si (fromInteger idx') of
      Just fi -> do
        -- Get the field offset and check that it fits
        -- in the pointer width
        let ioff = fromIntegral $ fiOffset fi
        unless (ioff <= maxSigned ptrWidth)
          (fail $ unwords ["Field offset too large for pointer width in structure:"
                          , show (ppMemType (StructType si))])
        let off  = app $ C.BVLit ptrWidth $ ioff

        -- Perform the pointer arithmetic and continue
        base' <- callPtrAddOffset base off
        let typ' = fiType fi
        calcGEP' typ' base' xs
      Nothing ->
        fail $ unwords ["Invalid field index", show idx', "for structure", show (ppMemType (StructType si))]

calcGEP' tp _ _ =
    fail $ unwords ["calcGEP': invalid arguments", show tp]


translateConversion
  :: (?lc :: TyCtx.LLVMContext)
  => L.ConvOp
  -> L.Typed L.Value
  -> L.Type
  -> LLVMGenerator h s ret (LLVMExpr s Expr)
translateConversion op x outty =
 case op of
    L.IntToPtr -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (IntrinsicRepr nm) _, IntrinsicRepr nm' )
             | Just Refl <- testEquality nm  (knownSymbol :: SymbolRepr "LLVM_pointer")
             , Just Refl <- testEquality nm' (knownSymbol :: SymbolRepr "LLVM_pointer") ->
                return x'
           _ -> fail "integer-to-pointer conversion failed"

    L.PtrToInt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (IntrinsicRepr nm) _, BVRepr w)
             | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer")
             , Just Refl <- testEquality w ptrWidth ->
                return x'
           _ -> fail "pointer-to-integer conversion failed"

    L.Trunc -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (BVRepr w) x'', (BVRepr w'))
             | Just LeqProof <- isPosNat w'
             , Just LeqProof <- testLeq (incNat w') w -> do
                 return (BaseExpr outty'' (App (C.BVTrunc w' w x'')))
           _ -> fail $ unwords ["invalid truncation:", show x, show outty]

    L.ZExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (BVRepr w) x'', (BVRepr w'))
             | Just LeqProof <- isPosNat w
             , Just LeqProof <- testLeq (incNat w) w' -> do
                 return (BaseExpr outty'' (App (C.BVZext w' w x'')))
           _ -> fail $ unwords ["invalid zero extension:", show x, show outty]

    L.SExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (BVRepr w) x'', BVRepr w')
             | Just LeqProof <- isPosNat w
             , Just LeqProof <- testLeq (incNat w) w' -> do
                 return (BaseExpr outty'' (App (C.BVSext w' w x'')))
           _ -> fail $ unwords ["invalid sign extension", show x, show outty]

    L.BitCast -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case asScalar x' of
           Scalar tyx _ | Just Refl <- testEquality tyx outty'' ->
             return x'
           _ -> fail $ unwords ["invalid bitcast", show x, show outty, show outty'']

    L.UiToFp -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (BVRepr w) x'', RealValRepr) -> do
             return $ BaseExpr RealValRepr
                        (App $ C.IntegerToReal $ App $ C.NatToInteger $ App $ C.BvToNat w x'')

           _ -> fail $ unwords ["Invalid uitofp:", show op, show x, show outty]

    L.SiToFp -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar (BVRepr w) x'', RealValRepr) -> do
             -- is the value negative?
             t <- AtomExpr <$> mkAtom (App $ C.BVSlt w x'' $ App $ C.BVLit w 0)
             -- unsigned value of the bitvector as a real
             v <- AtomExpr <$> mkAtom (App $ C.IntegerToReal $ App $ C.NatToInteger $ App $ C.BvToNat w x'')
             -- MAXINT as a real
             maxint <- AtomExpr <$> mkAtom (App $ C.RationalLit $ fromInteger $ maxUnsigned w)
             -- z = if neg then (v - MAXINT) else v
             let z = App $ C.RealIte t (App $ C.RealSub v maxint) v
             return $ BaseExpr RealValRepr z

           _ -> fail $ unwords ["Invalid uitofp:", show op, show x, show outty]

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
           _ -> fail $ unwords ["Invalid fptrunc:", show op, show x, show outty]

    L.FpExt -> do
       outty' <- liftMemType outty
       x' <- transTypedValue x
       llvmTypeAsRepr outty' $ \outty'' ->
         case (asScalar x', outty'') of
           (Scalar RealValRepr x'', RealValRepr) -> do
             return $ BaseExpr RealValRepr x''
           _ -> fail $ unwords ["Invalid fpext:", show op, show x, show outty]


-- | Do the heavy lifting of translating LLVM instructions to crucible code.
generateInstr :: forall h s ret
         . (?lc :: TyCtx.LLVMContext)
        => TypeRepr ret     -- ^ Type of the function return value
        -> L.BlockLabel     -- ^ The label of the current LLVM basic block
        -> L.Instr          -- ^ The instruction to translate
        -> (LLVMExpr s Expr -> LLVMGenerator h s ret ())
                            -- ^ A continuation to assign the produced value of this instruction to a register
        -> LLVMGenerator h s ret ()  -- ^ A continuation for translating the remaining statements in this function.
                                   --   Straightline instructions should enter this continuation,
                                   --   but block-terminating instructions should not.
        -> LLVMGenerator h s ret ()
generateInstr retType lab instr assign_f k =
  case instr of
    -- skip phi instructions, they are handled in definePhiBlock
    L.Phi _ _ -> k
    L.Comment _ -> k
    L.Unreachable -> reportError "LLVM unrechable code"

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
            y <- extractElt ty' (fromIntegral n) x'' i'
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
            y <- insertElt ty' (fromIntegral n) x'' v' i'
            assign_f y
            k

          _ -> fail $ unwords ["expected vector type in insertelement instruction:", show x]

    L.ShuffleVector _ _ _ ->
      fail "FIXME shuffleVector not implemented"

    L.Alloca tp num _align -> do
      -- ?? FIXME assert that the alignment value is appropriate...
      tp' <- liftMemType tp
      let dl = TyCtx.llvmDataLayout ?lc
      let tp_sz = memTypeSize dl tp'
      let tp_sz' = app $ C.BVLit ptrWidth $ fromIntegral tp_sz
      sz <- case num of
               Nothing -> return $ tp_sz'
               Just num' -> do
                  n <- transTypedValue num'
                  case n of
                     ZeroExpr _ -> return $ app $ C.BVLit ptrWidth 0
                     BaseExpr (BVRepr w) x
                        | Just Refl <- testEquality w ptrWidth ->
                             return $ app $ C.BVMul ptrWidth x tp_sz'
                     _ -> fail $ "Invalid alloca argument: " ++ show num
      p <- callAlloca sz
      assign_f (BaseExpr llvmPointerRepr p)
      k

    L.Load ptr _align -> do
      -- ?? FIXME assert that the alignment value is appropriate...
      tp'  <- liftMemType (L.typedType ptr)
      ptr' <- transValue tp' (L.typedValue ptr)
      case tp' of
        PtrType (MemType resTy) ->
          llvmTypeAsRepr resTy $ \expectTy -> do
            res <- callLoad resTy expectTy ptr'
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
           (fail "Pointer type does not mach value type in store instruction")
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
      assign_f (BaseExpr llvmPointerRepr p)
      k

    L.Conv op x outty -> do
      v <- translateConversion op x outty
      assign_f v
      k

    L.Call _tailCall fnTy@(L.PtrTo (L.FunTy _lretTy largTys varargs)) fn args

     -- Skip calls to debugging intrinsics.  We might want to support these in some way
     -- in the future.  However, they take metadata values as arguments, which
     -- would require some work to support.
     | L.ValSymbol nm <- fn
     , nm `elem` [ "llvm.dbg.declare"
                 , "llvm.dbg.value"
                 ] -> k

     -- For varargs functions, any arguments beyond the ones found in the function
     -- declaration are gathered into a vector of 'ANY' type, which is then passed
     -- as an additional final argument to the underlying Crucible function.  The
     -- called function is expected to know the types of these additional arguments,
     -- which it can unpack from the ANY values when it knows those types.
     | varargs -> do
           fnTy' <- liftMemType fnTy
           fn' <- transValue fnTy' fn
           args' <- mapM transTypedValue args
           let ?err = fail
           let (mainArgs, varArgs) = splitAt (length largTys) args'
           varArgs' <- unpackVarArgs varArgs
           unpackArgs mainArgs $ \argTypes mainArgs' ->
             case asScalar fn' of
                Scalar (FunctionHandleRepr argTypes' fnRetType) fn'' ->
                  case testEquality (argTypes Ctx.%> varArgsRepr) argTypes' of
                    Nothing -> fail $ unlines ["argument type mismatch in call to varargs function"
                                              , show fn, show args, show fnTy
                                              , show argTypes, show argTypes']
                    Just Refl -> do
                      ret <- call fn'' (mainArgs' Ctx.%> varArgs')
                      assign_f (BaseExpr fnRetType ret)
                      k
                _ -> fail $ unwords ["unsupported function value", show fn]

     -- Ordinary (non varargs) function call
     | otherwise -> do
           fnTy' <- liftMemType fnTy
           fn' <- transValue fnTy' fn
           args' <- mapM transTypedValue args
           let ?err = fail
           unpackArgs args' $ \argTypes args'' ->
              case asScalar fn' of
                Scalar (FunctionHandleRepr argTypes' fnRetType) fn'' ->
                  case testEquality argTypes argTypes' of
                     Nothing -> fail $ unwords ["argument type mismatch in call to"
                                               , show fn, show args, show fnTy]
                     Just Refl -> do
                         ret <- call fn'' args''
                         assign_f (BaseExpr fnRetType ret)
                         k

                _ -> fail $ unwords ["unsupported function value", show fn]

    L.Bit op x y -> do
           let bitop :: (1 <= w)
                     => NatRepr w
                     -> Expr s (BVType w)
                     -> Expr s (BVType w)
                     -> LLVMGenerator h s ret (Expr s (BVType w))
               bitop w a b =
                     case op of
                         L.And -> return $ App (C.BVAnd w a b)
                         L.Or  -> return $ App (C.BVOr w a b)
                         L.Xor -> return $ App (C.BVXor w a b)

                         L.Shl nuw nsw -> do
                           let wlit = App (C.BVLit w (natValue w))
                           assertExpr (App (C.BVUlt w b wlit))
                                      (litExpr "shift amount too large in shl")

                           res <- AtomExpr <$> mkAtom (App (C.BVShl w a b))

                           let nuwCond expr
                                | nuw = do
                                    m <- AtomExpr <$> mkAtom (App (C.BVLshr w res b))
                                    return $ App $ C.AddSideCondition (BaseBVRepr w)
                                       (App (C.BVEq w a m))
                                       "unsigned overflow on shl"
                                       expr
                                | otherwise = return expr

                           let nswCond expr
                                | nsw = do
                                    m <- AtomExpr <$> mkAtom (App (C.BVAshr w res b))
                                    return $ App $ C.AddSideCondition (BaseBVRepr w)
                                       (App (C.BVEq w a m))
                                       "signed overflow on shl"
                                       expr
                                | otherwise = return expr

                           nuwCond =<< nswCond =<< return res

                         L.Lshr exact -> do
                           let wlit = App (C.BVLit w (natValue w))
                           assertExpr (App (C.BVUlt w b wlit))
                                      (litExpr "shift amount too large in lshr")

                           res <- AtomExpr <$> mkAtom (App (C.BVLshr w a b))

                           let exactCond expr
                                | exact = do
                                    m <- AtomExpr <$> mkAtom (App (C.BVShl w res b))
                                    return $ App $ C.AddSideCondition (BaseBVRepr w)
                                       (App (C.BVEq w a m))
                                       "inexact logical right shift"
                                       expr
                                | otherwise = return expr

                           exactCond res

                         L.Ashr exact
                           | Just LeqProof <- isPosNat w -> do
                              let wlit = App (C.BVLit w (natValue w))
                              assertExpr (App (C.BVUlt w b wlit))
                                         (litExpr "shift amount too large in ashr")

                              res <- AtomExpr <$> mkAtom (App (C.BVAshr w a b))

                              let exactCond expr
                                   | exact = do
                                       m <- AtomExpr <$> mkAtom (App (C.BVShl w res b))
                                       return $ App $ C.AddSideCondition (BaseBVRepr w)
                                          (App (C.BVEq w a m))
                                          "inexact arithmetic right shift"
                                          expr
                                   | otherwise = return expr

                              exactCond res

                           | otherwise -> fail "cannot arithmetic right shift a 0-width integer"

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar ty@(BVRepr w)  x'',
              Scalar    (BVRepr w') y'')
               | Just Refl <- testEquality w w'
               , Just LeqProof <- isPosNat w -> do
                    ex <- bitop w x'' y''
                    assign_f (BaseExpr ty ex)
                    k

             _ -> fail $ unwords ["bitwise operation on unsupported values", show x, show y]

    L.Arith op x y -> do
           let intop :: (1 <= w)
                     => NatRepr w
                     -> Expr s (BVType w)
                     -> Expr s (BVType w)
                     -> LLVMGenerator h s ret (Expr s (BVType w))
               intop w a b =
                     case op of
                            L.Add nuw nsw -> do
                               let nuwCond expr
                                    | nuw = return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (notExpr (App (C.BVCarry w a b)))
                                               "unsigned overflow on addition"
                                               expr
                                    | otherwise = return expr

                               let nswCond expr
                                    | nsw = return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (notExpr (App (C.BVSCarry w a b)))
                                               "signed overflow on addition"
                                               expr
                                    | otherwise = return expr

                               nuwCond =<< nswCond (App (C.BVAdd w a b))

                            L.Sub nuw nsw -> do
                               let nuwCond expr
                                    | nuw = return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (notExpr (App (C.BVUlt w a b)))
                                               "unsigned overflow on subtraction"
                                               expr
                                    | otherwise = return expr

                               let nusCond expr
                                    | nsw = return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (notExpr (App (C.BVSBorrow w a b)))
                                               "signed overflow on subtraction"
                                               expr
                                    | otherwise = return expr

                               nuwCond =<< nusCond (App (C.BVSub w a b))

                            L.Mul nuw nsw -> do
                               let w' = addNat w w
                               Just LeqProof <- return $ isPosNat w'
                               Just LeqProof <- return $ testLeq (incNat w) w'

                               prod <- AtomExpr <$> mkAtom (App (C.BVMul w a b))
                               let nuwCond expr
                                    | nuw = do
                                        az <- AtomExpr <$> mkAtom (App (C.BVZext w' w a))
                                        bz <- AtomExpr <$> mkAtom (App (C.BVZext w' w b))
                                        wideprod <- AtomExpr <$> mkAtom (App (C.BVMul w' az bz))
                                        prodz <- AtomExpr <$> mkAtom (App (C.BVZext w' w prod))
                                        return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (App (C.BVEq w' wideprod prodz))
                                               "unsigned overflow on multiplication"
                                               expr
                                    | otherwise = return expr

                               let nswCond expr
                                    | nsw = do
                                        as <- AtomExpr <$> mkAtom (App (C.BVSext w' w a))
                                        bs <- AtomExpr <$> mkAtom (App (C.BVSext w' w b))
                                        wideprod <- AtomExpr <$> mkAtom (App (C.BVMul w' as bs))
                                        prods <- AtomExpr <$> mkAtom (App (C.BVSext w' w prod))
                                        return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (App (C.BVEq w' wideprod prods))
                                               "signed overflow on multiplication"
                                               expr
                                    | otherwise = return expr

                               nuwCond =<< nswCond prod

                            L.UDiv exact -> do
                               let z = App (C.BVLit w 0)
                               assertExpr (notExpr (App (C.BVEq w z b)))
                                          (litExpr "unsigned division-by-0")

                               q <- AtomExpr <$> mkAtom (App (C.BVUdiv w a b))

                               let exactCond expr
                                    | exact = do
                                        m <- AtomExpr <$> mkAtom (App (C.BVMul w q b))
                                        return $ App $ C.AddSideCondition (BaseBVRepr w)
                                               (App (C.BVEq w a m))
                                               "inexact result of unsigned division"
                                               expr
                                    | otherwise = return expr

                               exactCond q

                            L.SDiv exact
                              | Just LeqProof <- isPosNat w -> do
                                 let z      = App (C.BVLit w 0)
                                 let neg1   = App (C.BVLit w (-1))
                                 let minInt = App (C.BVLit w (minSigned w))
                                 assertExpr (notExpr (App (C.BVEq w z b)))
                                            (litExpr "signed division-by-0")
                                 assertExpr (notExpr ((App (C.BVEq w neg1 b))
                                                      .&&
                                                      (App (C.BVEq w minInt a)) ))
                                            (litExpr "signed division overflow (yes, really)")

                                 q <- AtomExpr <$> mkAtom (App (C.BVSdiv w a b))

                                 let exactCond expr
                                      | exact = do
                                          m <- AtomExpr <$> mkAtom (App (C.BVMul w q b))
                                          return $ App $ C.AddSideCondition (BaseBVRepr w)
                                                 (App (C.BVEq w a m))
                                                 "inexact result of signed division"
                                                 expr
                                      | otherwise = return expr

                                 exactCond q

                              | otherwise -> fail "cannot take the signed quotient of a 0-width bitvector"

                            L.URem -> do
                                 let z = App (C.BVLit w 0)
                                 assertExpr (notExpr (App (C.BVEq w z b)))
                                            (litExpr "unsigned division-by-0 in urem")
                                 return $ App (C.BVUrem w a b)

                            L.SRem
                              | Just LeqProof <- isPosNat w -> do
                                 let z      = App (C.BVLit w 0)
                                 let neg1   = App (C.BVLit w (-1))
                                 let minInt = App (C.BVLit w (minSigned w))
                                 assertExpr (notExpr (App (C.BVEq w z b)))
                                            (litExpr "signed division-by-0 in srem")
                                 assertExpr (notExpr ((App (C.BVEq w neg1 b))
                                                      .&&
                                                      (App (C.BVEq w minInt a)) ))
                                            (litExpr "signed division overflow in srem (yes, really)")

                                 return $ App (C.BVSrem w a b)

                              | otherwise -> fail "cannot take the signed remainder of a 0-width bitvector"

                            _ -> fail $ unwords ["unsupported integer arith operation", show op]

           let fop :: Expr s RealValType
                   -> Expr s RealValType
                   -> LLVMGenerator h s ret (Expr s RealValType)
               fop a b =
                     case op of
                        L.FAdd -> do
                          return $ App (C.RealAdd a b)
                        L.FSub -> do
                          return $ App (C.RealSub a b)
                        L.FMul -> do
                          return $ App (C.RealMul a b)
                            -- FIXME, implement remaining floating-point operations: FDiv and FRem
                        _ -> fail $ unwords ["unsupported floating-point arith operation", show op, show x, show y]

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar ty@(BVRepr w)  x'',
              Scalar    (BVRepr w') y'')
               | Just LeqProof <- isPosNat w
               , Just Refl <- testEquality w w' -> do
                 ex <- intop w x'' y''
                 assign_f (BaseExpr ty ex)
                 k
             (Scalar RealValRepr x'',
              Scalar RealValRepr y'') -> do
                 ex <- fop x'' y''
                 assign_f (BaseExpr RealValRepr ex)
                 k

             (Scalar (RecursiveRepr nm) x'',
              Scalar (BVRepr w) y'')
                | Just Refl <- testEquality w ptrWidth
                , Just Refl <- testEquality nm  (knownSymbol :: SymbolRepr "LLVM_pointer") ->
                    case op of
                      L.Add _ _ -> do
                        ex <- callPtrAddOffset x'' y''
                        assign_f (BaseExpr llvmPointerRepr ex)
                        k
                      L.Sub _ _ -> do
                        let off = App (C.BVSub w (App $ C.BVLit w 0) y'')
                        ex <- callPtrAddOffset x'' off
                        assign_f (BaseExpr llvmPointerRepr ex)
                        k

                      _ -> fail $ unwords ["Unsupported pointer arithmetic operation"]

             (Scalar (BVRepr w) x'',
              Scalar (RecursiveRepr nm) y'')
                | Just Refl <- testEquality w ptrWidth
                , Just Refl <- testEquality nm  (knownSymbol :: SymbolRepr "LLVM_pointer") ->
                    case op of
                      L.Add _ _ -> do
                        ex <- callPtrAddOffset y'' x''
                        assign_f (BaseExpr llvmPointerRepr ex)
                        k
                      _ -> fail $ unwords ["Unsupported pointer arithmetic operation"]

             (Scalar (RecursiveRepr nm) x'',
              Scalar (RecursiveRepr nm') y'')
                | Just Refl <- testEquality nm  (knownSymbol :: SymbolRepr "LLVM_pointer")
                , Just Refl <- testEquality nm' (knownSymbol :: SymbolRepr "LLVM_pointer") ->
                    case op of
                      L.Sub _ _ -> do
                        ex <- callPtrSubtract x'' y''
                        assign_f (BaseExpr (BVRepr ptrWidth) ex)
                        k
                      _ -> fail $ unwords ["Unsupported pointer arithmetic operation"]

             _ -> fail $ unwords ["arithmetic operation on unsupported values", show x, show y]

    L.FCmp op x y -> do
           let cmpf :: Expr s RealValType
                    -> Expr s RealValType
                    -> Expr s BoolType
               cmpf a b =
                  -- We assume that values are never NaN, so the ordered and unordered
                  -- operations are the same.
                  case op of
                    L.Ftrue  -> App (C.BoolLit True)
                    L.Ffalse -> App (C.BoolLit False)
                    L.Foeq   -> App (C.RealEq a b)
                    L.Fueq   -> App (C.RealEq a b)
                    L.Fone   -> App $ C.Not $ App (C.RealEq a b)
                    L.Fune   -> App $ C.Not $ App (C.RealEq a b)
                    L.Folt   -> App (C.RealLt a b)
                    L.Fult   -> App (C.RealLt a b)
                    L.Fogt   -> App (C.RealLt b a)
                    L.Fugt   -> App (C.RealLt b a)
                    L.Fole   -> App $ C.Not $ App (C.RealLt b a)
                    L.Fule   -> App $ C.Not $ App (C.RealLt b a)
                    L.Foge   -> App $ C.Not $ App (C.RealLt a b)
                    L.Fuge   -> App $ C.Not $ App (C.RealLt a b)
                    L.Ford   -> App (C.BoolLit True)  -- True if a <> QNAN and b <> QNAN
                    L.Funo   -> App (C.BoolLit False) -- True if a == QNNA or b == QNAN

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar RealValRepr x'',
              Scalar RealValRepr y'') -> do
                assign_f (BaseExpr (BVRepr (knownNat :: NatRepr 1))
                                   (App (C.BoolToBV knownNat (cmpf  x'' y''))))
                k

             _ -> fail $ unwords ["Floating point comparison on incompatible values", show x, show y]

    L.ICmp op x y -> do
           let opf :: (1 <= w)
                   => NatRepr w
                   -> Expr s (BVType w)
                   -> Expr s (BVType w)
                   -> Expr s BoolType
               opf w a b =
                  case op of
                     L.Ieq -> App (C.BVEq w a b)
                     L.Ine -> App (C.Not (App (C.BVEq w a b)))
                     L.Iult -> App (C.BVUlt w a b)
                     L.Iule -> App (C.BVUle w a b)
                     L.Iugt -> App (C.BVUlt w b a)
                     L.Iuge -> App (C.BVUle w b a)
                     L.Islt -> App (C.BVSlt w a b)
                     L.Isle -> App (C.BVSle w a b)
                     L.Isgt -> App (C.BVSlt w b a)
                     L.Isge -> App (C.BVSle w b a)

           x' <- transTypedValue x
           y' <- transTypedValue (L.Typed (L.typedType x) y)
           case (asScalar x', asScalar y') of
             (Scalar (BVRepr w) x'', Scalar (BVRepr w') y'')
               | Just Refl <- testEquality w w'
               , Just LeqProof <- isPosNat w -> do
                    assign_f (BaseExpr
                                   (BVRepr (knownNat :: NatRepr 1))
                                   (App (C.BoolToBV knownNat (opf w x'' y''))))
                    k
             (Scalar (RecursiveRepr sx) x'', Scalar (RecursiveRepr sy) y'')
               | Just Refl <- testEquality sx (knownSymbol :: SymbolRepr "LLVM_pointer")
               , Just Refl <- testEquality sy (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
                   pEq <- litExpr . llvmPtrEq . memModelOps . llvmContext <$> get
                   pLe <- litExpr . llvmPtrLe . memModelOps . llvmContext <$> get
                   memVar <- llvmMemVar . memModelOps . llvmContext <$> get
                   mem <- readGlobal memVar
                   res <-
                     case op of
                       L.Ieq -> do
                         isEq <- call pEq (Ctx.empty Ctx.%> mem Ctx.%> x'' Ctx.%> y'')
                         return $ isEq
                       L.Ine -> do
                         isEq <- call pEq (Ctx.empty Ctx.%> mem Ctx.%> x'' Ctx.%> y'')
                         return $ App (C.Not isEq)
                       L.Iule -> do
                         isLe <- call pLe (Ctx.empty Ctx.%> mem Ctx.%> x'' Ctx.%> y'')
                         return $ isLe
                       L.Iult -> do
                         isGe <- call pLe (Ctx.empty Ctx.%> mem Ctx.%> y'' Ctx.%> x'')
                         return $ App (C.Not isGe)
                       L.Iuge -> do
                         isGe <- call pLe (Ctx.empty Ctx.%> mem Ctx.%> y'' Ctx.%> x'')
                         return $ isGe
                       L.Iugt -> do
                         isLe <- call pLe (Ctx.empty Ctx.%> mem Ctx.%> x'' Ctx.%> y'')
                         return $ App (C.Not isLe)
                       _ -> fail $ unwords ["signed comparison on pointer values", show x, show y]
                   assign_f (BaseExpr (BVRepr (knownNat :: NatRepr 1))
                                      (App (C.BoolToBV knownNat res)))
                   k

             -- Special case: a pointer can be compared for equality with an integer, as long as
             -- that integer is 0, representing the null pointer.
             (Scalar (RecursiveRepr sx) x'', Scalar (BVRepr wy) y'')
               | Just Refl <- testEquality ptrWidth wy
               , Just Refl <- testEquality sx (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
                   pIsNull <- litExpr . llvmPtrIsNull . memModelOps . llvmContext <$> get
                   assertExpr (App (C.BVEq ptrWidth y'' (App (C.BVLit ptrWidth 0))))
                              "Attempted to compare a pointer to a non-0 integer value"
                   res <- case op of
                     L.Ieq  -> do
                        res <- call pIsNull (Ctx.empty Ctx.%> x'')
                        return res
                     L.Ine  -> do
                        res <- call pIsNull (Ctx.empty Ctx.%> x'')
                        return (App (C.Not res))
                     _ -> fail $ unwords ["arithmetic comparison on incompatible values", show x, show y]
                   assign_f (BaseExpr (BVRepr (knownNat :: NatRepr 1)) (App (C.BoolToBV knownNat res)))
                   k

             -- Symmetric special case to the above
             (Scalar (BVRepr wx) x'', Scalar (RecursiveRepr sy) y'')
               | Just Refl <- testEquality ptrWidth wx
               , Just Refl <- testEquality sy (knownSymbol :: SymbolRepr "LLVM_pointer") -> do
                   pIsNull <- litExpr . llvmPtrIsNull . memModelOps . llvmContext <$> get
                   assertExpr (App (C.BVEq ptrWidth x'' (App (C.BVLit ptrWidth 0))))
                              "Attempted to compare a pointer to a non-0 integer value"
                   res <- case op of
                     L.Ieq  -> do
                        res <- call pIsNull (Ctx.empty Ctx.%> y'')
                        return res
                     L.Ine  -> do
                        res <- call pIsNull (Ctx.empty Ctx.%> y'')
                        return (App (C.Not res))
                     _ -> fail $ unwords ["arithmetic comparison on incompatible values", show x, show y]
                   assign_f (BaseExpr (BVRepr (knownNat :: NatRepr 1)) (App (C.BoolToBV knownNat res)))
                   k

             _ -> fail $ unwords ["arithmetic comparison on incompatible values", show x, show y]

    -- FIXME, reimplement the select operation using expression if/then/else rather than branching...
    L.Select c x y -> do
         c' <- transTypedValue c
         x' <- transTypedValue x
         y' <- transTypedValue (L.Typed (L.typedType x) y)
         case asScalar c' of
           Scalar (BVRepr w) e -> do
             let e' = case isPosNat w of
                        Just LeqProof -> App (C.BVNonzero w e)
                        Nothing       -> App (C.BoolLit False)
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

           _ -> fail "expected boolean condition on select"

    L.Jump l' -> definePhiBlock lab l'

    L.Br v l1 l2 -> do
        v' <- transTypedValue v
        case asScalar v' of
          Scalar (BVRepr w) e -> do
            let e' = case isPosNat w of
                       Just LeqProof -> App (C.BVNonzero w e)
                       Nothing -> App (C.BoolLit False)
            a' <- mkAtom e'
            endNow $ \_ -> do
              phi1 <- newLabel
              phi2 <- newLabel
              endCurrentBlock (Br a' phi1 phi2)

              defineBlock phi1 (definePhiBlock lab l1)
              defineBlock phi2 (definePhiBlock lab l2)

          _ -> fail "expected boolean condition on branch!"

    L.Switch x def branches -> do
        x' <- transTypedValue x
        case asScalar x' of
          Scalar (BVRepr w) x'' | Just LeqProof <- isPosNat w ->
            buildSwitch w x'' lab def branches
          _ -> fail $ unwords ["expected integer value in switch", show instr]

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
                       returnFromFunction (App C.EmptyApp)
                    Nothing -> fail $ unwords ["tried to void return from non-void function", show retType]

    _ -> reportError $ App $ C.TextLit $ Text.pack $ unwords ["unsupported instruction", show instr]

-- | Build a switch statement by decomposing it into a linear sequence of branches.
--   FIXME? this could be more efficent if we sort the list and do binary search instead...
buildSwitch :: (1 <= w, ?lc :: TyCtx.LLVMContext)
            => NatRepr w
            -> Expr s (BVType w) -- ^ The expression to switch on
            -> L.BlockLabel        -- ^ The label of the current basic block
            -> L.BlockLabel        -- ^ The label of the default basic block if no other branch applies
            -> [(Integer, L.BlockLabel)] -- ^ The switch labels
            -> LLVMGenerator h s ret ()
buildSwitch _ _  curr_lab def [] =
   definePhiBlock curr_lab def
buildSwitch w ex curr_lab def ((i,l):bs) = do
   let test = App $ C.BVEq w ex $ App $ C.BVLit w i
   test_a <- mkAtom test
   endNow $ \_ -> do
     t_id <- newLabel
     f_id <- newLabel
     endCurrentBlock $! Br test_a t_id f_id
     defineBlock t_id (definePhiBlock curr_lab l)
     defineBlock f_id (buildSwitch w ex curr_lab def bs)

-- | Generate crucible code for each LLVM statement in turn.
generateStmts
        :: (?lc :: TyCtx.LLVMContext)
        => TypeRepr ret
        -> L.BlockLabel
        -> [L.Stmt]
        -> LLVMGenerator h s ret ()
generateStmts retType lab = go
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

setLocation
  :: (?lc :: TyCtx.LLVMContext)
  => [(String,L.ValMd)]
  -> LLVMGenerator h s ret ()
setLocation [] = return ()
setLocation (("dbg",L.ValMdLoc dl):_) = do
   let ln   = fromIntegral $ L.dlLine dl
       col  = fromIntegral $ L.dlCol dl
       file = Text.pack $ findFile $ L.dlScope dl
    in setPosition (SourcePos file ln col)
setLocation (_:xs) = setLocation xs

findFile :: (?lc :: TyCtx.LLVMContext) => L.ValMd -> String
findFile (L.ValMdRef x) =
  case TyCtx.lookupMetadata x of
    Just (L.ValMdNode (_:Just (L.ValMdRef y):_)) ->
      case TyCtx.lookupMetadata y of
        Just (L.ValMdNode [Just (L.ValMdString fname), Just (L.ValMdString _fpath)]) -> fname
        _ -> ""
    _ -> ""
findFile _ = ""

-- | Lookup the block info for the given LLVM block and then define a new crucible block
--   by translating the given LLVM statements.
defineLLVMBlock
        :: (?lc :: TyCtx.LLVMContext)
        => TypeRepr ret
        -> Map L.BlockLabel (LLVMBlockInfo s)
        -> L.BasicBlock
        -> LLVMEnd h s init ret ()
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
genDefn :: (?lc :: TyCtx.LLVMContext)
        => L.Define
        -> TypeRepr ret
        -> Generator h s LLVMState ret (Expr s ret)
genDefn defn retType =
  case L.defBody defn of
    [] -> fail "LLVM define with no blocks!"
    ( L.BasicBlock{ L.bbLabel = Nothing } : _ ) -> fail $ unwords ["entry block has no label"]
    ( L.BasicBlock{ L.bbLabel = Just entry_lab } : _ ) -> do
      callPushFrame
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
transDefine :: LLVMContext
            -> L.Define
            -> ST h (L.Symbol, AnyCFG)
transDefine ctx d = do
  let sym = L.defName d
  let ?lc = llvmTypeCtx ctx
  case ctx^.symbolMap^.at sym of
    Nothing -> fail "internal error: Could not find symbol"
    Just (LLVMHandleInfo _ (h :: FnHandle args ret)) -> do
      let argTypes = handleArgTypes h
      let retType  = handleReturnType h
      let def :: FunctionDef h LLVMState args ret
          def inputs = (s, f)
            where s = initialState d ctx argTypes inputs
                  f = genDefn d retType
      (SomeCFG g,[]) <- defineFunction InternalPos h def
      case toSSA g of
        C.SomeCFG g_ssa -> return (sym, AnyCFG g_ssa)

------------------------------------------------------------------------
-- initMemProc

genGlobalInit
            :: (?lc :: TyCtx.LLVMContext)
            => (L.Symbol, MemType, Maybe L.Value)
            -> Generator h s LLVMState ret ()
genGlobalInit (_sym,_ty,Nothing) =
  return ()
genGlobalInit (sym,ty,Just v) = do
  ptr <- transValue ty (L.ValSymbol sym)
  v'  <- transValue ty v
  callStore ty ptr v'


initMemProc :: forall s
            .  HandleAllocator s
            -> LLVMContext
            -> L.Module
            -> ST s (C.SomeCFG EmptyCtx UnitType)
initMemProc halloc ctx m = do
   let gs = L.modGlobals m
   let ?lc = llvmTypeCtx ctx
   h <- mkHandle halloc "_llvm_mem_init"
   gs_alloc <- mapM (\g -> do
                        ty <- liftMemType $ L.globalType g
                        return (L.globalSym g, ty, L.globalValue g))
                    gs
   let def :: FunctionDef s LLVMState EmptyCtx UnitType
       def _inputs = (st, f)
              where st = LLVMState
                         { _identMap = Map.empty
                         , _blockInfoMap = Map.empty
                         , llvmContext = ctx
                         }
                    f = do mapM_ genGlobalInit gs_alloc
                           return (App C.EmptyApp)

   (SomeCFG g,[]) <- defineFunction InternalPos h def
   return $! toSSA g

------------------------------------------------------------------------
-- translateModule

-- | Insert a declaration into the symbol handleMap if a handle for that
--   symbol does not already exist.
insDeclareHandle :: HandleAllocator s
                 -> LLVMContext
                 -> L.Declare
                 -> ST s LLVMContext
insDeclareHandle halloc ctx decl = do
   let s@(L.Symbol sbl) = L.decName decl
   case Map.lookup s (ctx^.symbolMap) of
     Just (LLVMHandleInfo _decl' _) ->
       -- FIXME check that decl and decl' are compatible...
       return ctx
     Nothing -> do
       let ?lc = llvmTypeCtx ctx
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
                -> ST s (LLVMContext, ModuleTranslation)
translateModule halloc m = do
  ctx0 <- mkLLVMContext halloc m
  -- Add handles for all functions declared in module.
  ctx <- foldM (insDeclareHandle halloc) ctx0 (allModuleDeclares m)
  -- Translate definitions
  pairs <- mapM (transDefine ctx) (L.modDefines m)
  -- Return result.
  initMem <- initMemProc halloc ctx m
  return (ctx, ModuleTranslation { cfgMap = Map.fromList pairs
                                 , initMemoryCFG = initMem
                                 })

-------------------------------------------------------------------------
-- initalizeMemory

-- | Build the initial memory for an LLVM program.  Note, this process
-- allocates space for global variables, but does not set their
-- initial values.  Run the `initMemoryCFG` procedure of the
-- `ModuleTranslation` produced by `translateModule` to set
-- the values of global variables.
initalizeMemory
   :: IsSymInterface sym
   => sym
   -> LLVMContext
   -> L.Module
   -> IO (MemImpl sym PtrWidth)
initalizeMemory sym llvm_ctx m = do
   --putStrLn "INIT MEMORY"
   let gs = L.modGlobals m
   let ?lc = llvmTypeCtx llvm_ctx
   let dl = TyCtx.llvmDataLayout ?lc
   gs_alloc <- mapM (\g -> do
                        ty <- liftMemType $ L.globalType g
                        let sz = memTypeSize dl ty
                        return (L.globalSym g, sz))
                    gs
   allocGlobals sym gs_alloc =<< emptyMem
