--------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Internal
-- Description      : Datastructures used while translating LLVM modules
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines datastructures used only during the translation of LLVM
-- modules into Crucible CFGs.
--------------------------------------------------------------

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Translation.Internal where

import Control.Monad.Except
import Control.Monad.Fail hiding (fail)
import Control.Lens hiding (op, (:>) )
import Data.Foldable (toList)
import qualified Data.List as List
import           Data.Maybe
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Some

import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.LLVM.Extension (ArchWidth)
import           Lang.Crucible.LLVM.Intrinsics
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.Types
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx

-------------------------------------------------------------------------
-- LLVMExpr

-- | A monad providing state and continuations for translating LLVM expressions
-- to CFGs.
type LLVMGenerator h s arch ret a =
  (?lc :: TyCtx.LLVMContext, HasPtrWidth (ArchWidth arch)) =>
    Generator (LLVM arch) h s (LLVMState arch) ret a

-- | @LLVMGenerator@ without the constraint, can be nested further inside monads.
type LLVMGenerator' h s arch ret a =
  Generator (LLVM arch) h s (LLVMState arch) ret a

-------------------------------------------------------------------------
-- LLVMExpr

-- | An intermediate form of LLVM expressions that retains some structure
--   that would otherwise be more difficult to retain if we translated directly
--   into crucible expressions.
data LLVMExpr s arch where
   BaseExpr   :: TypeRepr tp -> Expr (LLVM arch) s tp -> LLVMExpr s arch
   ZeroExpr   :: MemType -> LLVMExpr s arch
   UndefExpr  :: MemType -> LLVMExpr s arch
   VecExpr    :: MemType -> Seq (LLVMExpr s arch) -> LLVMExpr s arch
   StructExpr :: Seq (MemType, LLVMExpr s arch) -> LLVMExpr s arch

instance Show (LLVMExpr s arch) where
  show (BaseExpr _ x)   = C.showF x
  show (ZeroExpr mt)    = "<zero :" ++ show mt ++ ">"
  show (UndefExpr mt)   = "<undef :" ++ show mt ++ ">"
  show (VecExpr _mt xs) = "[" ++ concat (List.intersperse ", " (map show (toList xs))) ++ "]"
  show (StructExpr xs)  = "{" ++ concat (List.intersperse ", " (map f (toList xs))) ++ "}"
    where f (_mt,x) = show x

instrResultType ::
  (?lc :: TyCtx.LLVMContext, MonadFail m, HasPtrWidth wptr) =>
  L.Instr ->
  m MemType
instrResultType instr =
  case instr of
    L.Arith _ x _ -> liftMemType (L.typedType x)
    L.Bit _ x _   -> liftMemType (L.typedType x)
    L.Conv _ _ ty -> liftMemType ty
    L.Call _ (L.PtrTo (L.FunTy ty _ _)) _ _ -> liftMemType ty
    L.Call _ ty _ _ ->  fail $ unwords ["unexpected function type in call:", show ty]
    L.Invoke (L.FunTy ty _ _) _ _ _ _ -> liftMemType ty
    L.Invoke ty _ _ _ _ -> fail $ unwords ["unexpected function type in invoke:", show ty]
    L.Alloca ty _ _ -> liftMemType (L.PtrTo ty)
    L.Load x _ _ -> case L.typedType x of
                   L.PtrTo ty -> liftMemType ty
                   _ -> fail $ unwords ["load through non-pointer type", show (L.typedType x)]
    L.ICmp _ _ _ -> liftMemType (L.PrimType (L.Integer 1))
    L.FCmp _ _ _ -> liftMemType (L.PrimType (L.Integer 1))
    L.Phi tp _   -> liftMemType tp

    L.GEP inbounds base elts ->
       do gepRes <- runExceptT (translateGEP inbounds base elts)
          case gepRes of
            Left err -> fail err
            Right (GEPResult lanes tp _gep) ->
              let n = fromInteger (natValue lanes) in
              if n == 1 then
                return (PtrType (MemType tp))
              else
                return (VecType n (PtrType (MemType tp)))

    L.Select _ x _ -> liftMemType (L.typedType x)

    L.ExtractValue x idxes -> liftMemType (L.typedType x) >>= go idxes
         where go [] tp = return tp
               go (i:is) (ArrayType n tp')
                   | i < fromIntegral n = go is tp'
                   | otherwise = fail $ unwords ["invalid index into array type", showInstr instr]
               go (i:is) (StructType si) =
                      case siFields si V.!? (fromIntegral i) of
                        Just fi -> go is (fiType fi)
                        Nothing -> error $ unwords ["invalid index into struct type", showInstr instr]
               go _ _ = fail $ unwords ["invalid type in extract value instruction", showInstr instr]

    L.InsertValue x _ _ -> liftMemType (L.typedType x)

    L.ExtractElt x _ ->
       do tp <- liftMemType (L.typedType x)
          case tp of
            VecType _n tp' -> return tp'
            _ -> fail $ unwords ["extract element of non-vector type", showInstr instr]

    L.InsertElt x _ _ -> liftMemType (L.typedType x)

    L.ShuffleVector x _ i ->
      do xtp <- liftMemType (L.typedType x)
         itp <- liftMemType (L.typedType i)
         case (xtp, itp) of
           (VecType _n ty, VecType m _) -> return (VecType m ty)
           _ -> fail $ unwords ["invalid shufflevector:", showInstr instr]

    L.LandingPad x _ _ _ -> liftMemType x

    _ -> fail $ unwords ["instrResultType, unsupported instruction:", showInstr instr]


------------------------------------------------------------------------
-- LLVMState

-- | Maps identifiers to an associated register or defined expression.
type IdentMap s = Map L.Ident (Either (Some (Reg s)) (Some (Atom s)))

data LLVMState arch s
   = LLVMState
   { -- | Map from identifiers to associated register shape
     _identMap :: !(IdentMap s)
   , _blockInfoMap :: !(Map L.BlockLabel (LLVMBlockInfo s))
   , llvmContext :: LLVMContext arch
   }

identMap :: Simple Lens (LLVMState arch s) (IdentMap s)
identMap = lens _identMap (\s v -> s { _identMap = v })

blockInfoMap :: Simple Lens (LLVMState arch s) (Map L.BlockLabel (LLVMBlockInfo s))
blockInfoMap = lens _blockInfoMap (\s v -> s { _blockInfoMap = v })

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

buildBlockInfoMap :: L.Define -> LLVMGenerator h s arch ret (Map L.BlockLabel (LLVMBlockInfo s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: L.BasicBlock -> LLVMGenerator h s arch ret (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let Just blk_lbl = L.bbLabel bb
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_label = lab
                                })

-- Given the statements in a basic block, find all the phi instructions and
-- compute the list of assignments that must be made for each predecessor block.
buildPhiMap :: [L.Stmt] -> Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value))
buildPhiMap ss = go ss Map.empty
 where go (L.Result ident (L.Phi tp xs) _ : stmts) m = go stmts (go' ident tp xs m)
       go _ m = m

       f x mseq = Just (fromMaybe Seq.empty mseq Seq.|> x)

       go' ident tp ((v, lbl) : xs) m = go' ident tp xs (Map.alter (f (ident,tp,v)) lbl m)
       go' _ _ [] m = m
