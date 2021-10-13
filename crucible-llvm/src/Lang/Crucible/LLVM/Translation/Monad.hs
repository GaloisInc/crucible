-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Monad
-- Description      : Translation monad for LLVM and support operations
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-----------------------------------------------------------------------
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Translation.Monad
  ( -- * Generator monad
    LLVMGenerator
  , LLVMGenerator'
  , LLVMState(..)
  , identMap
  , blockInfoMap
  , buildBlockInfoMap
  , translationWarnings
  , functionSymbol
  , addWarning
  , IdentMap
  , LLVMBlockInfo(..)
  , initialState

  , getMemVar

    -- * Malformed modules
  , MalformedLLVMModule(..)
  , malformedLLVMModule
  , renderMalformedLLVMModule

    -- * LLVMContext
  , LLVMContext(..)
  , llvmTypeCtx
  , mkLLVMContext

  , useTypedVal
  ) where

import Control.Lens hiding (op, (:>), to, from )
import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.IORef (IORef, modifyIORef)
import Data.List (foldl')
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some

import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.Panic ( panic )

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MalformedLLVMModule
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.Types

------------------------------------------------------------------------
-- ** LLVMContext

-- | Information about the LLVM module.
data LLVMContext arch
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     llvmArch       :: ArchRepr arch
   , llvmPtrWidth   :: forall a. (16 <= (ArchWidth arch) => NatRepr (ArchWidth arch) -> a) -> a
   , llvmMemVar     :: GlobalVar Mem
   , _llvmTypeCtx   :: TypeContext
     -- | For each global variable symbol, compute the set of
     --   aliases to that symbol
   , llvmGlobalAliases   :: Map L.Symbol (Set L.GlobalAlias)
     -- | For each function symbol, compute the set of
     --   aliases to that symbol
   , llvmFunctionAliases :: Map L.Symbol (Set L.GlobalAlias)
   }

llvmTypeCtx :: Simple Lens (LLVMContext arch) TypeContext
llvmTypeCtx = lens _llvmTypeCtx (\s v -> s{ _llvmTypeCtx = v })

mkLLVMContext :: GlobalVar Mem
              -> L.Module
              -> IO (Some LLVMContext)
mkLLVMContext mvar m = do
  let (errs, typeCtx) = typeContextFromModule m
  unless (null errs) $
    malformedLLVMModule "Failed to construct LLVM type context" errs
  let dl = llvmDataLayout typeCtx

  case mkNatRepr (ptrBitwidth dl) of
    Some (wptr :: NatRepr wptr) | Just LeqProof <- testLeq (knownNat @16) wptr ->
      withPtrWidth wptr $
        do let archRepr = X86Repr wptr -- FIXME! we should select the architecture based on
                                       -- the target triple, but llvm-pretty doesn't capture this
                                       -- currently.
           let ctx :: LLVMContext (X86 wptr)
               ctx = LLVMContext
                     { llvmArch     = archRepr
                     , llvmMemVar   = mvar
                     , llvmPtrWidth = \x -> x wptr
                     , _llvmTypeCtx = typeCtx
                     , llvmGlobalAliases = mempty   -- these are computed later
                     , llvmFunctionAliases = mempty -- these are computed later
                     }
           return (Some ctx)
    _ ->
      fail ("Cannot load LLVM bitcode file with illegal pointer width: " ++ show (dl^.ptrSize))


-- | A monad providing state and continuations for translating LLVM expressions
-- to CFGs.
type LLVMGenerator s arch ret a =
  (?lc :: TypeContext, HasPtrWidth (ArchWidth arch)) =>
    Generator LLVM s (LLVMState arch) ret IO a

-- | @LLVMGenerator@ without the constraint, can be nested further inside monads.
type LLVMGenerator' s arch ret =
  Generator LLVM s (LLVMState arch) ret IO


-- LLVMState

getMemVar :: LLVMGenerator s arch reg (GlobalVar Mem)
getMemVar = llvmMemVar . llvmContext <$> get

-- | Maps identifiers to an associated register or defined expression.
type IdentMap s = Map L.Ident (Either (Some (Reg s)) (Some (Atom s)))

data LLVMState arch s
   = LLVMState
   { -- | Map from identifiers to associated register shape
     _identMap :: !(IdentMap s)
   , _blockInfoMap :: !(Map L.BlockLabel (LLVMBlockInfo s))
   , llvmContext :: LLVMContext arch
   , _translationWarnings :: IORef [(L.Symbol, Position, Text)]
   , _functionSymbol :: L.Symbol
   }

identMap :: Lens' (LLVMState arch s) (IdentMap s)
identMap = lens _identMap (\s v -> s { _identMap = v })

blockInfoMap :: Lens' (LLVMState arch s) (Map L.BlockLabel (LLVMBlockInfo s))
blockInfoMap = lens _blockInfoMap (\s v -> s { _blockInfoMap = v })

translationWarnings :: Lens' (LLVMState arch s) (IORef [(L.Symbol,Position,Text)])
translationWarnings = lens _translationWarnings (\s v -> s { _translationWarnings = v })

functionSymbol :: Lens' (LLVMState arch s) L.Symbol
functionSymbol = lens _functionSymbol (\s v -> s{ _functionSymbol = v })

addWarning :: Text -> LLVMGenerator s arch ret ()
addWarning warn =
  do r <- use translationWarnings
     s <- use functionSymbol
     p <- getPosition
     liftIO (modifyIORef r ((s,p,warn):))

-- | Information about an LLVM basic block computed before be we begin the
--   translation proper.
data LLVMBlockInfo s
  = LLVMBlockInfo
    {
      -- | The crucible block label corresponding to this LLVM block
      block_label :: Label s

      -- | The computed "use" set for this block.  This is the set
      -- of identifiers that must be assigned prior to jumping to this
      -- block. They are either used directly in this block or used
      -- by a successor of this block.  Note! "metadata" nodes
      -- do not contribute to the use set.  Note! values referenced
      -- in phi nodes are also not included in this set, they are instead
      -- handled when examining the terminal statements of predecessor blocks.
    , block_use_set :: !(Set L.Ident)

      -- | The predecessor blocks to this block (i.e., all those blocks
      -- that can jump to this one).
    , block_pred_set :: !(Set L.BlockLabel)

      -- | The successor blocks to this block (i.e., all those blocks
      -- that this block can jump to).
    , block_succ_set :: !(Set L.BlockLabel)

      -- | The statements defining this block
    , block_body :: ![L.Stmt]

      -- | Map from labels to assignments that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map :: !(Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value)))
    }

buildBlockInfoMap :: L.Define -> LLVMGenerator s arch ret (Map L.BlockLabel (LLVMBlockInfo s))
buildBlockInfoMap d =
  do bim0 <- Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)
     let bim1 = updatePredSets bim0
     return (computeUseSets bim1)


buildBlockInfo :: L.BasicBlock -> LLVMGenerator s arch ret (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let succ_set = buildSuccSet (L.bbStmts bb)
  let blk_lbl = case L.bbLabel bb of
                  Just l -> l
                  Nothing -> panic "crucible-llvm:Translation.buildBlockInfo"
                             [ "unable to obtain label from BasicBlock" ]
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_use_set = mempty
                                , block_pred_set = mempty
                                , block_succ_set = succ_set
                                , block_body = L.bbStmts bb
                                , block_label = lab
                                })

-- | Compute predecessor sets from the successor sets already computed in @buildBlockInfo@
updatePredSets :: Map L.BlockLabel (LLVMBlockInfo s) -> Map L.BlockLabel (LLVMBlockInfo s)
updatePredSets bim0 = foldl' upd bim0 predEdges
  where
   upd bim (to,from) = Map.adjust (\bi -> bi{ block_pred_set = Set.insert from (block_pred_set bi) }) to bim

   predEdges =
     [ (to,from) | (from, bi) <- Map.assocs bim0
                 , to <- Set.elems (block_succ_set bi)
     ]

-- | Given the statements in a basic block, find all the successor blocks,
-- i.e. the blocks this one may jump to.
buildSuccSet :: [L.Stmt] -> Set L.BlockLabel
buildSuccSet [] = mempty
buildSuccSet (s:ss) =
  case L.stmtInstr s of
    L.Ret{} -> mempty
    L.RetVoid -> mempty
    L.Unreachable -> mempty
    L.Jump l -> Set.singleton l
    L.Br _ l1 l2 -> Set.fromList [l1,l2]
    L.Invoke _ _ _ l1 l2 -> Set.fromList [l1,l2]
    L.IndirectBr _ ls -> Set.fromList ls
    L.Switch _ ldef ls -> Set.fromList (ldef:map snd ls)
    _ -> buildSuccSet ss

-- | Compute use sets for each basic block.  This is essentially a backward fixpoint
--   computation based on the identifiers used in the block statements.  We iterate the
--   use/def transfer function until no more changes are made.  Because it is a backward
--   analysis, we (heuristicly) examine the blocks in descending order, and re-add blocks
--   to the workset based on predecessor maps.
computeUseSets :: Map L.BlockLabel (LLVMBlockInfo s) -> Map L.BlockLabel (LLVMBlockInfo s)
computeUseSets bim0 = loop bim0 (Map.keysSet bim0)
  where
  loop bim ws =
    case Set.maxView ws of
      Nothing -> bim
      Just (l, ws') ->
        case Map.lookup l bim of
          Nothing -> panic "computeUseSets" ["Could not find label", show l]
          Just bi ->
            case updateUseSet l bi bim of
              Nothing -> loop bim ws'
              Just bi' ->
                loop (Map.insert l bi' bim) (Set.union ws (block_pred_set bi'))

-- Run the use/def transfer function on the block body and update the block info if
-- any changes are detected
updateUseSet :: L.BlockLabel -> LLVMBlockInfo s -> Map L.BlockLabel (LLVMBlockInfo s) -> Maybe (LLVMBlockInfo s)
updateUseSet lab bi bim = if newuse == block_use_set bi then Nothing else Just bi{ block_use_set = newuse }
  where
  newuse = loop (block_body bi)

  loop [] = mempty
  loop (L.Result nm i _md:ss) = Set.union (instrUse lab i bim) (Set.delete nm (loop ss))
  loop (L.Effect i _md:ss) = Set.union (instrUse lab i bim) (loop ss)

instrUse :: L.BlockLabel -> L.Instr -> Map L.BlockLabel (LLVMBlockInfo s) -> Set L.Ident
instrUse from i bim = Set.unions $ case i of
  L.Phi{} -> [] -- NB, phi node use is handled in `useLabel`
  L.RetVoid -> []
  L.Ret tv -> [useTypedVal tv]
  L.Arith _op x y -> [useTypedVal x, useVal y]
  L.Bit _op x y -> [useTypedVal x, useVal y ]
  L.Conv _op x _tp -> [useTypedVal x]
  L.Call _tailCall _tp f args -> useVal f : map useTypedVal args
  L.Alloca _tp Nothing  _align -> []
  L.Alloca _tp (Just x) _align -> [useTypedVal x]
  L.Load p _ord _align -> [useTypedVal p]
  L.Store p v _ord _align -> [useTypedVal p, useTypedVal v]
  L.Fence{} -> []
  L.CmpXchg _weak _vol p v1 v2 _s _o1 _o2 -> map useTypedVal [p,v1,v2]
  L.AtomicRW _vol _op p v _s _o -> [useTypedVal p, useTypedVal v]
  L.ICmp _op x y -> [useTypedVal x, useVal y]
  L.FCmp _op x y -> [useTypedVal x, useVal y]
  L.GEP _ib base args -> useTypedVal base : map useTypedVal args
  L.Select c x y -> [ useTypedVal c, useTypedVal x, useVal y ]
  L.ExtractValue x _ixs -> [useTypedVal x]
  L.InsertValue x y _ixs -> [useTypedVal x, useTypedVal y]
  L.ExtractElt x y -> [useTypedVal x, useVal y]
  L.InsertElt x y z -> [useTypedVal x, useTypedVal y, useVal z]
  L.ShuffleVector x y z -> [useTypedVal x, useVal y, useTypedVal z]
  L.Jump l -> [useLabel from l bim]
  L.Br c l1 l2 -> [useTypedVal c, useLabel from l1 bim, useLabel from l2 bim]
  L.Invoke _tp f args l1 l2 -> [useVal f, useLabel from l1 bim, useLabel from l2 bim] ++ map useTypedVal args
  L.Comment{} -> []
  L.Unreachable -> []
  L.Unwind -> [] -- ??
  L.VaArg x _tp -> [useTypedVal x]
  L.IndirectBr x ls -> useTypedVal x : [ useLabel from l bim | l <- ls ]
  L.Switch c def bs -> useTypedVal c : useLabel from def bim : [ useLabel from l bim | (_,l) <- bs ]
  L.Resume x -> [useTypedVal x]
  L.LandingPad _tp Nothing _ cls -> map useClause cls
  L.LandingPad _tp (Just cleanup) _ cls -> useTypedVal cleanup : map useClause cls
  L.UnaryArith _op x -> [useTypedVal x]
  L.Freeze x -> [useTypedVal x]

useClause :: L.Clause -> Set L.Ident
useClause (L.Catch v) = useTypedVal v
useClause (L.Filter v) = useTypedVal v

useLabel :: L.BlockLabel -> L.BlockLabel -> Map L.BlockLabel (LLVMBlockInfo s) -> Set L.Ident
useLabel from to bim =
  case Map.lookup to bim of
    Nothing -> panic "useLabel" ["Could not find label", show to]
    Just bi ->
      let phiList =
            case Map.lookup from (block_phi_map bi) of
              Nothing -> []
              Just ps -> toList ps
      in Set.unions (block_use_set bi : [ useVal v | (_,_,v) <- phiList ])

useTypedVal :: L.Typed (L.Value) -> Set L.Ident
useTypedVal tv = useVal (L.typedValue tv)

useVal :: L.Value -> Set L.Ident
useVal v = case v of
  L.ValInteger{} -> mempty
  L.ValBool{} -> mempty
  L.ValFloat{} -> mempty
  L.ValDouble{} -> mempty
  L.ValFP80{} -> mempty
  L.ValIdent i -> Set.singleton i
  L.ValSymbol _s -> mempty
  L.ValNull -> mempty
  L.ValArray _tp vs -> Set.unions (map useVal vs)
  L.ValVector _tp vs -> Set.unions (map useVal vs)
  L.ValStruct vs -> Set.unions (map useTypedVal vs)
  L.ValPackedStruct vs -> Set.unions (map useTypedVal vs)
  L.ValString _ -> mempty
  L.ValConstExpr{} -> mempty -- TODO? should we look through constant exprs?
  L.ValUndef -> mempty
  L.ValLabel _ -> mempty
  L.ValZeroInit -> mempty
  L.ValAsm{} -> mempty -- TODO! inline asm ...

  -- NB! metadata values are not considered as part of our use analysis
  L.ValMd _md -> mempty


-- Given the statements in a basic block, find all the phi instructions and
-- compute the list of assignments that must be made for each predecessor block.
buildPhiMap :: [L.Stmt] -> Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value))
buildPhiMap ss = go ss Map.empty
 where go (L.Result ident (L.Phi tp xs) _ : stmts) m = go stmts (go' ident tp xs m)
       go _ m = m

       f x mseq = Just (fromMaybe Seq.empty mseq Seq.|> x)

       go' ident tp ((v, lbl) : xs) m = go' ident tp xs (Map.alter (f (ident,tp,v)) lbl m)
       go' _ _ [] m = m


-- Given a list of LLVM formal parameters and a corresponding crucible
-- register assignment, build an IdentMap mapping LLVM identifiers to
-- corresponding crucible registers.
buildIdentMap :: (?lc :: TypeContext, HasPtrWidth wptr)
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
      panic "crucible-llvm:Translation.buildIdentMap"
      [ "buildIdentMap: passed arguments do not match LLVM input signature" ]
buildIdentMap (ti:ts) _ ctx asgn m = do
  let ty = case liftMemType (L.typedType ti) of
             Right t -> t
             Left err -> panic "crucible-llvm:Translation.buildIdentMap"
                         [ "Error attempting to lift type " <> show ti
                         , show err
                         ]
  packType ty ctx asgn $ \x ctx' asgn' ->
     buildIdentMap ts False ctx' asgn' (Map.insert (L.typedValue ti) (Right x) m)

-- | Build the initial LLVM generator state upon entry to to the entry point of a function.
initialState :: (?lc :: TypeContext, HasPtrWidth wptr)
             => L.Define
             -> LLVMContext arch
             -> CtxRepr args
             -> Ctx.Assignment (Atom s) args
             -> IORef [(L.Symbol,Position,Text)]
             -> LLVMState arch s
initialState d llvmctx args asgn warnRef =
   let m = buildIdentMap (reverse (L.defArgs d)) (L.defVarArgs d) args asgn Map.empty in
     LLVMState { _identMap = m
               , _blockInfoMap = Map.empty
               , llvmContext = llvmctx
               , _translationWarnings = warnRef
               , _functionSymbol = L.defName d
               }

-- | Given an LLVM type and a type context and a register assignment,
--   peel off the rightmost register from the assignment, which is
--   expected to match the given LLVM type.  Pass the register and
--   the remaining type and register context to the given continuation.
--
--   This procedure is used to set up the initial state of the
--   registers at the entry point of a function.
packType :: (?lc :: TypeContext, HasPtrWidth wptr)
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
