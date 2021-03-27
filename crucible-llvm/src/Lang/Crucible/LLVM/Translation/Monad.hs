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
  ) where

import Control.Lens hiding (op, (:>) )
import Control.Monad.State.Strict
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)

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

import           Lang.Crucible.FunctionHandle
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

buildBlockInfoMap :: L.Define -> LLVMGenerator s arch ret (Map L.BlockLabel (LLVMBlockInfo s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: L.BasicBlock -> LLVMGenerator s arch ret (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let blk_lbl = case L.bbLabel bb of
                  Just l -> l
                  Nothing -> panic "crucible-llvm:Translation.buildBlockInfo"
                             [ "unable to obtain label from BasicBlock" ]
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
             -> LLVMState arch s
initialState d llvmctx args asgn =
   let m = buildIdentMap (reverse (L.defArgs d)) (L.defVarArgs d) args asgn Map.empty in
     LLVMState { _identMap = m, _blockInfoMap = Map.empty, llvmContext = llvmctx }

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
