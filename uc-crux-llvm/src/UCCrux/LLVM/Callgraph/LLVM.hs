{-
Module           : UCCrux.LLVM.Callgraph.LLVM
Description      : Callgraph of LLVM functions
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE LambdaCase #-}

module UCCrux.LLVM.Callgraph.LLVM
  ( LLVMFuncCallgraph
  , directCalls
  , funcCallees
  , funcCallers
  )
where

import           Data.Maybe (mapMaybe)
import           Data.Set (Set)

import qualified Text.LLVM.AST as L

import           UCCrux.LLVM.Callgraph (Callgraph)
import qualified UCCrux.LLVM.Callgraph as CG

-- | Function-level callgraph of an LLVM module
newtype LLVMFuncCallgraph
  = LLVMFuncCallgraph
      { getLLVMCallgraph :: Callgraph () L.Symbol L.Symbol }
  deriving (Eq, Ord, Show)

-- | Create a callgraph consisting of the direct calls found in the LLVM module.
directCalls :: L.Module -> LLVMFuncCallgraph
directCalls m =
  LLVMFuncCallgraph (CG.fromList (concatMap defEdges (L.modDefines m)))
  where
    defEdges def =
      mapMaybe (fmap (mkEdge def) . stmtCalls) (concatMap L.bbStmts (L.defBody def))

    mkEdge def symb =
      CG.Edge
        { CG.edgeCaller = L.defName def
        , CG.edgeCallee = symb
        , CG.edgeTag = ()
        }

    stmtCalls =
      \case
        L.Result _ instr _ -> instrDirectlyCalls instr
        L.Effect instr _ -> instrDirectlyCalls instr

    instrDirectlyCalls =
      \case
        L.Call _ _ (L.ValSymbol f) _args -> Just f
        L.Invoke _ (L.ValSymbol f) _args _ _ -> Just f
        _ -> Nothing

funcCallees :: LLVMFuncCallgraph -> L.Symbol -> Set L.Symbol
funcCallees cg symb = CG.callees (getLLVMCallgraph cg) symb

funcCallers :: LLVMFuncCallgraph -> L.Symbol -> Set L.Symbol
funcCallers cg symb = CG.callers (getLLVMCallgraph cg) symb
