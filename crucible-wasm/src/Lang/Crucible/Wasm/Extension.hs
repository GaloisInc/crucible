{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Wasm.Extension where

import Control.Lens
import Control.Monad.Trans
import Control.Monad.Trans.State
import Data.Kind
import Prettyprinter

import Data.Parameterized.TraversableFC
import qualified Data.BitVector.Sized as BV

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Extension
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Types

import Lang.Crucible.LLVM.MemModel (HasLLVMAnn, MemOptions)

import Lang.Crucible.Wasm.Instantiate
import Lang.Crucible.Wasm.Memory
import Lang.Crucible.Wasm.Utils

import What4.Interface

import qualified Language.Wasm.Structure as Wasm

data WasmExt

type instance ExprExtension WasmExt = EmptyExprExtension
type instance StmtExtension WasmExt = WasmStmt

instance IsSyntaxExtension WasmExt

type WasmPointer = BVType 32

data WasmStmt (f :: CrucibleType -> Type) :: CrucibleType -> Type where
  Wasm_IndirectFunction ::
    Wasm.FuncType {- ^ Type of the function to lookup -} ->
    FuncTable {- ^ table in which to look up functions -} ->
    TypeRepr (FunctionHandleType args ret) {- ^ Crucible type of the function to look up -} ->
    !(f (BVType 32)) {- ^ computed table index -} ->
    WasmStmt f (FunctionHandleType args ret)

  Wasm_MemSize ::
    GlobalVar WasmMem ->
    WasmStmt f (BVType 32)

  Wasm_MemGrow ::
    GlobalVar WasmMem ->
    !(f (BVType 32)) ->
    WasmStmt f (BVType 32)

  Wasm_LoadInt8 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (BVType 8)

  Wasm_LoadInt16 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (BVType 16)

  Wasm_LoadInt32 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (BVType 32)

  Wasm_LoadInt64 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (BVType 64)

  Wasm_LoadFloat ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (FloatType SingleFloat)

  Wasm_LoadDouble ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    WasmStmt f (FloatType DoubleFloat)

  Wasm_StoreInt8::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (BVType 8)) ->
    WasmStmt f UnitType

  Wasm_StoreInt16 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (BVType 16)) ->
    WasmStmt f UnitType

  Wasm_StoreInt32 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (BVType 32)) ->
    WasmStmt f UnitType

  Wasm_StoreInt64 ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (BVType 64)) ->
    WasmStmt f UnitType

  Wasm_StoreFloat ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (FloatType SingleFloat)) ->
    WasmStmt f UnitType

  Wasm_StoreDouble ::
    GlobalVar WasmMem ->
    !(f WasmPointer) ->
    !(f (FloatType DoubleFloat)) ->
    WasmStmt f UnitType

extImpl :: HasLLVMAnn sym =>
           MemOptions ->
           ExtensionImpl p sym WasmExt
extImpl mo =
  let ?memOpts = mo in
  ExtensionImpl
  { -- There are no interesting extension expression formers
    extensionEval = \_ _ _ _ _ -> \case{}
  , extensionExec = evalWasmExt
  }

evalWasmExt :: (HasLLVMAnn sym, ?memOpts :: MemOptions) =>
               EvalStmtFunc p sym WasmExt
evalWasmExt stmt cst =
  withBackend (cst^.stateContext) $ \bak ->
    runStateT (evalStmt bak stmt) cst

type EvalM p sym ext rtp blocks ret args a =
  StateT (CrucibleState p sym ext rtp blocks ret args) IO a

evalStmt :: forall p sym bak ext rtp blocks ret args tp.
  (IsSymBackend sym bak, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak  ->
  WasmStmt (RegEntry sym) tp ->
  EvalM p sym ext rtp blocks ret args (RegValue sym tp)
evalStmt bak = eval
  where

  getMem :: GlobalVar WasmMem -> EvalM p sym ext rtp blocks ret args (WasmMemImpl sym)
  getMem gv =
    do gs <- use (stateTree.actFrame.gpGlobals)
       case lookupGlobal gv gs of
         Just mem -> return mem
         Nothing -> panic "getMem" ["memory not allocated!"]

  setMem ::
    GlobalVar WasmMem ->
    WasmMemImpl sym ->
    EvalM p sym ext rtp blocks ret args ()
  setMem gv mem = stateTree.actFrame.gpGlobals %= insertGlobal gv mem

  eval ::
    WasmStmt (RegEntry sym) tp ->
    EvalM p sym ext rtp blocks ret args (RegValue sym tp)
  eval = \case
    Wasm_IndirectFunction fty ftab rty (regValue -> x)
      | Just i <- BV.asUnsigned <$> asBV x ->
          case lookupFuncTable (fromIntegral i) ftab of
            Nothing -> fail ("Invalid indirect function offset: " ++ show i)
            Just (ftyActual, SomeHandle hdl)
              | fty == ftyActual, Just Refl <- testEquality rty (handleType hdl)
              -> pure (HandleFnVal hdl)

              | otherwise -> fail ("Type error in indirect function: " ++ show i)

      | otherwise ->
          unimplemented "Wasm_IndirectFunction: cannot handle symbolic inputs"

    Wasm_MemSize gv ->
      do mem  <- getMem gv
         return (wasmMemSize mem)

    Wasm_MemGrow gv (regValue -> n) ->
      do mem <- getMem gv
         (res, mem') <- liftIO $ wasmGrowMem bak n mem
         setMem gv mem'
         return res

    Wasm_StoreInt8 gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreInt @8 bak p v mem)
         setMem gv mem'

    Wasm_StoreInt16 gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreInt @16 bak p v mem)
         setMem gv mem'

    Wasm_StoreInt32 gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreInt @32 bak p v mem)
         setMem gv mem'

    Wasm_StoreInt64 gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreInt @64 bak p v mem)
         setMem gv mem'

    Wasm_StoreFloat gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreFloat bak p v mem)
         setMem gv mem'

    Wasm_StoreDouble gv (regValue -> p) (regValue -> v) ->
      do mem <- getMem gv
         mem' <- liftIO (wasmStoreDouble bak p v mem)
         setMem gv mem'

    Wasm_LoadInt8 gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadInt bak p (knownNat @8) mem)

    Wasm_LoadInt16 gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadInt bak p (knownNat @16) mem)

    Wasm_LoadInt32 gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadInt bak p (knownNat @32) mem)

    Wasm_LoadInt64 gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadInt bak p (knownNat @64) mem)

    Wasm_LoadFloat gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadFloat bak p mem)

    Wasm_LoadDouble gv (regValue -> p) ->
      do mem <- getMem gv
         liftIO (wasmLoadDouble bak p mem)


instance PrettyApp WasmStmt where
  ppApp pp e =
    case e of
      Wasm_IndirectFunction fty _tbl _tyr val ->
        pretty "indirectFunction" <+> viaShow fty <+> pp val

      Wasm_MemSize gv ->
        pretty "memSize" <+> pretty (globalName gv)
      Wasm_MemGrow gv x ->
        pretty "memGrow" <+> pretty (globalName gv) <+> pp x

      Wasm_LoadInt8 gv p ->
        pretty "loadInt8" <+> pretty (globalName gv) <+> pp p
      Wasm_LoadInt16 gv p ->
        pretty "loadInt16" <+> pretty (globalName gv) <+> pp p
      Wasm_LoadInt32 gv p ->
        pretty "loadInt32" <+> pretty (globalName gv) <+> pp p
      Wasm_LoadInt64 gv p ->
        pretty "loadInt64" <+> pretty (globalName gv) <+> pp p
      Wasm_LoadFloat gv p ->
        pretty "loadFloat" <+> pretty (globalName gv) <+> pp p
      Wasm_LoadDouble gv p ->
        pretty "loadDouble" <+> pretty (globalName gv) <+> pp p

      Wasm_StoreInt8 gv p x ->
        pretty "storeInt8" <+> pretty (globalName gv) <+> pp p <+> pp x
      Wasm_StoreInt16 gv p x ->
        pretty "storeInt16" <+> pretty (globalName gv) <+> pp p <+> pp x
      Wasm_StoreInt32 gv p x ->
        pretty "storeInt32" <+> pretty (globalName gv) <+> pp p <+> pp x
      Wasm_StoreInt64 gv p x ->
        pretty "storeInt64" <+> pretty (globalName gv) <+> pp p <+> pp x
      Wasm_StoreFloat gv p x ->
        pretty "storeFloat" <+> pretty (globalName gv) <+> pp p <+> pp x
      Wasm_StoreDouble gv p x ->
        pretty "storeDouble" <+> pretty (globalName gv) <+> pp p <+> pp x

instance TypeApp WasmStmt where
  appType e =
    case e of
      Wasm_IndirectFunction _fty _tab tpr _idx -> tpr
      Wasm_MemSize{} -> knownRepr
      Wasm_MemGrow{} -> knownRepr
      Wasm_LoadInt8{}  -> knownRepr
      Wasm_LoadInt16{}  -> knownRepr
      Wasm_LoadInt32{}  -> knownRepr
      Wasm_LoadInt64{}  -> knownRepr
      Wasm_LoadFloat{}  -> knownRepr
      Wasm_LoadDouble{} -> knownRepr
      Wasm_StoreInt8{} -> knownRepr
      Wasm_StoreInt16{} -> knownRepr
      Wasm_StoreInt32{} -> knownRepr
      Wasm_StoreInt64{} -> knownRepr
      Wasm_StoreFloat{} -> knownRepr
      Wasm_StoreDouble{} -> knownRepr

instance FunctorFC WasmStmt where
  fmapFC = fmapFCDefault
instance FoldableFC WasmStmt where
  foldMapFC = foldMapFCDefault
instance TraversableFC WasmStmt where
  traverseFC f e =
    case e of
      Wasm_IndirectFunction fty tab tpr idx -> Wasm_IndirectFunction fty tab tpr <$> f idx
      Wasm_MemSize gv     -> pure (Wasm_MemSize gv)
      Wasm_MemGrow gv x   -> Wasm_MemGrow gv <$> f x
      Wasm_LoadInt8  gv p -> Wasm_LoadInt8 gv <$> f p
      Wasm_LoadInt16 gv p -> Wasm_LoadInt16 gv <$> f p
      Wasm_LoadInt32 gv p -> Wasm_LoadInt32 gv <$> f p
      Wasm_LoadInt64 gv p -> Wasm_LoadInt64 gv <$> f p
      Wasm_LoadFloat gv p  -> Wasm_LoadFloat gv <$> f p
      Wasm_LoadDouble gv p -> Wasm_LoadDouble gv <$> f p

      Wasm_StoreInt8 gv p x  -> Wasm_StoreInt8 gv <$> f p <*> f x
      Wasm_StoreInt16 gv p x -> Wasm_StoreInt16 gv <$> f p <*> f x
      Wasm_StoreInt32 gv p x -> Wasm_StoreInt32 gv <$> f p <*> f x
      Wasm_StoreInt64 gv p x -> Wasm_StoreInt64 gv <$> f p <*> f x
      Wasm_StoreFloat gv p x  -> Wasm_StoreFloat gv <$> f p <*> f x
      Wasm_StoreDouble gv p x -> Wasm_StoreDouble gv <$> f p <*> f x
