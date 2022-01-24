{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Wasm
( ExternalType(..)
, Address
, Namespace
, FuncTable
, lookupFuncTable
, Store(..)
, ModuleInstance(..)
, WasmGlobal(..)
, instantiateModule
, execScript
, emptyScriptState
, WasmExt
, extImpl
, wasmIntrinsicTypes
) where

import Control.Lens hiding (Empty, (:>),Index )
import Control.Monad
import Control.Monad.Trans

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Text.Lazy as TL
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Parameterized.Map as MapF
import           Data.Word

import Data.Parameterized.Context as Ctx
import Data.Parameterized.Some

import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm

import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator
import Lang.Crucible.Types

import           Lang.Crucible.LLVM.MemModel (HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel.Generic as G

import Lang.Crucible.Wasm.Extension
import Lang.Crucible.Wasm.Instantiate
import Lang.Crucible.Wasm.Memory
import Lang.Crucible.Wasm.Translate
import Lang.Crucible.Wasm.Utils

import What4.Interface

wasmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
wasmIntrinsicTypes =
  MapF.insert (knownSymbol @"Wasm_Mem") IntrinsicMuxFn $
  MapF.empty


data ScriptState =
  ScriptState
  { scriptStore :: Store
  , scriptNamespace :: Namespace
  , scriptLoadedModules :: Namespace
  , scriptCurrentModule :: Maybe (Maybe Wasm.Ident, Wasm.ValidModule, ModuleInstance)
  }

emptyScriptState :: ScriptState
emptyScriptState =
  ScriptState
  { scriptStore = emptyStore
  , scriptNamespace = emptyNamespace
  , scriptLoadedModules = emptyNamespace
  , scriptCurrentModule = Nothing
  }

type WasmOverride p sym = OverrideSim p sym WasmExt (RegEntry sym UnitType)

execScript :: HasLLVMAnn sym =>
              [Wasm.Command] -> ScriptState -> WasmOverride p sym EmptyCtx UnitType ScriptState
execScript script ss = foldM (flip execCommand) ss script

execCommand :: HasLLVMAnn sym =>
               Wasm.Command -> ScriptState -> WasmOverride p sym EmptyCtx UnitType ScriptState
execCommand (Wasm.ModuleDef mdef) ss =
  do halloc <- use (stateContext . to simHandleAllocator)
     let st = scriptStore ss
     let ns = scriptNamespace ss
     ((nm,vm,im), st') <- runInstM st (defineModule halloc ns mdef)

     initGlobals im st'
     initMemories im st'

     mapM_ registerFnBinding =<< liftIO (translateFunctions im st')
     debug (show (instDataSegs im))
     mapM_ writeDataSegment (instDataSegs im)

     executeStart im

     let lmods' = case nm of
                    Nothing  -> scriptLoadedModules ss
                    Just nm' -> namespaceInsertModule nm' im (scriptLoadedModules ss)

     return ss{ scriptStore = st'
              , scriptLoadedModules = lmods'
              , scriptCurrentModule = Just (nm,vm,im)
              }

execCommand (Wasm.Assertion a) ss =
  do execAssertion a ss
     return ss

execCommand (Wasm.Action a) ss =
  do _ <- execAction a ss
     return ss

execCommand c ss =
  do liftIO $ putStrLn $ unwords ["Command not implemented", show c] -- TODO!
     return ss


executeStart ::
  ModuleInstance ->
  WasmOverride p sym EmptyCtx UnitType ()
executeStart im =
  case instStartFunc im of
    Nothing -> pure ()
    Just startFn ->
      do ctx <- getContext
         ctxSolverProof ctx $ void $
           callFnVal' (HandleFnVal startFn) Empty

writeDataSegment ::
  HasLLVMAnn sym =>
  (GlobalVar WasmMem, Word32, LBS.ByteString) ->
  WasmOverride p sym EmptyCtx UnitType ()
writeDataSegment (mvar, offset, chunk) =
  ovrWithBackend $ \bak -> 
    do let sym = backendGetSym bak
       mem  <- readGlobal mvar
       mem' <- liftIO $
               do offset' <- bvLit sym knownNat (BV.word32 offset)
                  wasmStoreChunk bak offset' chunk mem
       debug (show (G.ppMem (wasmMemHeap mem')))
       writeGlobal mvar mem'

initMemories ::
  ModuleInstance ->
  Store ->
  WasmOverride p sym EmptyCtx UnitType ()
initMemories im st =
  ovrWithBackend $ \bak ->
    do let sym = backendGetSym bak
       forM_ (instMemAddrs im) \case
         (Wasm.Memory lim, True, addr) ->
           case Seq.lookup addr (storeMemories st) of
             Nothing -> panic "initMemories" ["could not resolve memory address " ++ show addr]
             Just gv ->
               do mem <- liftIO (freshMemory sym lim)
                  writeGlobal gv mem
  
         -- imported memory, no need to initialize
         _ -> return ()

initGlobals ::
  ModuleInstance ->
  Store ->
  WasmOverride p sym EmptyCtx UnitType ()
initGlobals im st =
  do ctx <- getContext
     sym <- getSymInterface
     ctxSolverProof ctx $ forM_ (instGlobalAddrs im) \case
       (_gty, Just cv, addr) ->
          case Seq.lookup addr (storeGlobals st) of
            Nothing -> panic "initGlobals" ["could not resolve global address " ++ show addr]
            Just (ConstantGlobal _) -> return () -- TODO? shouldn't happen, error?
            Just (MutableGlobal gv) ->
              case cv of
                I32Val w
                  | Just Refl <- testEquality (globalType gv) (BVRepr (knownNat @32))
                  -> writeGlobal gv =<< liftIO (bvLit sym knownNat (BV.word32 w))
                I64Val w
                  | Just Refl <- testEquality (globalType gv) (BVRepr (knownNat @64))
                  -> writeGlobal gv =<< liftIO (bvLit sym knownNat (BV.word64 w))
                F32Val _ -> unimplemented "initGlobals F32Val"
                F64Val _ -> unimplemented "initGlobals F64Val"

                _ -> panic "initGlobals" ["type mismatch!"]

       -- Imported or constant global value, nothing to initialize
       (_,Nothing,_) -> return ()


getModule ::
  Maybe Wasm.Ident ->
  ScriptState ->
  WasmOverride p sym EmptyCtx UnitType ModuleInstance
getModule Nothing ss =
  case scriptCurrentModule ss of
    Nothing -> fail "No current module loaded"
    Just (_,_,im) -> pure im
getModule (Just nm) ss =
  case namespaceModule nm (scriptLoadedModules ss) of
    Nothing -> fail $ unwords ["Could not find loaded module", show nm]
    Just im -> pure im

getModuleFunc ::
  Maybe Wasm.Ident ->
  TL.Text ->
  ModuleInstance ->
  Store ->
  WasmOverride p sym EmptyCtx UnitType (Wasm.FuncType, SomeHandle)
getModuleFunc modNm nm im st =
  case Map.lookup nm (instExports im) of
    Just (ExternalFunc fty, addr)
      | Just h <- Seq.lookup addr (storeFuncs st)
      -> pure (fty,h)
    _ -> fail $ unwords ["Could not find function", show nm
                        , case modNm of Nothing -> "in current module"
                                        Just m  -> "in module " ++ show m
                        ]

computeConstantValues :: forall sym ctx.
  IsSymInterface sym =>
  sym ->
  ModuleInstance ->
  Store ->
  Assignment TypeRepr ctx ->
  [Wasm.Expression] ->
  IO (Assignment (RegEntry sym) ctx)
computeConstantValues sym im st tps exprs =
  do (xs,_) <- runInstM st (mapM (evalConst im) exprs)
     let mkVal :: Index ctx tp -> TypeRepr tp -> IO (RegEntry sym tp)
         mkVal idx tp =
           case Prelude.drop (indexVal idx) xs of
             (I32Val w : _)
               | Just Refl <- testEquality tp (BVRepr (knownNat @32))
               -> do v <- bvLit sym (knownNat @32) (BV.word32 w)
                     return (RegEntry tp v)
               | otherwise -> fail "type mismatch in computeConstantValues!"

             (I64Val w : _)
               | Just Refl <- testEquality tp (BVRepr (knownNat @64))
               -> do v <- bvLit sym (knownNat @64) (BV.word64 w)
                     return (RegEntry tp v)
               | otherwise -> fail "type mismatch in computeConstantValues!"

             (F32Val _ : _) -> unimplemented "compute F32"
             (F64Val _ : _) -> unimplemented "compute F64"
             [] -> fail "not enough arguments in computeConstantValues!"

     traverseWithIndex mkVal tps

execAction ::
  Wasm.Action ->
  ScriptState ->
  WasmOverride p sym EmptyCtx UnitType (ModuleInstance, Some (RegEntry sym))
execAction (Wasm.Invoke md nm args) ss =
  do ctx <- getContext
     im <- getModule md ss
     let st = scriptStore ss
     (_fty, SomeHandle h) <- getModuleFunc md nm im st
     sym <- getSymInterface
     ctxSolverProof ctx do
       args' <- liftIO (computeConstantValues sym im st (handleArgTypes h) args)
       x <- callFnVal (HandleFnVal h) (RegMap args')
       pure (im, Some x)

execAction (Wasm.Get _md _nm) _ss = unimplemented "execAction: get"

execAssertion :: Wasm.Assertion -> ScriptState -> WasmOverride p sym EmptyCtx UnitType ()

execAssertion ast@(Wasm.AssertReturn act rets) ss =
  ovrWithBackend $ \bak ->
  do let sym = backendGetSym bak
     (im, Some (RegEntry rty result)) <- execAction act ss
     case rty of
         UnitRepr | Prelude.null rets -> return ()
         StructRepr ts | length rets > 1 -> liftIO $
               do expected <- computeConstantValues sym im (scriptStore ss) ts rets
                  assertEqResults bak (show ast) result expected
         t | length rets == 1 -> liftIO $
               do expected <- computeConstantValues sym im (scriptStore ss) (Empty :> t) rets
                  assertEqResults bak (show ast) (Empty :> RV result) expected
           | otherwise -> fail "type mismatch in execAssertion!"

execAssertion a _ =
  liftIO $ putStrLn $ unwords ["Assertion not implemented", show a] -- TODO


assertEqResults :: forall sym bak ctx.
  (IsSymBackend sym bak) =>
  bak ->
  String ->
  Assignment (RegValue' sym) ctx ->
  Assignment (RegEntry sym) ctx ->
  IO ()
assertEqResults bak ast xs ys = traverseWithIndex_ f ys
  where
  sym = backendGetSym bak

  f :: Index ctx tp -> RegEntry sym tp -> IO ()
  f idx (RegEntry tp y) =
     let RV x = xs Ctx.! idx in
     case tp of
       BVRepr _ ->
         do p <- bvEq sym x y
            case asConstantPred p of
              Just False ->
                debug $ unlines
                  [ unwords ["equality postcondition", show (printSymExpr x), show (printSymExpr y)]
                  , ast
                  ]
              _ -> return ()
            assert bak p (GenericSimError "assert return failed")

       _ -> unimplemented $ unwords ["assert return could not handle type", show tp]
