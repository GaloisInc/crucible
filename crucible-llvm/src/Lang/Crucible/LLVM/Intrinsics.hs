-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics
-- Description      : Override definitions for LLVM intrinsic and basic
--                    library functions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.LLVM.Intrinsics
( LLVM
, llvmIntrinsicTypes
, LLVMHandleInfo(..)
, LLVMContext(..)
, LLVMOverride(..)
, SymbolHandleMap
, symbolMap
, llvmTypeCtx
, mkLLVMContext
, register_llvm_override
, register_llvm_overrides
, build_llvm_override
, llvmDeclToFunHandleRepr
) where

import           GHC.TypeNats (KnownNat)
import           Control.Applicative
import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bits
import           Data.Foldable( asum )
import qualified Data.List as List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Numeric
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           What4.FunctionName
import           What4.Interface
import           What4.Utils.MonadST

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.Utils.MonadVerbosity

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.LLVM.Intrinsics.Types
import qualified Lang.Crucible.LLVM.Intrinsics.Libc as Libc

llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn $
   MapF.empty

register_llvm_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_overrides llvm_module llvm_ctx =
  flip execStateT llvm_ctx $
    forM_ (L.modDeclares llvm_module) $ \decl ->
      runMaybeT (runReaderT do_register_overrides decl) >> return ()

do_register_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  RegOverrideM p sym arch rtp l a ()
do_register_overrides = do
  llvmctx <- get
  let ?lc = llvmctx^.llvmTypeCtx

  -- LLVM Compiler intrinsics
  asum
   [ register_llvm_override llvmLifetimeStartOverride
   , register_llvm_override llvmLifetimeEndOverride
   , register_llvm_override (llvmLifetimeOverrideOverload "start" (knownNat @8))
   , register_llvm_override (llvmLifetimeOverrideOverload "end" (knownNat @8))
   , register_llvm_override llvmMemcpyOverride_8_8_32
   , register_llvm_override llvmMemcpyOverride_8_8_64
   , register_llvm_override llvmMemmoveOverride_8_8_32
   , register_llvm_override llvmMemmoveOverride_8_8_64
   , register_llvm_override llvmMemsetOverride_8_32
   , register_llvm_override llvmMemsetOverride_8_64

   , register_llvm_override llvmObjectsizeOverride_32
   , register_llvm_override llvmObjectsizeOverride_64

   , register_llvm_override llvmObjectsizeOverride_32'
   , register_llvm_override llvmObjectsizeOverride_64'

   , register_llvm_override llvmStacksave
   , register_llvm_override llvmStackrestore

   , register_1arg_polymorphic_override "llvm.ctlz" (\w -> SomeLLVMOverride (llvmCtlz w))
   , register_1arg_polymorphic_override "llvm.cttz" (\w -> SomeLLVMOverride (llvmCttz w))
   , register_1arg_polymorphic_override "llvm.ctpop" (\w -> SomeLLVMOverride (llvmCtpop w))
   , register_1arg_polymorphic_override "llvm.bitreverse" (\w -> SomeLLVMOverride (llvmBitreverse w))

   , register_llvm_override (llvmBSwapOverride (knownNat @2))  -- 16 = 2 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @4))  -- 32 = 4 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @6))  -- 48 = 6 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @8))  -- 64 = 8 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @10)) -- 80 = 10 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @12)) -- 96 = 12 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @14)) -- 112 = 14 * 8
   , register_llvm_override (llvmBSwapOverride (knownNat @16)) -- 128 = 16 * 8

   , register_1arg_polymorphic_override "llvm.sadd.with.overflow"
       (\w -> SomeLLVMOverride (llvmSaddWithOverflow w))
   , register_1arg_polymorphic_override "llvm.uadd.with.overflow"
       (\w -> SomeLLVMOverride (llvmUaddWithOverflow w))
   , register_1arg_polymorphic_override "llvm.ssub.with.overflow"
       (\w -> SomeLLVMOverride (llvmSsubWithOverflow w))
   , register_1arg_polymorphic_override "llvm.usub.with.overflow"
       (\w -> SomeLLVMOverride (llvmUsubWithOverflow w))
   , register_1arg_polymorphic_override "llvm.smul.with.overflow"
       (\w -> SomeLLVMOverride (llvmSmulWithOverflow w))
   , register_1arg_polymorphic_override "llvm.umul.with.overflow"
       (\w -> SomeLLVMOverride (llvmUmulWithOverflow w))

    -- C standard library functions
   , register_llvm_override Libc.llvmAssertRtnOverride
   , register_llvm_override Libc.llvmMemcpyOverride
   , register_llvm_override Libc.llvmMemcpyChkOverride
   , register_llvm_override Libc.llvmMemmoveOverride
   , register_llvm_override Libc.llvmMemsetOverride
   , register_llvm_override Libc.llvmMemsetChkOverride
   , register_llvm_override Libc.llvmMallocOverride
   , register_llvm_override Libc.llvmCallocOverride
   , register_llvm_override Libc.llvmFreeOverride
   , register_llvm_override Libc.llvmReallocOverride
   , register_llvm_override Libc.llvmStrlenOverride
   , register_llvm_override Libc.llvmPrintfOverride
   , register_llvm_override Libc.llvmPrintfChkOverride
   , register_llvm_override Libc.llvmPutsOverride
   , register_llvm_override Libc.llvmPutCharOverride

   -- Some architecture-dependent intrinsics
   , register_llvm_override llvmX86_SSE2_storeu_dq
   , register_llvm_override llvmX86_pclmulqdq
   ]

------------------------------------------------------------------------
-- LLVMHandleInfo

-- | Information about an LLVM handle, including both its
--   LLVM and Crucible type information as well as the Crucible
--   handle allocated to this symbol.
data LLVMHandleInfo where
  LLVMHandleInfo :: L.Declare
                 -> FnHandle init ret
                 -> LLVMHandleInfo

------------------------------------------------------------------------
-- LLVMContext

-- | Maps symbol to information about associated handle.
type SymbolHandleMap = Map L.Symbol LLVMHandleInfo

-- | Information about the LLVM module.
data LLVMContext arch
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     _symbolMap     :: !SymbolHandleMap
   , llvmArch       :: ArchRepr arch
   , llvmPtrWidth   :: forall a. (16 <= (ArchWidth arch) => NatRepr (ArchWidth arch) -> a) -> a
   , llvmMemVar     :: GlobalVar Mem
   , _llvmTypeCtx   :: TypeContext
   }

symbolMap :: Simple Lens (LLVMContext arch) SymbolHandleMap
symbolMap = lens _symbolMap (\s v -> s { _symbolMap = v })

llvmTypeCtx :: Simple Lens (LLVMContext arch) TypeContext
llvmTypeCtx = lens _llvmTypeCtx (\s v -> s{ _llvmTypeCtx = v })

mkLLVMContext :: HandleAllocator s
              -> L.Module
              -> ST s (Some LLVMContext)
mkLLVMContext halloc m = do
  let (errs, typeCtx) = typeContextFromModule m
  unless (null errs) $
    fail $ unlines
         $ [ "Failed to construct LLVM type context:" ] ++ map show errs
  let dl = llvmDataLayout typeCtx

  case mkNatRepr (ptrBitwidth dl) of
    Some (wptr :: NatRepr wptr) | Just LeqProof <- testLeq (knownNat @16) wptr ->
      withPtrWidth wptr $
        do mvar <- mkMemVar halloc
           let archRepr = X86Repr wptr -- FIXME! we should select the architecture based on
                                       -- the target triple, but llvm-pretty doesn't capture this
                                       -- currently.
           let ctx :: LLVMContext (X86 wptr)
               ctx = LLVMContext
                     { _symbolMap = Map.empty
                     , llvmArch     = archRepr
                     , llvmMemVar   = mvar
                     , llvmPtrWidth = \x -> x wptr
                     , _llvmTypeCtx = typeCtx
                     }
           return (Some ctx)
    _ ->
      fail ("Cannot load LLVM bitcode file with illegal pointer width: " ++ show (dl^.ptrSize))

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall arch rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym (LLVM arch) rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall arch rtp l a.
    RegValue sym tp ->
    OverrideSim p sym (LLVM arch) rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym args args'.
  (IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformLLVMArgs _ Empty Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs sym (rest' :> tp') (rest :> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformLLVMRet sym tp tp'
                 (ArgTransformer fs) <- transformLLVMArgs sym rest' rest
                 xs' <- fs xs
                 x'  <- RegEntry tp' <$> f (regValue x)
                 pure (xs' :> x')))
transformLLVMArgs _ _ _ =
  panic "Intrinsics.transformLLVMArgs"
    [ "transformLLVMArgs: argument shape mismatch!" ]

transformLLVMRet ::
  (IsSymInterface sym, Monad m) =>
  sym ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
transformLLVMRet sym (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . llvmPointer_bv sym))
transformLLVMRet sym (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . projectLLVM_bv sym))
transformLLVMRet sym (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet sym tp tp'
       return (ValTransformer (traverse f))
transformLLVMRet sym (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs sym ctx' ctx
       return (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet _sym ret ret'
  = panic "Intrinsics.transformLLVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the LLVM calling convention.  This basically just coerces
--   between values of @BVType w@ and values of @LLVMPointerType w@.
build_llvm_override ::
  IsSymInterface sym =>
  sym ->
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (RegEntry sym) args ->
   OverrideSim p sym (LLVM arch) rtp' l' a' (RegValue sym ret)) ->
  OverrideSim p sym (LLVM arch) rtp l a (Override p sym (LLVM arch) args' ret')
build_llvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformLLVMArgs sym args args'
     fret  <- transformLLVMRet  sym ret  ret'
     return $ mkOverride' fnm ret' $
            do RegMap xs <- getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs


type RegOverrideM p sym arch rtp l a =
  ReaderT L.Declare (MaybeT (StateT (LLVMContext arch) (OverrideSim p sym (LLVM arch) rtp l a)))


register_1arg_polymorphic_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym arch) ->
  RegOverrideM p sym arch rtp l a ()
register_1arg_polymorphic_override prefix overrideFn =
  do L.Symbol nm <- L.decName <$> ask
     case List.stripPrefix prefix nm of
       Just ('.':'i': (readDec -> (sz,[]):_))
         | Some w <- mkNatRepr sz
         , Just LeqProof <- isPosNat w
         -> case overrideFn w of SomeLLVMOverride ovr -> register_llvm_override ovr
       _ -> empty

register_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMOverride p sym arch args ret ->
  RegOverrideM p sym arch rtp l a ()
register_llvm_override llvmOverride = do
  requestedDecl <- ask
  llvmctx <- get
  let decl = llvmOverride_declare llvmOverride

  if (requestedDecl /= decl) then
    do when (L.decName requestedDecl == L.decName decl) $
         do logFn <- lift $ lift $ lift $ getLogFunction
            liftIO $ logFn 3 $ unwords
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found: "     ++ show decl
              , ""
              ]
       empty
  else
   do let nm@(L.Symbol str_nm) = L.decName decl
      let fnm  = functionNameFromText (Text.pack str_nm)

      sym <- lift $ lift $ lift $ getSymInterface

      let mvar = llvmMemVar llvmctx
      let overrideArgs = llvmOverride_args llvmOverride
      let overrideRet  = llvmOverride_ret llvmOverride

      let ?lc = llvmctx^.llvmTypeCtx

      decl' <- either fail return $ liftDeclare decl
      llvmDeclToFunHandleRepr decl' $ \derivedArgs derivedRet -> do
        o <- lift $ lift $ lift $ build_llvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet
                      (llvmOverride_def llvmOverride mvar sym)
        case Map.lookup nm (llvmctx^.symbolMap) of
          Just (LLVMHandleInfo _decl' h) -> do
            case testEquality (handleArgTypes h) derivedArgs of
               Nothing ->
                 panic "Intrinsics.register_llvm_override"
                   [ "Argument type mismatch when registering LLVM mss override."
                   , "*** Override name: " ++ show nm
                   , "*** Declared type: " ++ show (handleArgTypes h)
                   , "*** Expected type: " ++ show derivedArgs
                   ]
               Just Refl ->
                 case testEquality (handleReturnType h) derivedRet of
                   Nothing ->
                     panic "Intrinsics.register_llvm_override"
                       [ "return type mismatch when registering LLVM mss override"
                       , "*** Override name: " ++ show nm
                       ]
                   Just Refl -> lift $ lift $ lift $ bindFnHandle h (UseOverride o)
          Nothing ->
            do ctx <- lift $ lift $ lift $ use stateContext
               let ha = simHandleAllocator ctx
               h <- lift $ lift $ liftST $ mkHandle' ha fnm derivedArgs derivedRet
               lift $ lift $ lift $ bindFnHandle h (UseOverride o)
               put (llvmctx & symbolMap %~ Map.insert nm (LLVMHandleInfo decl h))


-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- accesses.
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-start-intrinsic LLVM docs>
llvmLifetimeStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeStartOverride =
  let nm = "llvm.lifetime.start" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @64 :> PtrRepr)
  UnitRepr
  (\_ops _sym _args -> return ())

-- | See comment on 'llvmLifetimeStartOverride'
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-end-intrinsic LLVM docs>
llvmLifetimeEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeEndOverride =
  let nm = "llvm.lifetime.end" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer 64, L.PtrTo (L.PrimType $ L.Integer 8) ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> KnownBV @64 :> PtrRepr)
  UnitRepr
  (\_ops _sym _args -> return ())

-- | This is a no-op.
--
-- The language reference doesn't mention the use of this intrinsic.
llvmLifetimeOverrideOverload
  :: forall width sym wptr arch p
   . ( 1 <= width, KnownNat width
     , IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => String -- ^ "start" or "end"
  -> NatRepr width
  -> LLVMOverride p sym arch
        (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
        UnitType -- It appears in practice that this is always void
llvmLifetimeOverrideOverload startOrEnd widthRepr =
  let
    width' :: Int
    width' = widthVal widthRepr
    nm = "llvm.lifetime." ++ startOrEnd ++ ".p0i" ++ show width'
  in LLVMOverride
      ( L.Declare
        { L.decRetType = L.PrimType $ L.Void
        , L.decName    = L.Symbol nm
        , L.decArgs    = [ L.PrimType $ L.Integer $ 64
                         , L.PtrTo $ L.PrimType $ L.Integer $ fromIntegral width'
                         ]
        , L.decVarArgs = False
        , L.decAttrs   = []
        , L.decComdat  = mempty
        }
      )
      (Empty :> KnownBV @64 :> PtrRepr)
      UnitRepr
      (\_ops _sym _args -> return ())

llvmStacksave
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch EmptyCtx (LLVMPointerType wptr)
llvmStacksave =
  let nm = "llvm.stacksave" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PtrTo $ L.PrimType $ L.Integer 8
    , L.decName    = L.Symbol nm
    , L.decArgs    = [
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  Empty
  PtrRepr
  (\_memOps sym _args -> liftIO (mkNullPointer sym PtrWidth))


llvmStackrestore
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) UnitType
llvmStackrestore =
  let nm = "llvm.stackrestore" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr)
  UnitRepr
  (\_memOps _sym _args -> return ())

llvmMemmoveOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32 =
  let nm = "llvm.memmove.p0i8.p0i8.i32" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemmove sym memOps) args)


llvmMemmoveOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64 =
  let nm = "llvm.memmove.p0i8.p0i8.i64" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemmove sym memOps) args)


llvmMemsetOverride_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64 =
  let nm = "llvm.memset.p0i8.i64" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer  8
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer  1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @8 :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemset sym memOps) args)


llvmMemsetOverride_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32 =
  let nm = "llvm.memset.p0i8.i32" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer  8
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer  1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @8 :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemset sym memOps) args)

llvmMemcpyOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32 =
  let nm = "llvm.memcpy.p0i8.p0i8.i32" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @32 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemcpy sym memOps) args)


llvmMemcpyOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64 =
  let nm = "llvm.memcpy.p0i8.p0i8.i64" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.PrimType $ L.Integer 64
                     , L.PrimType $ L.Integer 32
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> PtrRepr :> KnownBV @64 :> KnownBV @32 :> KnownBV @1)
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemcpy sym memOps) args)

llvmObjectsizeOverride_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32 =
  let nm = "llvm.objectsize.i32.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmObjectsizeOverride_32'
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32' =
  let nm = "llvm.objectsize.i32.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 32
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1 :> KnownBV @1)
  (KnownBV @32)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize' sym memOps knownNat) args)

llvmObjectsizeOverride_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64 =
  let nm = "llvm.objectsize.i64.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 64
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1)
  (KnownBV @64)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmObjectsizeOverride_64'
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64' =
  let nm = "llvm.objectsize.i64.p0i8" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer 64
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo $ L.PrimType $ L.Integer 8
                     , L.PrimType $ L.Integer 1
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> KnownBV @1 :> KnownBV @1)
  (KnownBV @64)
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize' sym memOps knownNat) args)

llvmSaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSaddWithOverflow w =
  let nm = "llvm.sadd.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSaddWithOverflow sym memOps) args)


llvmUaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUaddWithOverflow w =
  let nm = "llvm.uadd.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUaddWithOverflow sym memOps) args)


llvmSsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSsubWithOverflow w =
  let nm = "llvm.ssub.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSsubWithOverflow sym memOps) args)


llvmUsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUsubWithOverflow w =
  let nm = "llvm.usub.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUsubWithOverflow sym memOps) args)

llvmSmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSmulWithOverflow w =
  let nm = "llvm.smul.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callSmulWithOverflow sym memOps) args)

llvmUmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUmulWithOverflow w =
  let nm = "llvm.umul.with.overflow.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Struct
                     [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> BVRepr w)
  (StructRepr (Empty :> BVRepr w :> BVRepr (knownNat @1)))
  (\memOps sym args -> Ctx.uncurryAssignment (callUmulWithOverflow sym memOps) args)


llvmCtlz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCtlz w =
  let nm = "llvm.ctlz.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromIntegral (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> KnownBV @1)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCtlz sym memOps) args)


llvmCttz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCttz w =
  let nm = "llvm.cttz.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromIntegral (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     , L.PrimType $ L.Integer 1
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w :> KnownBV @1)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCttz sym memOps) args)

llvmCtpop
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmCtpop w =
  let nm = "llvm.ctpop.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromIntegral (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callCtpop sym memOps) args)

llvmBitreverse
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmBitreverse w =
  let nm = "llvm.bitreverse.i" ++ show (natValue w) in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Integer (fromIntegral (natValue w))
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PrimType $ L.Integer (fromIntegral (natValue w))
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> BVRepr w)
  (BVRepr w)
  (\memOps sym args -> Ctx.uncurryAssignment (callBitreverse sym memOps) args)


-- | <https://llvm.org/docs/LangRef.html#llvm-bswap-intrinsics LLVM docs>
llvmBSwapOverride
  :: forall width sym wptr arch p
   . ( 1 <= width, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr width
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType (width * 8))
         (BVType (width * 8))
llvmBSwapOverride widthRepr =
  let width8 = natMultiply widthRepr (knownNat @8)
      width' :: Int
      width' = widthVal width8
      nm = "llvm.bswap.i" ++ show width'
  in
    case mulComm widthRepr (knownNat @8) of { Refl ->
    case leqMulMono (knownNat @8) widthRepr :: LeqProof width (width * 8) of { LeqProof ->
    case leqTrans (LeqProof :: LeqProof 1 width)
                  (LeqProof :: LeqProof width (width * 8)) of { LeqProof ->
      LLVMOverride
        ( -- From the LLVM docs:
          -- declare i16 @llvm.bswap.i16(i16 <id>)
          L.Declare
          { L.decRetType = L.PrimType $ L.Integer $ fromIntegral width'
          , L.decName    = L.Symbol nm
          , L.decArgs    = [ L.PrimType $ L.Integer $ fromIntegral width' ]
          , L.decVarArgs = False
          , L.decAttrs   = []
          , L.decComdat  = mempty
          }
        )
        (Empty :> BVRepr width8)
        (BVRepr width8)
        (\_ sym args -> liftIO $
            let vec :: SymBV sym (width * 8)
                vec = regValue (args^._1)
            in bvSwap sym widthRepr vec)
    }}}


llvmX86_pclmulqdq
--declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) #1
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> VectorType (BVType 64)
                   ::> VectorType (BVType 64)
                   ::> BVType 8)
         (VectorType (BVType 64))
llvmX86_pclmulqdq =
  let nm = "llvm.x86.pclmulqdq" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.Vector 2 (L.PrimType $ L.Integer 64)
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.Vector 2 (L.PrimType $ L.Integer 64)
                     , L.Vector 2 (L.PrimType $ L.Integer 64)
                     , L.PrimType $ L.Integer 8
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> VectorRepr (KnownBV @64) :> VectorRepr (KnownBV @64) :> KnownBV @8)
  (VectorRepr (KnownBV @64))
  (\memOps sym args -> Ctx.uncurryAssignment (callX86_pclmulqdq sym memOps) args)


llvmX86_SSE2_storeu_dq
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType (BVType 8))
         UnitType
llvmX86_SSE2_storeu_dq =
  let nm = "llvm.x86.sse2.storeu.dq" in
  LLVMOverride
  ( L.Declare
    { L.decRetType = L.PrimType $ L.Void
    , L.decName    = L.Symbol nm
    , L.decArgs    = [ L.PtrTo (L.PrimType $ L.Integer 8)
                     , L.Vector 16 (L.PrimType $ L.Integer 8)
                     ]
    , L.decVarArgs = False
    , L.decAttrs   = []
    , L.decComdat  = mempty
    }
  )
  (Empty :> PtrRepr :> VectorRepr (KnownBV @8))
  UnitRepr
  (\memOps sym args -> Ctx.uncurryAssignment (callStoreudq sym memOps) args)


callX86_pclmulqdq :: forall p sym arch wptr r args ret.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  sym ->
  GlobalVar Mem ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (BVType 8) ->
  OverrideSim p sym (LLVM arch) r args ret (RegValue sym (VectorType (BVType 64)))
callX86_pclmulqdq sym _mvar
  (regValue -> xs)
  (regValue -> ys)
  (regValue -> imm) =
    do unless (V.length xs == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in llvm.x86.pclmulqdq intrinsic"
           ,"Expected <2 x i64>, but got vector of length ", show (V.length xs)
           ]
       unless (V.length ys == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in llvm.x86.pclmulqdq intrinsic"
           ,"Expected <2 x i64>, but got vector of length ", show (V.length ys)
           ]
       case asUnsignedBV imm of
         Just byte ->
           do let xidx = if byte .&. 0x01 == 0 then 0 else 1
              let yidx = if byte .&. 0x10 == 0 then 0 else 1
              liftIO $ doPcmul (xs V.! xidx) (ys V.! yidx)
         _ ->
             liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
                ["Illegal selector argument to llvm.x86.pclmulqdq"
                ,"  Expected concrete value but got ", show (printSymExpr imm)
                ]
  where
  doPcmul :: SymBV sym 64 -> SymBV sym 64 -> IO (V.Vector (SymBV sym 64))
  doPcmul x y =
    do r <- carrylessMultiply sym x y
       lo <- bvTrunc sym (knownNat @64) r
       hi <- bvSelect sym (knownNat @64) (knownNat @64) r
       -- NB, little endian because X86
       return $ V.fromList [ lo, hi ]

callStoreudq
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType (BVType 8))
  -> OverrideSim p sym (LLVM arch) r args ret ()
callStoreudq sym mvar
  (regValue -> dest)
  (regValue -> vec) =
    do mem <- readGlobal mvar
       unless (V.length vec == 16) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError $ unlines
           ["Vector length mismatch in stored_qu intrinsic."
           ,"Expected <16 x i8>, but got vector of length ", show (V.length vec)
           ]
       mem' <- liftIO $ doStore
                 sym
                 mem
                 dest
                 (VectorRepr (KnownBV @8))
                 (arrayType 16 (bitvectorType (Bytes 1)))
                 noAlignment
                 vec
       writeGlobal mvar mem'


-- Excerpt from the LLVM documentation:
--
-- The llvm.objectsize intrinsic is designed to provide information to
-- the optimizers to determine at compile time whether a) an operation
-- (like memcpy) will overflow a buffer that corresponds to an object,
-- or b) that a runtime check for overflow isn’t necessary. An object
-- in this context means an allocation of a specific class, structure,
-- array, or other object.
--
-- The llvm.objectsize intrinsic takes two arguments. The first
-- argument is a pointer to or into the object. The second argument is
-- a boolean and determines whether llvm.objectsize returns 0 (if
-- true) or -1 (if false) when the object size is unknown. The second
-- argument only accepts constants.
--
-- The llvm.objectsize intrinsic is lowered to a constant representing
-- the size of the object concerned. If the size cannot be determined
-- at compile time, llvm.objectsize returns i32/i64 -1 or 0 (depending
-- on the min argument).
callObjectsize
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize sym _mvar w
  (regValue -> _ptr)
  (regValue -> flag) = liftIO $ do
    -- Ignore the pointer value, and just return the value for unknown, as
    -- defined by the documenatation.  If an `objectsize` invocation survives
    -- through compilation for us to see, that means the compiler could not
    -- determine the value.
    t <- bvIsNonzero sym flag
    z <- bvLit sym w 0
    n <- bvNotBits sym z -- NB: -1 is the boolean negation of zero
    bvIte sym t z n

callObjectsize'
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize' sym mvar w ptr flag _nullKnown = callObjectsize sym mvar w ptr flag


callCtlz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtlz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Ctlz called with disallowed zero value")
       bvCountLeadingZeros sym val

callSaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')


callCttz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCttz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Cttz called with disallowed zero value")
       bvCountTrailingZeros sym val

callCtpop
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtpop sym _mvar
  (regValue -> val) = liftIO $ bvPopcount sym val

callBitreverse
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callBitreverse sym _mvar
  (regValue -> val) = liftIO $ bvBitreverse sym val

