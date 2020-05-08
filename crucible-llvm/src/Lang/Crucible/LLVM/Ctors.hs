 ------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Ctors
-- Description      : Extract and manipulate the @llvm.global_ctors@ variable
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Ctors
  ( Ctor(..)
  , globalCtors
  , callCtors
  , callAllCtors
  , callCtorsCFG
  ) where

import           Data.Data (Data)
import           Data.String(fromString)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Data.Parameterized.Nonce

import           Control.Monad.Except as Except
import           Data.List (find, sortBy)
import           Data.Ord (comparing, Down(..))
import           Data.Maybe (fromMaybe)

import qualified Text.LLVM.AST as L

import           Lang.Crucible.LLVM.Translation.Instruction (callFunction)
import           Lang.Crucible.LLVM.Translation.Monad (LLVMGenerator, LLVMState(..))

-- Generating CFGs

import           Data.Map.Strict (empty)
import           Data.Text (Text)
import           GHC.TypeNats

import qualified Data.Parameterized.Context.Unsafe as Ctx


import qualified Lang.Crucible.CFG.Core as Core
import           Lang.Crucible.CFG.Expr (App(EmptyApp))
import           Lang.Crucible.CFG.Generator (FunctionDef, defineFunction)
import           Lang.Crucible.CFG.Reg (Expr(App))
import qualified Lang.Crucible.CFG.Reg as Reg
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle (HandleAllocator, mkHandle')
import           Lang.Crucible.FunctionName (functionNameFromText)
import           Lang.Crucible.ProgramLoc (Position(InternalPos))
import           Lang.Crucible.Types (UnitType, TypeRepr(UnitRepr))
import           Lang.Crucible.LLVM.Extension (LLVM, ArchWidth)
import           Lang.Crucible.LLVM.Translation.Monad (LLVMContext, _llvmTypeCtx, malformedLLVMModule)
import           Lang.Crucible.LLVM.Types (HasPtrWidth)

{- Example:

@llvm.global_ctors = appending global [3 x { i32, void ()*, i8* }] [{ i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_HkdfTest.cpp, i8* null }, { i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_gtest_all.cc, i8* null }, { i32, void ()*, i8* } { i32 65535, void ()* @_GLOBAL__sub_I_iostream.cpp, i8* null }]

-}

-- | A representation of well-typed inhabitants of the @llvm.global_ctors@ array
--
-- See https://llvm.org/docs/LangRef.html#the-llvm-global-ctors-global-variable
data Ctor = Ctor
  { ctorPriority :: Integer
  , ctorFunction :: L.Symbol
  , ctorData     :: Maybe L.Symbol
  } deriving (Data, Eq, Generic, Ord, Show, Typeable)

-- | Get the global variable representing @llvm.global_ctors@.
getGlobalCtorsGlobal :: L.Module -> Maybe L.Global
getGlobalCtorsGlobal mod_ =
  let symb = L.Symbol "llvm.global_ctors"
  in find (\x -> L.globalSym x == symb) (L.modGlobals mod_)

-- | Unpack a @ctors@ value of type @{ i32, void ()*, i8* }@ from the AST
extractCtors :: L.Value -> Maybe Ctor
extractCtors val =
  case val of
    -- This is permissive about the integer widths... No reason to get caught up.
    L.ValStruct [ L.Typed (L.PrimType (L.Integer _w0)) (L.ValInteger priority)
                , L.Typed (L.PtrTo (L.FunTy (L.PrimType L.Void) [] _bool)) (L.ValSymbol symb)
                , L.Typed (L.PtrTo (L.PrimType (L.Integer _w1))) data0_
                ] -> Just . Ctor priority symb $
                       case data0_ of
                         L.ValSymbol data_ -> Just data_
                         _                 -> Nothing
    _ -> Nothing

-- | Unpack and sort the values in @llvm.global_ctors@ by priority
globalCtors :: (MonadError String m)
            => L.Module
            -> m [Ctor]
globalCtors mod_ =
  case getGlobalCtorsGlobal mod_ >>= L.globalValue of -- in the Maybe monad
    Just (L.ValArray _ty vs) -> do

      -- Assert that each value is of the expected type.
      vs' <- forM vs $ \v ->
        fromMaybe
          (throwError $ unlines $ [ "Ill-typed value in llvm.global_ctors: "
                                  , show v
                                  ])
          (pure <$> extractCtors v)

      -- Sort the values by priority, highest to lowest.
      pure (sortBy (comparing (Down . ctorPriority)) vs')

    -- @llvm.ctors value not found, assume there are no global_ctors to run
    Nothing -> return []

    Just v  -> throwError $ unlines $
      [ "llvm.global_ctors wasn't an array"
      , "Value: " ++ show v
      ]

----------------------------------------------------------------------
-- ** callCtors

-- | Call some or all of the functions in @llvm.global_ctors@
callCtors :: (Ctor -> Bool) -- ^ Filter function
          -> L.Module
          -> LLVMGenerator s arch UnitType (Expr (LLVM arch) s UnitType)
callCtors select mod_ = do
  let err msg = malformedLLVMModule "Error loading @llvm.global_ctors" [fromString msg]
  let ty = L.FunTy (L.PrimType L.Void) [] False

  ctors <- either err (pure . filter select) (globalCtors mod_)
  forM_ ctors $ \ctor ->
    callFunction Nothing False ty (L.ValSymbol (ctorFunction ctor)) [] (const (pure ()))
  return (App EmptyApp)

-- | Call each function in @llvm.global_ctors@ in order of decreasing priority
callAllCtors :: L.Module -> LLVMGenerator s arch UnitType (Expr (LLVM arch) s UnitType)
callAllCtors = callCtors (const True)

----------------------------------------------------------------------
-- ** callCtorsCFG

-- | Make a 'LLVMGenerator' into a CFG by making it a function with no arguments
-- that returns unit.
generatorToCFG :: forall arch wptr ret. (HasPtrWidth wptr, wptr ~ ArchWidth arch, 16 <= wptr)
               => Text
               -> HandleAllocator
               -> LLVMContext arch
               -> (forall s. LLVMGenerator s arch ret (Expr (LLVM arch) s ret))
               -> TypeRepr ret
               -> IO (Core.SomeCFG (LLVM arch) Core.EmptyCtx ret)
generatorToCFG name halloc llvmctx gen ret = do
  let ?lc = _llvmTypeCtx llvmctx
  let def :: forall args. FunctionDef (LLVM arch) (LLVMState arch) args ret IO
      def _inputs = (state, gen)
        where state = LLVMState { _identMap     = empty
                                , _blockInfoMap = empty
                                , llvmContext   = llvmctx
                                }

  hand <- mkHandle' halloc (functionNameFromText name) Ctx.empty ret
  sng <- newIONonceGenerator
  (Reg.SomeCFG g, []) <- defineFunction InternalPos sng hand def
  return $! toSSA g

-- | Create a CFG that calls some of the functions in @llvm.global_ctors@.
callCtorsCFG :: forall arch wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch, 16 <= wptr)
             => (Ctor -> Bool) -- ^ Filter function
             -> L.Module
             -> HandleAllocator
             -> LLVMContext arch
             -> IO (Core.SomeCFG (LLVM arch) Core.EmptyCtx UnitType)
callCtorsCFG select mod_ halloc llvmctx = do
  generatorToCFG "llvm_global_ctors" halloc llvmctx (callCtors select mod_) UnitRepr
