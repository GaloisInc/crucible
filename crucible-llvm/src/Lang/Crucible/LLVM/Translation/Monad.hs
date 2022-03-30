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
  , translationWarnings
  , functionSymbol
  , addWarning
  , LLVMTranslationWarning(..)
  , IdentMap
  , LLVMBlockInfo(..)
  , LLVMBlockInfoMap
  , buildBlockInfoMap
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
import Data.IORef (IORef, modifyIORef)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
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
import           Lang.Crucible.LLVM.Translation.BlockInfo
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

-- | A warning generated during translation
data LLVMTranslationWarning =
  LLVMTranslationWarning
    L.Symbol  -- ^ Function name in which the warning was generated
    Position  -- ^ Source position where the warning was generated
    Text      -- ^ Description of the warning

data LLVMState arch s
   = LLVMState
   { -- | Map from identifiers to associated register shape
     _identMap :: !(IdentMap s)
   , _blockInfoMap :: !(LLVMBlockInfoMap s)
   , llvmContext :: LLVMContext arch
   , _translationWarnings :: IORef [LLVMTranslationWarning]
   , _functionSymbol :: L.Symbol
   }

identMap :: Lens' (LLVMState arch s) (IdentMap s)
identMap = lens _identMap (\s v -> s { _identMap = v })

blockInfoMap :: Lens' (LLVMState arch s) (LLVMBlockInfoMap s)
blockInfoMap = lens _blockInfoMap (\s v -> s { _blockInfoMap = v })

translationWarnings :: Lens' (LLVMState arch s) (IORef [LLVMTranslationWarning])
translationWarnings = lens _translationWarnings (\s v -> s { _translationWarnings = v })

functionSymbol :: Lens' (LLVMState arch s) L.Symbol
functionSymbol = lens _functionSymbol (\s v -> s{ _functionSymbol = v })

addWarning :: Text -> LLVMGenerator s arch ret ()
addWarning warn =
  do r <- use translationWarnings
     s <- use functionSymbol
     p <- getPosition
     liftIO (modifyIORef r ((LLVMTranslationWarning s p warn):))


-- | Given a list of LLVM formal parameters and a corresponding crucible
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
             -> IORef [LLVMTranslationWarning]
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
packType :: HasPtrWidth wptr
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
