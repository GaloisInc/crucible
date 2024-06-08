------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Globals
-- Description      : Operations for working with LLVM global variables
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides support for dealing with LLVM global variables,
-- including initial allocation and populating variables with their
-- initial values.  A @GlobalInitializerMap@ is constructed during
-- module translation and can subsequently be used to populate
-- global variables.  This can either be done all at once using
-- @populateAllGlobals@; or it can be done in a more selective manner,
-- using one of the other \"populate\" operations.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Globals
  ( initializeMemory
  , initializeAllMemory
  , initializeMemoryConstGlobals
  , populateGlobal
  , populateGlobals
  , populateAllGlobals
  , populateConstGlobals

  , GlobalInitializerMap
  , makeGlobalMap
  ) where

import           Control.Arrow ((&&&))
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Except (MonadError(..))
import           Control.Lens hiding (op, (:>) )
import           Data.List (foldl', genericLength, isPrefixOf)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.String
import           Control.Monad.State (StateT, runStateT, get, put)
import           Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx

import qualified Text.LLVM.AST as L

import           Data.Parameterized.NatRepr as NatRepr

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Functions (allocLLVMFunPtrs)
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.PrettyPrint as LPP
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.Backend

import           What4.Interface

import           GHC.Stack

------------------------------------------------------------------------
-- GlobalInitializerMap

-- | A @GlobalInitializerMap@ records the initialized values of globals in an @L.Module@.
--
-- The @Left@ constructor is used to signal errors in translation,
-- which can happen when:
--  * The declaration is ill-typed
--  * The global isn't linked (@extern global@)
--
-- The @Nothing@ constructor is used to signal that the global isn't actually a
-- compile-time constant.
--
-- These failures are as granular as possible (attached to the values)
-- so that simulation still succeeds if the module has a bad global that the
-- verified function never touches.
--
-- To actually initialize globals, saw-script translates them into
-- instances of @MemModel.LLVMVal@.
type GlobalInitializerMap = Map L.Symbol (L.Global, Either String (MemType, Maybe LLVMConst))


------------------------------------------------------------------------
-- makeGlobalMap

-- | @makeGlobalMap@ creates a map from names of LLVM global variables
-- to the values of their initializers, if any are included in the module.
makeGlobalMap :: forall arch wptr. (?lc :: TypeContext, HasPtrWidth wptr)
              => LLVMContext arch
              -> L.Module
              -> GlobalInitializerMap
makeGlobalMap ctx m = foldl' addAliases globalMap1 (Map.toList (llvmGlobalAliases ctx))

  where
   addAliases mp (glob, aliases) =
        case Map.lookup glob mp of
          Just initzr -> insertAll (map L.aliasName (Set.toList aliases)) initzr mp
          Nothing     -> mp -- should this be an error/exception?

   globalMap0 = Map.fromList $ map (\g -> (L.globalSym g, g)) (L.modGlobals m)
   globalMap1 = Map.map (id &&& globalToConst) globalMap0
   loadRelConstInitMap = buildLoadRelConstInitMap globalMap0 m

   insertAll ks v mp = foldr (flip Map.insert v) mp ks

   -- Catch the error from @transConstant@, turn it into @Either@
   globalToConst :: L.Global -> Either String (MemType, Maybe LLVMConst)
   globalToConst g =
     catchError
       (globalToConst' g)
       (\err -> Left $
         "Encountered error while processing global "
           ++ show (LPP.ppSymbol (L.globalSym g))
           ++ ": "
           ++ err)

   globalToConst' :: forall m. (MonadError String m)
                  => L.Global -> m (MemType, Maybe LLVMConst)
   globalToConst' g =
     do let ?lc  = ctx^.llvmTypeCtx -- implicitly passed to transConstant
        let (gty, mbGval) =
              -- Check if a global variable was passed as an argument to
              -- llvm.load.relative.i* (i.e., if it is reltable-like), and if
              -- so, use an altered value for the constant initializer that uses
              -- `bitcast`. See
              -- Note [Undoing LLVM's relative table lookup conversion pass].
              case Map.lookup (L.globalSym g) loadRelConstInitMap of
                Just (L.Typed constInitTy constInitVal) ->
                  (constInitTy, Just constInitVal)
                Nothing ->
                  (L.globalType g, L.globalValue g)
        mt <- liftMemType gty
        mbVal <- traverse (transConstant' mt) mbGval
        return (mt, mbVal)

-------------------------------------------------------------------------
-- initializeMemory

-- | Build the initial memory for an LLVM program.  Note, this process
-- allocates space for global variables, but does not set their
-- initial values.
initializeAllMemory
   :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
      , ?memOpts :: MemOptions )
   => bak
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeAllMemory = initializeMemory (const True)

initializeMemoryConstGlobals
   :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
      , ?memOpts :: MemOptions )
   => bak
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeMemoryConstGlobals = initializeMemory (L.gaConstant . L.globalAttrs)

initializeMemory
   :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
      , ?memOpts :: MemOptions )
   => (L.Global -> Bool)
   -> bak
   -> LLVMContext arch
   -> L.Module
   -> IO (MemImpl sym)
initializeMemory predicate bak llvm_ctx llvmModl = do
   -- Create initial memory of appropriate endianness
   let ?lc = llvm_ctx^.llvmTypeCtx
   let dl = llvmDataLayout ?lc
   let endianness = dl^.intLayout
   mem0 <- emptyMem endianness

   -- allocate pointers values for function symbols, but do not yet bind them to
   -- function handles
   mem <- allocLLVMFunPtrs bak llvm_ctx mem0 llvmModl

   -- Allocate global values
   let globAliases = llvmGlobalAliases llvm_ctx
   let globals     = L.modGlobals llvmModl
   let globalMap   = Map.fromList $ map (\g -> (L.globalSym g, g)) globals
   let loadRelConstInitMap = buildLoadRelConstInitMap globalMap llvmModl
   gs_alloc <- mapM (\g -> do
                        let err msg = malformedLLVMModule
                                    ("Invalid type for global" <> fromString (show (L.globalSym g)))
                                    [fromString msg]
                        -- Check if a global variable was passed as an argument
                        -- to llvm.load.relative.i* (i.e., if it is
                        -- reltable-like), and if so, use an altered type that
                        -- uses pointers instead of `i32`s. Also, do not use the
                        -- original global's alignment. See
                        -- Note [Undoing LLVM's relative table lookup conversion pass].
                        (ty, mbGlobAlign) <-
                          case Map.lookup (L.globalSym g) loadRelConstInitMap of
                            Just constInit -> do
                              ty <- either err return $
                                    liftMemType $
                                    L.typedType constInit
                              -- Return Nothing for the alignment so that we
                              -- will instead use crucible-llvm's alignment
                              -- inference to compute the alignment of the
                              -- new constant initializer.
                              pure (ty, Nothing)
                            Nothing -> do
                              ty <- either err return $ liftMemType $ L.globalType g
                              pure (ty, L.globalAlign g)
                        let sz      = memTypeSize dl ty
                        let tyAlign = memTypeAlign dl ty
                        let aliases = map L.aliasName . Set.toList $
                              fromMaybe Set.empty (Map.lookup (L.globalSym g) globAliases)
                        -- LLVM documentation regarding global variable alignment:
                        --
                        -- An explicit alignment may be specified for
                        -- a global, which must be a power of 2. If
                        -- not present, or if the alignment is set to
                        -- zero, the alignment of the global is set by
                        -- the target to whatever it feels
                        -- convenient. If an explicit alignment is
                        -- specified, the global is forced to have
                        -- exactly that alignment.
                        alignment <-
                          case mbGlobAlign of
                            Just a | a > 0 ->
                              case toAlignment (toBytes a) of
                                Nothing -> fail $ "Invalid alignemnt: " ++ show a ++ "\n  " ++
                                                  "specified for global: " ++ show (L.globalSym g)
                                Just al -> return al
                            _ -> return tyAlign
                        return (g, aliases, sz, alignment))
                    globals
   allocGlobals bak (filter (\(g, _, _, _) -> predicate g) gs_alloc) mem


------------------------------------------------------------------------
-- ** populateGlobals

-- | Populate the globals mentioned in the given @GlobalInitializerMap@
--   provided they satisfy the given filter function.
--
--   This will (necessarily) populate any globals that the ones in the
--   filtered list transitively reference.
populateGlobals ::
  ( ?lc :: TypeContext
  , ?memOpts :: MemOptions
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
  , IsSymBackend sym bak) =>
  (L.Global -> Bool)   {- ^ Filter function, globals that cause this to return true will be populated -} ->
  bak ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobals select bak gimap mem0 = foldM f mem0 (Map.elems gimap)
  where
  f mem (gl, _) | not (select gl)    = return mem
  f _   (_,  Left msg)               = fail msg
  f mem (gl, Right (mty, Just cval)) = populateGlobal bak gl mty cval gimap mem
  f mem (gl, Right (mty, Nothing))   = populateExternalGlobal bak gl mty mem


-- | Populate all the globals mentioned in the given @GlobalInitializerMap@.
populateAllGlobals ::
  ( ?lc :: TypeContext
  , ?memOpts :: MemOptions
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
  , IsSymBackend sym bak) =>
  bak ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateAllGlobals = populateGlobals (const True)


-- | Populate only the constant global variables mentioned in the
--   given @GlobalInitializerMap@ (and any they transitively refer to).
populateConstGlobals ::
  ( ?lc :: TypeContext
  , ?memOpts :: MemOptions
  , 16 <= wptr
  , HasPtrWidth wptr
  , HasLLVMAnn sym
  , IsSymBackend sym bak) =>
  bak ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateConstGlobals = populateGlobals f
  where f = L.gaConstant . L.globalAttrs


-- | Ordinarily external globals do not receive initalizing writes.  However,
--   when 'lax-loads-and-stores` is enabled in the `stable-symbolic` mode, we
--   populate external global variables with fresh bytes.
populateExternalGlobal ::
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymBackend sym bak
  , HasLLVMAnn sym
  , HasCallStack
  , ?memOpts :: MemOptions
  ) =>
  bak ->
  L.Global {- ^ The global to populate -} ->
  MemType {- ^ Type of the global -} ->
  MemImpl sym ->
  IO (MemImpl sym)
populateExternalGlobal bak gl memty mem
  | laxLoadsAndStores ?memOpts
  , indeterminateLoadBehavior ?memOpts == StableSymbolic

  =  do let sym = backendGetSym bak
        bytes <- freshConstant sym emptySymbol
                    (BaseArrayRepr (Ctx.singleton $ BaseBVRepr ?ptrWidth)
                        (BaseBVRepr (knownNat @8)))
        let dl = llvmDataLayout ?lc
        let sz = memTypeSize dl memty
        let tyAlign = memTypeAlign dl memty
        sz' <- bvLit sym PtrWidth (bytesToBV PtrWidth sz)
        ptr <- doResolveGlobal bak mem (L.globalSym gl)
        doArrayConstStore bak mem ptr tyAlign bytes sz'

  | otherwise = return mem


-- | Write the value of the given LLVMConst into the given global variable.
--   This is intended to be used at initialization time, and will populate
--   even read-only global data.
populateGlobal :: forall sym bak wptr.
  ( ?lc :: TypeContext
  , 16 <= wptr
  , HasPtrWidth wptr
  , IsSymBackend sym bak
  , HasLLVMAnn sym
  , ?memOpts :: MemOptions
  , HasCallStack
  ) =>
  bak ->
  L.Global {- ^ The global to populate -} ->
  MemType {- ^ Type of the global -} ->
  LLVMConst {- ^ Constant value to initialize with -} ->
  GlobalInitializerMap ->
  MemImpl sym ->
  IO (MemImpl sym)
populateGlobal bak gl memty cval giMap mem =
  do let sym = backendGetSym bak
     let alignment = memTypeAlign (llvmDataLayout ?lc) memty

     -- So that globals can populate and look up the globals they reference
     -- during initialization
     let populateRec :: HasCallStack
                     => L.Symbol -> StateT (MemImpl sym) IO (LLVMPtr sym wptr)
         populateRec symbol = do
           memimpl0 <- get
           memimpl <-
            case Map.lookup symbol (memImplGlobalMap mem) of
              Just _  -> pure memimpl0 -- We already populated this one
              Nothing ->
                -- For explanations of the various modes of failure, see the
                -- comment on 'GlobalInitializerMap'.
                case Map.lookup symbol giMap of
                  Nothing -> fail $ unlines $
                    [ "Couldn't find global variable: " ++ show symbol ]
                  Just (glob, Left str) -> fail $ unlines $
                    [ "Couldn't find global variable's initializer: " ++
                        show symbol
                    , "Reason:"
                    , str
                    , "Full definition:"
                    , show glob
                    ]
                  Just (glob, Right (_, Nothing)) -> fail $ unlines $
                    [ "Global was not a compile-time constant:" ++ show symbol
                    , "Full definition:"
                    , show glob
                    ]
                  Just (glob, Right (memty_, Just cval_)) ->
                    liftIO $ populateGlobal bak glob memty_ cval_ giMap memimpl0
           put memimpl
           liftIO $ doResolveGlobal bak memimpl symbol

     ty <- toStorableType memty
     ptr <- doResolveGlobal bak mem (L.globalSym gl)
     (val, mem') <- runStateT (constToLLVMValP sym populateRec cval) mem
     storeConstRaw bak mem' ptr ty alignment val

------------------------------------------------------------------------
-- ** llvm.load.relative constant initializers

-- | A map of global variable names ('L.Symbol's) that appear as arguments to
-- calls to the @llvm.load.relative.i*@ intrinsic. See
-- @Note [Undoing LLVM's relative table lookup conversion pass]@ for why we need
-- this.
type LoadRelConstInitMap = Map L.Symbol (L.Typed L.Value)

-- | @buildLoadRelConstInitMap globalMap m@ takes a 'L.Module' (@m@) and a map
-- of global variable symbols to their definitions (@globalMap@) and computes
-- a 'LoadRelConstInitMap'. See
-- @Note [Undoing LLVM's relative table lookup conversion pass]@ for why we need
-- to do this.
buildLoadRelConstInitMap ::
  Map L.Symbol L.Global ->
  L.Module ->
  LoadRelConstInitMap
buildLoadRelConstInitMap globalMap m = foldMap defineConstInits (L.modDefines m)
  where
    defineConstInits :: L.Define -> LoadRelConstInitMap
    defineConstInits def = foldMap basicBlockConstInits (L.defBody def)

    basicBlockConstInits :: L.BasicBlock -> LoadRelConstInitMap
    basicBlockConstInits bb = foldMap stmtConstInits (L.bbStmts bb)

    stmtConstInits :: L.Stmt -> LoadRelConstInitMap
    stmtConstInits (L.Result _ instr _) = instrConstInits instr
    stmtConstInits (L.Effect instr _)   = instrConstInits instr

    instrConstInits :: L.Instr -> LoadRelConstInitMap
    instrConstInits (L.Call _ _ (L.ValSymbol fun) [ptr, _offset])
      | L.Symbol funStr <- fun
      , "llvm.load.relative.i" `isPrefixOf` funStr
      , Just (gs, foldedConstTy, foldedConstInit) <-
          foldLoadRelConstInit (L.typedValue ptr)
      = Map.singleton gs (L.Typed foldedConstTy foldedConstInit)
    instrConstInits _ =
      Map.empty

    -- Check if the first argument to a call to llvm.load.relative.i* is
    -- "reltable-like", and if so, return @Just (symb, ty, val)@, where:
    --
    -- - @symb@ is the name of the global variable corresponding to the
    --   argument.
    --
    -- - @ty@ is the type of the global variable's new constant initializer.
    --
    -- - @val@ is the new constant initializer value.
    --
    -- See Note [Undoing LLVM's relative table lookup conversion pass] for an
    -- explanation of what "reltable-like" means.
    foldLoadRelConstInit :: L.Value -> Maybe (L.Symbol, L.Type, L.Value)
    foldLoadRelConstInit (L.ValSymbol s)
      | Just global <- Map.lookup s globalMap
      , Just constInit <- L.globalValue global
      -- Check that the type of the global variable is
      -- [<constInitElems> x i32].
      , L.ValArray (L.PrimType (L.Integer 32)) constInitElems <- constInit
      , Just foldedConstInitElems <-
          traverse (foldLoadRelConstInitElem global) constInitElems
      = Just ( L.globalSym global
             , L.Array (genericLength constInitElems) ptrToI8Type
             , L.ValArray ptrToI8Type foldedConstInitElems
             )
    foldLoadRelConstInit (L.ValConstExpr (L.ConstConv L.BitCast tv _)) =
      foldLoadRelConstInit (L.typedValue tv)
    foldLoadRelConstInit _ =
      Nothing

    -- Check that an element of a constant initializer is of the form
    -- `trunc(ptrtoint x - ptrtoint p)`, and if so, return `Just x`. Otherwise,
    -- return Nothing.
    foldLoadRelConstInitElem :: L.Global -> L.Value -> Maybe L.Value
    foldLoadRelConstInitElem global constInitElem
      | L.ValConstExpr
          (L.ConstConv L.Trunc
            (L.Typed { L.typedValue =
              L.ValConstExpr
                (L.ConstArith
                  (L.Sub _ _)
                  (L.Typed { L.typedValue =
                    L.ValConstExpr (L.ConstConv L.PtrToInt x _) })
                  (L.ValConstExpr (L.ConstConv L.PtrToInt p _))) })
            _truncTy) <- constInitElem
      , L.ValSymbol pSym <- L.typedValue p
      , L.globalSym global == pSym
      = Just (L.ValConstExpr (L.ConstConv L.BitCast x ptrToI8Type))

      | otherwise
      = Nothing

    -- Type type i8*.
    ptrToI8Type :: L.Type
    ptrToI8Type = L.PtrTo $ L.PrimType $ L.Integer 8

{-
Note [Undoing LLVM's relative table lookup conversion pass]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Clang 14.0.0+ include a `rel-lookup-table-converter` optimization pass that is
enabled with -O1 or greater. This optimization usually applies to code that
looks like table lookups. For instance, this pass would take this C code:

  const char *F(int tag) {
    static const char *const table[] = {
      "A",
      "B",
    };

    return table[tag];
  }

And optimize it to LLVM bitcode that looks like this:

  @reltable.F = internal unnamed_addr constant [2 x i32] [i32 trunc (i64 sub (i64 ptrtoint ([2 x i8]* @.str to i64), i64 ptrtoint ([2 x i32]* @reltable.F to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint ([2 x i8]* @.str.1 to i64), i64 ptrtoint ([2 x i32]* @reltable.F to i64)) to i32)], align 4
  @.str = private unnamed_addr constant [2 x i8] c"A\00", align 1
  @.str.1 = private unnamed_addr constant [2 x i8] c"B\00", align 1

  define dso_local i8* @F(i32 noundef %0) local_unnamed_addr #0 {
    %2 = sext i32 %0 to i64
    %3 = shl i64 %2, 2
    %4 = call i8* @llvm.load.relative.i64(i8* bitcast ([2 x i32]* @reltable.F to i8*), i64 %3)
    ret i8* %4
  }

There are several remarkable things about this LLVM bitcode:

* The definition of @F is backed up a relative lookup table @reltable.F.
  Invoking @F is tantamount to looking up a value in the table by using the
  special @llvm.load.relative.i* intrinsic, which is described here:
  https://releases.llvm.org/17.0.1/docs/LangRef.html#llvm-load-relative-intrinsic

* The definition of @reltable.F itself is quite unorthodox. Conceptually, it is
  an array of strings (@.str and @.str1), but where each element of the array
  contains the relative offset of the string to the table itself. As a result,
  it is not an array of pointers, but rather an array of i32s!

* Each i32 in the array consists of the address of each string represented as an
  integer (obtained via ptrtoint) subtracted from the address of the table,
  followed by a trunc to ensure the result fits in an i32. (One weird result of
  this encoding is that @reltable.F is defined recursively in terms of itself.)

This optimization pass is handy for Clang's purposes, as it allows Clang to
produce more efficient assembly code. Unfortunately, this encoding is quite
problematic for crucible-llvm. The problem ultimately lies in the fact that we
are performing pointer arithmetic on pointers from completely different
allocation regions (e.g., subtracting @reltable.F from @.str), which
crucible-llvm has no ability to reason about. (This optimization is also
problematic for CHERI, which tracks pointer provenance in a similar way—see
https://github.com/CTSRD-CHERI/llvm-project/issues/572).

What's more, we don't have a reliable way of avoiding this optimization, as
Clang's optimization pass manager doesn't provide a way to disable individual
passes via command-line arguments. We could tell users to downgrade from -O1
from -O0, but this would be a pretty severe workaround.

Our solution is to manually "undo" the optimization ourselves. That is, we
replace the definition of @reltable.F with bitcode that looks like this:

  @reltable.F = internal unnamed_addr constant [2 x i8*] [i8* bitcast ([2 x i8]* @.str to i8*), i8* bitcast ([2 x i8]* @.str.1 to i8*)]

This avoids any problematic uses of pointer arithmetic altogether. Here is how
we do this:

1. When processing global definitions in an LLVM module, we identify the names
   of all globals that are passed as the first argument to
   @llvm.load.relative.i*. We'll refer to these as "reltable-like" globals.

   This check assumes that the globals are passed directly to
   @llvm.load.relative.i*, rather than going through any intermediate
   variables. This is likely a safe assumption to make, considering that
   Clang's -O1 settings will usually optimize away any such intermediate
   variables.

2. For each reltable-like global, we check that the global has a constant
   initializer of type [<N> x i32] where each element is of the form
   `trunc (ptrtoint x - ptrtoint p)`. This is somewhat fragile, but the
   documentation for llvm.load.relative.i* implies that LLVM itself checks
   for code that looks like this, so we follow suit.

3. For each element in the constant initializer array, we turn
   `trunc (ptrtoint x - ptrtoint p)` into `bitcast x to i8*`. Note that the
   this changes its type from `i32` to `i8*`.

4. When translating a global definition to Crucible, we check if the global
   is reltable-like. If so, we replace its constant initializer with the
   `bitcast`ed version. We must also make sure that the global is translated
   at type `[<N> x i8*]` rather than `[<N> x i32]`.

   Furthermore, we must also make sure not to use the original global's
   alignment, as the `bitcast`ed version will almost certainly have different
   alignment requirements. We rely on crucible-llvm's alignment inference to
   figure out what the new alignment should be.

5. In the override for llvm.load.relative.i*, we make sure to adjust the second
   argument (the pointer offset). This is because LLVM assumes that the offset
   is for something of type `[<N> x i32]`, so an offset value of 4 (four bytes)
   refers to the first element, an offset value of 8 refers to the second
   element, and so on. On the other hand, something of type `[<N> x i8*]` will
   likely require different offsets, since the size of a pointer may be greater
   than four bytes (e.g., it is eight bytes on 64-bit architectures).

   To account for this difference, we divide the offset value by 4 and then
   multiply it by the number of bytes in the size of a pointer.

It is worth emphasizing that this is a very ad hoc workaround. At the same time,
it is likely the best we can do without substantially changing how crucible-llvm
tracks pointer provenance.
-}
