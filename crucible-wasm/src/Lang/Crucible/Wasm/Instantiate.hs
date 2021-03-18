{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Wasm.Instantiate where

import Control.Exception
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Numeric.Natural

import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Sequence as Seq
import           Data.String
import           Data.Word

import Data.Parameterized.Context
import Data.Parameterized.Some

import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm

import Lang.Crucible.Simulator
import Lang.Crucible.CFG.Common (freshGlobalVar)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types

import Lang.Crucible.Wasm.Memory( WasmMem )
import Lang.Crucible.Wasm.Utils

defineModule ::
  HandleAllocator ->
  Namespace ->
  Wasm.ModuleDef ->
  InstM (Maybe Wasm.Ident, Wasm.ValidModule, ModuleInstance)
defineModule halloc ns mdef =
  do (ident,m) <- buildModule mdef
     vm <- case Wasm.validate m of
             Left verr -> throwE (ValidationError verr)
             Right vm  -> pure vm
     im <- instantiateModule halloc ns vm
     pure (ident, vm, im)


buildModule :: Wasm.ModuleDef -> InstM (Maybe Wasm.Ident, Wasm.Module)
buildModule (Wasm.RawModDef ident m) = pure (ident, m)
buildModule (Wasm.TextModDef{}) = unimplemented "build module: text"
buildModule (Wasm.BinaryModDef{}) = unimplemented "build module: binary"

data ExternalType
  = ExternalFunc   Wasm.FuncType
  | ExternalTable  Wasm.TableType
  | ExternalMem    Wasm.Memory
  | ExternalGlobal Wasm.GlobalType
 deriving (Eq,Show)

type Address = Int

type ExternalValue = (ExternalType, Address)

newtype Namespace =
  Namespace (Map.Map TL.Text ModuleInstance)

emptyNamespace :: Namespace
emptyNamespace = Namespace mempty

namespaceInsertModule :: Wasm.Ident -> ModuleInstance -> Namespace -> Namespace
namespaceInsertModule (Wasm.Ident modName) im (Namespace m) =
  Namespace (Map.insert modName im m)

namespaceLookup :: Wasm.Ident -> TL.Text -> Namespace -> Maybe ExternalValue
namespaceLookup sourceModule name ns =
  Map.lookup name . instExports =<< namespaceModule sourceModule ns

namespaceModule :: Wasm.Ident -> Namespace -> Maybe ModuleInstance
namespaceModule (Wasm.Ident sourceModule) (Namespace m) =
  Map.lookup sourceModule m

-- | This is a (potentially sparse) table mapping indices to
-- function addresses, which can then be looked up in the
-- @storeFuncs@ field of the @Store@ to get a crucible
-- function handle.  Tables like this are used to implement
-- computed functions in Wasm, e.g., for vtables and such.
data  FuncTable =
  FuncTable !Wasm.TableType !(IntMap.IntMap (Wasm.FuncType, SomeHandle))

updateFuncTable :: Int -> Wasm.FuncType -> SomeHandle -> FuncTable -> FuncTable
updateFuncTable i fty hdl (FuncTable tty m) = FuncTable tty (IntMap.insert i (fty,hdl) m)

lookupFuncTable :: Int -> FuncTable -> Maybe (Wasm.FuncType, SomeHandle)
lookupFuncTable idx (FuncTable _ m) = IntMap.lookup idx m

-- | When we translate a module, there are several layers
-- of indirection to unwind.  Static indices found in the module syntax
-- are looked up in a \"module instance\" to get an address.
-- Addresses are then looked up in the @Store@ to get Crucible or
-- Haskell layer objects, which can then be used in the translation.
-- This most closely follows the WebAssembly specification, but it
-- might be possible and desirable to undwind some of the indirections.
-- For now, I'm leaving them as-is.
data Store =
  Store
  { storeFuncs    :: Seq.Seq SomeHandle
  , storeTables   :: Seq.Seq FuncTable
  , storeMemories :: Seq.Seq (GlobalVar WasmMem)
  , storeGlobals  :: Seq.Seq WasmGlobal
  }

emptyStore :: Store
emptyStore =
  Store
  { storeFuncs = mempty
  , storeTables = mempty
  , storeMemories = mempty
  , storeGlobals = mempty
  }

allocStoreFunc :: SomeHandle -> Store -> (Address, Store)
allocStoreFunc hdl s = (addr, s')
   where
   s'   = s{ storeFuncs = storeFuncs s Seq.|> hdl }
   addr = Seq.length (storeFuncs s)

allocStoreTable :: Wasm.TableType -> Store -> (Address, Store)
allocStoreTable tty s = (addr, s')
  where
  s'   = s{ storeTables = storeTables s Seq.|> FuncTable tty mempty }
  addr = Seq.length (storeTables s)

allocStoreMemory :: GlobalVar WasmMem -> Store -> (Address, Store)
allocStoreMemory gv s = (addr, s')
  where
  s'   = s{ storeMemories = storeMemories s Seq.|> gv }
  addr = Seq.length (storeMemories s)

allocStoreGlobal :: WasmGlobal -> Store -> (Address, Store)
allocStoreGlobal wg s = (addr, s')
  where
  s'   = s{ storeGlobals = storeGlobals s Seq.|> wg }
  addr = Seq.length (storeGlobals s)

data WasmGlobal
  = ConstantGlobal ConstantValue
  | forall tp. MutableGlobal (GlobalVar tp)

data ModuleInstance =
  ModuleInstance
  { instTypes       :: Seq.Seq Wasm.FuncType
  , instFuncAddrs   :: Seq.Seq (Wasm.FuncType, Maybe Wasm.Function, Address)
  , instTableAddrs  :: Seq.Seq (Wasm.TableType, Address)
  , instMemAddrs    :: Seq.Seq (Wasm.Memory, Bool, Address)
  , instGlobalAddrs :: Seq.Seq (Wasm.GlobalType, Maybe ConstantValue, Address)
  , instExports     :: Map.Map TL.Text ExternalValue
  , instStartFunc   :: Maybe (FnHandle EmptyCtx UnitType)
  , instDataSegs    :: [(GlobalVar WasmMem, Word32, LBS.ByteString)]
  }

resolveTypeIndex :: Wasm.TypeIndex -> ModuleInstance -> Maybe Wasm.FuncType
resolveTypeIndex idx i = resolveSeq idx (instTypes i)

resolveFuncIndex :: Wasm.FuncIndex -> ModuleInstance -> Maybe (Wasm.FuncType, Maybe Wasm.Function, Address)
resolveFuncIndex idx i = resolveSeq idx (instFuncAddrs i)

resolveTableIndex :: Wasm.TableIndex -> ModuleInstance -> Maybe (Wasm.TableType, Address)
resolveTableIndex idx i = resolveSeq idx (instTableAddrs i)

resolveMemIndex :: Wasm.MemoryIndex -> ModuleInstance -> Maybe (Wasm.Memory, Bool, Address)
resolveMemIndex idx i = resolveSeq idx (instMemAddrs i)

resolveGlobalIndex ::
  Wasm.GlobalIndex ->
  ModuleInstance ->
  Maybe (Wasm.GlobalType, Maybe ConstantValue, Address)
resolveGlobalIndex idx i = resolveSeq idx (instGlobalAddrs i)

resolveSeq :: Natural -> Seq.Seq a -> Maybe a
resolveSeq idx xs
  | idx < fromIntegral (Seq.length xs) = Just (Seq.index xs (fromIntegral idx))
  | otherwise = Nothing

emptyInstance :: ModuleInstance
emptyInstance =
  ModuleInstance
  { instTypes       = mempty
  , instFuncAddrs   = mempty
  , instTableAddrs  = mempty
  , instMemAddrs    = mempty
  , instGlobalAddrs = mempty
  , instExports     = mempty
  , instStartFunc   = Nothing
  , instDataSegs    = []
  }

data ConstantValue
  = I32Val Word32
  | I64Val Word64
  | F32Val Float
  | F64Val Double

type InstM = ExceptT InstantiationFailure (StateT Store IO)

data InstantiationFailure
  = InstantiationFailure TL.Text
  | ValidationError Wasm.ValidationError

instance Show InstantiationFailure where
  show (InstantiationFailure msg) =
    "Module instantiation failure: " ++ TL.unpack msg
  show (ValidationError verr) =
    "Module validation error: " ++ show verr

instance Exception InstantiationFailure

instErr :: TL.Text -> InstM a
instErr = throwE . InstantiationFailure

runInstM :: (MonadFail m, MonadIO m) => Store -> (InstM a) -> m (a, Store)
runInstM st m =
  do x <- liftIO (runStateT (runExceptT m) st)
     case x of
       (Left err, _) -> liftIO (throwIO err)
       (Right a, st') -> pure (a, st')

allocateModule ::
  HandleAllocator ->
  Wasm.Module ->
  [ConstantValue] ->
  ModuleInstance ->
  InstM ModuleInstance
allocateModule halloc md gvals =
  allocateFuncs   >=>
  allocateTables  >=>
  allocateMems    >=>
  allocateGlobals >=>
  prepareExports  >=>
  resolveStartFn (Wasm.start md)

 where
  allocateFuncs   i = foldM (allocateFunc halloc) i (Wasm.functions md)
  allocateTables  i = foldM allocateTable i (Wasm.tables md)
  allocateMems    i = foldM (allocateMem halloc) i (Wasm.mems md)
  allocateGlobals i = foldM (allocateGlobal halloc) i (zip gvals (Wasm.globals md))
  prepareExports  i = foldM prepareExport i (Wasm.exports md)
  resolveStartFn Nothing i = pure i
  resolveStartFn (Just (Wasm.StartFunction fidx)) i =
    case resolveFuncIndex fidx i of
      Nothing -> instErr ("Could not resolve start function " <> fromString (show fidx))
      Just (_,_,addr) ->
        do st <- lift get
           case Seq.lookup addr (storeFuncs st) of
             Nothing -> instErr ("Could not resolve start function address " <> fromString (show addr))
             Just (SomeHandle h)
               | Just Refl <- testEquality (handleType h) (FunctionHandleRepr Empty UnitRepr)
               -> pure i{ instStartFunc = Just h }
               | otherwise -> instErr "Type mismatch in start function"


valueTypeToType :: Wasm.ValueType -> Some TypeRepr
valueTypeToType Wasm.I32 = Some (BVRepr (knownNat @32))
valueTypeToType Wasm.I64 = Some (BVRepr (knownNat @64))
valueTypeToType Wasm.F32 = Some (FloatRepr SingleFloatRepr)
valueTypeToType Wasm.F64 = Some (FloatRepr DoubleFloatRepr)

valueTypesToContext :: [Wasm.ValueType] -> Some (Assignment TypeRepr)
valueTypesToContext = fromList . map valueTypeToType

returnContextToType ::
  Assignment TypeRepr ctx ->
  Some TypeRepr
returnContextToType Empty        = Some UnitRepr
returnContextToType (Empty :> t) = Some t
returnContextToType ctx          = Some (StructRepr ctx)


allocateFunc ::
  HandleAllocator ->
  ModuleInstance ->
  Wasm.Function ->
  InstM ModuleInstance
allocateFunc halloc i f@Wasm.Function{ funcType = idx } =
  case resolveTypeIndex idx i of
    Just fty@Wasm.FuncType{ params = ps, results = rs } ->
      do Some args <- pure (valueTypesToContext ps)
         Some rets <- pure (valueTypesToContext rs)
         Some ret  <- pure (returnContextToType rets)
         let name = ""
         h <- liftIO (mkHandle' halloc name args ret)
         addr <- lift (state (allocStoreFunc (SomeHandle h)))
         pure i{ instFuncAddrs = instFuncAddrs i Seq.|> (fty,Just f,addr) }

    Nothing -> instErr ("Cannot resolve type index " <> fromString (show idx))

allocateTable ::
  ModuleInstance ->
  Wasm.Table ->
  InstM ModuleInstance
allocateTable i (Wasm.Table tty) =
  do addr <- lift (state (allocStoreTable tty))
     pure i{ instTableAddrs = instTableAddrs i Seq.|> (tty,addr) }

allocateMem ::
  HandleAllocator ->
  ModuleInstance ->
  Wasm.Memory ->
  InstM ModuleInstance
allocateMem halloc i mty =
  do n <- Seq.length . storeMemories <$> lift get
     let name = ("Wasm Memory " <> T.pack (show n))
     gv <- liftIO (freshGlobalVar halloc name knownRepr)
     addr <- lift (state (allocStoreMemory gv))
     pure i { instMemAddrs = instMemAddrs i Seq.|> (mty,True,addr) }

allocateGlobal ::
  HandleAllocator ->
  ModuleInstance ->
  (ConstantValue, Wasm.Global) ->
  InstM ModuleInstance
allocateGlobal _halloc i (initVal, Wasm.Global{ globalType = gt@(Wasm.Const _vt) }) =
  do addr <- lift (state (allocStoreGlobal (ConstantGlobal initVal)))
     pure i{ instGlobalAddrs = instGlobalAddrs i Seq.|> (gt,Nothing,addr) }

allocateGlobal halloc i (initVal, Wasm.Global{ globalType = gt@(Wasm.Mut vt) }) =
  do let name = "" -- TODO, find name info?
     Some tp <- pure (valueTypeToType vt)
     gv <- liftIO (freshGlobalVar halloc name tp)
     addr <- lift (state (allocStoreGlobal (MutableGlobal gv)))
     pure i{ instGlobalAddrs = instGlobalAddrs i Seq.|> (gt,Just initVal,addr) }


prepareExport ::
  ModuleInstance ->
  Wasm.Export ->
  InstM ModuleInstance
prepareExport i Wasm.Export{..} =
  do exval <-
        case desc of
          Wasm.ExportFunc fidx ->
            case resolveFuncIndex fidx i of
              Just (fty, _, addr) -> pure (ExternalFunc fty, addr)
              Nothing -> instErr ("Could not resolve function index " <> fromString (show fidx))
          Wasm.ExportTable tidx ->
            case resolveTableIndex tidx i of
              Just (tty, addr) -> pure (ExternalTable tty, addr)
              Nothing -> instErr ("Could not resolve table index " <> fromString (show tidx))
          Wasm.ExportMemory midx ->
            case resolveMemIndex midx i of
              Just (mty, _, addr) -> pure (ExternalMem mty, addr)
              Nothing -> instErr ("Could not resolve memory index " <> fromString (show midx))
          Wasm.ExportGlobal gidx ->
            case resolveGlobalIndex gidx i of
              Just (gty, _, addr) -> pure (ExternalGlobal gty, addr)
              Nothing -> instErr ("Could not resolve global index " <> fromString (show gidx))
     pure i{ instExports = Map.insert name exval (instExports i) }

instantiateModule ::
  HandleAllocator ->
  Namespace ->
  Wasm.ValidModule ->
  InstM ModuleInstance
instantiateModule halloc ns (Wasm.getModule -> md) =
  do i0 <- instantiateImports ns md
     gvals <- mapM (computeGlobalValue i0) (Wasm.globals md)
     i <- allocateModule halloc md gvals i0

     mapM_ (installElemSegment i) (Wasm.elems md)
     ds <- mapM (computeDataSegment i) (Wasm.datas md)
     pure i{ instDataSegs = ds }


computeDataSegment ::
  ModuleInstance ->
  Wasm.DataSegment ->
  InstM (GlobalVar WasmMem, Word32, LBS.ByteString)
computeDataSegment i Wasm.DataSegment{ .. } =
  do st <- lift get
     case resolveMemIndex memIndex i of
       Nothing -> instErr ("Could not resolve memory index " <> fromString (show memIndex))
       Just (_,_,addr) ->
         case Seq.lookup addr (storeMemories st) of
           Nothing -> instErr ("Could not resolve memory address " <> fromString (show addr))
           Just gv ->
             evalConst i offset >>= \case
               I32Val x -> pure (gv, x, chunk)
               _ -> instErr "data segment offset type mismatch"

installElemSegment ::
  ModuleInstance ->
  Wasm.ElemSegment ->
  InstM ()
installElemSegment im es@Wasm.ElemSegment{ .. } =
  do I32Val tblOff <- evalConst im offset
     st <- lift get
     debug "installing element segment"
     debug (show es)
     debug (show (instTableAddrs im))
     case updStore (fromIntegral tblOff) st of
       Nothing  -> instErr ("failed to evaluate element segment: " <> TL.pack (show es))
       Just st' -> lift (put st')

 where
  updTable st ft (loc, (fty,_,faddr)) =
    do hdl <- Seq.lookup faddr (storeFuncs st)
       pure (updateFuncTable loc fty hdl ft)

  updStore :: Int -> Store -> Maybe Store
  updStore off st =
    do (Wasm.TableType (Wasm.Limit lmin _) Wasm.AnyFunc, addr) <- resolveTableIndex tableIndex im
       functab <- Seq.lookup addr (storeTables st)
       guard (toInteger off + toInteger (length funcIndexes) <= toInteger lmin)
       funaddrs <- mapM (\i -> resolveFuncIndex i im) funcIndexes
       functab' <- foldM (updTable st) functab (zip [ off .. ] funaddrs)
       pure st{ storeTables = Seq.update addr functab' (storeTables st) }


computeGlobalValue ::
  ModuleInstance ->
  Wasm.Global ->
  InstM ConstantValue
computeGlobalValue i (Wasm.Global{ globalType = t, initializer = expr }) =
  do let i' = emptyInstance{ instGlobalAddrs = instGlobalAddrs i }
     c <- evalConst i' expr
     case t of
        Wasm.Const vt -> checkConstantType c vt
        Wasm.Mut vt -> checkConstantType c vt
     return c

checkConstantType :: ConstantValue -> Wasm.ValueType -> InstM ()
checkConstantType _ _ = return () -- TODO!

evalConst ::
  ModuleInstance ->
  Wasm.Expression ->
  InstM ConstantValue
evalConst _i [Wasm.I32Const x] = pure (I32Val x)
evalConst _i [Wasm.I64Const x] = pure (I64Val x)
evalConst _i [Wasm.F32Const x] = pure (F32Val x)
evalConst _i [Wasm.F64Const x] = pure (F64Val x)

evalConst i [Wasm.GetGlobal idx] =
  do st <- lift get
     case resolveGlobalIndex idx i of
       Just (_,_,addr) | Just gv <- Seq.lookup addr (storeGlobals st)  ->
         case gv of
           ConstantGlobal v -> pure v
           _ -> instErr ("global index not a constant " <> fromString (show idx))
       _ -> instErr ("could not resolve global index " <> fromString (show idx))

evalConst _ _ = instErr "expression not a constant!"

bindImport :: Namespace -> ModuleInstance -> Wasm.Import -> InstM ExternalValue
bindImport ns i Wasm.Import{ .. } =
  case namespaceLookup (Wasm.Ident sourceModule) name ns of
    Just (et,a)
      | Just et' <- matchImportDesc i desc et -> pure (et',a)
      | otherwise -> instErr ("Entity did not have expected type" <> sourceModule <> " " <> name)
    Nothing -> instErr ("Could not lookup entity " <> sourceModule <> " " <> name)

matchImportDesc :: ModuleInstance -> Wasm.ImportDesc -> ExternalType -> Maybe ExternalType
matchImportDesc i (Wasm.ImportFunc tidx) (ExternalFunc t)
  | Just t' <- resolveTypeIndex tidx i, t == t' = Just (ExternalFunc t)
  | otherwise = Nothing

matchImportDesc _ (Wasm.ImportGlobal gt) (ExternalGlobal gt')
  | gt == gt' = Just (ExternalGlobal gt)

matchImportDesc _ (Wasm.ImportTable (Wasm.TableType lim tt))
                    (ExternalTable (Wasm.TableType lim' tt'))
  | tt == tt' && matchLim lim lim' = Just (ExternalTable (Wasm.TableType lim tt))

matchImportDesc _ (Wasm.ImportMemory mt) (ExternalMem (Wasm.Memory mt'))
  | matchLim mt mt' = Just (ExternalMem (Wasm.Memory mt))

matchImportDesc _ _ _ = Nothing

-- TODO double check that we have correctly implemented the limit checks
--  as specified in the Wasm spec.  It's a little tricky to be sure that
--  we've gotten the inequalities in the right places, etc.
matchLim ::
  Wasm.Limit {- ^ requested -} ->
  Wasm.Limit {- ^ actual -} ->
  Bool
matchLim (Wasm.Limit rmin rmax) (Wasm.Limit amin amax) =
  rmin <= amin &&
  case (rmax, amax) of
    (Nothing, _)      -> True
    (Just _, Nothing) -> False
    (Just x, Just y)  -> x >= y

instantiateImports ::
  Namespace ->
  Wasm.Module ->
  InstM ModuleInstance
instantiateImports ns md =
  do let i0 = emptyInstance{ instTypes = Seq.fromList (Wasm.types md) }
     evs <- mapM (bindImport ns i0) (Wasm.imports md)
     pure
       ModuleInstance
       { instTypes       = Seq.fromList (Wasm.types md)
       , instFuncAddrs   = Seq.fromList [ (fty,Nothing,a) | (ExternalFunc fty, a) <- evs ]
       , instTableAddrs  = Seq.fromList [ (tty,a) | (ExternalTable tty,  a) <- evs ]
       , instMemAddrs    = Seq.fromList [ (mty,False,a) | (ExternalMem mty,    a) <- evs ]
       , instGlobalAddrs = Seq.fromList [ (gty,Nothing,a) | (ExternalGlobal gty, a) <- evs ]
       , instExports     = mempty
       , instStartFunc   = Nothing
       , instDataSegs    = []
       }
