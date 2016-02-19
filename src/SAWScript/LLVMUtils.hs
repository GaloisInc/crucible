{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE CPP #-}
{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMUtils where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Lens
import Control.Monad.State
import qualified Data.Map as Map
import Data.Maybe
import Verifier.LLVM.Backend
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Codebase hiding (Global)
import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals
import Verifier.SAW.SharedTerm
import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.LLVMExpr
import SAWScript.Utils

type SpecBackend = SAWBackend SAWCtx
type SpecPathState = Path SpecBackend
type SpecLLVMValue = SharedTerm SAWCtx

resolveType :: Codebase s -> MemType -> MemType
resolveType cb (PtrType ty) = PtrType $ resolveSymType cb ty
resolveType _ ty = ty

resolveSymType :: Codebase s -> SymType -> SymType
resolveSymType cb (MemType mt) = MemType $ resolveType cb mt
resolveSymType cb ty@(Alias i) =
  fromMaybe ty $ lookupAlias i where ?lc = cbLLVMContext cb
resolveSymType _ ty = ty

scLLVMValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scLLVMValue sc ty name = scFreshGlobal sc name ty

addrPlusOffsetSim :: (Functor m, MonadIO m) =>
                     SBETerm sbe -> Offset
                  -> Simulator sbe m (SBETerm sbe)
addrPlusOffsetSim a o = do
  sbe <- gets symBE
  w <- ptrBitwidth <$> getDL
  ot <- liftSBE $ termInt sbe w (fromIntegral o)
  liftSBE $ applyTypedExpr sbe (PtrAdd a ot)

addrPlusOffset :: DataLayout -> SharedContext SAWCtx -> SpecLLVMValue -> Offset
               -> IO SpecLLVMValue
addrPlusOffset dl sc a o = do
  let w = fromIntegral (ptrBitwidth dl)
  ot <- scBvConst sc w (fromIntegral o)
  wt <- scNat sc w
  scBvAdd sc wt a ot

structFieldAddr :: (Functor m, MonadIO m) =>
                   StructInfo -> Int -> SBETerm sbe
                -> Simulator sbe m (SBETerm sbe)
structFieldAddr si idx base =
  case siFieldOffset si idx of
    Just off -> addrPlusOffsetSim base off
    Nothing -> fail $ "Struct field index " ++ show idx ++ " out of bounds"

storePathState :: SBE SpecBackend
               -> SharedTerm SAWCtx
               -> MemType
               -> SharedTerm SAWCtx
               -> SpecPathState
               -> IO SpecPathState
storePathState sbe dst tp val ps = do
  (c, m') <- sbeRunIO sbe (memStore sbe (ps ^. pathMem) dst tp val 0)
  ps' <- addAssertion sbe c ps
  return (ps' & pathMem .~ m')

loadPathState :: SBE SpecBackend
              -> SharedTerm SAWCtx
              -> MemType
              -> SpecPathState
              -> IO (SpecLLVMValue, SpecLLVMValue)
loadPathState sbe src tp ps =
  sbeRunIO sbe (memLoad sbe (ps ^. pathMem) tp src 0)

loadGlobal :: SBE SpecBackend
           -> GlobalMap SpecBackend
           -> Symbol
           -> MemType
           -> SpecPathState
           -> IO (SpecLLVMValue, SpecLLVMValue)
loadGlobal sbe gm sym tp ps = do
  case Map.lookup sym gm of
    Just addr -> loadPathState sbe addr tp ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

storeGlobal :: SBE SpecBackend
            -> GlobalMap SpecBackend
            -> Symbol
            -> MemType
            -> SpecLLVMValue
            -> SpecPathState
            -> IO SpecPathState
storeGlobal sbe gm sym tp v ps = do
  case Map.lookup sym gm of
    Just addr -> storePathState sbe addr tp v ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

-- | Add assertion for predicate to path state.
addAssertion :: SBE SpecBackend -> SharedTerm SAWCtx -> SpecPathState -> IO SpecPathState
addAssertion sbe x p = do
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

allocSome :: (Functor sbe, Functor m, MonadIO m) =>
             SBE sbe
          -> DataLayout
          -> Integer
          -> MemType
          -> Simulator sbe m (SBETerm sbe)
allocSome sbe dl n ty = do
  let aw = ptrBitwidth dl
  sz <- liftSBE (termInt sbe aw n)
  malloc ty aw sz

-- LLVM memory operations

readLLVMTermAddr :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                    [SBETerm sbe] -> LLVMExpr
                 -> Simulator sbe m (SBETerm sbe)
readLLVMTermAddr args (Term e) =
  case e of
    Arg _ _ _ -> fail "Can't read address of argument"
    Global s _ -> evalExprInCC "readLLVMTerm:Global" (SValSymbol s)
    Deref ae _ -> readLLVMTerm args ae 1
    StructField ae si idx _ ->
      structFieldAddr si idx =<< readLLVMTerm args ae 1
    ReturnValue _ -> fail "Can't read address of return value"

writeLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                 [SBETerm sbe]
              -> (LLVMExpr, SBETerm sbe, Integer)
              -> Simulator sbe m ()
writeLLVMTerm args (e, t, cnt) = do
  addr <- readLLVMTermAddr args e
  let ty = lssTypeOfLLVMExpr e
      ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
          | otherwise = ty
  dl <- getDL
  store ty' t addr (memTypeAlign dl ty')

readLLVMTerm :: (Functor m, Monad m, MonadIO m, Functor sbe) =>
                [SBETerm sbe]
             -> LLVMExpr
             -> Integer
             -> Simulator sbe m (SBETerm sbe)
readLLVMTerm args et@(Term e) cnt =
  case e of
    Arg n _ _ -> return (args !! n)
    ReturnValue _ -> do
      rslt <- getProgramReturnValue
      case rslt of
        (Just v) -> return v
        Nothing -> fail "Program did not return a value"
    _ -> do
      let ty = lssTypeOfLLVMExpr et
      addr <- readLLVMTermAddr args et
      let ty' | cnt > 1 = ArrayType (fromIntegral cnt) ty
              | otherwise = ty
      -- Type should be type of value, not type of ptr
      dl <- getDL
      load ty' addr (memTypeAlign dl ty')

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."
