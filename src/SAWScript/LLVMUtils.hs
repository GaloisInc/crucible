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
import Verifier.LLVM.Codebase
import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals
import Verifier.SAW.SharedTerm
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

addrPlusOffset :: (Functor m, MonadIO m) =>
                  SBETerm sbe -> Offset
               -> Simulator sbe m (SBETerm sbe)
addrPlusOffset a o = do
  sbe <- gets symBE
  w <- ptrBitwidth <$> getDL
  ot <- liftSBE $ termInt sbe w (fromIntegral o)
  liftSBE $ applyTypedExpr sbe (PtrAdd a ot)

structFieldAddr :: (Functor m, MonadIO m) =>
                   StructInfo -> Int -> SBETerm sbe
                -> Simulator sbe m (SBETerm sbe)
structFieldAddr si idx base =
  case siFieldOffset si idx of
    Just off -> addrPlusOffset base off
    Nothing -> fail $ "Struct field index " ++ show idx ++ " out of bounds"

storePathState :: SBE SpecBackend
               -> SharedTerm SAWCtx
               -> MemType
               -> SharedTerm SAWCtx
               -> SpecPathState
               -> IO SpecPathState
storePathState sbe dst tp val ps = do
  (c, m') <- sbeRunIO sbe (memStore sbe (ps ^. pathMem) dst tp val 0)
  _ps' <- addAssertion sbe c ps
  -- FIXME: don't discard ps'!
  return (ps & pathMem .~ m')

loadPathState :: SBE SpecBackend
              -> SharedTerm SAWCtx
              -> MemType
              -> SpecPathState
              -> IO SpecLLVMValue
loadPathState sbe src tp ps = do
  (c, v) <- sbeRunIO sbe (memLoad sbe (ps ^. pathMem) tp src 0)
  _ps' <- addAssertion sbe c ps
  -- FIXME: don't discard ps'!
  return v

loadGlobal :: SBE SpecBackend
           -> GlobalMap SpecBackend
           -> Symbol
           -> MemType
           -> SpecPathState
           -> IO SpecLLVMValue
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
