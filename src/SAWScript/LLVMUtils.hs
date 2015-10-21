{-# LANGUAGE ImplicitParams #-}
{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMUtils where

import Control.Monad.State
import Data.Maybe
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase
import Verifier.LLVM.Codebase.LLVMContext
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals
import Verifier.SAW.SharedTerm

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
