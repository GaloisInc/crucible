{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.GlobalInfo
-- Description      : Information about global variables, for building a model
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.GlobalInfo
  ( GlobalInfo (..),
    getGlobalInfo,
    globalSymbols,
    globalSymbolsAsSolverSymbols,
    globalTypeReprs,
    symbolString,
  )
where

import Data.Functor.Const (Const (..))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC (fmapFC)
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.LLVM.MemType
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.LLVM.TypeContext
import Lang.Crucible.ModelChecker.SallyWhat4
import Lang.Crucible.Simulator
import qualified Text.LLVM as TL
import qualified Prettyprinter as PP
import qualified What4.Interface as What4

-- | @GlobalInfo sym tp@ captures the information we collect about global
-- variables.  Currently we retain their name @Symbol@, their type @TypeRepr@,
-- and their initial value @RegValue@.
data GlobalInfo sym tp = GlobalInfo
  { globalMemType :: MemType,
    globalTypeRepr :: Core.TypeRepr tp,
    globalSymbol :: TL.Symbol,
    globalRegValue :: RegValue sym tp
  }

instance PP.Pretty (GlobalInfo sym tp) where
  pretty GlobalInfo {..} = PP.pretty (show globalSymbol) PP.<+> ":" PP.<+> PP.pretty globalTypeRepr PP.<+> ":=" PP.<+> "TODO"

globalSymbols :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment (Const TL.Symbol) ctx
globalSymbols = fmapFC (Const . globalSymbol)

symbolString :: TL.Symbol -> String
symbolString (TL.Symbol s) = s

globalSymbolsAsSolverSymbols :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment (Const What4.SolverSymbol) ctx
globalSymbolsAsSolverSymbols = fmapFC (Const . userSymbol' . symbolString . globalSymbol)

globalTypeReprs :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment Core.TypeRepr ctx
globalTypeReprs = fmapFC globalTypeRepr

-- FIXME: check whether we need any of the fields before the very end
-- If not, we can probably just pass the GlobalInitializerMap to the final step,
-- and do these computations only then
getGlobalInfo ::
  Backend.IsSymInterface sym =>
  HasPtrWidth (ArchWidth arch) =>
  (?lc :: TypeContext) =>
  -- only here for typeclass resolution
  ArchRepr arch ->
  sym ->
  MemImpl sym ->
  (TL.Symbol, (TL.Global, Either String (MemType, Maybe LLVMConst))) ->
  IO (Core.Some (GlobalInfo sym))
getGlobalInfo _ sym mem (s, (_, Right (mty, Just c))) =
  llvmTypeAsRepr mty $ \tp ->
    do
      c' <- constToLLVMVal sym mem c
      rv <- unpackMemValue sym tp c'
      return $ Core.Some $
        GlobalInfo
          { globalMemType = mty,
            globalRegValue = rv,
            globalSymbol = s,
            globalTypeRepr = tp
          }
getGlobalInfo _ _ _ _ = error "getGlobInfo: encountered badly initialized global"
