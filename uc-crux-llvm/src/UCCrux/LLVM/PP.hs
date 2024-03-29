{-
Module       : UCCrux.LLVM.PP
Description  : Pretty-printing
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module UCCrux.LLVM.PP
  ( ppRegValue,
    ppRegMap,
    ppProgramLoc,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens (to, (^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Data.Functor.Const (Const(Const, getConst))
import           Data.Proxy (Proxy(Proxy))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:) (Refl))

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified What4.ProgramLoc as What4

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Simulator as Crucible

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes (ixF')
import           Data.Parameterized.TraversableFC (toListFC)

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames, argumentStorageTypes)
import           UCCrux.LLVM.FullType.CrucibleType (SomeIndex(..), translateIndex)
import           UCCrux.LLVM.FullType.Type (MapToCrucibleType)
{- ORMOLU_ENABLE -}

ppRegValue ::
  ( Crucible.IsSymInterface sym,
    ArchOk arch,
    MonadIO f
  ) =>
  proxy arch ->
  sym ->
  LLVMMem.MemImpl sym ->
  LLVMMem.StorageType ->
  Crucible.RegEntry sym tp ->
  f (Doc ann)
ppRegValue _proxy sym mem storageType (Crucible.RegEntry typeRepr regValue) =
  do
    val <- liftIO $ LLVMMem.packMemValue sym storageType typeRepr regValue
    pure $
      LLVMMem.ppLLVMValWithGlobals
        sym
        (LLVMMem.memImplSymbolMap mem)
        val

ppRegMap ::
  forall proxy f m arch sym argTypes ann.
  ( Crucible.IsSymInterface sym,
    ArchOk arch,
    MonadIO f
  ) =>
  proxy arch ->
  FunctionContext m arch argTypes ->
  sym ->
  LLVMMem.MemImpl sym ->
  Crucible.RegMap sym (MapToCrucibleType arch argTypes) ->
  f [Doc ann]
ppRegMap _proxy funCtx sym mem (Crucible.RegMap regmap) =
  toListFC getConst
    <$> Ctx.traverseWithIndex
      ( \index (Const storageType) ->
          case translateIndex (Proxy @arch) (Ctx.size (funCtx ^. argumentStorageTypes)) index of
            SomeIndex idx Refl ->
              do
                let regEntry = regmap Ctx.! idx
                arg <-
                  liftIO $
                    ppRegValue (Proxy @arch) sym mem storageType regEntry
                pure $
                  Const $
                    PP.hsep
                      [ PP.pretty "Argument #" <> PP.viaShow (Ctx.indexVal index),
                        maybe mempty PP.pretty (funCtx ^. argumentNames . ixF' index . to getConst) <> PP.pretty ":",
                        PP.viaShow arg
                        -- , "(type:"
                        -- , Text.pack (show (Crucible.regType arg)) <> ")"
                      ]
      )
      (funCtx ^. argumentStorageTypes)


-- TODO(lb): Make this return a Doc ann
-- TODO(lb): Also print the function name?
ppProgramLoc :: What4.ProgramLoc -> Text
ppProgramLoc = Text.pack . show . What4.plSourceLoc
