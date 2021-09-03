{-
Module       : UCCrux.LLVM.Context.Module
Description  : LLVM module-level read-only context.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Context.Module
  ( ModuleContext,
    SomeModuleContext (..),
    moduleFilePath,
    makeModuleContext,
    llvmModule,
    moduleTypes,
    globalTypes,
    declTypes,
    moduleTranslation,
    dataLayout,
    withTypeContext,

    -- * Looking up CFGs
    CFGWithTypes (..),
    findFun,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), Simple, Getter, Lens, lens, to, at)
import           Data.Proxy (Proxy(Proxy))
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import           Text.LLVM (Module, Symbol(Symbol))

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible
import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           Lang.Crucible.LLVM.DataLayout (DataLayout)
import           Lang.Crucible.LLVM.Extension (LLVM)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext, llvmDataLayout)

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (testCompatibility)
import           UCCrux.LLVM.FullType.Translation (DeclSymbol, GlobalMap, DeclMap, TranslatedTypes(..), TypeTranslationError, FunctionTypes(..), MatchingAssign(..), translateModuleDefines, declSymbol, getDeclSymbol)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr, ModuleTypes, MapToCrucibleType)
import           UCCrux.LLVM.FullType.ReturnType (ReturnType(..), ReturnTypeToCrucibleType)
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr, varArgsReprToBool)
{- ORMOLU_ENABLE -}

-- | The @m@ type parameter represents a specific LLVM module
data ModuleContext m arch = ModuleContext
  { _moduleFilePath :: FilePath,
    _llvmModule :: Module,
    _moduleTypes :: ModuleTypes m,
    _globalTypes :: GlobalMap m (Some (FullTypeRepr m)),
    _declTypes :: DeclMap m (FunctionTypes m arch),
    _moduleTranslation :: ModuleTranslation arch
  }

moduleFilePath :: Simple Lens (ModuleContext m arch) FilePath
moduleFilePath = lens _moduleFilePath (\s v -> s {_moduleFilePath = v})

llvmModule :: Simple Lens (ModuleContext m arch) Module
llvmModule = lens _llvmModule (\s v -> s {_llvmModule = v})

moduleTypes :: Simple Lens (ModuleContext m arch) (ModuleTypes m)
moduleTypes = lens _moduleTypes (\s v -> s {_moduleTypes = v})

globalTypes :: Simple Lens (ModuleContext m arch) (GlobalMap m (Some (FullTypeRepr m)))
globalTypes = lens _globalTypes (\s v -> s {_globalTypes = v})

declTypes :: Simple Lens (ModuleContext m arch) (DeclMap m (FunctionTypes m arch))
declTypes = lens _declTypes (\s v -> s {_declTypes = v})

moduleTranslation :: Simple Lens (ModuleContext m arch) (ModuleTranslation arch)
moduleTranslation = lens _moduleTranslation (\s v -> s {_moduleTranslation = v})

dataLayout :: Getter (ModuleContext m arch) DataLayout
dataLayout = moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx . to llvmDataLayout

withTypeContext :: ModuleContext m arch -> ((?lc :: TypeContext) => a) -> a
withTypeContext context computation =
  let ?lc = context ^. moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
   in computation

makeModuleContext ::
  ArchOk arch =>
  FilePath ->
  Module ->
  ModuleTranslation arch ->
  Either TypeTranslationError (SomeModuleContext arch)
makeModuleContext path llvmMod trans =
  let ?lc = trans ^. LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
   in case translateModuleDefines llvmMod trans of
        Left err -> Left err
        Right (TranslatedTypes modTypes globTypes decTypes) ->
          Right $
            SomeModuleContext $
              ModuleContext path llvmMod modTypes globTypes decTypes trans

-- ------------------------------------------------------------------------------
-- Looking up CFGs

data CFGWithTypes m arch = forall argTypes ret blocks.
  CFGWithTypes
  { cfgWithTypes ::
      Crucible.CFG
        LLVM
        blocks
        (MapToCrucibleType arch argTypes)
        (ReturnTypeToCrucibleType arch ret),
    cfgArgFullTypes :: Ctx.Assignment (FullTypeRepr m) argTypes,
    cfgRetFullType :: ReturnType m ret,
    cfgIsVarArgs :: Some VarArgsRepr
  }

data SomeModuleContext arch
  = forall m. SomeModuleContext (ModuleContext m arch)

-- | This function has a lot of calls to @panic@, these are all justified by the
-- invariant on 'DeclTypes' (namely that it contains types for declarations in
-- the module specified by the @m@ type parameter), and the invariant on
-- 'ModuleContext' that the @moduleTypes@ and @declTypes@ correspond to the
-- @moduleTranslation@.
findFun ::
  forall m arch.
  ArchOk arch =>
  ModuleContext m arch ->
  DeclSymbol m ->
  CFGWithTypes m arch
findFun modCtx declSym =
  case modCtx ^. declTypes . declSymbol declSym of
    FunctionTypes (MatchingAssign argFTys argCTys) retTy (Some varArgs) ->
      do let sym@(Symbol name) = getDeclSymbol declSym
         case modCtx ^. moduleTranslation . to LLVMTrans.cfgMap . at sym of
           Nothing -> panic "findFunc" ["Missing function:" ++ name]
           Just (_decl, Crucible.AnyCFG cfg) ->
             if varArgsReprToBool varArgs
             then unimplemented "findFun" Unimplemented.VarArgsFunction
             else
               case testEquality (Crucible.cfgArgTypes cfg) argCTys of
                 Nothing -> panic "findFunc" ["Mismatched argument types"]
                 Just Refl ->
                   case Crucible.cfgReturnType cfg of
                     CrucibleTypes.UnitRepr ->
                       case retTy of
                         Just (Some _) ->
                           panic
                             "findFun"
                             [ unwords
                                 [ "Extra return type: Crucible function type was void",
                                   "but the translated type was not."
                                 ]
                             ]
                         Nothing ->
                           CFGWithTypes
                             { cfgWithTypes = cfg,
                               cfgArgFullTypes = argFTys,
                               cfgRetFullType = Void,
                               cfgIsVarArgs = Some varArgs
                             }
                     cRetTy ->
                       case retTy of
                         Nothing -> panic "findFun" ["Missing return type"]
                         Just (Some retTy') ->
                           case testCompatibility (Proxy :: Proxy arch) retTy' cRetTy of
                             Just Refl ->
                               CFGWithTypes
                                 { cfgWithTypes = cfg,
                                   cfgArgFullTypes = argFTys,
                                   cfgRetFullType = NonVoid retTy',
                                   cfgIsVarArgs = Some varArgs
                                 }
                             Nothing -> panic "findFun" ["Bad return type"]
