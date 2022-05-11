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
    funcTypes,
    defnTypes,
    declTypes,
    moduleTranslation,
    moduleDecls,
    dataLayout,
    withTypeContext,
    withModulePtrWidth,

    -- * Looking up CFGs
    CFGWithTypes (..),
    findFun,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Lens ((^.), Simple, Getter, Lens, lens, to, at)
import           Data.Type.Equality ((:~:)(Refl))
import           GHC.Stack (HasCallStack)

import           Text.LLVM.AST (Symbol(Symbol))
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as Crucible

import           Lang.Crucible.LLVM.DataLayout (DataLayout)
import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVM)
import           Lang.Crucible.LLVM.MemModel (HasPtrWidth, withPtrWidth)
import           Lang.Crucible.LLVM.Translation (ModuleTranslation)
import qualified Lang.Crucible.LLVM.Translation as LLVMTrans
import           Lang.Crucible.LLVM.TypeContext (TypeContext, llvmDataLayout)

import           Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.CrucibleType (testCompatibilityAssign, testCompatibilityReturn)
import           UCCrux.LLVM.FullType.FuncSig (ReturnTypeRepr, ReturnTypeToCrucibleType, FuncSigRepr(..))
import           UCCrux.LLVM.FullType.Translation (TranslatedTypes(..), TypeTranslationError, translateModuleDefines, throwTypeTranslationError)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr, ModuleTypes, MapToCrucibleType)
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr, varArgsReprToBool)
import           UCCrux.LLVM.Module (Module, FuncSymbol, DeclMap, DefnMap, FuncMap, GlobalMap, funcSymbol, getFuncSymbol, funcMapDecls, funcMapDefns, allModuleDeclMap)
{- ORMOLU_ENABLE -}

-- | The @m@ type parameter represents a specific LLVM module
data ModuleContext m arch = ModuleContext
  { _moduleFilePath :: FilePath,
    _llvmModule :: Module m,
    _moduleTypes :: ModuleTypes m,
    _globalTypes :: GlobalMap m (Some (FullTypeRepr m)),
    _funcTypes :: FuncMap m (Some (FuncSigRepr m)),
    _moduleTranslation :: ModuleTranslation arch,
    _moduleDecls :: FuncMap m L.Declare
  }

moduleFilePath :: Simple Lens (ModuleContext m arch) FilePath
moduleFilePath = lens _moduleFilePath (\s v -> s {_moduleFilePath = v})

llvmModule :: Simple Lens (ModuleContext m arch) (Module m)
llvmModule = lens _llvmModule (\s v -> s {_llvmModule = v})

moduleTypes :: Simple Lens (ModuleContext m arch) (ModuleTypes m)
moduleTypes = lens _moduleTypes (\s v -> s {_moduleTypes = v})

globalTypes :: Simple Lens (ModuleContext m arch) (GlobalMap m (Some (FullTypeRepr m)))
globalTypes = lens _globalTypes (\s v -> s {_globalTypes = v})

funcTypes :: Simple Lens (ModuleContext m arch) (FuncMap m (Some (FuncSigRepr m)))
funcTypes = lens _funcTypes (\s v -> s {_funcTypes = v})

declTypes :: Simple Lens (ModuleContext m arch) (DeclMap m (Some (FuncSigRepr m)))
declTypes = funcTypes . funcMapDecls

defnTypes :: Simple Lens (ModuleContext m arch) (DefnMap m (Some (FuncSigRepr m)))
defnTypes = funcTypes . funcMapDefns

moduleTranslation :: Simple Lens (ModuleContext m arch) (ModuleTranslation arch)
moduleTranslation = lens _moduleTranslation (\s v -> s {_moduleTranslation = v})

moduleDecls :: Simple Lens (ModuleContext m arch) (FuncMap m L.Declare)
moduleDecls = lens _moduleDecls (\s v -> s {_moduleDecls = v})

dataLayout :: Getter (ModuleContext m arch) DataLayout
dataLayout = moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx . to llvmDataLayout

withTypeContext :: ModuleContext m arch -> ((?lc :: TypeContext) => a) -> a
withTypeContext context computation =
  let ?lc = context ^. moduleTranslation . LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
   in computation

-- | Any errors encountered in this function are bugs in UC-Crux or results of a
-- malformed LLVM module, and are thrown as exceptions.
makeModuleContext ::
  HasCallStack =>
  ArchOk arch =>
  FilePath ->
  L.Module ->
  ModuleTranslation arch ->
  SomeModuleContext arch
makeModuleContext path llvmMod trans =
  case tryMakeModuleContext path llvmMod trans of
    Left err -> throwTypeTranslationError err
    Right modCtx -> modCtx

tryMakeModuleContext ::
  ArchOk arch =>
  FilePath ->
  L.Module ->
  ModuleTranslation arch ->
  Either TypeTranslationError (SomeModuleContext arch)
tryMakeModuleContext path llvmMod trans =
  let ?lc = trans ^. LLVMTrans.transContext . LLVMTrans.llvmTypeCtx
   in case translateModuleDefines llvmMod trans of
        Left err -> Left err
        Right (TranslatedTypes llvmMod' modTypes globTypes decTypes) ->
          Right $
            SomeModuleContext $
              ModuleContext path llvmMod' modTypes globTypes decTypes trans (allModuleDeclMap llvmMod')

withModulePtrWidth ::
  ModuleContext m arch ->
  (HasPtrWidth (ArchWidth arch) => a) ->
  a
withModulePtrWidth modCtx computation =
  LLVMTrans.llvmPtrWidth
    (modCtx ^. moduleTranslation . LLVMTrans.transContext)
    (\ptrW -> withPtrWidth ptrW computation)

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
    cfgRetFullType :: ReturnTypeRepr m ret,
    cfgIsVarArgs :: Some VarArgsRepr
  }

data SomeModuleContext arch
  = forall m. SomeModuleContext (ModuleContext m arch)

-- | This function has a lot of calls to @panic@, these are all justified by the
-- invariant on 'FuncTypes' (namely that it contains types for declarations and
-- definitions in the module specified by the @m@ type parameter), and the
-- invariant on 'ModuleContext' that the @moduleTypes@ and @funcTypes@
-- correspond to the @moduleTranslation@.
findFun ::
  forall m arch.
  ArchOk arch =>
  ModuleContext m arch ->
  FuncSymbol m ->
  CFGWithTypes m arch
findFun modCtx funcSym =
  case modCtx ^. funcTypes . funcSymbol funcSym of
    Some (FuncSigRepr varArgs argFTys retTy) ->
      do let sym@(Symbol name) = getFuncSymbol funcSym
         case modCtx ^. moduleTranslation . to LLVMTrans.cfgMap . at sym of
           Nothing -> panic "findFunc" ["Missing function:" ++ name]
           Just (_decl, Crucible.AnyCFG cfg) ->
             if varArgsReprToBool varArgs
             then unimplemented "findFun" Unimplemented.VarArgsFunction
             else
               case testCompatibilityAssign modCtx argFTys (Crucible.cfgArgTypes cfg) of
                 Nothing -> panic "findFunc" ["Mismatched argument types"]
                 Just Refl ->
                   case testCompatibilityReturn modCtx retTy (Crucible.cfgReturnType cfg) of
                     Nothing -> panic "findFunc" ["Mismatched return types"]
                     Just Refl ->
                       CFGWithTypes
                         { cfgWithTypes = cfg,
                           cfgArgFullTypes = argFTys,
                           cfgRetFullType = retTy,
                           cfgIsVarArgs = Some varArgs
                         }
