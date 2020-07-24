-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Extension.Syntax
-- Description      : LLVM interface for Crucible
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : rdockins@galois.com
-- Stability        : provisional
--
-- Syntax extension definitions for LLVM
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Extension.Syntax where

import           Data.Kind
import           Data.List.NonEmpty (NonEmpty)
import           GHC.TypeLits
import           Data.Text (Text)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Functor.Classes (Eq1(..), Ord1(..))
import           Data.Parameterized.Classes
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.Arch.X86 as X86
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension.Arch
import           Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior( UndefinedBehavior )
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.Types


data LLVMSideCondition (f :: CrucibleType -> Type) =
  LLVMSideCondition (f BoolType) (UndefinedBehavior f)

instance TestEqualityC LLVMSideCondition where
  testEqualityC sub (LLVMSideCondition px dx) (LLVMSideCondition py dy) =
    isJust (sub px py) && testEqualityC sub dx dy

instance OrdC LLVMSideCondition where
  compareC sub (LLVMSideCondition px dx) (LLVMSideCondition py dy) =
    toOrdering (sub px py) <> compareC sub dx dy

instance FunctorF LLVMSideCondition where
  fmapF = fmapFDefault

instance FoldableF LLVMSideCondition where
  foldMapF = foldMapFDefault

instance TraversableF LLVMSideCondition where
  traverseF f (LLVMSideCondition p desc) =
      LLVMSideCondition <$> f p <*> traverseF f desc

data LLVMExtensionExpr (arch :: LLVMArch) :: (CrucibleType -> Type) -> (CrucibleType -> Type) where
  X86Expr :: !(X86.ExtX86 f t) -> LLVMExtensionExpr (X86 wptr) f t

  LLVM_SideConditions ::
    !(TypeRepr tp) ->
    !(NonEmpty (LLVMSideCondition f)) ->
    !(f tp) ->
    LLVMExtensionExpr arch f tp

  LLVM_PointerExpr ::
    (1 <= w) => !(NatRepr w) -> !(f NatType) -> !(f (BVType w)) ->
    LLVMExtensionExpr arch f (LLVMPointerType w)

  LLVM_PointerBlock ::
    (1 <= w) => !(NatRepr w) -> !(f (LLVMPointerType w)) ->
    LLVMExtensionExpr arch f NatType

  LLVM_PointerOffset ::
    (1 <= w) => !(NatRepr w) -> !(f (LLVMPointerType w)) ->
    LLVMExtensionExpr arch f (BVType w)

  LLVM_PointerIte ::
    (1 <= w) => !(NatRepr w) ->
    !(f BoolType) -> !(f (LLVMPointerType w)) -> !(f (LLVMPointerType w)) ->
    LLVMExtensionExpr arch f (LLVMPointerType w)


-- | Extension statements for LLVM.  These statements represent the operations
--   necessary to interact with the LLVM memory model.
data LLVMStmt (wptr :: Nat) (f :: CrucibleType -> Type) :: CrucibleType -> Type where

  -- | Indicate the beginning of a new stack frame upon entry to a function.
  LLVM_PushFrame ::
     !Text ->
     !(GlobalVar Mem) {- Memory global variable -} ->
     LLVMStmt wptr f UnitType

  -- | Indicate the end of the current stack frame upon exit from a function.
  LLVM_PopFrame ::
     !(GlobalVar Mem) {- Memory global variable -} ->
     LLVMStmt wptr f UnitType

  -- | Allocate a new memory object in the current stack frame.  This memory
  --   will be automatically deallocated when the corresponding PopFrame
  --   statement is executed.
  LLVM_Alloca ::
     !(NatRepr wptr)       {- Pointer width -} ->
     !(GlobalVar Mem)      {- Memory global variable -} ->
     !(f (BVType wptr))    {- Number of bytes to allocate -} ->
     !Alignment            {- Minimum alignment of this allocation -} ->
     !String               {- Location string to identify this allocation for debugging purposes -} ->
     LLVMStmt wptr f (LLVMPointerType wptr)

  -- | Load a value from the memory.  The load is defined only if
  --   the given pointer is a live pointer; if the bytes in the memory
  --   at that location can be read and reconstructed into a value of the
  --   desired type; and if the given pointer is actually aligned according
  --   to the given alignment value.
  LLVM_Load ::
     !(GlobalVar Mem)            {- Memory global variable -} ->
     !(f (LLVMPointerType wptr)) {- Pointer to load from -} ->
     !(TypeRepr tp)              {- Expected crucible type of the result -} ->
     !StorageType                {- Storage type -} ->
     !Alignment                  {- Assumed alignment of the pointer -} ->
     LLVMStmt wptr f tp

  -- | Store a value in to the memory.  The store is defined only if the given
  --   pointer is a live pointer; if the given value fits into the memory object
  --   at the location pointed to; and the given pointer is aligned according
  --   to the given alignment value.
  LLVM_Store ::
     !(GlobalVar Mem)            {- Memory global variable -} ->
     !(f (LLVMPointerType wptr)) {- Pointer to store at -} ->
     !(TypeRepr tp)              {- Crucible type of the value being stored -} ->
     !StorageType                {- Storage type of the value -} ->
     !Alignment                  {- Assumed alignment of the pointer -} ->
     !(f tp)                     {- Value to store -} ->
     LLVMStmt wptr f UnitType

  -- | Clear a region of memory by setting all the bytes in it to the zero byte.
  --   This is primarily used for initializing the value of global variables,
  --   but can also result from zero initializers.
  LLVM_MemClear ::
     !(GlobalVar Mem)            {- Memory global variable -} ->
     !(f (LLVMPointerType wptr)) {- Pointer to store at -} ->
     !Bytes                      {- Number of bytes to clear -} ->
     LLVMStmt wptr f UnitType

  -- | Load the Crucible function handle that corresponds to a function pointer value.
  --   This load is defined only if the given pointer was previously allocated as
  --   a function pointer value and associated with a Crucible function handle of
  --   the expected type.
  LLVM_LoadHandle ::
     !(GlobalVar Mem)            {- Memory global variable -} ->
     !(f (LLVMPointerType wptr)) {- Pointer to load from -} ->
     !(CtxRepr args)             {- Expected argument types of the function -} ->
     !(TypeRepr ret)             {- Expected return type of the function -} ->
     LLVMStmt wptr f (FunctionHandleType args ret)

  -- | Resolve the given global symbol name to a pointer value.
  LLVM_ResolveGlobal ::
     !(NatRepr wptr)      {- Pointer width -} ->
     !(GlobalVar Mem)     {- Memory global variable -} ->
     GlobalSymbol         {- The symbol to resolve -} ->
     LLVMStmt wptr f (LLVMPointerType wptr)

  -- | Test two pointer values for equality.
  --   Note! This operation is defined only
  --   in case both pointers are live or null.
  LLVM_PtrEq ::
     !(GlobalVar Mem)            {- Pointer width -} ->
     !(f (LLVMPointerType wptr)) {- First pointer to compare -} ->
     !(f (LLVMPointerType wptr)) {- First pointer to compare -} ->
     LLVMStmt wptr f BoolType

  -- | Test two pointer values for ordering.
  --   Note! This operation is only defined if
  --   both pointers are live pointers into the
  --   same memory object.
  LLVM_PtrLe ::
     !(GlobalVar Mem)            {- Pointer width -} ->
     !(f (LLVMPointerType wptr)) {- First pointer to compare -} ->
     !(f (LLVMPointerType wptr)) {- First pointer to compare -} ->
     LLVMStmt wptr f BoolType

  -- | Add an offset value to a pointer.
  --   Note! This operation is only defined if both
  --   the input pointer is a live pointer, and
  --   the resulting computed pointer remains in the bounds
  --   of its associated memory object (or one past the end).
  LLVM_PtrAddOffset ::
     !(NatRepr wptr)             {- Pointer width -} ->
     !(GlobalVar Mem)            {- Memory global variable -} ->
     !(f (LLVMPointerType wptr)) {- Pointer value -} ->
     !(f (BVType wptr))          {- Offset value -} ->
     LLVMStmt wptr f (LLVMPointerType wptr)

  -- | Compute the offset between two pointer values.
  --   Note! This operation is only defined if both pointers
  --   are live pointers into the same memory object.
  LLVM_PtrSubtract ::
     !(NatRepr wptr)             {- Pointer width -} ->
     !(GlobalVar Mem)            {- Memory global value -} ->
     !(f (LLVMPointerType wptr)) {- First pointer -} ->
     !(f (LLVMPointerType wptr)) {- Second pointer -} ->
     LLVMStmt wptr f (BVType wptr)

$(return [])

instance TypeApp (LLVMExtensionExpr arch) where
  appType e =
    case e of
      X86Expr ex             -> appType ex
      LLVM_SideConditions tpr _ _ -> tpr
      LLVM_PointerExpr w _ _ -> LLVMPointerRepr w
      LLVM_PointerBlock _ _  -> NatRepr
      LLVM_PointerOffset w _ -> BVRepr w
      LLVM_PointerIte w _ _ _ -> LLVMPointerRepr w

instance PrettyApp (LLVMExtensionExpr arch) where
  ppApp pp e =
    case e of
      X86Expr ex -> ppApp pp ex
      LLVM_SideConditions _ _conds ex ->
        text "sideConditions" <+> pp ex -- TODO? Print the conditions?
      LLVM_PointerExpr _ blk off ->
        text "pointerExpr" <+> pp blk <+> pp off
      LLVM_PointerBlock _ ptr ->
        text "pointerBlock" <+> pp ptr
      LLVM_PointerOffset _ ptr ->
        text "pointerOffset" <+> pp ptr
      LLVM_PointerIte _ cond x y ->
        text "pointerIte" <+> pp cond <+> pp x <+> pp y

instance TestEqualityFC (LLVMExtensionExpr arch) where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|LLVMExtensionExpr|]
       [ (U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       , (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       , (U.ConType [t|X86.ExtX86|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|testEqualityFC testSubterm|])
       , (U.ConType [t|NonEmpty|] `U.TypeApp` (U.ConType [t|LLVMSideCondition|] `U.TypeApp` U.AnyType)
         , [| \x y -> if liftEq (testEqualityC testSubterm) x y then Just Refl else Nothing |]
         )
       ])

instance OrdFC (LLVMExtensionExpr arch) where
  compareFC testSubterm =
    $(U.structuralTypeOrd [t|LLVMExtensionExpr|]
       [ (U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       , (U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       , (U.ConType [t|X86.ExtX86|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|compareFC testSubterm|])
       , (U.ConType [t|NonEmpty|] `U.TypeApp` (U.ConType [t|LLVMSideCondition|] `U.TypeApp` U.AnyType)
         , [| \x y -> fromOrdering (liftCompare (compareC testSubterm) x y) |]
         )
       ])

instance FunctorFC (LLVMExtensionExpr arch) where
  fmapFC = fmapFCDefault

instance FoldableFC (LLVMExtensionExpr arch) where
  foldMapFC = foldMapFCDefault


traverseConds ::
  Applicative m =>
  (forall s. f s -> m (g s)) ->
  NonEmpty (LLVMSideCondition f) ->
  m (NonEmpty (LLVMSideCondition g))
traverseConds f = traverse (traverseF f)


instance TraversableFC (LLVMExtensionExpr arch) where
  traverseFC = $(U.structuralTraversal [t|LLVMExtensionExpr|]
     [(U.ConType [t|X86.ExtX86|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType, [|traverseFC|])
     ,(U.ConType [t|NonEmpty|] `U.TypeApp` (U.ConType [t|LLVMSideCondition|] `U.TypeApp` U.AnyType)
      , [| traverseConds |]
      )
     ])

instance (1 <= wptr) => TypeApp (LLVMStmt wptr) where
  appType = \case
    LLVM_PushFrame{} -> knownRepr
    LLVM_PopFrame{} -> knownRepr
    LLVM_Alloca w _ _ _ _ -> LLVMPointerRepr w
    LLVM_Load _ _ tp _ _  -> tp
    LLVM_Store{} -> knownRepr
    LLVM_MemClear{} -> knownRepr
    LLVM_LoadHandle _ _ args ret -> FunctionHandleRepr args ret
    LLVM_ResolveGlobal w _ _ -> LLVMPointerRepr w
    LLVM_PtrEq{} -> knownRepr
    LLVM_PtrLe{} -> knownRepr
    LLVM_PtrAddOffset w _ _ _ -> LLVMPointerRepr w
    LLVM_PtrSubtract w _ _ _ -> BVRepr w

instance PrettyApp (LLVMStmt wptr) where
  ppApp pp = \case
    LLVM_PushFrame nm mvar ->
       text "pushFrame" <+> text (show nm) <+> text (show mvar)
    LLVM_PopFrame mvar  ->
       text "popFrame" <+> text (show mvar)
    LLVM_Alloca _ mvar sz a loc ->
       text "alloca" <+> text (show mvar) <+> pp sz <+> text (show a) <+> text loc
    LLVM_Load mvar ptr _tpr tp a ->
       text "load" <+> text (show mvar) <+> pp ptr <+> text (show tp) <+> text (show a)
    LLVM_Store mvar ptr _tpr tp a v ->
       text "store" <+> text (show mvar) <+> pp ptr <+> text (show tp) <+> text (show a) <+> pp v
    LLVM_MemClear mvar ptr len ->
       text "memClear" <+> text (show mvar) <+> pp ptr <+> text (show len)
    LLVM_LoadHandle mvar ptr args ret ->
       text "loadFunctionHandle" <+> text (show mvar) <+> pp ptr <+> text "as" <+> text (show (FunctionHandleRepr args ret))
    LLVM_ResolveGlobal _ mvar gs ->
       text "resolveGlobal" <+> text (show mvar) <+> text (show (globalSymbolName gs))
    LLVM_PtrEq mvar x y ->
       text "ptrEq" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrLe mvar x y ->
       text "ptrEq" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrAddOffset _ mvar x y ->
       text "ptrAddOffset" <+> text (show mvar) <+> pp x <+> pp y
    LLVM_PtrSubtract _ mvar x y ->
       text "ptrSubtract" <+> text (show mvar) <+> pp x <+> pp y

instance TestEqualityFC (LLVMStmt wptr) where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|testSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ,(U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
       ])

instance OrdFC (LLVMStmt wptr) where
  compareFC compareSubterm =
    $(U.structuralTypeOrd [t|LLVMStmt|]
       [(U.DataArg 1 `U.TypeApp` U.AnyType, [|compareSubterm|])
       ,(U.ConType [t|NatRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|GlobalVar|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|CtxRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ,(U.ConType [t|TypeRepr|] `U.TypeApp` U.AnyType, [|compareF|])
       ])

instance FunctorFC (LLVMStmt wptr) where
  fmapFC = fmapFCDefault

instance FoldableFC (LLVMStmt wptr) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (LLVMStmt wptr) where
  traverseFC =
    $(U.structuralTraversal [t|LLVMStmt|] [])
