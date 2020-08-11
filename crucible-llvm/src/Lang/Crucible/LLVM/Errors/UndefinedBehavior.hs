-- |
-- Module           : Lang.Crucible.LLVM.Errors.UndefinedBehavior
-- Description      : All about undefined behavior
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
-- This module is intended to be imported qualified.
--
-- This module serves as an ad-hoc reference for the sort of undefined behaviors
-- that the Crucible LLVM memory model is aware of. The information contained
-- here is used in
--  * providing helpful error messages
--  * configuring which safety checks to perform
--
-- Disabling checks for undefined behavior does not change the behavior of any
-- memory operations. If it is used to enable the simulation of undefined
-- behavior, the result is that any guarantees that Crucible provides about the
-- code essentially have an additional hypothesis: that the LLVM
-- compiler/hardware platform behave identically to Crucible's simulator when
-- encountering such behavior.
--------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Errors.UndefinedBehavior
  (
  -- ** Undefined Behavior
    PtrComparisonOperator(..)
  , UndefinedBehavior(..)
  , cite
  , details
  , explain
  , ppDetails
  , ppCitation
  , pp

  , concUB
  ) where

import           Prelude

import           GHC.Generics (Generic)
import           Data.Data (Data)
import           Data.Kind (Type)
import           Data.Maybe (isJust)
import           Data.Text (unpack)
import           Data.Typeable (Typeable)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes (toOrdering, fromOrdering)
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import qualified Data.Parameterized.TraversableF as TF

import qualified What4.Interface as W4I
import           What4.Expr (GroundValue)

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)
import           Lang.Crucible.LLVM.Errors.Standards
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import           Lang.Crucible.LLVM.MemModel.Pointer (ppPtr, concBV, concPtr')
import           Lang.Crucible.LLVM.MemModel.Type (StorageType)
import           Lang.Crucible.LLVM.Types (LLVMPointerType)

-- -----------------------------------------------------------------------
-- ** UndefinedBehavior

-- | The various comparison operators you can use on pointers
data PtrComparisonOperator =
    Eq
  | Leq
  deriving (Data, Eq, Generic, Enum, Ord, Read, Show)

ppPtrComparison :: PtrComparisonOperator -> Doc
ppPtrComparison Eq  = text "Equality comparison (==)"
ppPtrComparison Leq = text "Ordering comparison (<=)"

-- | This type is parameterized on a higher-kinded term constructor so that it
-- can be instantiated for expressions at translation time (i.e. the 'Expr' in
-- 'LLVMGenerator'), or for expressions at runtime ('SymExpr').
--
-- See 'cite' and 'explain' for what each constructor means at the C/LLVM level.
--
-- The commented-out constructors correspond to behaviors that don't have
-- explicit checks yet (but probably should!).
data UndefinedBehavior (e :: CrucibleType -> Type) where

  -- -------------------------------- Memory management

  FreeBadOffset ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    UndefinedBehavior e

  FreeUnallocated ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    UndefinedBehavior e

  -- | Arguments: Destination pointer, fill byte, length
  MemsetInvalidRegion ::
    (1 <= w, 1 <= v) =>
    e (LLVMPointerType w) ->
    e (BVType 8) ->
    e (BVType v) ->
    UndefinedBehavior e

  -- | Arguments: Read destination, alignment
  ReadBadAlignment ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    Alignment ->
    UndefinedBehavior e

  -- | Arguments: Write destination, alignment
  WriteBadAlignment ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    Alignment ->
    UndefinedBehavior e

  -- -------------------------------- Pointer arithmetic

  PtrAddOffsetOutOfBounds ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    e (BVType w) ->
    UndefinedBehavior e

  -- | Arguments: kind of comparison, the invalid pointer, the other pointer
  CompareInvalidPointer ::
    (1 <= w) =>
    PtrComparisonOperator ->
    e (LLVMPointerType w) ->
    e (LLVMPointerType w) ->
    UndefinedBehavior e

  -- | "In all other cases, the behavior is undefined"
  -- TODO: 'PtrComparisonOperator' argument?
  CompareDifferentAllocs ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    e (LLVMPointerType w) ->
    UndefinedBehavior e

  -- | "When two pointers are subtracted, both shall point to elements of the
  -- same array object"
  PtrSubDifferentAllocs ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    e (LLVMPointerType w) ->
    UndefinedBehavior e

  -- | Pointer cast to an integer type other than
  --   pointer width integers
  PointerIntCast ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    StorageType ->
    UndefinedBehavior e

  -- | Pointer used in an unsupported arithmetic or bitvector operation
  PointerUnsupportedOp ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    String ->
    UndefinedBehavior e

  -- | Pointer cast to a floating-point type
  PointerFloatCast ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    StorageType ->
    UndefinedBehavior e

  -- | "One of the following shall hold: [...] one operand is a pointer and the
  -- other is a null pointer constant."
  ComparePointerToBV ::
    (1 <= w) =>
    e (LLVMPointerType w) ->
    e (BVType w) ->
    UndefinedBehavior e

  -------------------------------- LLVM: arithmetic

  -- | @SymBV@ or @Expr _ _ (BVType w)@
  UDivByZero   :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e
  SDivByZero   :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e
  URemByZero   :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e
  SRemByZero   :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e
  SDivOverflow :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e
  SRemOverflow :: (1 <= w) => e (BVType w) -> e (BVType w) -> UndefinedBehavior e

  PoisonValueCreated ::
    Poison.Poison e ->
    UndefinedBehavior e

  {-
  MemcpyDisjoint          :: UndefinedBehavior e
  DoubleFree              :: UndefinedBehavior e
  DereferenceBadAlignment :: UndefinedBehavior e
  ModifiedStringLiteral   :: UndefinedBehavior e
  -}
  deriving (Typeable)

-- | Which document prohibits this behavior?
standard :: UndefinedBehavior e -> Standard
standard =
  \case

    -- -------------------------------- Memory management

    FreeBadOffset{}           -> CStd C11
    FreeUnallocated{}         -> CStd C11
    MemsetInvalidRegion{}     -> CStd C11
    ReadBadAlignment{}        -> CStd C11
    WriteBadAlignment{}       -> CStd C11

    -- -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds{} -> CStd C11
    CompareInvalidPointer{}   -> CStd C11
    CompareDifferentAllocs{}  -> CStd C11
    PtrSubDifferentAllocs{}   -> CStd C11
    ComparePointerToBV{}      -> CStd C11
    PointerFloatCast{}        -> CStd C11
    PointerIntCast{}          -> CStd C11
    PointerUnsupportedOp{}    -> CStd C11

    -- -------------------------------- LLVM: arithmetic

    UDivByZero{}   -> CStd C11
    SDivByZero{}   -> CStd C11
    URemByZero{}   -> CStd C11
    SRemByZero{}   -> CStd C11
    SDivOverflow{} -> CStd C11
    SRemOverflow{} -> CStd C11

    PoisonValueCreated p -> Poison.standard p

    {-
    MemcpyDisjoint          -> CStd C11
    DoubleFree              -> CStd C11
    DereferenceBadAlignment -> CStd C11
    ModifiedStringLiteral   -> CStd C11
    -}

-- | Which section(s) of the document prohibit this behavior?
cite :: UndefinedBehavior e -> Doc
cite =
  \case

    -------------------------------- Memory management

    FreeBadOffset{}           -> "§7.22.3.3 The free function, ¶2"
    FreeUnallocated{}         -> "§7.22.3.3 The free function, ¶2"
    MemsetInvalidRegion{}     -> "§7.24.1 String function conventions, ¶1"
    ReadBadAlignment{}        -> "§6.5.3.2 Address and indirection operators, ¶4"
    WriteBadAlignment{}       -> "§6.5.3.2 Address and indirection operators, ¶4"

    ---------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds{} -> "§6.5.6 Additive operators, ¶8"
    CompareInvalidPointer{}   -> "§6.5.8 Relational operators, ¶5"
    CompareDifferentAllocs{}  -> "§6.5.8 Relational operators, ¶5"
    PtrSubDifferentAllocs{}   -> "§6.5.6 Additive operators, ¶9"
    ComparePointerToBV{}      -> "§6.5.9 Equality operators, ¶2"
    PointerFloatCast{}        -> "§6.5.4 Cast operators, ¶4"
    PointerIntCast{}          -> "§6.3.2.3 Conversions, pointers, ¶6"
    PointerUnsupportedOp{}    -> "§6.3.2.3 Conversions, pointers, ¶6"

    -------------------------------- Division operators

    UDivByZero{}   -> "§6.5.5 Multiplicitive operators, ¶5"
    SDivByZero{}   -> "§6.5.5 Multiplicitive operators, ¶5"
    URemByZero{}   -> "§6.5.5 Multiplicitive operators, ¶5"
    SRemByZero{}   -> "§6.5.5 Multiplicitive operators, ¶5"
    SDivOverflow{} -> "§6.5.5 Multiplicitive operators, ¶6"
    SRemOverflow{} -> "§6.5.5 Multiplicitive operators, ¶6"

    PoisonValueCreated p -> Poison.cite p

    -------------------------------- Other

    {-
    MemcpyDisjoint          -> "§7.24.2.1 The memcpy function"
    DoubleFree              -> "§7.22.3.3 The free function"
    DereferenceBadAlignment -> "§6.5.3.2 Address and indirection operators"
    ModifiedStringLiteral   -> "§J.2 Undefined behavior" -- 6.4.5
    -}

-- | What happened, and why is it a problem?
--
-- This is a generic explanation that doesn't use the included data.
explain :: UndefinedBehavior e -> Doc
explain =
  \case

    -- -------------------------------- Memory management

    FreeBadOffset _ -> cat $
      [ "`free` called on pointer that was not previously returned by `malloc`"
      , "`calloc`, or another memory management function (the pointer did not"
      , "point to the base of an allocation, its offset should be 0)"
      ]
    FreeUnallocated _ ->
      "`free` called on pointer that didn't point to a live region of the heap"
    MemsetInvalidRegion{} ->
      "Pointer passed to `memset` didn't point to a mutable allocation with enough space"
    WriteBadAlignment _ _ ->
      "Wrote a value into a pointer with insufficent alignment"
    ReadBadAlignment _ _ ->
      "Read a value from a pointer with insufficent alignment"

    -- -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds _ _ ->
      "Addition of an offset to a pointer resulted in a pointer to an address outside of the allocation"
    CompareInvalidPointer{} ->
      "Comparison of a pointer which wasn't null or a pointer to a live heap object"
    CompareDifferentAllocs _ _ ->
      "Comparison of pointers from different allocations"
    PtrSubDifferentAllocs _ _ ->
      "Subtraction of pointers from different allocations"
    ComparePointerToBV _ _ ->
      "Comparison of a pointer to a non zero (null) integer value"
    PointerFloatCast{} ->
      "Cast of a pointer to a floating-point type"
    PointerIntCast{} ->
      "Cast of a pointer to an incompatible integer type"
    PointerUnsupportedOp{} ->
      "Pointer cast to an integer used in an unsupported operation"

    -------------------------------- LLVM: arithmetic

    UDivByZero{}   -> "Unsigned division by zero"
    SDivByZero{}   -> "Signed division by zero"
    URemByZero{}   -> "Unsigned division by zero via remainder"
    SRemByZero{}   -> "Signed division by zero via remainder"
    SDivOverflow{} -> "Overflow during signed division"
    SRemOverflow{} -> "Overflow during signed division (via signed remainder)"

    PoisonValueCreated p -> vcat [ "Poison value created", Poison.explain p ]

    -------------------------------- Other

    {-
    MemcpyDisjoint     -> "Use of `memcpy` with non-disjoint regions of memory"
    DoubleFree         -> "`free` called on already-freed memory"
    DereferenceBadAlignment ->
      "Dereferenced a pointer to a type with the wrong alignment"
    ModifiedStringLiteral -> "Modified the underlying array of a string literal"
    -}

-- | Pretty-print the additional information held by the constructors
-- (for symbolic expressions)
details :: W4I.IsExpr (W4I.SymExpr sym)
        => UndefinedBehavior (RegValue' sym)
        -> [Doc]
details =
  \case

    -------------------------------- Memory management

    FreeBadOffset ptr   -> [ "Pointer:" <+> ppPtr1 ptr ]
    FreeUnallocated ptr -> [ "Pointer:" <+> ppPtr1 ptr ]
    MemsetInvalidRegion destPtr fillByte len ->
      [ "Destination pointer:" <+> ppPtr1 destPtr
      , "Fill byte:          " <+> (W4I.printSymExpr $ unRV fillByte)
      , "Length:             " <+> (W4I.printSymExpr $ unRV len)
      ]
    WriteBadAlignment ptr alignment ->
      [ "Required alignment:" <+> text (show (fromAlignment alignment)) <+> "bytes"
      , ppPtr1 ptr
      ]
    ReadBadAlignment ptr alignment ->
      [ "Required alignment:" <+> text (show (fromAlignment alignment)) <+> "bytes"
      , ppPtr1 ptr
      ]

    -------------------------------- Pointer arithmetic

    PtrAddOffsetOutOfBounds ptr offset ->
      [ ppPtr1 ptr
      , ppOffset (unRV offset)
      ]
    CompareInvalidPointer comparison invalid other ->
      [ "Comparison:                    " <+> ppPtrComparison comparison
      , "Invalid pointer:               " <+> ppPtr1 invalid
      , "Other (possibly valid) pointer:" <+> ppPtr1 other
      ]
    CompareDifferentAllocs ptr1 ptr2 -> [ ppPtr2 ptr1 ptr2 ]
    PtrSubDifferentAllocs ptr1 ptr2  -> [ ppPtr2 ptr1 ptr2 ]
    ComparePointerToBV ptr bv ->
      [ ppPtr1 ptr
      , "Bitvector:" <+> (W4I.printSymExpr $ unRV bv)
      ]
    PointerFloatCast ptr castType ->
      [ ppPtr1 ptr
      , "Cast to:" <+> text (show castType)
      ]
    PointerIntCast ptr castType ->
      [ ppPtr1 ptr
      , "Cast to:" <+> text (show castType)
      ]
    PointerUnsupportedOp ptr msg ->
      [ ppPtr1 ptr
      , text msg
      ]

    -------------------------------- Division operators

    -- The cases are manually listed to prevent unintentional fallthrough if a
    -- constructor is added.
    UDivByZero v1 v2   -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]
    SDivByZero v1 v2   -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]
    URemByZero v1 v2   -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]
    SRemByZero v1 v2   -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]
    SDivOverflow v1 v2 -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]
    SRemOverflow v1 v2 -> [ "op1: " <+> (W4I.printSymExpr $ unRV v1)
                          , "op2: " <+> (W4I.printSymExpr $ unRV v2)
                          ]

    PoisonValueCreated p -> Poison.details p

  where ppPtr1 :: W4I.IsExpr (W4I.SymExpr sym) => RegValue' sym (LLVMPointerType w) -> Doc
        ppPtr1 (RV p) = "Pointer:" <+> ppPtr p

        ppPtr2 (RV ptr1) (RV ptr2) =
          vcat [ "Pointer 1:" <+>  ppPtr ptr1
               , "Pointer 2:" <+>  ppPtr ptr2
               ]

        ppOffset :: W4I.IsExpr e => e (BaseBVType w) -> Doc
        ppOffset = ("Offset:" <+>) . W4I.printSymExpr

pp :: (UndefinedBehavior e -> [Doc]) -- ^ Printer for constructor data
   -> UndefinedBehavior e
   -> Doc
pp extra ub = vcat (explain ub : extra ub ++ ppCitation ub)

-- | Pretty-printer for symbolic backends
ppDetails ::
  W4I.IsExpr (W4I.SymExpr sym) =>
  UndefinedBehavior (RegValue' sym) ->
  Doc
ppDetails ub = vcat (details ub ++ ppCitation ub)

ppCitation :: UndefinedBehavior e -> [Doc]
ppCitation ub =
   (cat [ "Reference: "
        , indent 2 (text (unpack (ppStd (standard ub))))
        , indent 2 (cite ub)
        ]
    : case stdURL (standard ub) of
        Just url -> [ indent 2 ("Document URL:" <+> text (unpack url)) ]
        Nothing  -> [])

-- -----------------------------------------------------------------------
-- ** Instances

$(return [])

instance TestEqualityC UndefinedBehavior where
  testEqualityC subterms x y = isJust $
    $(U.structuralTypeEquality [t|UndefinedBehavior|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| subterms |]
         )
       , ( U.ConType [t|Poison.Poison|] `U.TypeApp` U.AnyType
         , [| \a b -> if testEqualityC subterms a b then Just Refl else Nothing |]
         )
       ]
     ) x y

instance OrdC UndefinedBehavior where
  compareC subterms ub1 ub2 = toOrdering $
    $(U.structuralTypeOrd [t|UndefinedBehavior|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| subterms |]
         )
       , ( U.ConType [t|Poison.Poison|] `U.TypeApp` U.AnyType
         , [| \a b -> fromOrdering (compareC subterms a b) |]
         )
       ]
     ) ub1 ub2

instance FunctorF UndefinedBehavior where
  fmapF = TF.fmapFDefault

instance FoldableF UndefinedBehavior where
  foldMapF = TF.foldMapFDefault

instance TraversableF UndefinedBehavior where
  traverseF subterms =
    $(U.structuralTraversal [t|UndefinedBehavior|]
       [ ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| \_ x -> subterms x |]
         )
       , ( U.ConType [t|Poison.Poison|] `U.TypeApp` U.AnyType
         , [| \_ x -> traverseF subterms x |]
         )
       ]
     ) subterms


concUB :: forall sym.
  W4I.IsExprBuilder sym =>
  sym ->
  (forall tp. W4I.SymExpr sym tp -> IO (GroundValue tp)) ->
  UndefinedBehavior (RegValue' sym) -> IO (UndefinedBehavior (RegValue' sym))
concUB sym conc ub =
  let bv :: forall w. (1 <= w) => RegValue' sym (BVType w) -> IO (RegValue' sym (BVType w))
      bv (RV x) = RV <$> concBV sym conc x in
  case ub of
    FreeBadOffset ptr ->
      FreeBadOffset <$> concPtr' sym conc ptr
    FreeUnallocated ptr ->
      FreeUnallocated <$> concPtr' sym conc ptr
    MemsetInvalidRegion ptr val len ->
      MemsetInvalidRegion <$> concPtr' sym conc ptr <*> bv val <*> bv len
    ReadBadAlignment ptr a ->
      ReadBadAlignment <$> concPtr' sym conc ptr <*> pure a
    WriteBadAlignment ptr a ->
      WriteBadAlignment <$> concPtr' sym conc ptr <*> pure a

    PtrAddOffsetOutOfBounds ptr off ->
      PtrAddOffsetOutOfBounds <$> concPtr' sym conc ptr <*> bv off
    CompareInvalidPointer op p1 p2 ->
      CompareInvalidPointer op <$> concPtr' sym conc p1 <*> concPtr' sym conc p2
    CompareDifferentAllocs p1 p2 ->
      CompareDifferentAllocs <$> concPtr' sym conc p1 <*> concPtr' sym conc p2
    PtrSubDifferentAllocs p1 p2 ->
      PtrSubDifferentAllocs <$> concPtr' sym conc p1 <*> concPtr' sym conc p2
    PointerFloatCast ptr tp ->
      PointerFloatCast <$> concPtr' sym conc ptr <*> pure tp
    PointerIntCast ptr tp ->
      PointerIntCast <$> concPtr' sym conc ptr <*> pure tp
    PointerUnsupportedOp ptr msg ->
      PointerUnsupportedOp <$> concPtr' sym conc ptr <*> pure msg
    ComparePointerToBV ptr val ->
      ComparePointerToBV <$> concPtr' sym conc ptr <*> bv val
    UDivByZero v1 v2 ->
      UDivByZero <$> bv v1 <*> bv v2
    SDivByZero v1 v2 ->
      SDivByZero <$> bv v1 <*> bv v2
    URemByZero v1 v2 ->
      URemByZero <$> bv v1 <*> bv v2
    SRemByZero v1 v2 ->
      SRemByZero <$> bv v1 <*> bv v2
    SDivOverflow v1 v2 ->
      SDivOverflow <$> bv v1 <*> bv v2
    SRemOverflow v1 v2 ->
      SRemOverflow <$> bv v1 <*> bv v2

    PoisonValueCreated poison ->
      PoisonValueCreated <$> Poison.concPoison sym conc poison
