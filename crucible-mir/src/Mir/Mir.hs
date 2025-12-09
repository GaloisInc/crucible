{- |
Module           : Mir.Mir
Description      : Type definitions and serialization functions for Mir
License          : BSD3
-}


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

module Mir.Mir where

import qualified Data.ByteString as B
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import Data.Word (Word64)

import Control.Lens (makeLenses, makePrisms, makeWrapped)

import GHC.Generics

import Mir.DefId

import Data.Coerce(coerce)

-- NOTE: below, all unwinding calls can be ignored
--
--

-- SCW:
-- High-level description of MIR: https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md
-- documentation of rustc data structures
--   https://doc.rust-lang.org/nightly/nightly-rustc/rustc/mir/index.html
-- Source code:
--   https://github.com/rust-lang/rust/blob/master/src/librustc/mir/mod.rs

data BaseSize =
    USize
      | B8
      | B16
      | B32
      | B64
      | B128
      deriving (Eq, Ord, Show, Generic)

data FloatKind
  = F32
  | F64
  deriving (Eq, Ord, Show, Generic)

-- | Type parameters
newtype Substs = Substs [Ty]
  deriving (Eq, Ord, Show, Generic)
  deriving newtype (Semigroup, Monoid)

data Ty =
        TyBool               -- The primitive boolean type. Written as bool.
      | TyChar
      | TyInt !BaseSize
      | TyUint !BaseSize
      | TyTuple ![Ty]         -- A tuple type. For example, (i32, bool)
      | TySlice !Ty
      | TyArray !Ty !Int
      | TyRef !Ty !Mutability  -- Written &'a mut T or &'a T
      -- For TyAdt, we keep both the monomorphized name and the pre-mono name +
      -- substs because the Ty patterns in Mir.TransTy (such as `CTyVector`)
      -- need to consult the pre-mono information.  This duplicates information
      -- that's present in the `Adt` entry, but the `Adt` (actually the whole
      -- `Collection`) is not accessible inside `tyToRepr`.
      | TyAdt !DefId !DefId !Substs -- first DefId is the monomorphized name, second is pre-mono
      | TyFnDef !DefId
      | TyClosure [Ty]      -- the Tys are the types of the upvars
      | TyCoroutine
        -- ^ @crucible-mir@ does not support coroutines (#1369), but we
        -- nevertheless include this as a 'Ty' so that we can successfully
        -- translate code that mentions it. Provided that that code is never
        -- simulated, this should work out.
      | TyCoroutineClosure [Ty]     -- the Tys are the types of the upvars
      | TyStr
      | TyFnPtr !FnSig              -- written as fn() -> i32
      | TyDynamic !TraitName        -- trait object (defid is trait name)
      | TyRawPtr !Ty !Mutability    -- Written as *mut T or *const T
      | TyFloat !FloatKind
      | TyDowncast !Ty !Integer     -- result type of downcasting an ADT. Ty must be an ADT type
      | TyNever
      | TyForeign       -- External types, of unknown size and alignment

      | TyConst !ConstVal
        -- ^ Represents constants in 'Substs'. This has no effect on the
        -- semantics of @crucible-mir@, but it is used for looking up
        -- instantiations of polymorphic functions or ADTs in SAW.
      | TyLifetime      -- Placeholder for representing lifetimes in `Substs`

      -- | The erased concrete type of a trait object.  This is never emitted
      -- by mir-json.  It's used in vtable shims, to replace the type of the
      -- receiver argument.  The effect is for the vtable shim to take in a
      -- Crucible "Any" value (the translation of TyErased), which it then
      -- downcasts to the concrete receiver type and passes to the
      -- implementation of the trait method.
      | TyErased

      -- | Special variant used during deserialization to represent interned
      -- types.  These are all replaced with other variants in `uninternTys`,
      -- which runs just after JSON decoding is done.
      | TyInterned TyName
      deriving (Eq, Ord, Show, Generic)

data NamedTy = NamedTy
  { _ntName :: Text
  , _ntTy :: Ty
    -- | If 'Nothing' then the type is unsized.
  , _ntLayout :: Maybe Layout
    -- | Whether the type needs drop glue
  , _ntNeedsDrop :: Bool
  }
  deriving (Eq, Ord, Show, Generic)

-- | Layout of a type.
data Layout = Layout
  { -- | ABI alignment in bytes
    _layAlign :: Word64
    -- | Size in bytes
  , _laySize :: Word64
  }
  deriving (Eq, Ord, Show, Generic)

data LangItem = LangItem
  { -- | The original 'DefId' for a lang item (e.g., @core::option::Option@).
    _liOrigDefId :: DefId
    -- | The @$lang@-based 'DefId' for a lang item (e.g., @$lang::Option@).
  , _liLangItemDefId :: DefId
  }
  deriving (Eq, Ord, Show, Generic)

data FnSig = FnSig {
    _fsarg_tys    :: ![Ty]
  , _fsreturn_ty  :: !Ty
  , _fsabi        :: Abi
  }
  deriving (Eq, Ord, Show, Generic)

data Abi
    = RustAbi
    | RustCall RustCallBodyInfo
    | OtherAbi
    deriving (Show, Eq, Ord, Generic)

data RustCallBodyInfo
    = RcNoBody
    -- ^ The `FnSig` containing this `RustCall` `Abi` isn't the signature of a
    -- `Fn` body.  For example, @extern "rust-call"@ function pointers always
    -- have an ABI of @`RustCall` `RcNoBody`@.
    | RcNoSpreadArg
    -- ^ The `FnSig` is associated with a body, but the body's @spread_arg@
    -- field is unset.  This applies to closure implementations, which are
    -- are @extern "rust-call"@ and are called with tupled arguments, but are
    -- defined with un-tupled arguments (and no @spread_arg@).  For such
    -- functions, `fsarg_tys` will contain the un-tupled arguments, and the ABI
    -- will be @`RustCall` `RcNoSpreadArg`@.
    | RcSpreadArg Int
    -- ^ The `FnSig` is associated with a body, and the body has a @spread_arg@
    -- index.  This applies to various @extern "rust-call"@ closure-related
    -- shims and vtable methods, which are both called and defined with a
    -- tupled signature.
    deriving (Show, Eq, Ord, Generic)

data Instance = Instance
    { _inKind :: InstanceKind
    -- | The meaning of this `DefId` depends on the `InstanceKind`.  Usually,
    -- it's the ID of the original generic definition of the function that's
    -- been monomorphized to produce this instance.
    , _inDefId :: DefId
    -- | The substitutions used to construct this instance from the generic
    -- definition.  Typically (but again depending on the `InstanceKind`),
    -- applying these substs to the signature of the generic def gives the
    -- signature of the instance.
    , _inSubsts :: Substs
    }
    deriving (Eq, Ord, Show, Generic)

data InstanceKind =
      IkItem
    | IkIntrinsic
    | IkVtableShim
    | IkReifyShim
    | IkFnPtrShim Ty
    | IkVirtual !TraitName !Integer
    | IkClosureOnceShim
    | IkDropGlue (Maybe Ty)
    | IkCloneShim Ty [DefId]
    | IkClosureFnPointerShim
    -- ^ Shim used when converting a closure to a function pointer.  This
    -- function builds a dummy closure value and then passes it to `_inDefId`,
    -- which is the closure's `call_mut` method.
    deriving (Eq, Ord, Show, Generic)

data Adt = Adt
    { _adtname :: DefId
    , _adtkind :: AdtKind
    , _adtvariants :: [Variant]
    , _adtSize :: Int
    , _adtReprTransparent :: Bool
    , _adtOrigDefId :: DefId
    , _adtOrigSubsts :: Substs
    }
    deriving (Eq, Ord, Show, Generic)

data AdtKind
    = Struct
    | Enum { -- | The type of the discriminant used to pick which variant of
             -- the enum to use. This type can be of varying sizes depending
             -- on how many variants the enum has.
             _enumDiscrTy :: Ty }
    | Union
    deriving (Eq, Ord, Show, Generic)

data VariantDiscr
  = Explicit DefId
  | Relative Int
  deriving (Eq, Ord, Show, Generic)


data CtorKind
  = FnKind
  | ConstKind
  deriving (Eq, Ord, Show, Generic)


data Variant = Variant {
  _vname :: DefId,
  _vdiscr :: VariantDiscr,
  _vfields :: [Field],
  _vctorkind :: Maybe CtorKind,
  _discrval :: Maybe Integer,
  _vinhabited :: Bool }
    deriving (Eq, Ord,Show, Generic)


data Field = Field {_fName :: DefId, _fty :: Ty}
    deriving (Show, Eq, Ord, Generic)


data Mutability
  = Mut
  | Immut
  deriving (Eq, Ord, Show, Generic)

data Var = Var {
    _varname :: Text,
    _varmut :: Mutability,
    _varty :: Ty,
    _varIsZST :: Bool }
    deriving (Eq, Show, Generic)

instance Ord Var where
    compare (Var n _ _ _) (Var m _ _ _) = compare n m

data Collection = Collection {
    _version   :: !Word64,
    _functions :: !(Map MethName Fn),
    _adts      :: !(Map AdtName Adt),
    -- ADTs, indexed by original (pre-monomorphization) DefId
    _adtsOrig  :: !(Map AdtName [Adt]),
    _traits    :: !(Map TraitName Trait),
    -- Static decls, indexed by name.  For each of these, there is an
    -- initializer in `functions` with the same name.
    _statics   :: !(Map DefId Static),
    _vtables   :: !(Map VtableName Vtable),
    _intrinsics :: !(Map IntrinsicName Intrinsic),
    -- | This corresponds to the @tys@ table from @mir-json@ and is cleared
    -- after uninterning. 'TypeInfo' provides information that helps us fill out
    -- several parts of the 'Collection':
    -- - A @TyName -> Ty@ mapping, which is used for uninterning the types in
    --   the rest of the 'Collection'
    -- - A @Ty -> Maybe Layout@ mapping, which is saved into '_layouts'
    -- - A @Ty -> Bool@ mapping (indicating whether or not the type needs drop
    --   glue), which is saved into `_needDrops`
    _namedTys  :: !(Map TyName TyInfo),
    -- | Layouts for known types. If the value is 'Nothing' then the type is
    -- unsized. This is not populated until uninterning.
    _layouts   :: !(Map Ty (Maybe Layout)),
    -- | Types that need drop glue.
    _needDrops :: !(Set Ty),
    -- | Map the original 'DefId's for lang items to their custom, @$lang@-based
    -- 'DefId's (e.g., map @core::option::Option@ to @$lang/Option@).
    _langItems :: !(Map DefId DefId),
    -- | The roots of all things that were translated
    _roots     :: ![MethName],
    -- | The subset of roots that was marked as tests to execute
    _tests     :: ![MethName]

} deriving (Show, Eq, Ord, Generic)

-- | Information about a type (minus its name), as seen in the @tys@ table in
-- @mir-json@-generated JSON.
data TyInfo = TyInfo
    { _tiLayout :: Maybe Layout
    , _tiNeedsDrop :: Bool
    , _tiTy :: Ty
    }
    deriving (Show, Eq, Ord, Generic)

data Intrinsic = Intrinsic
    { _intrName :: IntrinsicName
    , _intrInst :: Instance
    }
    deriving (Show, Eq, Ord, Generic)


data Fn = Fn {
     _fname       :: DefId
    ,_fargs       :: [Var]
    ,_fsig        :: FnSig
    ,_fbody       :: MirBody
    }
    deriving (Show,Eq, Ord, Generic)


data MirBody = MirBody {
    _mvars :: [Var],
    _mblocks :: [BasicBlock],
    _mblockmap :: Map BasicBlockInfo BasicBlockData
}
    deriving (Show,Eq, Ord, Generic)


data BasicBlock = BasicBlock {
    _bbinfo :: BasicBlockInfo,
    _bbdata :: BasicBlockData
}
    deriving (Show,Eq, Ord, Generic)



data BasicBlockData = BasicBlockData {
    _bbstmts :: [Statement],
    _bbterminator :: Terminator
}
    deriving (Show,Eq, Ord, Generic)

-- | A pair of a 'StatementKind' and its source position.
data Statement = Statement
    { _stmtKind :: StatementKind
    , _stmtPos :: Text
    }
    deriving (Eq, Ord, Show, Generic)

-- | The various kinds of statements that can appear in MIR.
data StatementKind =
      Assign { _alhs :: Lvalue, _arhs :: Rvalue }
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _slv :: Var }
      | StorageDead { _sdv :: Var }
      | Nop
      | Deinit
      | StmtIntrinsic NonDivergingIntrinsic
      | ConstEvalCounter
    deriving (Show,Eq, Ord, Generic)

data NonDivergingIntrinsic =
        NDIAssume Operand
      | NDICopyNonOverlapping Operand Operand Operand
    deriving (Show,Eq, Ord, Generic)

data PlaceElem =
        Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int, _sfrom_end :: Bool }
        -- ^ Project into a subslice of a sequence (i.e. slice or array). For a
        -- sequence @s@, when @fromEnd@ is `False`, @Subslice from to fromEnd@
        -- is like saying @s[from..to]@ in Rust - it selects elements in @s@ in
        -- the half-open range @[from, to)@. When @fromEnd@ is `True`, @to@ is
        -- interpreted relative to the end of the sequence, rather than the
        -- beginning - so if @s@ has length @len@, elements are instead selected
        -- from the (still half-open) range @[from, len - to)@.
      | Downcast Integer
      | Subtype Ty
      deriving (Show, Eq, Ord, Generic)

-- Called "Place" in rustc itself, hence the names of PlaceBase and PlaceElem
data Lvalue =
        LBase Var
      | LProj Lvalue PlaceElem
      deriving (Show, Eq, Generic)

instance Ord Lvalue where
    compare l1 l2 = compare (show l1) (show l2)


data Rvalue =
        Use { _uop :: Operand }
        -- ^ just read an lvalue
      | Repeat { _rop :: Operand, _rlen :: ConstUsize }
      | Ref { _rbk :: BorrowKind, _rvar :: Lvalue, _rregion :: Text }
      | AddressOf { _aomutbl :: Mutability, _aoplace :: Lvalue }
      | Len { _lenvar :: Lvalue }
        -- ^ load length from a slice
      | Cast { _cck :: CastKind, _cop :: Operand, _cty :: Ty }
      | BinaryOp { _bop :: BinOp, _bop1 :: Operand, _bop2 :: Operand }
      | NullaryOp { _nuop :: NullOp, _nty :: Ty }
      | UnaryOp { _unop :: UnOp, _unoperand :: Operand}
      | Discriminant { _dvar :: Lvalue,
                       -- | The type of the discriminant. That is, /not/ the
                       -- type of the enum itself, but rather the type of the
                       -- value used to choose which variant of the enum to use.
                       --
                       -- Although this type is also stored in the 'Lvalue', it
                       -- can only be retrieved in a monadic context. We cache
                       -- the type here for the benefit of `Rvalue`'s 'TypeOf'
                       -- instance, which requires a pure context.
                       _dty :: Ty }
      | Aggregate { _ak :: AggregateKind, _ops :: [Operand] }
      | RAdtAg AdtAg
      | ShallowInitBox { _sibptr :: Operand, _sibty :: Ty }
      | CopyForDeref Lvalue
      | ThreadLocalRef DefId Ty
    deriving (Show,Eq, Ord, Generic)

-- | An aggregate ADT expression.
data AdtAg = AdtAg {
    _agadt :: Adt,
    _avgariant :: Integer,
    _aops :: [Operand],
    _adtagty :: Ty,
    -- | For union aggregates, there's only operand in `_aops`, and `_afield`
    -- indicates which field of the union the value is written to.
    _afield :: Maybe Int
    }
    deriving (Show, Eq, Ord, Generic)

-- | A pair of a 'TerminatorKind' and its source position.
data Terminator = Terminator
    { _termKind :: TerminatorKind
    , _termPos :: Text
    }
    deriving (Eq, Ord, Show, Generic)

-- | The various kinds of terminators, representing ways of exiting from a basic
-- block.
data TerminatorKind =
        Goto { _gbb :: BasicBlockInfo}
        -- ^ normal control flow
      | SwitchInt { _sdiscr    :: Operand,
                    _switch_ty :: Ty,
                    _svalues   :: [Maybe Integer],
                    _stargets  :: [BasicBlockInfo] }
        -- ^ case
      | Resume
      | Abort
      | Return
        -- ^ return to caller normally
      | Unreachable
      | Drop { _dloc    :: Lvalue,
               _dtarget :: BasicBlockInfo,
               -- | The DefId of the `drop_in_place` implementation for the
               -- type being dropped.  `Nothing` indicates the type has no
               -- custom drop implementation (and neither do its fields,
               -- transitively).
               _ddrop_fn :: Maybe MethName }
      | Call { _cfunc   :: Operand,
               _cargs   :: [Operand],
               _cdest   :: Maybe (Lvalue, BasicBlockInfo) }
      | Assert { _acond     :: Operand,
                 _aexpected :: Bool,
                 _amsg      :: AssertMessage,
                 _atarget   :: BasicBlockInfo }
      | InlineAsm
        -- ^ @crucible-mir@ does not support simulating inline assembly, but we
        -- nevertheless include this as a 'TerminatorKind' so that we can
        -- successfully translate code that mentions it. Provided that that
        -- code is never simulated, this should work out.
      deriving (Show,Eq, Ord, Generic)

data Operand =
        Copy Lvalue
      | Move Lvalue
      | OpConstant Constant
      -- | The result of evaluating an Rvalue.  This never appears in
      -- rustc-generated MIR, but we produce them internally in some cases.
      | Temp Rvalue
      deriving (Show, Eq, Ord, Generic)

data NullOp =
        SizeOf
      | AlignOf
      | UbChecks
      deriving (Show,Eq, Ord, Generic)



data BorrowKind =
        Shared
      | Unique
      | Mutable
      deriving (Show,Eq, Ord, Generic)


data UnOp =
    Not
  | Neg
  | PtrMetadata
  deriving (Show,Eq, Ord, Generic)


data BinOp =
    Add
      | Sub
      | Mul
      | Div
      | Rem
      | BitXor
      | BitAnd
      | BitOr
      | Shl
      | Shr
      | Beq
      | Lt
      | Le
      | Ne
      | Ge
      | Gt
      | Offset
      | Cmp
      | Unchecked BinOp
        -- ^ A variant of a 'BinOp' for which overflow is undefined behavior.
      | WithOverflow BinOp
        -- ^ A variant of a 'BinOp' that returns @(T, bool)@ of both the wrapped
        -- result and a @bool@ indicating whether it overflowed.
  deriving (Show,Eq, Ord, Generic)

data VtableItem = VtableItem
    { _vtFn :: DefId        -- ^ ID of the implementation that should be stored in the vtable
    , _vtDef :: DefId       -- ^ ID of the item definition in the trait
    }
    deriving (Show, Eq, Ord, Generic)

data Vtable = Vtable
    { _vtName :: VtableName
    , _vtItems :: [VtableItem]
    }
    deriving (Show, Eq, Ord, Generic)

-- TODO: add other castkinds (see https://github.com/GaloisInc/crucible/issues/1223)
data CastKind =
    Misc
  | ReifyFnPointer
  | ClosureFnPointer DefId
  -- ^ Closure-to-fnptr cast.  The `DefId` refers to the
  -- `IkClosureFnPointerShim` that is the result of the cast.
  | UnsafeFnPointer
  | Unsize
  | UnsizeVtable VtableName
  | MutToConstPointer
  | Transmute
  deriving (Show,Eq, Ord, Generic)

data Constant = Constant Ty ConstVal
  deriving (Eq, Ord, Show, Generic)

data IntLit
  = U8 Integer
  | U16 Integer
  | U32 Integer
  | U64 Integer
  | U128 Integer
  | Usize Integer
  | I8 Integer
  | I16 Integer
  | I32 Integer
  | I64 Integer
  | I128 Integer
  | Isize Integer
  deriving (Eq, Ord, Show, Generic)

data FloatLit
  = FloatLit FloatKind String
  deriving (Eq, Ord, Show, Generic)


data ConstVal =
    ConstFloat FloatLit
  | ConstInt IntLit
  -- | A reference to a static allocation for a slice (type is `&[T]` or `&str`)
  -- The DefId can lead to either a ConstArray or a ConstStrBody.
  | ConstSliceRef DefId Int
  -- | A string body, of type [u8]. Currently only arises from string literals,
  -- but might in the future be used for all [u8]s.
  | ConstStrBody B.ByteString
  | ConstBool Bool
  | ConstChar Char
  | ConstVariant DefId
  | ConstFunction DefId
  | ConstTuple [ConstVal]
  | ConstClosure [ConstVal]
  | ConstCoroutineClosure [ConstVal]
  | ConstArray [ConstVal]
  | ConstRepeat ConstVal Int
  | ConstInitializer DefId
  -- | A reference to a static, of type `&T`.
  | ConstStaticRef DefId
  | ConstZST
  | ConstRawPtr Integer
  | ConstStruct [ConstVal]
  | ConstEnum Int [ConstVal]
  | ConstUnion
  | ConstFnPtr DefId
  deriving (Show,Eq, Ord, Generic)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure
      | AKCoroutine
      | AKCoroutineClosure
      | AKRawPtr Ty Mutability
      deriving (Show,Eq, Ord, Generic)

data Trait = Trait { _traitName       :: !DefId,
                     _traitItems      :: ![TraitItem]
                   }
    deriving (Eq, Ord, Show, Generic)


data TraitItem
    = TraitMethod DefId FnSig
    deriving (Eq, Ord, Show, Generic)

data Static   = Static {
    _sName          :: DefId            -- ^ name of fn that initializes this static
  , _sTy            :: Ty
  , _sMutable       :: Bool             -- ^ true for "static mut"
  , _sConstVal      :: Maybe ConstVal   -- ^ 'Just' if this static is initialized
                                        -- with a constant value. 'Nothing' otherwise.
  }
  deriving (Show, Eq, Ord, Generic)

-- Documentation for particular use-cases of DefIds
type TraitName  = DefId
type MethName   = DefId
type AdtName    = DefId
type VtableName = DefId
type IntrinsicName = DefId

--- Other texts
type ConstUsize = Integer
type VisibilityScope = Text
type AssertMessage = Text
type BasicBlockInfo = Text
type TyName     = Text


--------------------------------------------------------------------------------------
-- Lenses
--------------------------------------------------------------------------------------


makeLenses ''Variant
makeLenses ''Field
makeLenses ''Var
makeLenses ''Collection
makeLenses ''Fn
makeLenses ''FnSig
makeLenses ''MirBody
makeLenses ''BasicBlock
makeLenses ''BasicBlockData
makeLenses ''Adt
makePrisms ''AdtKind
makeLenses ''AdtAg
makeLenses ''Trait
makeLenses ''Static
makeLenses ''Vtable
makeLenses ''Intrinsic
makeLenses ''Instance
makeLenses ''NamedTy
makeLenses ''TyInfo
makeLenses ''Layout
makeLenses ''LangItem
makeLenses ''Statement
makeLenses ''Terminator
makeWrapped ''Substs

--------------------------------------------------------------------------------------
--- aux functions ---
--------------------------------------------------------------------------------------

-- | access the Integer in an IntLit
fromIntegerLit :: IntLit -> Integer
fromIntegerLit (U8 i)    = i
fromIntegerLit (U16 i)   = i
fromIntegerLit (U32 i)   = i
fromIntegerLit (U64 i)   = i
fromIntegerLit (U128 i)  = i
fromIntegerLit (Usize i) = i
fromIntegerLit (I8 i)    = i
fromIntegerLit (I16 i)   = i
fromIntegerLit (I32 i)   = i
fromIntegerLit (I64 i)   = i
fromIntegerLit (I128 i)  = i
fromIntegerLit (Isize i) = i


-- Get the only variant of a struct or union ADT.
onlyVariant :: Adt -> Variant
onlyVariant (Adt _ _ [v] _ _ _ _) = v
onlyVariant (Adt name kind _ _ _ _ _) = error $
    "expected " ++ show kind ++ " " ++ show name ++ " to have only one variant"





--------------------------------------------------------------------------------------
-- | arithType

data ArithType = Signed | Unsigned deriving (Eq,Ord,Show)

class ArithTyped a where
    arithType :: a -> Maybe ArithType
instance TypeOf a => ArithTyped a where
    arithType a =
      case typeOf a of
        (TyInt _) -> Just Signed
        (TyUint _ ) -> Just Unsigned
        TyChar -> Just Unsigned
        _  -> Nothing

--------------------------------------------------------------------------------------
-- | Lang items

pattern CTyOrdering :: Ty
pattern CTyOrdering <- TyAdt _ $(explodedDefIdPat ["$lang", "OrderingEnum"]) (Substs [])
  where CTyOrdering = TyAdt
          (textId "$lang/0::OrderingEnum::_adt[0]")
          (textId "$lang/0::OrderingEnum")
          (Substs [])

--------------------------------------------------------------------------------------
-- | TypeOf

class TypeOf a where
    typeOf :: a -> Ty

instance TypeOf Ty where
    typeOf ty = ty

instance TypeOf Var where
    typeOf (Var _ _ t _) = t

instance TypeOf Lvalue where
    typeOf (LBase base) = typeOf base
    typeOf (LProj l elm) = typeOfProj elm $ typeOf l

typeOfProj :: PlaceElem -> Ty -> Ty
typeOfProj elm baseTy = case elm of
    PField _ t      -> t
    Deref           -> peelRef baseTy
    Index{}         -> peelIdx baseTy
    ConstantIndex{} -> peelIdx baseTy
    Downcast i      -> TyDowncast baseTy i   --- TODO: check this
    Subslice{}      -> TySlice (peelIdx baseTy)
    Subtype t       -> t
  where
    peelRef :: Ty -> Ty
    peelRef (TyRef t _) = t
    peelRef (TyRawPtr t _) = t
    peelRef (TyAdt _ $(explodedDefIdPat ["alloc", "boxed", "Box"]) (Substs [t])) = t
    peelRef t = t

    peelIdx :: Ty -> Ty
    peelIdx (TyArray t _) = t
    peelIdx (TySlice t)   = t
    peelIdx (TyRef t m)   = TyRef (peelIdx t) m
    peelIdx t             = t

instance TypeOf Rvalue where
  typeOf (Use a) = typeOf a
  typeOf (Repeat a sz) = TyArray (typeOf a) (fromIntegral sz)
  typeOf (Ref Shared lv _)  = TyRef (typeOf lv) Immut
  typeOf (Ref Mutable lv _) = TyRef (typeOf lv) Mut
  typeOf (Ref Unique lv _)  = TyRef (typeOf lv) Mut
  typeOf (AddressOf mutbl lv) = TyRawPtr (typeOf lv) mutbl
  typeOf (Len _) = TyUint USize
  typeOf (Cast _ _ ty) = ty
  typeOf (BinaryOp op x _y) =
    let ty = typeOf x
        f op' = case op' of
            Add -> ty
            Sub -> ty
            Mul -> ty
            Div -> ty
            Rem -> ty
            BitXor -> ty
            BitAnd -> ty
            BitOr -> ty
            Shl -> ty
            Shr -> ty
            Beq -> TyBool
            Lt -> TyBool
            Le -> TyBool
            Ne -> TyBool
            Ge -> TyBool
            Gt -> TyBool
            -- ptr::offset
            Offset -> ty
            Cmp -> CTyOrdering
            Unchecked op'' -> f op''
            WithOverflow op'' -> TyTuple [f op'', TyBool]
    in f op
  typeOf (NullaryOp op _ty) = case op of
    SizeOf -> TyUint USize
    AlignOf -> TyUint USize
    UbChecks -> TyBool
  typeOf (UnaryOp op x) =
    let ty = typeOf x
    in case op of
        Not -> ty
        Neg -> ty
        PtrMetadata -> case ty of
            TyRef (TySlice _) _ -> TyUint USize
            TyRawPtr (TySlice _) _ -> TyUint USize
            -- FIXME: also handle `&dyn Trait` and custom DSTs
            _ -> TyTuple []
  typeOf (Discriminant _lv ty) = ty
  typeOf (Aggregate (AKArray ty) ops) = TyArray ty (length ops)
  typeOf (Aggregate AKTuple ops) = TyTuple $ map typeOf ops
  typeOf (Aggregate AKClosure ops) = TyClosure $ map typeOf ops
  typeOf (Aggregate (AKRawPtr ty mutbl) _ops) = TyRawPtr ty mutbl
  typeOf (Aggregate AKCoroutine _ops) = TyCoroutine
  typeOf (Aggregate AKCoroutineClosure ops) = TyCoroutineClosure $ map typeOf ops
  typeOf (RAdtAg (AdtAg _ _ _ ty _)) = ty
  typeOf (ShallowInitBox _ ty) = ty
  typeOf (CopyForDeref lv) = typeOf lv
  typeOf (ThreadLocalRef _ ty) = ty

instance TypeOf Operand where
    typeOf (Move lv) = typeOf lv
    typeOf (Copy lv) = typeOf lv
    typeOf (OpConstant c) = typeOf c
    typeOf (Temp rv) = typeOf rv

instance TypeOf Constant where
    typeOf (Constant a _b) = a


--------------------------------------------------------------------------------------------
-- coercing list operations to Substs
-------------------------------------------------------------------------------

-- | insertAt xs k ys  is equivalent to take k ++ xs ++ drop k
insertAt :: [a] -> Int -> [a] -> [a]
insertAt xs 0 ys = xs ++ ys
insertAt xs _n [] = xs
insertAt xs n (y:ys) = y : insertAt xs (n - 1)ys

-- | access nth component (if possible)
safeNth :: Int -> [a] -> Maybe a
safeNth n (x:xs)
  | n > 0     = safeNth (n-1) xs
  | n == 0    = Just x
  | otherwise = Nothing
safeNth _n []  = Nothing

-----------------

-- | is the substs empty?
nullSubsts :: Substs -> Bool
nullSubsts = coerce (null @[] @Ty)

-- | If the substs is infinite, this may not terminate
lengthSubsts :: Substs -> Int
lengthSubsts = coerce (length @[] @Ty)

-- | insertAt xs k ys  is equivalent to take k ++ xs ++ drop k
insertAtSubsts :: Substs -> Int -> Substs -> Substs
insertAtSubsts = coerce (insertAt @Ty)

-- | access nth component (if possible)
safeNthSubsts :: Int -> Substs -> Maybe Ty
safeNthSubsts = coerce (safeNth @Ty)

-- | Truncate a substitution by the first n
takeSubsts :: Int -> Substs -> Substs
takeSubsts = coerce (take @Ty)

-- | drop n xs returns the suffix of xs after the first n elements, or [] if n > length xs:
dropSubsts :: Int -> Substs -> Substs
dropSubsts = coerce (drop @Ty)

-- | splitAt n xs returns a tuple where first element is xs prefix of
-- length n and second element is the remainder of the list
splitAtSubsts :: Int -> Substs -> (Substs,Substs)
splitAtSubsts = coerce (splitAt @Ty)


