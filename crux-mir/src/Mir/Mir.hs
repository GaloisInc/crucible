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

{-# LANGUAGE OverloadedStrings #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-unticked-promoted-constructors #-}

module Mir.Mir where

import qualified Data.ByteString as B
import Data.Map.Strict (Map)
import Data.Text (Text)

import Data.Semigroup (Semigroup(..))

import Control.Lens (makeLenses)

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
      | TyStr
      | TyFnPtr !FnSig              -- written as fn() -> i32
      | TyDynamic !TraitName        -- trait object (defid is trait name)
      | TyRawPtr !Ty !Mutability    -- Written as *mut T or *const T
      | TyFloat !FloatKind
      | TyDowncast !Ty !Integer     -- result type of downcasting an ADT. Ty must be an ADT type
      | TyNever
      | TyForeign       -- External types, of unknown size and alignment

      | TyLifetime      -- Placeholder for representing lifetimes in `Substs`
      | TyConst         -- Placeholder for representing constants in `Substs`

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

data NamedTy = NamedTy { _ntName :: Text, _ntTy :: Ty }
  deriving (Eq, Ord, Show, Generic)

data FnSig = FnSig {
    _fsarg_tys    :: ![Ty]
  , _fsreturn_ty  :: !Ty
  , _fsabi        :: Abi
  -- TODO: current handling of spread_arg is a hack.
  --
  -- Correct behavior would be (1) always pass args tupled for rust-call abi
  -- (in other words, translate the MIR as-is, with no special case for calls
  -- to rust-call fns), and (2) in rust-call functions, if `spread_arg` is
  -- null, adjust the sig (by tupling up the argument types) and explicitly
  -- untuple the values on entry to the function.  Current behavior is (2)
  -- translate rust-call function bodies as-is, and (1) tuple argument values
  -- at the call site if the target has rust-call abi and spread_arg is null.
  -- However, on the rust side, the value of spread_arg is part of the
  -- mir::Body, not the signature, which means this design is broken in the
  -- presence of function pointers.
  --
  -- Anyway, that's why this weird `fsspreadarg` field is here.  The sig of a
  -- function definition will include the value of `spread_arg` from the
  -- `mir::Body`, and that will be visible at *direct* calls (not via fn ptr)
  -- of the function, to make decisions about whether to untuple the args.
  , _fsspreadarg  :: Maybe Int
  }
  deriving (Eq, Ord, Show, Generic)

data Abi = RustAbi | RustCall | RustIntrinsic | OtherAbi
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
    deriving (Eq, Ord, Show, Generic)

data Adt = Adt
    { _adtname :: DefId
    , _adtkind :: AdtKind
    , _adtvariants :: [Variant]
    , _adtOrigDefId :: DefId
    , _adtOrigSubsts :: Substs
    }
    deriving (Eq, Ord, Show, Generic)

data AdtKind = Struct | Enum | Union
    deriving (Eq, Ord, Show, Generic)

data VariantDiscr
  = Explicit DefId
  | Relative Int
  deriving (Eq, Ord, Show, Generic)


data CtorKind
  = FnKind
  | ConstKind
  | FictiveKind
  deriving (Eq, Ord, Show, Generic)


data Variant = Variant {_vname :: DefId, _vdiscr :: VariantDiscr, _vfields :: [Field], _vctorkind :: CtorKind}
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
    _namedTys  :: !(Map TyName Ty),
    _roots     :: !([MethName])
} deriving (Show, Eq, Ord, Generic)

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
    _mblocks :: [BasicBlock]
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


data Statement =
      Assign { _alhs :: Lvalue, _arhs :: Rvalue, _apos :: Text }
      -- TODO: the rest of these variants also have positions
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _slv :: Var }
      | StorageDead { _sdv :: Var }
      | Nop
    deriving (Show,Eq, Ord, Generic)

data PlaceElem =
        Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int, _sfrom_end :: Bool }
      | Downcast Integer
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
      | CheckedBinaryOp { _cbop :: BinOp, _cbop1 :: Operand, _cbop2 :: Operand }
      | NullaryOp { _nuop :: NullOp, _nty :: Ty }
      | UnaryOp { _unop :: UnOp, _unoperand :: Operand}
      | Discriminant { _dvar :: Lvalue }
      | Aggregate { _ak :: AggregateKind, _ops :: [Operand] }
      | RAdtAg AdtAg
    deriving (Show,Eq, Ord, Generic)

data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand], _adtagty :: Ty }
    deriving (Show, Eq, Ord, Generic)


data Terminator =
        Goto { _gbb :: BasicBlockInfo}
        -- ^ normal control flow
      -- TODO: the rest of these variants also have positions
      | SwitchInt { _sdiscr    :: Operand,
                    _switch_ty :: Ty,
                    _svalues   :: [Maybe Integer],
                    _stargets  :: [BasicBlockInfo],
                    _spos      :: Text }
        -- ^ case  
      | Resume
      | Abort
      | Return
        -- ^ return to caller normally
      | Unreachable
      | Drop { _dloc    :: Lvalue,
               _dtarget :: BasicBlockInfo,
               _dunwind :: Maybe BasicBlockInfo,
               -- | The DefId of the `drop_in_place` implementation for the
               -- type being dropped.  `Nothing` indicates the type has no
               -- custom drop implementation (and neither do its fields,
               -- transitively).
               _ddrop_fn :: Maybe MethName }
      | DropAndReplace { _drloc    :: Lvalue,
                         _drval    :: Operand,
                         _drtarget :: BasicBlockInfo,
                         _drunwind :: Maybe BasicBlockInfo,
                         _drdrop_fn :: Maybe MethName }
      | Call { _cfunc   :: Operand,
               _cargs   :: [Operand],
               _cdest   :: Maybe (Lvalue, BasicBlockInfo),
               _cleanup :: Maybe BasicBlockInfo }
      | Assert { _acond     :: Operand,
                 _aexpected :: Bool,
                 _amsg      :: AssertMessage,
                 _atarget   :: BasicBlockInfo,
                 _acleanup  :: Maybe BasicBlockInfo}
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
      | Box
      deriving (Show,Eq, Ord, Generic)



data BorrowKind =
        Shared
      | Unique
      | Mutable
      deriving (Show,Eq, Ord, Generic)


data UnOp =
    Not
  | Neg
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

data CastKind =
        Misc
      | ReifyFnPointer
      | ClosureFnPointer
      | UnsafeFnPointer
      | Unsize
      | UnsizeVtable VtableName
      | MutToConstPointer
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
  | ConstStr B.ByteString
  | ConstByteStr B.ByteString
  | ConstBool Bool
  | ConstChar Char
  | ConstVariant DefId
  | ConstFunction DefId
  | ConstTuple [ConstVal]
  | ConstArray [ConstVal]
  | ConstRepeat ConstVal Int
  | ConstInitializer DefId
  -- | A reference to a static, of type `&T`.
  | ConstStaticRef DefId
  | ConstZST
  | ConstRawPtr Integer
  | ConstStruct [ConstVal]
  | ConstEnum Int [ConstVal]
  deriving (Show,Eq, Ord, Generic)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure
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
makeLenses ''AdtAg
makeLenses ''Trait
makeLenses ''Static
makeLenses ''Vtable
makeLenses ''Intrinsic
makeLenses ''Instance
makeLenses ''NamedTy

--------------------------------------------------------------------------------------
-- Other instances for ADT types
--------------------------------------------------------------------------------------

instance Semigroup Collection where
  (Collection f1 a1 a1' t1 s1 v1 n1 tys1 r1) <> (Collection f2 a2 a2' t2 s2 v2 n2 tys2 r2) =
    Collection (f1 <> f2) (a1 <> a2) (a1' <> a2') (t1 <> t2) (s1 <> s2) (v1 <> v2) (n1 <> n2) (tys1 <> tys2) (r1 <> r2)
instance Monoid Collection where
  mempty  = Collection mempty mempty mempty mempty mempty mempty mempty mempty mempty
  mappend = (<>)

  

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
onlyVariant (Adt _ _ [v] _ _) = v
onlyVariant (Adt name kind _ _ _) = error $
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
  where
    peelRef :: Ty -> Ty
    peelRef (TyRef t _) = t
    peelRef (TyRawPtr t _) = t
    peelRef (TyAdt _ $(normDefIdPat "alloc::boxed::Box") (Substs [t])) = t
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
    in case op of
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
  typeOf (CheckedBinaryOp op x y) =
    let resTy = typeOf $ BinaryOp op x y
    in TyTuple [resTy, TyBool]
  typeOf (NullaryOp op ty) = case op of
    SizeOf -> TyUint USize
    Box -> TyAdt (textId "type::adt") (textId "alloc::boxed::Box") (Substs [ty])
  typeOf (UnaryOp op x) =
    let ty = typeOf x
    in case op of
        Not -> ty
        Neg -> ty
  typeOf (Discriminant _lv) = TyInt USize
  typeOf (Aggregate (AKArray ty) ops) = TyArray ty (length ops)
  typeOf (Aggregate AKTuple ops) = TyTuple $ map typeOf ops
  typeOf (Aggregate AKClosure ops) = TyClosure $ map typeOf ops
  typeOf (RAdtAg (AdtAg _ _ _ ty)) = ty

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


