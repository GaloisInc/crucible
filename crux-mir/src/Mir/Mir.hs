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
import Data.Vector (Vector)

import Data.Semigroup(Semigroup(..))


import Control.Lens(makeLenses, Simple, Lens, lens)

import GHC.Generics 
import GHC.Stack

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

-- | Associated types
--   The projection of an associated type from a Rust trait, at specific types
type AssocTy = (DefId, Substs)

data Ty =
        TyBool               -- The primitive boolean type. Written as bool.
      | TyChar
      | TyInt !BaseSize
      | TyUint !BaseSize
      | TyTuple ![Ty]         -- A tuple type. For example, (i32, bool)
      | TySlice !Ty
      | TyArray !Ty !Int
      | TyRef !Ty !Mutability  -- Written &'a mut T or &'a T
      | TyAdt !DefId !Substs 
      | TyUnsupported
      | TyCustom !CustomTy
      | TyParam !Integer
      | TyFnDef !DefId !Substs
      | TyClosure [Ty]      -- the Tys are the types of the upvars
      | TyStr
      | TyFnPtr !FnSig              -- written as fn() -> i32
      | TyDynamic [Predicate]       -- trait object (defid is trait name)
      | TyRawPtr !Ty !Mutability    -- Written as *mut T or *const T
      | TyFloat !FloatKind
      | TyDowncast !Ty !Integer     -- result type of downcasting an ADT. Ty must be an ADT type
      | TyProjection !DefId !Substs -- The projection of an associated type. For example, <T as Trait<..>>::N.
      | TyNever

      | TyLifetime      -- Placeholder for representing lifetimes in `Substs`
      | TyConst         -- Placeholder for representing constants in `Substs`

      -- | The erased concrete type of a trait object.  This is never emitted
      -- by mir-json.  It's used in vtable shims, to replace the type of the
      -- receiver argument.  The effect is for the vtable shim to take in a
      -- Crucible "Any" value (the translation of TyErased), which it then
      -- downcasts to the concrete receiver type and passes to the
      -- implementation of the trait method.
      | TyErased
      deriving (Eq, Ord, Show, Generic)

data FnSig = FnSig {
    _fsarg_tys    :: ![Ty]
  , _fsreturn_ty  :: !Ty
  , _fsgenerics   :: ![Param]
  , _fspredicates :: ![Predicate]
  , _fsassoc_tys  :: ![AssocTy]    -- new params added in a pre-pass
  , _fsabi        :: Abi
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
    | IkFnPtrShim Ty
    | IkVirtual !Integer
    | IkClosureOnceShim
    | IkDropGlue (Maybe Ty)
    | IkCloneShim Ty
    deriving (Eq, Ord, Show, Generic)

data Adt = Adt {_adtname :: DefId, _adtkind :: AdtKind, _adtvariants :: [Variant]}
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


data Field = Field {_fName :: DefId, _fty :: Ty, _fsubsts :: Substs}
    deriving (Show, Eq, Ord, Generic)


data CustomTy =
        BoxTy Ty
      | VecTy Ty                 -- ::vec::Vec<Ty>
      | IterTy Ty
      | CEnum DefId [Integer]    -- C-style Enumeration, all variants must be trivial
    deriving (Eq, Ord, Show, Generic)

data Mutability
  = Mut
  | Immut
  deriving (Eq, Ord, Show, Generic)

data Var = Var {
    _varname :: Text,
    _varmut :: Mutability,
    _varty :: Ty,
    _varIsZST :: Bool,
    _varscope :: VisibilityScope,
    _varpos :: Text }
    deriving (Eq, Show, Generic)

instance Ord Var where
    compare (Var n _ _ _ _ _) (Var m _ _ _ _ _) = compare n m

data Collection = Collection {
    _functions :: !(Map MethName Fn),
    _adts      :: !(Map AdtName Adt),
    _traits    :: !(Map TraitName Trait),
    _impls     :: !([TraitImpl]),
    _statics   :: !(Map DefId Static),
    _vtables   :: !(Map VtableName Vtable),
    _intrinsics :: !(Map IntrinsicName Intrinsic),
    _roots     :: !([MethName])
} deriving (Show, Eq, Ord, Generic)

data Intrinsic = Intrinsic
    { _intrName :: IntrinsicName
    , _intrInst :: Instance
    }
    deriving (Show, Eq, Ord, Generic)

data Predicate =
  TraitPredicate {
    _ptrait :: !DefId,
    _psubst :: !Substs
    }
  | TraitProjection {
      _plhs    :: !Ty
    , _prhs    :: !Ty
    }
  -- | Special representation for auto-trait predicates in `TyDynamic`.  This
  -- is equivalent to `TraitPredicate ptrait (Substs [])`, but auto-trait
  -- predicates need special handling around vtables, so it's useful to have a
  -- separate variant.
  | AutoTraitPredicate {
    _ptrait :: !DefId
    }
  | UnknownPredicate
    deriving (Show, Eq, Ord, Generic)

data Param = Param {
    _pname :: Text
} deriving (Show, Eq, Ord, Generic)

newtype Params = Params [Param]
   deriving (Show, Eq, Ord, Generic)


newtype Predicates = Predicates [Predicate]
   deriving (Show, Eq, Ord, Generic)


data Fn = Fn {
     _fname       :: DefId
    ,_fargs       :: [Var]
    ,_fsig        :: FnSig
    ,_fbody       :: MirBody
    ,_fpromoted   :: Vector DefId
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

data PlaceBase =
        Local { _lvar :: Var }
      | PStatic DefId Ty
      | PPromoted Int Ty
      deriving (Show, Eq, Generic)

data PlaceElem =
        Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int }
      | Downcast Integer
      deriving (Show, Eq, Ord, Generic)

-- Called "Place" in rustc itself, hence the names of PlaceBase and PlaceElem
data Lvalue =
        LBase PlaceBase
      | LProj Lvalue PlaceElem
      deriving (Show, Eq, Generic)

instance Ord Lvalue where
    compare l1 l2 = compare (show l1) (show l2)


data Rvalue =
        Use { _uop :: Operand }
        -- ^ just read an lvalue
      | Repeat { _rop :: Operand, _rlen :: ConstUsize }
      | Ref { _rbk :: BorrowKind, _rvar :: Lvalue, _rregion :: Text }
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
      | RCustom CustomAggregate
    deriving (Show,Eq, Ord, Generic)

data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand], _adtagty :: Ty }
    deriving (Show, Eq, Ord, Generic)


data Terminator =
        Goto { _gbb :: BasicBlockInfo}
        -- ^ normal control flow
      | SwitchInt { _sdiscr    :: Operand,
                    _switch_ty :: Ty,
                    _svalues   :: [Maybe Integer],
                    _stargets  :: [BasicBlockInfo] }
        -- ^ case  
      | Resume
      | Return
        -- ^ return to caller normally
      | Unreachable
      | Drop { _dloc    :: Lvalue,
               _dtarget :: BasicBlockInfo,
               _dunwind :: Maybe BasicBlockInfo }
      | DropAndReplace { _drloc    :: Lvalue,
                         _drval    :: Operand,
                         _drtarget :: BasicBlockInfo,
                         _drunwind :: Maybe BasicBlockInfo }
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
      deriving (Show, Eq, Ord, Generic)

data Constant = Constant { _conty :: Ty, _conliteral :: Literal } deriving (Show, Eq, Ord, Generic)



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

data Literal =
    Item DefId Substs
  | Value ConstVal
  | LitPromoted Promoted
  deriving (Show,Eq, Ord, Generic)

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
  | ConstStr String
  | ConstByteStr B.ByteString
  | ConstBool Bool
  | ConstChar Char
  | ConstVariant DefId
  | ConstFunction DefId Substs
  | ConstStruct
  | ConstTuple [ConstVal]
  | ConstArray [ConstVal]
  | ConstRepeat ConstVal Int
  | ConstInitializer DefId Substs
  deriving (Show,Eq, Ord, Generic)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure DefId Substs
      deriving (Show,Eq, Ord, Generic)

data CustomAggregate =
    CARange Ty Operand Operand -- deprecated but here in case something else needs to go here
    deriving (Show,Eq, Ord, Generic)

data Trait = Trait { _traitName       :: !DefId,
                     _traitItems      :: ![TraitItem],
                     _traitSupers     :: ![TraitName],
                     _traitParams     :: ![Param],
                     _traitPredicates :: ![Predicate],
                     _traitAssocTys   :: ![AssocTy]    -- new params added in a pre-pass
                   } 
    deriving (Eq, Ord, Show, Generic)


data TraitItem
    = TraitMethod DefId FnSig 
    | TraitType DefId         -- associated type
    | TraitConst DefId Ty
    deriving (Eq, Ord, Show, Generic)

data TraitRef
    = TraitRef DefId Substs 
      -- Indicates the trait this impl implements.
      -- The two `substs` gives the type arguments for the trait
      -- both the initial arguments, plus any extra after the
      -- associated types translation
    deriving (Show, Eq, Ord, Generic)

data TraitImpl
    = TraitImpl { _tiName       :: DefId
                -- name of the impl group 
                , _tiTraitRef   :: TraitRef
                -- name of the trait and the type we are implementing it
                , _tiPreTraitRef :: TraitRef
                -- pre-AT translation trait ref
                , _tiGenerics   :: [Param]
                , _tiPredicates :: [Predicate]
                , _tiItems      :: [TraitImplItem]
                , _tiAssocTys   :: [AssocTy]
                }
    deriving (Show, Eq, Ord, Generic)
data TraitImplItem
    = TraitImplMethod { _tiiName :: DefId
                        -- the def path of the item
                        -- should match the name of the corresponding entry in 'fns'
                      , _tiiImplements :: DefId
                        -- The def path of the trait-item that this impl-item implements.
                        -- If there is no impl-item that `implements` a particular
                        -- trait-item, that means the impl uses the default from the trait.
                      , _tiiGenerics :: [Param]
                        -- Generics for the method itself.  
                        -- should match the generics of the `fn`.  This consists of the generics
                        -- inherited from the impl (if any), followed by any generics
                        -- declared on the impl-item itself.
                      , _tiiPredicates :: [Predicate]
                      , _tiiSignature  :: FnSig
                      }
      | TraitImplType { _tiiName       :: DefId
                      , _tiiImplements :: DefId
                      , _tiiGenerics   :: [Param]
                      , _tiiPredicates :: [Predicate]
                      , _tiiType       :: Ty
                      }
      deriving (Show, Eq, Ord, Generic)

newtype Promoted = Promoted Int
  deriving (Show, Eq, Ord, Generic)

data Static   = Static {
    _sName          :: DefId            -- ^ name of fn that initializes this static
  , _sTy            :: Ty
  , _sMutable       :: Bool             -- ^ true for "static mut"          
  , _sPromotedFrom  :: Maybe DefId      -- ^ name of fn that static was promoted from
  , _sPromoted      :: Maybe Promoted
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
type ClosureSubsts = Text
type BasicBlockInfo = Text


--------------------------------------------------------------------------------------
-- Lenses
--------------------------------------------------------------------------------------


makeLenses ''Variant
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

makeLenses ''TraitImpl
makeLenses ''TraitImplItem

itemName :: Simple Lens TraitItem DefId
itemName = lens (\ti -> case ti of
                          TraitMethod did _  -> did
                          TraitType did -> did
                          TraitConst did _ -> did)
              (\ti nd -> case ti of
                  TraitMethod _ s  -> TraitMethod nd s 
                  TraitType _ -> TraitType nd
                  TraitConst _ t -> TraitConst nd t)

--------------------------------------------------------------------------------------
-- Other instances for ADT types
--------------------------------------------------------------------------------------

instance Semigroup Collection where
  (Collection f1 a1 t1 i1 s1 v1 n1 r1) <> (Collection f2 a2 t2 i2 s2 v2 n2 r2) =
    Collection (f1 <> f2) (a1 <> a2) (t1 <> t2) (i1 <> i2) (s1 <> s2) (v1 <> v2) (n1 <> n2) (r1 <> r2)
instance Monoid Collection where
  mempty  = Collection mempty mempty mempty mempty mempty mempty mempty mempty
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



-- | Access *all* of the params of the trait
--traitParamsWithAssocTys :: Trait -> [Param]
--traitParamsWithAssocTys trait =
--   trait^.traitParams ++ map toParam (trait^.traitAssocTys)



varOfLvalue :: HasCallStack => Lvalue -> Var
varOfLvalue (LBase (Local v)) = v
varOfLvalue l = error $ "bad var of lvalue: " ++ show l


lValueofOp :: HasCallStack => Operand -> Lvalue
lValueofOp (Copy lv) = lv
lValueofOp (Move lv) = lv
lValueofOp l = error $ "bad lvalue of op: " ++ show l

funcNameofOp :: HasCallStack => Operand -> DefId
funcNameofOp (OpConstant (Constant _ (Value (ConstFunction id1 _substs)))) = id1
funcNameofOp _ = error "bad extract func name"

funcSubstsofOp :: HasCallStack => Operand -> Substs
funcSubstsofOp (OpConstant (Constant _ (Value (ConstFunction _id1 substs)))) = substs
funcSubstsofOp _ = error "bad extract func name"


-- Get the only variant of a struct or union ADT.
onlyVariant :: Adt -> Variant
onlyVariant (Adt _ _ [v]) = v
onlyVariant (Adt name kind _) = error $
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
    typeOf (Var _ _ t _ _ _) = t

instance TypeOf Lvalue where
    typeOf (LBase base) = typeOf base
    typeOf (LProj l elm) = typeOfProj elm $ typeOf l

instance TypeOf PlaceBase where
    typeOf pb = case pb of
        Local (Var _ _ t _ _ _) -> t
        PStatic _ t -> t
        PPromoted _ t -> t

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
  typeOf (Ref Unique _lv _)  = error "FIXME? type of Unique reference?"
  typeOf (Len _) = TyUint USize
  typeOf (Cast _ _ ty) = ty
  typeOf (NullaryOp _op ty) = ty
  typeOf (RAdtAg (AdtAg _ _ _ ty)) = ty
  typeOf rv = error ("typeOf Rvalue unimplemented: " ++ show rv)

instance TypeOf Operand where
    typeOf (Move lv) = typeOf lv
    typeOf (Copy lv) = typeOf lv
    typeOf (OpConstant c) = typeOf c

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


