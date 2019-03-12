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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

{-# LANGUAGE OverloadedStrings #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-unticked-promoted-constructors #-}

module Mir.Mir where

import qualified Data.ByteString as B
import qualified Data.Map.Strict as Map
import           Data.Text (Text)
import Control.Lens(makeLenses)
import Data.Maybe (fromMaybe)


import GHC.Generics 
import GHC.Stack

import Mir.DefId

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
      deriving (Eq, Ord, Show, Generic, GenericOps)

data FloatKind
  = F32
  | F64
  deriving (Eq, Ord, Show, Generic, GenericOps)

-- | Type parameters
newtype Substs = Substs [Ty]
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (GenericOps)
  deriving newtype (Semigroup, Monoid)

data Ty =
        TyBool               -- The primitive boolean type. Written as bool.
      | TyChar
      | TyInt BaseSize
      | TyUint BaseSize
      | TyTuple [Ty]         -- A tuple type. For example, (i32, bool)
      | TySlice Ty
      | TyArray Ty Int
      | TyRef Ty Mutability  -- Written &'a mut T or &'a T
      | TyAdt DefId Substs 
      | TyUnsupported
      | TyCustom CustomTy
      | TyParam Integer
      | TyFnDef DefId Substs
      | TyClosure DefId Substs
      | TyStr
      | TyFnPtr FnSig             -- written as fn() -> i32
      | TyDynamic DefId
      | TyRawPtr Ty Mutability    -- Written as *mut T or *const T
      | TyFloat FloatKind
      | TyDowncast Ty Integer     -- result type of downcasting an ADT. Ty must be an ADT type
      | TyProjection DefId Substs -- The projection of an associated type. For example, <T as Trait<..>>::N.
      | TyLifetime
      deriving (Eq, Ord, Show, Generic)

data FnSig = FnSig [Ty] Ty 
    deriving (Eq, Ord, Show, Generic, GenericOps)

data Adt = Adt {_adtname :: DefId, _adtvariants :: [Variant]}
    deriving (Eq, Ord, Show, Generic, GenericOps)

data VariantDiscr
  = Explicit DefId
  | Relative Int
  deriving (Eq, Ord, Show, Generic, GenericOps)


data CtorKind
  = FnKind
  | ConstKind
  | FictiveKind
  deriving (Eq, Ord, Show, Generic, GenericOps)


data Variant = Variant {_vname :: DefId, _vdiscr :: VariantDiscr, _vfields :: [Field], _vctorkind :: CtorKind}
    deriving (Eq, Ord,Show, Generic, GenericOps)


data Field = Field {_fName :: DefId, _fty :: Ty, _fsubsts :: Substs}
    deriving (Show, Eq, Ord, Generic, GenericOps)


data CustomTy =
        BoxTy Ty
      | VecTy Ty                 -- ::vec::Vec<Ty>
      | IterTy Ty
      | CEnum DefId [Integer]    -- C-style Enumeration, all variants must be trivial
    deriving (Eq, Ord, Show, Generic, GenericOps)

data Mutability
  = Mut
  | Immut
  deriving (Eq, Ord, Show, Generic, GenericOps)

data Var = Var {
    _varname :: Text,
    _varmut :: Mutability,
    _varty :: Ty,
    _varscope :: VisibilityScope,
    _varpos :: Text }
    deriving (Eq, Show, Generic)

instance Ord Var where
    compare (Var n _ _ _ _) (Var m _ _ _ _) = compare n m


data Collection = Collection {
    _functions :: [Fn],
    _adts      :: [Adt],
    _traits    :: [Trait]
} deriving (Show, Eq, Ord, Generic, GenericOps)

data Predicate =
  TraitPredicate {
    _ptrait :: DefId,
    _psubst :: Substs
    }
  | TraitProjection {
    _pitemid :: DefId,
    _psubst  :: Substs,
    _ty      :: Ty
    }
  | UnknownPredicate
    deriving (Show, Eq, Ord, Generic, GenericOps)

data Param = Param {
    _pname :: Text
} deriving (Show, Eq, Ord, Generic, GenericOps)

newtype Params = Params [Param]
   deriving (Show, Eq, Ord, Generic)
   deriving anyclass (GenericOps)

newtype Predicates = Predicates [Predicate]
   deriving (Show, Eq, Ord, Generic)
   deriving anyclass (GenericOps)

data Fn = Fn {
    _fname :: DefId,
    _fargs :: [Var],
    _freturn_ty :: Ty,
    _fbody :: MirBody,
    _fgenerics :: [Param],
    _fpredicates :: [Predicate]
    }
    deriving (Show,Eq, Ord, Generic, GenericOps)



data MirBody = MirBody {
    _mvars :: [Var],
    _mblocks :: [BasicBlock]
}
    deriving (Show,Eq, Ord, Generic, GenericOps)


data BasicBlock = BasicBlock {
    _bbinfo :: BasicBlockInfo,
    _bbdata :: BasicBlockData
}
    deriving (Show,Eq, Ord, Generic, GenericOps)



data BasicBlockData = BasicBlockData {
    _bbstmts :: [Statement],
    _bbterminator :: Terminator
}
    deriving (Show,Eq, Ord, Generic, GenericOps)


data Statement =
      Assign { _alhs :: Lvalue, _arhs :: Rvalue, _apos :: Text }
      -- TODO: the rest of these variants also have positions
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _slv :: Var }
      | StorageDead { _sdv :: Var }
      | Nop
    deriving (Show,Eq, Ord, Generic, GenericOps)

-- This is called 'Place' now
data Lvalue =
      Local { _lvar :: Var}         -- ^ local variable
    | Static                        -- ^ static or static mut variable
    | LProjection LvalueProjection  -- ^ projection out of a place (access a field, deref a pointer, etc)
    | Promoted Promoted Ty          -- ^ Constant code promoted to an injected static
    | Tagged Lvalue Text -- for internal use during the translation
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
    deriving (Show,Eq, Ord, Generic, GenericOps)

data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand], _adtagty :: Ty }
    deriving (Show, Eq, Ord, Generic, GenericOps)


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
      deriving (Show,Eq, Ord, Generic, GenericOps)

data Operand =
        Copy Lvalue
      | Move Lvalue
      | OpConstant Constant
      deriving (Show, Eq, Ord, Generic, GenericOps)

data Constant = Constant { _conty :: Ty, _conliteral :: Literal } deriving (Show, Eq, Ord, Generic, GenericOps)

data LvalueProjection = LvalueProjection { _lvpbase :: Lvalue, _lvpkind :: Lvpelem }
    deriving (Show,Eq, Ord, Generic, GenericOps)

data Lvpelem =
    Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int }
      | Downcast Integer
      deriving (Show, Eq, Ord, Generic, GenericOps)



data NullOp =
        SizeOf
      | Box
      deriving (Show,Eq, Ord, Generic, GenericOps)



data BorrowKind =
        Shared
      | Unique
      | Mutable
      deriving (Show,Eq, Ord, Generic, GenericOps)


data UnOp =
    Not
  | Neg
  deriving (Show,Eq, Ord, Generic, GenericOps)


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
      deriving (Show,Eq, Ord, Generic, GenericOps)

data CastKind =
    Misc
      | ReifyFnPointer
      | ClosureFnPointer
      | UnsafeFnPointer
      | Unsize
      deriving (Show,Eq, Ord, Generic, GenericOps)

data Literal =
    Item DefId Substs
  | Value ConstVal
  | LPromoted Promoted
  deriving (Show,Eq, Ord, Generic, GenericOps)

data IntLit
  = U8 Integer
  | U16 Integer
  | U32 Integer
  | U64 Integer
  | Usize Integer
  | I8 Integer
  | I16 Integer
  | I32 Integer
  | I64 Integer
  | Isize Integer
  deriving (Eq, Ord, Show, Generic, GenericOps)

data FloatLit
  = FloatLit FloatKind String
  deriving (Eq, Ord, Show, Generic, GenericOps)


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
  deriving (Show,Eq, Ord, Generic, GenericOps)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure DefId Substs
      deriving (Show,Eq, Ord, Generic, GenericOps)

data CustomAggregate =
    CARange Ty Operand Operand -- deprecated but here in case something else needs to go here
    deriving (Show,Eq, Ord, Generic, GenericOps)

data Trait = Trait { _traitName   :: DefId,
                     _traitItems  :: [TraitItem],
                     _traitSupers :: [TraitName]
                   } 
    deriving (Eq, Ord, Show, Generic, GenericOps)


data TraitItem
    = TraitMethod DefId FnSig  
    | TraitType DefId         -- associated type
    | TraitConst DefId Ty
    deriving (Eq, Ord, Show, Generic, GenericOps)



-- Documentation for particular use-cases of DefIds
type TraitName = DefId
type MethName  = DefId
type AdtName   = DefId

--- Other texts
type Promoted = Text
type ConstUsize = Integer
type VisibilityScope = Text
type AssertMessage = Text
type ClosureSubsts = Text
type BasicBlockInfo = Text


--------------------------------------------------------------------------------------
--
-- Generic operations
--

-- These operations are defined via GHC.Generics so that they can automatically
-- adapt to changes in the Mir AST.  

class GenericOps a where

  -- | Crawl over the AST and rename the module that defIds live in.
  -- We need this because we are loading our own variant of the standard
  -- library, but all of the definitions there will have the wrong name.
  relocate :: a -> a
  default relocate :: (Generic a, GenericOps' (Rep a)) => a -> a
  relocate x = to (relocate' (from x))

  -- | Find all C-style Adts in the AST and convert them to Custom (CEnum _)
  markCStyle :: ([Adt],Collection) -> a -> a 
  default markCStyle :: (Generic a, GenericOps' (Rep a)) => ([Adt],Collection) -> a -> a
  markCStyle s x = to (markCStyle' s (from x))

  -- | Type variable substitution. Type variables are represented via indices.
  tySubst :: Substs -> a -> a 
  default tySubst :: (Generic a, GenericOps' (Rep a)) => Substs -> a -> a
  tySubst s x = to (tySubst' s (from x))

  -- | Renaming for term variables
  replaceVar :: Var -> Var -> a -> a
  default replaceVar :: (Generic a, GenericOps' (Rep a)) => Var -> Var -> a -> a
  replaceVar o n x = to (replaceVar' o n (from x))

  -- |
  replaceLvalue :: Lvalue -> Lvalue -> a -> a
  default replaceLvalue :: (Generic a, GenericOps' (Rep a)) => Lvalue -> Lvalue -> a -> a
  replaceLvalue o n x = to (replaceLvalue' o n (from x))

  
findAdt :: DefId -> [Adt] -> Maybe Adt
findAdt n (a:as) = if n == _adtname a then Just a else findAdt n as
findAdt _n []    = Nothing

findFn :: DefId -> [Fn] -> Maybe Fn
findFn n (f:fs) = if n == _fname f then Just f else findFn n fs
findFn _n []    = Nothing

fromIntegerLit :: IntLit -> Integer
fromIntegerLit (U8 i) = i
fromIntegerLit (U16 i) = i
fromIntegerLit (U32 i) = i
fromIntegerLit (U64 i) = i
fromIntegerLit (Usize i) = i
fromIntegerLit (I8 i) = i
fromIntegerLit (I16 i) = i
fromIntegerLit (I32 i) = i
fromIntegerLit (I64 i) = i
fromIntegerLit (Isize i) = i


-- | For ADTs that are represented as CEnums, we need to find the actual numbers that we
-- use to represent each of the constructors.
adtIndices :: Adt -> Collection -> [Integer]
adtIndices (Adt _aname vars) col = map go vars where
 go (Variant _vname (Explicit did) _fields _knd) =
    case findFn did (_functions col) of
      Just (Fn _name _args _ret_ty (MirBody _vars blocks) _gens _preds) ->
        case blocks of
          [ BasicBlock _info (BasicBlockData [Assign _lhs (Use (OpConstant (Constant _ty (Value (ConstInt i))))) _loc] _term) ] ->
            fromIntegerLit i
            
          _ -> error "CEnum should only have one basic block"
          
      Nothing -> error "cannot find CEnum value"
 go (Variant _vname (Relative i) _fields _kind) = toInteger i    --- TODO: check this

    
-- special case for DefIds
instance GenericOps DefId where
  relocate     = relocateDefId 
  markCStyle _   = id
  tySubst    _   = id
  replaceVar _ _ = id
  replaceLvalue _ _ = id  

-- special case for Tys
instance GenericOps Ty where

  -- Translate C-style enums to CEnum types
  markCStyle (ads,s) (TyAdt n ps)  | Just adt <- findAdt n ads =
   if ps == Substs [] then
      TyCustom (CEnum n (adtIndices adt s))
   else
      error "Cannot have params to C-style enum!"
  markCStyle s ty = to (markCStyle' s (from ty))

  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | fromInteger i < length substs = substs !! fromInteger i 
     | otherwise    = error $ "Indexing at " ++ show i ++ "  from subst " ++ show substs
  tySubst substs ty = to (tySubst' substs (from ty))

-- special case for Vars
instance GenericOps Var where
  replaceVar old new v = if _varname v == _varname old then new else v

  replaceLvalue (Local old) (Local new) v = replaceVar old new v
  replaceLvalue _ _ v = v

-- special case for LValue
instance GenericOps Lvalue where
    replaceLvalue old new v = fromMaybe v (repl_lv v)
      where
        repl_lv :: Lvalue -> Maybe Lvalue -- some light unification
        repl_lv v0 =
          case v0 of
            LProjection (LvalueProjection lb k)
              | Just ans <- repl_lv lb -> Just $ LProjection (LvalueProjection ans k)
            Tagged lb _ | Just ans <- repl_lv lb -> Just ans
            _ | v == old -> Just new
            _ -> Nothing


class GenericOps' f where
  relocate'   :: f p -> f p
  markCStyle' :: ([Adt],Collection) -> f p -> f p
  tySubst'    :: Substs -> f p -> f p 
  replaceVar' :: Var -> Var -> f p -> f p
  replaceLvalue' :: Lvalue -> Lvalue -> f p -> f p
  
instance GenericOps' V1 where
  relocate' _x      = error "impossible: this is a void type"
  markCStyle' _ _x  = error "impossible: this is a void type"
  tySubst' _ _      = error "impossible: this is a void type"
  replaceVar' _ _ _ = error "impossible: this is a void type"
  replaceLvalue' _ _ _ = error "impossible: this is a void type"

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :+: g) where
  relocate'     (L1 x) = L1 (relocate' x)
  relocate'     (R1 x) = R1 (relocate' x)
  markCStyle' s (L1 x) = L1 (markCStyle' s x)
  markCStyle' s (R1 x) = R1 (markCStyle' s x)
  tySubst'    s (L1 x) = L1 (tySubst' s x)
  tySubst'    s (R1 x) = R1 (tySubst' s x)
  replaceVar' o n (L1 x) = L1 (replaceVar' o n x)
  replaceVar' o n (R1 x) = R1 (replaceVar' o n x)
  replaceLvalue' o n (L1 x) = L1 (replaceLvalue' o n x)
  replaceLvalue' o n (R1 x) = R1 (replaceLvalue' o n x)


instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  relocate'       (x :*: y) = relocate'   x     :*: relocate' y
  markCStyle' s   (x :*: y) = markCStyle'   s x :*: markCStyle' s y
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  replaceVar' o n (x :*: y) = replaceVar' o n x :*: replaceVar' o n y
  replaceLvalue' o n (x :*: y) = replaceLvalue' o n x :*: replaceLvalue' o n y
  

instance (GenericOps c) => GenericOps' (K1 i c) where
  relocate'     (K1 x) = K1 (relocate x)
  markCStyle' s (K1 x) = K1 (markCStyle s x)
  tySubst'    s (K1 x) = K1 (tySubst s x)
  replaceVar' o n (K1 x) = K1 (replaceVar o n x)
  replaceLvalue' o n (K1 x) = K1 (replaceLvalue o n x)  
  
instance (GenericOps' f) => GenericOps' (M1 i t f) where
  relocate'     (M1 x) = M1 (relocate' x)
  markCStyle' s (M1 x) = M1 (markCStyle' s x)
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  replaceVar' o n (M1 x) = M1 (replaceVar' o n x)
  replaceLvalue' o n (M1 x) = M1 (replaceLvalue' o n x)

instance (GenericOps' U1) where
  relocate'      U1 = U1
  markCStyle' _s U1 = U1
  tySubst'    _s U1 = U1
  replaceVar' _ _ U1 = U1
  replaceLvalue' _ _ U1 = U1 

                      
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)
instance GenericOps Int     where
   relocate   = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Integer where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Char    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Bool    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Text    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps B.ByteString where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id   

instance GenericOps b => GenericOps (Map.Map a b) where
   relocate       = Map.map relocate 
   markCStyle s    = Map.map (markCStyle s)
   tySubst s      = Map.map (tySubst s)
   replaceVar o n = Map.map (replaceVar o n)
   replaceLvalue o n = Map.map (replaceLvalue o n)   

replaceList :: GenericOps a => [(Lvalue, Lvalue)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replaceLvalue old new a
    

--------------------------------------------------------------------------------------


makeLenses ''Variant
makeLenses ''Var
makeLenses ''Collection
makeLenses ''Fn
makeLenses ''Trait

instance Semigroup Collection where
  (Collection f1 a1 t1)<> (Collection f2 a2 t2) =
    Collection (f1 ++ f2) (a1 ++ a2) (t1 ++ t2)
instance Monoid Collection where
  mempty = Collection [] [] []
  

--------------------------------------------------------------------------------------
--- aux functions ---
--------------------------------------------------------------------------------------

-- A CStyle ADT is one that is an enumeration of numeric valued options
-- containing no data
isCStyle :: Adt -> Bool
isCStyle (Adt _ variants) = all isConst variants where
    isConst (Variant _ _ [] ConstKind) = True
    isConst _ = False

varOfLvalue :: HasCallStack => Lvalue -> Var
varOfLvalue (Local v) = v
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



isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) || isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = foldl (\acc t -> acc || isMutRefTy t) False ts
isMutRefTy (TyCustom (BoxTy t)) = isMutRefTy t
isMutRefTy _ = False


-- | Does this type contain any type parameters
isPoly :: Ty -> Bool
isPoly (TyParam _) = True
isPoly (TyTuple ts) = any isPoly ts
isPoly (TySlice ty) = isPoly ty
isPoly (TyArray ty _i) = isPoly ty
isPoly (TyRef ty _mut) = isPoly ty
isPoly (TyRawPtr ty _mut) = isPoly ty
isPoly (TyAdt _ (Substs params)) = any isPoly params
isPoly (TyFnDef _ (Substs params)) = any isPoly params
isPoly (TyClosure _ (Substs params)) = any isPoly params
isPoly (TyCustom (BoxTy ty)) = isPoly ty
isPoly (TyCustom (VecTy ty)) = isPoly ty
isPoly (TyCustom (IterTy ty)) = isPoly ty
isPoly _x = False           

isNever :: Ty -> Bool
isNever (TyAdt defId _) = fst (did_name defId) == "Never"
isNever _ = False


-- | Calculate the number of free variables in a Mir type
numParams :: FnSig -> Integer
numParams (FnSig argtys retty) = maximum (paramBound retty : map paramBound argtys) where
  paramBound :: Ty -> Integer
  paramBound (TyParam x) = x + 1
  paramBound (TyTuple []) = 0
  paramBound (TyTuple tys) = maximum (map paramBound tys)
  paramBound (TySlice ty)  = paramBound ty
  paramBound (TyArray ty _) = paramBound ty
  paramBound (TyRef ty _)   = paramBound ty
  paramBound (TyAdt _ substs) = paramBoundSubsts substs
  paramBound (TyFnDef _ substs) = paramBoundSubsts substs
  paramBound (TyClosure _ substs) = paramBoundSubsts substs
  paramBound (TyFnPtr sig) = numParams sig   --- no top-level generalization???
  paramBound (TyRawPtr ty _) = paramBound ty
  paramBound (TyDowncast ty _) = paramBound ty
  paramBound (TyProjection _ substs) = paramBoundSubsts substs
  paramBound _ = 0

  paramBoundSubsts :: Substs -> Integer
  paramBoundSubsts (Substs []) = 0
  paramBoundSubsts (Substs tys) = maximum (map paramBound tys)


-- | Convert field to type. Perform the corresponding substitution if field is a type param.
fieldToTy :: HasCallStack => Field -> Ty
fieldToTy (Field _ t substs) = tySubst substs t

-- | Replace the subst on the Field 
substField :: Substs -> Field -> Field
substField subst (Field a t _subst)  = Field a t subst


--------------------------------------------------------------------------------------
-- | arithType

data ArithType = Signed | Unsigned

class ArithTyped a where
    arithType :: a -> Maybe ArithType
instance TypeOf a => ArithTyped a where
    arithType a =
      case typeOf a of
        (TyInt _) -> Just Signed
        (TyUint _ ) -> Just Unsigned
        _  -> Nothing

--------------------------------------------------------------------------------------
-- | TypeOf

class TypeOf a where
    typeOf :: a -> Ty

instance TypeOf Ty where
    typeOf ty = ty

instance TypeOf Var where
    typeOf (Var _ _ t _ _) = t

instance TypeOf Lvalue where
  typeOf lv = case lv of
    Static                -> error "typeOf: static"
    Tagged lv' _          -> typeOf lv'
    Local (Var _ _ t _ _) -> t
    LProjection proj      -> typeOf proj
    Promoted _ t          -> t

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

instance TypeOf LvalueProjection where
  typeOf (LvalueProjection base kind) =
    case kind of
      PField _ t      -> t
      Deref           -> peelRef (typeOf base)
      Index{}         -> peelIdx (typeOf base)
      ConstantIndex{} -> peelIdx (typeOf base)
      Downcast i      -> TyDowncast (typeOf base) i   --- TODO: check this
      Subslice{}      -> TySlice (peelIdx (typeOf base))

   where
   peelRef :: Ty -> Ty
   peelRef (TyRef t _) = t
   peelRef t = t

   peelIdx :: Ty -> Ty
   peelIdx (TyArray t _) = t
   peelIdx (TySlice t)   = t
   peelIdx (TyRef t m)   = TyRef (peelIdx t) m
   peelIdx t             = t

  
--------------------------------------------------------------------------------------------
