{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}


module Mir.Mir where
import Data.Aeson
import qualified Data.HashMap.Lazy as HML 
import qualified Data.ByteString as B
import qualified Text.Regex as Regex
import qualified Data.Map.Strict as Map
import Data.Text (Text, unpack)
import Data.List
import System.IO.Unsafe

-- NOTE: below, all unwinding calls can be ignored 
--
--

class PPrint a where
    pprint :: a -> String

pprint_fn1 :: (PPrint a) => String -> a -> String
pprint_fn1 fn a = fn ++ "(" ++ (pprint a) ++ ");"

pprint_fn2 :: (PPrint a, PPrint b) => String -> a -> b -> String
pprint_fn2 fn a b = fn ++ "(" ++ (pprint a) ++ ", " ++ (pprint b) ++ ");"

pprint_fn3 :: (PPrint a, PPrint b, PPrint c) => String -> a -> b -> c -> String
pprint_fn3 fn a b c = fn ++ "(" ++ (pprint a) ++ ", " ++ (pprint b) ++ ", " ++ (pprint c) ++ ");"

instance PPrint a => PPrint (Maybe a) where
    pprint (Just a) = pprint a
    pprint Nothing = ""

instance PPrint Text where
    pprint a = unpack a

instance PPrint Int where
    pprint = show

instance PPrint a => PPrint [a] where
    pprint as = "(" ++ pas ++ ")" where
        pas = mconcat $ Data.List.intersperse ", " (Prelude.map pprint as)

instance (PPrint a, PPrint b) => PPrint (a,b) where
    pprint (a,b) = "(" ++ (pprint a) ++ ", " ++ (pprint b) ++ ")"

instance PPrint Bool where
    pprint = show

data BaseSize =
    USize
      | B8
      | B16
      | B32
      | B64
      | B128
      deriving (Eq, Show)

instance PPrint BaseSize where
    pprint = show

instance FromJSON BaseSize where
    parseJSON = withText "BaseSize" $ \t -> case t of
                                              "USize" -> pure USize
                                              "8" -> pure B8
                                              "16" -> pure B16
                                              "32" -> pure B32
                                              "64" -> pure B64
                                              "128" -> pure B128

data Ty =
    TyBool
      | TyChar
      | TyInt BaseSize
      | TyUint BaseSize
      | TyTuple [Ty]
      | TySlice Ty
      | TyArray Ty Int
      | TyRef Ty Text -- text is for mutability
      | TyAdt Adt
      | TyUnsupported
      | TyCustom CustomTy
      | TyParam Integer
      | TyFnDef DefId [Maybe Ty]
      | TyClosure DefId [Maybe Ty]
      deriving (Eq, Show)

class TypeOf a where
    typeOf :: a -> Ty

instance PPrint Ty where
    pprint = show

instance FromJSON Ty where
    parseJSON = withObject "Ty" $ \v -> case (HML.lookup "kind" v) of
                                          Just (String "Bool") -> pure TyBool
                                          Just (String "Char") -> pure TyChar
                                          Just (String "Int") -> TyInt <$> v .: "intkind"
                                          Just (String "Uint") -> TyUint <$> v .: "uintkind" 
                                          Just (String "Unsupported") -> pure TyUnsupported
                                          Just (String "Tuple") -> TyTuple <$> v .: "tys"
                                          Just (String "Slice") -> TySlice <$> v .: "ty"
                                          Just (String "Array") -> TyArray <$> v .: "ty" <*> v .: "size"
                                          Just (String "ref") ->  TyRef <$> v .: "ty" <*> v .: "mutability"
                                          Just (String "custom") -> TyCustom <$> v .: "data"
                                          Just (String "fndef") -> TyFnDef <$> v .: "defid" <*> v .: "substs"
                                          Just (String "adt") -> TyAdt <$> v .: "adt"
                                          Just (String "param") -> TyParam <$> v .: "param"
                                          Just (String "closure") -> TyClosure <$> v .: "defid" <*> v .: "closuresubsts"
                                          _ -> error "unsupported ty"


data Adt = Adt {_adtname :: Text, _adtvariants :: [Variant]}
    deriving (Eq, Show)

instance FromJSON Adt where
    parseJSON = withObject "Adt" $ \v -> Adt <$> v .: "name" <*> v .: "variants"

data Variant = Variant {_vname :: Text, _vdiscr :: Int, _vfields :: [Field], _vctorkind :: Text}
    deriving (Eq,Show)

instance FromJSON Variant where
    parseJSON = withObject "Variant" $ \v -> Variant <$> v .: "name" <*> v .: "discr" <*> v .: "fields" <*> v .: "ctor_kind"

data Field = Field {_fName :: Text, _fty :: Ty, _fsubsts :: [Maybe Ty]}
    deriving (Show, Eq)

instance FromJSON Field where
    parseJSON = withObject "Field" $ \v -> Field <$> v .: "name" <*> v .: "ty" <*> v .: "substs"






data CustomTy =
    RangeTy Ty
      | BoxTy Ty
      | VecTy Ty

    deriving (Eq, Show)

instance PPrint CustomTy where
    pprint = show

instance FromJSON CustomTy where
    parseJSON = withObject "CustomTy" $ \v -> case (HML.lookup "kind" v) of
                                                Just (String "Range") -> RangeTy <$> v .: "range_ty"
                                                Just (String "Box") -> BoxTy <$> v .: "box_ty"
                                                Just (String "Vec") -> VecTy <$> v .: "vec_ty"



data Var = Var {
    _varname :: Text,
    _varmut :: Text,
    _varty :: Ty,
    _varscope :: VisibilityScope }
    deriving (Eq, Show)

instance Ord Var where
    compare (Var n _ _ _) (Var m _ _ _) = compare n m

instance TypeOf Var where
    typeOf (Var _ _ t _) = t

instance PPrint Var where
    pprint (Var vn vm vty vs) = j ++ (unpack vn) ++ ": " ++ ( pprint vty)
        where
            j = case vm of
                  "mut" -> "mut "
                  _ -> ""

instance FromJSON Var where
    parseJSON = withObject "Var" $ \v -> Var
        <$>  v .: "name"
        <*> v .: "mut"
        <*>  v .: "ty"
        <*>  v .: "scope"

type Collection = [Fn]

data Fn = Fn {
    _fname :: Text,
    _fargs :: [Var],
    _freturn_ty :: Ty,
    _fbody :: MirBody
    }
    deriving (Show,Eq)

instance PPrint Fn where
    pprint (Fn fname fargs fty fbody) = (pprint fname) ++ "(" ++ pargs ++ ") -> " ++ (pprint fty) ++ " {\n" ++ (pprint fbody) ++ "}\n"
        where
            pargs = mconcat $ Data.List.intersperse "\n" (Prelude.map pprint fargs)

instance FromJSON Fn where
    parseJSON = withObject "Fn" $ \v -> Fn
        <$>  v .: "name"
        <*> v .: "args"
        <*> v .: "return_ty"
        <*> v .: "body"

data MirBody = MirBody {
    _mvars :: [Var],
    _mblocks :: [BasicBlock]
}
    deriving (Show,Eq)

instance PPrint MirBody where
    pprint (MirBody mvs mbs) = pvs ++ "\n" ++ pbs ++ "\n"
        where
            pvs = mconcat $ Data.List.intersperse "\n" (Prelude.map ((\s -> "alloc " ++ s) . pprint) mvs)
            pbs = mconcat $ Data.List.intersperse "\n" (Prelude.map pprint mbs)

instance FromJSON MirBody where
    parseJSON = withObject "MirBody" $ \v -> MirBody
        <$> v .: "vars"
        <*> v .: "blocks"

data BasicBlock = BasicBlock {
    _bbinfo :: BasicBlockInfo,
    _bbdata :: BasicBlockData
}
    deriving (Show,Eq)

instance PPrint BasicBlock where
    pprint (BasicBlock info dat) = (pprint info) ++ " { \n" ++ (pprint dat) ++ "} \n"

instance FromJSON BasicBlock where
    parseJSON = withObject "BasicBlock" $ \v -> BasicBlock
        <$> v .: "blockid"
        <*> v .: "block"

data BasicBlockData = BasicBlockData { 
    _bbstmts :: [Statement],
    _bbterminator :: Terminator
}
    deriving (Show,Eq)

instance PPrint BasicBlockData where
    pprint (BasicBlockData bbds bbt) = pbs ++ "\n" ++ "\t" ++ (pprint bbt) ++ "\n"
        where
            a = (Prelude.map pprint bbds)
            b = (Prelude.map (\v -> "\t" ++ v) a)
            pbs = mconcat $ Data.List.intersperse "\n" b


instance FromJSON BasicBlockData where
    parseJSON = withObject "BasicBlockData" $ \v -> BasicBlockData
        <$> v .: "data"
        <*>  v .: "terminator"

data Statement = 
      Assign { _alhs :: Lvalue, _arhs :: Rvalue}
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _sllv :: Lvalue }
      | StorageDead { _sdlv :: Lvalue }
      | Nop
    deriving (Show,Eq)


instance PPrint Statement where
    pprint (Assign lhs rhs) = (pprint lhs) ++ " = " ++ (pprint rhs) ++ ";"
    pprint (SetDiscriminant lhs rhs) = (pprint lhs) ++ " = " ++ (pprint rhs) ++ ";"
    pprint (StorageLive l) = pprint_fn1 "StorageLive" l
    pprint (StorageDead l) = pprint_fn1 "StorageDead" l
    pprint (Nop) = "nop;"

instance FromJSON Statement where
    parseJSON = withObject "Statement" $ \v -> case (HML.lookup "kind" v) of
                             Just (String "Assign") ->  Assign <$> v.: "lhs" <*> v .: "rhs"
                             Just (String "SetDiscriminant") -> SetDiscriminant <$> v .: "lvalue" <*> v .: "variant_index"
                             Just (String "StorageLive") -> StorageLive <$> v .: "slvar"
                             Just (String "StorageDead") -> StorageDead <$> v .: "sdvar"
                             Just (String "Nop") -> pure Nop
                             _ -> error "kind not found for statement"
instance TypeOf Lvalue where
    typeOf (Tagged lv _) = typeOf lv
    typeOf (Local (Var _ _ t _)) = t
    typeOf Static = error "static"
    typeOf (LProjection (LvalueProjection base (PField _ t))) = t
    typeOf (LProjection (LvalueProjection base Deref)) = peelType $ typeOf base
        where peelType :: Ty -> Ty
              peelType (TyRef t _) = t
              peelType t = t
    typeOf (LProjection (LvalueProjection base (Index ind))) = peelType $ typeOf base
        where peelType :: Ty -> Ty
              peelType (TyArray t _) = t
              peelType (TySlice t) = t
              peelType (TyRef t _) = peelType t
              peelType t = t

    typeOf l = error $ "unimp: " ++ (show l)

data Lvalue =
    Local { _lvar :: Var}
      | Static
      | LProjection LvalueProjection
      | Tagged Lvalue Text -- for internal use during the translation
    deriving (Show, Eq)



instance Ord Lvalue where
    compare l1 l2 = compare (show l1) (show l2)

instance PPrint Lvalue where
    pprint (Local v) = pprint v  
    pprint (Static) = "STATIC"
    pprint (LProjection p) = pprint p
    pprint (Tagged lv t) = (show t) ++ "(" ++ (pprint lv) ++ ")"

instance FromJSON Lvalue where
    parseJSON = withObject "Lvalue" $ \v -> case (HML.lookup "kind" v) of
                                              Just (String "local") ->  Local <$> v .: "localvar"
                                              Just (String "static") -> pure Static
                                              Just (String "projection") ->  LProjection <$> v .: "data"
                                              _ -> error "kind not found"

data Rvalue =
    Use { _uop :: Operand }
      | Repeat { _rop :: Operand, _rlen :: ConstUsize }
      | Ref { _rbk :: BorrowKind, _rvar :: Lvalue, _rregion :: Text }
      | Len { _lenvar :: Lvalue }
      | Cast { _cck :: CastKind, _cop :: Operand, _cty :: Ty }
      | BinaryOp { _bop :: BinOp, _bop1 :: Operand, _bop2 :: Operand }
      | CheckedBinaryOp { _cbop :: BinOp, _cbop1 :: Operand, _cbop2 :: Operand }
      | NullaryOp { _nuop :: NullOp, _nty :: Ty }
      | UnaryOp { _unop :: UnOp, _unoperand :: Operand}
      | Discriminant { _dvar :: Lvalue }
      | Aggregate { _ak :: AggregateKind, _ops :: [Operand] }
      | RAdtAg AdtAg
      | RCustom CustomAggregate
    deriving (Show,Eq)


instance PPrint Rvalue where
    pprint (Use a) = pprint_fn1 "Use" a
    pprint (Repeat a b) = pprint_fn2 "Repeat" a b
    pprint (Ref a b _) = pprint_fn2 "Ref" a b
    pprint (Len a) = pprint_fn1 "Ref" a
    pprint (Cast a b c) = pprint_fn3 "Cast" a b c
    pprint (BinaryOp a b c) = pprint_fn3 "BinaryOp" a b c
    pprint (CheckedBinaryOp a b c) = pprint_fn3 "CheckedBinaryOp" a b c
    pprint (NullaryOp a b) = pprint_fn2 "NullaryOp" a b
    pprint (UnaryOp a b) = pprint_fn2 "UnaryOp" a b
    pprint (Discriminant a) = pprint_fn1 "Discriminant" a
    pprint (Aggregate a b) = pprint_fn2 "Aggregate" a b

instance FromJSON Rvalue where
    parseJSON = withObject "Rvalue" $ \v -> case (HML.lookup "kind" v) of
                                              Just (String "use") -> Use <$> v .: "usevar"
                                              Just (String "repeat") -> Repeat <$> v .: "op" <*> v .: "len"
                                              Just (String "ref") ->  Ref <$> v .: "borrowkind" <*> v .: "refvar" <*> v .: "region"
                                              Just (String "len") -> Len <$> v .: "lv"
                                              Just (String "cast") -> Cast <$> v .: "type" <*> v .: "op" <*> v .: "ty"
                                              Just (String "binaryop") -> BinaryOp <$> v .: "op" <*> v .: "L" <*> v .: "R"
                                              Just (String "checkedbinaryop") -> CheckedBinaryOp <$> v .: "op" <*> v .: "L" <*> v .: "R"
                                              Just (String "nullaryop") -> NullaryOp <$> v .: "op" <*> v .: "ty"
                                              Just (String "unaryop") -> UnaryOp <$> v .: "uop" <*> v .: "op"
                                              Just (String "discriminant") -> Discriminant <$> v .: "val"
                                              Just (String "aggregate") -> Aggregate <$> v .: "akind" <*> v .: "ops"
                                              Just (String "adtag") -> RAdtAg <$> v .: "ag"
                                              Just (String "custom") -> RCustom <$> v .: "data"
                                              _ -> error "err"


data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand]}
    deriving (Show, Eq)

instance FromJSON AdtAg where
    parseJSON = withObject "AdtAg" $ \v -> AdtAg <$> v .: "adt" <*> v .: "variant" <*> v .: "ops"

data Terminator = 
    Goto { _gbb :: BasicBlockInfo}
      | SwitchInt { _sdiscr :: Operand, _switch_ty :: Ty, _svalues :: [Integer], _stargets :: [BasicBlockInfo] }
      | Resume
      | Return
      | Unreachable
      | Drop { _dloc :: Lvalue, _dtarget :: BasicBlockInfo, _dunwind :: Maybe BasicBlockInfo }
      | DropAndReplace { _drloc :: Lvalue, _drval :: Operand, _drtarget :: BasicBlockInfo, _drunwind :: Maybe BasicBlockInfo }
      | Call { _cfunc :: Operand, _cargs :: [Operand], _cdest :: Maybe (Lvalue, BasicBlockInfo), _cleanup :: Maybe BasicBlockInfo } 
    
      | Assert { _acond :: Operand, _aexpected :: Bool, _amsg :: AssertMessage, _atarget :: BasicBlockInfo, _acleanup :: Maybe BasicBlockInfo}
      deriving (Show,Eq)

instance PPrint Terminator where
    pprint (Goto g) = "goto " ++ (pprint g) ++ ";"
    pprint (SwitchInt op ty vs bs) = "switchint " ++ (pprint op) ++ ": " ++ (pprint ty) ++ " " ++ (pprint vs) ++ " -> " ++ (pprint bs)
    pprint (Return) = "return;"
    pprint (Resume) = "resume;"
    pprint (Unreachable) = "unreachable;"
    pprint (Drop l target unwind) = "drop;"
    pprint (DropAndReplace _ _ _ _) = "dropreplace;"
    pprint (Call f args dest cleanup) = "call " ++ (pprint f) ++ (pprint args) ++ " -> " ++ (pprint dest)
    pprint (Assert op expect msg target cleanup) = "assert " ++ (pprint op) ++ " == " ++ (pprint expect) ++ " -> " ++ (pprint target)


instance FromJSON Terminator where
    parseJSON = withObject "Terminator" $ \v -> case (HML.lookup "kind" v) of
                                                  Just (String "goto") -> Goto <$> v .: "target"
                                                  Just (String "switchint") -> SwitchInt <$> v .: "discr" <*> v .: "switch_ty" <*> v .: "values" <*> v .: "targets"
                                                  Just (String "resume") -> pure Resume
                                                  Just (String "return") -> pure Return
                                                  Just (String "unreachable") -> pure Unreachable
                                                  Just (String "drop") -> Drop <$> v .: "location" <*> v .: "target" <*> v .: "unwind"
                                                  Just (String "dropandreplace") -> DropAndReplace <$> v .: "location" <*> v .: "value" <*> v .: "target" <*> v .: "unwind"
                                                  Just (String "call") ->  Call <$> v .: "func" <*> v .: "args" <*> v .: "destination" <*> v .: "cleanup"
                                                  Just (String "assert") -> Assert <$> v .: "cond" <*> v .: "expected" <*> v .: "msg" <*> v .: "target" <*> v .: "cleanup"
                                                  _ -> error "err"


data Operand = 
    Consume Lvalue
      | OpConstant Constant
      deriving (Show, Eq)

lValueofOp :: Operand -> Lvalue
lValueofOp (Consume lv) = lv
lValueofOp l = error $ "bad lvalue of op: " ++ (show l)

funcNameofOp :: Operand -> Text
funcNameofOp (OpConstant (Constant _ (Value (ConstFunction id substs)))) = id
funcNameofOp _ = error $ "bad extract func name"

instance TypeOf Operand where
    typeOf (Consume lv) = typeOf lv
    typeOf (OpConstant c) = typeOf c



instance PPrint Operand where
    pprint (Consume lv) = "Consume(" ++ (pprint lv) ++ ")"
    pprint (OpConstant c) = "Constant(" ++ (pprint c) ++ ")"

instance FromJSON Operand where
    parseJSON = withObject "Operand" $ \v -> case (HML.lookup "kind" v) of
                                               Just (String "consume") -> Consume <$> v .: "data"
                                               Just (String "constant") -> OpConstant <$> v .: "data"

data Constant = Constant { _conty :: Ty, _conliteral :: Literal } deriving (Show, Eq)
instance TypeOf Constant where
    typeOf (Constant a b) = a
instance PPrint Constant where
    pprint (Constant a b) = pprint_fn2 "Constant" a b

instance FromJSON Constant where
    parseJSON = withObject "Constant" $ \v -> Constant <$> v .: "ty" <*> v .: "literal"


data LvalueProjection = LvalueProjection { _lvpbase :: Lvalue, _lvpkind :: Lvpelem }
    deriving (Show,Eq)
instance PPrint LvalueProjection where
    pprint (LvalueProjection lv le) = "Projection(" ++ (pprint lv) ++", " ++  (pprint le) ++ ")"

instance FromJSON LvalueProjection where
    parseJSON = withObject "LvalueProjection" $ \v -> LvalueProjection <$> v .: "base" <*> v .: "data"

data Lvpelem =
    Deref
      | PField Int Ty
      | Index Operand
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int }
      | Downcast Integer
      deriving (Show, Eq)

instance PPrint Lvpelem where
    pprint Deref = "Deref"
    pprint (PField a b) = pprint_fn2 "Field" a b
    pprint (Index a) = pprint_fn1 "Index" a
    pprint (ConstantIndex a b c) = pprint_fn3 "ConstantIndex" a b c
    pprint (Subslice a b) = pprint_fn2 "Subslice" a b
    pprint (Downcast a) = pprint_fn1 "Downcast" a

instance FromJSON Lvpelem where
    parseJSON = withObject "Lvpelem" $ \v -> case (HML.lookup "kind" v) of
                                               Just (String "deref") -> pure Deref
                                               Just (String "field") -> PField <$> v .: "field" <*> v .: "ty"
                                               Just (String "index") -> Index <$> v .: "op"
                                               Just (String "constantindex") -> ConstantIndex <$> v .: "offset" <*> v .: "min_length" <*> v .: "from_end"
                                               Just (String "subslice") -> Subslice <$> v .: "from" <*> v .: "to"
                                               Just (String "downcast") -> Downcast <$> v .: "variant"

data NullOp =
    SizeOf
      | Box
      deriving (Show,Eq)

instance PPrint NullOp where
    pprint = show

instance FromJSON NullOp where
    parseJSON = withObject "NullOp" $ \v -> case (HML.lookup "kind" v) of
                                             Just (String "SizeOf") -> pure SizeOf
                                             Just (String "Box") -> pure Box

data BorrowKind =
    Shared
      | Unique
      | Mut
      deriving (Show,Eq)

instance PPrint BorrowKind where
    pprint = show

instance FromJSON BorrowKind where
    parseJSON = withObject "BorrowKind" $ \v -> case (HML.lookup "kind" v) of
                                             Just (String "Shared") -> pure Shared
                                             Just (String "Unique") -> pure Unique
                                             Just (String "Mut") -> pure Mut
data UnOp =
    Not
      | Neg
      deriving (Show,Eq)

instance PPrint UnOp where
    pprint = show

instance FromJSON UnOp where
    parseJSON = withObject "UnOp" $ \v -> case (HML.lookup "kind" v) of
                                             Just (String "Not") -> pure Not
                                             Just (String "Neg") -> pure Neg

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
      deriving (Show,Eq)

instance PPrint BinOp where
    pprint = show

instance FromJSON BinOp where
    parseJSON = withObject "BinOp" $ \v -> case (HML.lookup "kind" v) of
                                             Just (String "Add") -> pure Add
                                             Just (String "Sub") -> pure Sub
                                             Just (String "Mul") -> pure Mul
                                             Just (String "Div") -> pure Div
                                             Just (String "Rem") -> pure Rem
                                             Just (String "BitXor") -> pure BitXor
                                             Just (String "BitAnd") -> pure BitAnd
                                             Just (String "BitOr") -> pure BitOr
                                             Just (String "Shl") -> pure Shl
                                             Just (String "Shr") -> pure Shr
                                             Just (String "Eq") -> pure Beq
                                             Just (String "Lt") -> pure Lt
                                             Just (String "Le") -> pure Le
                                             Just (String "Ne") -> pure Ne
                                             Just (String "Ge") -> pure Ge
                                             Just (String "Gt") -> pure Gt
                                             Just (String "Offset") -> pure Offset

data CastKind =
    Misc
      | ReifyFnPointer
      | ClosureFnPointer
      | UnsafeFnPointer
      | Unsize
      deriving (Show,Eq)

instance PPrint CastKind where
    pprint = show

instance FromJSON CastKind where
    parseJSON = withObject "CastKind" $ \v -> case (HML.lookup "kind" v) of
                                               Just (String "Misc") -> pure Misc
                                               Just (String "ReifyFnPointer") -> pure ReifyFnPointer
                                               Just (String "ClosureFnPointer") -> pure ClosureFnPointer
                                               Just (String "UnsafeFnPointer") -> pure UnsafeFnPointer
                                               Just (String "Unsize") -> pure Unsize
                                     
data Literal =
    Item DefId [Maybe Ty]
      | Value ConstVal
      | LPromoted Promoted
      deriving (Show,Eq)

instance PPrint Literal where
    pprint (Item a b) = pprint_fn2 "Item" a b
    pprint (Value a) = pprint_fn1 "Value" a
    pprint (LPromoted a) = pprint a

instance FromJSON Literal where
    parseJSON = withObject "Literal" $ \v -> case (HML.lookup "kind" v) of
                                               Just (String "item") -> Item <$> v .: "def_id" <*> v .: "substs" 
                                               Just (String "value") -> Value <$> v .: "value"
                                               Just (String "promoted") -> LPromoted <$> v .: "index"



data ConstVal =
    ConstFloat Float
      | ConstInt Integer
      | ConstStr String
      | ConstByteStr B.ByteString
      | ConstBool Bool
      | ConstChar Char
      | ConstVariant DefId
      | ConstFunction DefId [Maybe Ty]
      | ConstStruct
      | ConstTuple [ConstVal]
      | ConstArray [ConstVal]
      | ConstRepeat ConstVal Int
    deriving (Show,Eq)

instance PPrint ConstVal where
    pprint (ConstFloat i) = show i
    pprint (ConstInt i) = show i
    pprint (ConstStr i) = show i
    pprint (ConstByteStr i) = show i
    pprint (ConstBool i) = show i
    pprint (ConstChar i) = show i
    pprint (ConstVariant i) = pprint i
    pprint (ConstTuple cs) = "("++pcs++")" where
        pcs = mconcat $ Data.List.intersperse ", " (Prelude.map pprint cs)
    pprint (ConstArray cs) = "["++pcs++"]" where
        pcs = mconcat $ Data.List.intersperse ", " (Prelude.map pprint cs)
    pprint (ConstRepeat cv i) = "["++(pprint cv)++"; " ++ (show i) ++ "]"
    pprint (ConstFunction a b) = show a

instance FromJSON ConstVal where
    parseJSON = withObject "ConstVal" $ \v -> case (HML.lookup "kind" v) of
                                                Just (String "int") -> ConstInt <$> v .: "data"
                                                Just (String "bool") -> ConstBool <$> v .: "data"
                                                Just (String "tuple") -> ConstTuple <$> v .: "data"
                                                Just (String "function") -> ConstFunction <$> v .: "fname" <*> v .: "substs"
                                                Just (String "array") -> ConstArray <$> v .: "data:"
                                                _ -> error "rest of const unimp"

data AggregateKind =
    AKArray Ty
      | AKTuple
      | AKClosure DefId [Maybe Ty]
      deriving (Show,Eq)

instance PPrint AggregateKind where
    pprint (AKArray t) = "[" ++ (pprint t) ++ "]"
    pprint (AKTuple) = "tup"
    pprint f = show f

instance FromJSON AggregateKind where
    parseJSON = withObject "AggregateKind" $ \v -> case (HML.lookup "kind" v) of
                                                     Just (String "array") -> AKArray <$> v .: "ty"
                                                     Just (String "tuple") -> pure AKTuple
                                                     Just (String "agclosure") -> AKClosure <$> v .: "defid" <*> v .: "closuresubsts"
                                                     Just (String unk) -> error $ "unimp: " ++ (unpack unk)

data CustomAggregate = 
    CARange Ty Operand Operand
    deriving (Show,Eq)

instance PPrint CustomAggregate where
    pprint = show

instance FromJSON CustomAggregate where
    parseJSON = withObject "CustomAggregate" $ \v -> case (HML.lookup "kind" v) of
                                                       Just (String "range") -> CARange <$> v .: "range_ty" <*> v .: "f1" <*> v .: "f2"

instance PPrint Integer where
    pprint = show

type DefId = Text
type Promoted = Text
type ConstUsize = Integer
type VisibilityScope = Text
type AssertMessage = Text
type ClosureSubsts = Text
type BasicBlockInfo = Text

--- aux functions ---
--

data ArithType = Signed | Unsigned

class ArithTyped a where
    arithType :: a -> Maybe ArithType

instance ArithTyped Ty where
    arithType (TyInt _) = Just Signed
    arithType (TyUint _) = Just Unsigned
    arithType _ = Nothing

instance ArithTyped Var where
    arithType (Var _ _ ty _) = arithType ty

instance ArithTyped Lvalue where
    arithType (Local var) = arithType var
    arithType Static = Nothing
    arithType (LProjection (LvalueProjection a (PField f ty))) = arithType ty 
    arithType _ = error "unimpl arithtype"

instance ArithTyped Operand where
    arithType (Consume lv) = arithType lv
    arithType (OpConstant (Constant ty _)) = arithType ty

----

class Replace v a where
    replace :: v -> v -> a -> a

instance (Replace v [Var], Replace v MirBody) => Replace v Fn where
    replace old new (Fn fname args fretty fbody) = Fn fname (replace old new args) fretty (replace old new fbody)

instance (Replace v [Var], Replace v [BasicBlock]) => Replace v MirBody where
    replace old new (MirBody a blocks) = MirBody a $ replace old new blocks

instance Replace v a => Replace v (Map.Map b a) where
    replace old new am = Map.map (replace old new) am

instance Replace v a => Replace v [a] where
    replace old new as = Data.List.map (replace old new) as

instance (Replace v BasicBlockData) => Replace v BasicBlock where
    replace old new (BasicBlock bbi bbd) = BasicBlock bbi $ replace old new bbd

instance (Replace v [Statement], Replace v Terminator) => Replace v BasicBlockData where
    replace old new (BasicBlockData stmts term) = BasicBlockData (replace old new stmts) (replace old new term)

instance (Replace v Operand, Replace v Lvalue) => Replace v Terminator where
    replace old new (SwitchInt op ty vals targs) = SwitchInt (replace old new op) ty vals targs
    replace old new (Drop loc targ un) = Drop (replace old new loc) targ un
    replace old new (DropAndReplace loc val targ un) = DropAndReplace (replace old new loc) (replace old new val) targ un
    replace old new (Call f args (Just (d1, d2)) cl) 
      = Call (replace old new f) (replace old new args) (Just ((replace old new d1), d2)) cl
    replace old new (Assert cond exp m t cl) = Assert (replace old new cond) exp m t cl
    replace old new t = t



instance (Replace v Lvalue, Replace v Rvalue) => Replace v Statement where
    replace old new (Assign lv rv) = Assign (replace old new lv) (replace old new rv) 
    replace old new (SetDiscriminant lv i) = SetDiscriminant (replace old new lv) i
    replace old new (StorageLive l) = StorageLive (replace old new l)
    replace old new (StorageDead l) = StorageDead (replace old new l)
    replace old new Nop = Nop

instance Replace Var Var where
    replace old new v = if _varname v == _varname old then new else v

instance Replace Lvalue Var where
    replace (Local old) (Local new) v = replace old new v
    replace _ _ v = v

instance Replace Var Lvalue where
    replace old new (Tagged lv t) = Tagged (replace old new lv) t
    replace old new (Local v) = Local $ replace old new v
    replace old new Static = Static
    replace old new (LProjection (LvalueProjection lbase lkind)) = LProjection $ LvalueProjection (replace old new lbase) lkind

instance Replace Lvalue Lvalue where
    replace old new v = 
        case repl_lv old new v of
          Just c -> c
          _ -> v

instance (Replace v Lvalue) => Replace v Operand where
    replace old new (Consume lv) = Consume (replace old new lv)
    replace old new o = o

instance (Replace v Operand, Replace v Lvalue, Replace v Var) => Replace v Rvalue where
    replace old new (Use o) = Use (replace old new o)
    replace old new (Repeat a b) = Repeat (replace old new a) b
    replace old new (Ref a b c) = Ref a (replace old new b) c
    replace old new (Len a) = Len (replace old new a)
    replace old new (Cast a b c) = Cast a (replace old new b) c
    replace old new (BinaryOp a b c) = BinaryOp a (replace old new b) (replace old new c)
    replace old new (CheckedBinaryOp a b c) = CheckedBinaryOp a (replace old new b) (replace old new c)
    replace old new (Discriminant v) = Discriminant (replace old new v)
    replace old new (Aggregate a bs) = Aggregate a (replace old new bs)
    replace old new (RCustom (CARange ty o1 o2)) = RCustom (CARange ty (replace old new o1) (replace old new o2))
    replace old new (UnaryOp a b) = UnaryOp a b
    replace old new t = error $ "bad replacevar: " ++ (show t)


instance PPrint (Map.Map Lvalue Lvalue) where
    pprint m = unwords $ Data.List.map (\(k,v) -> (pprint k) ++ " => " ++ (pprint v) ++ "\n") p
        where p = Map.toList m

replaceList :: (Replace v a) => [(v, v)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replace old new a


replaceVar :: (Replace Var a) => Var -> Var -> a -> a
replaceVar old new a = replace old new a

replaceLvalue :: (Replace Lvalue a) => Lvalue -> Lvalue -> a -> a
replaceLvalue old new a = replace old new a

repl_lv :: Lvalue -> Lvalue -> Lvalue -> Maybe Lvalue -- some light unification
repl_lv old new v = 
    case v of
      LProjection (LvalueProjection lb k) | Just ans <- repl_lv old new lb -> Just $ LProjection (LvalueProjection ans k)
      Tagged lb _ | Just ans <- repl_lv old new lb -> Just ans
      _ | v == old -> Just new
      _ -> Nothing

--- Custom stuff
--

isCustomFunc :: Text -> Maybe Text
isCustomFunc fname 
  | Just _ <- Regex.matchRegex (Regex.mkRegex "::boxed\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::new\\[[0-9]+\\]") (unpack fname)
    = Just "boxnew"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::slice\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::into_vec\\[[0-9]+\\]") (unpack fname)
    = Just "slice_tovec"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::vec\\[[0-9]+\\]::\\{\\{impl\\}\\}\\[[0-9]+\\]::as_mut_slice\\[[0-9]+\\]") (unpack fname)
    = Just "vec_asmutslice"
        
  | Just _ <- Regex.matchRegex (Regex.mkRegex "::ops\\[[0-9]+\\]::index\\[[0-9]+\\]::Index\\[[0-9]+\\]::index\\[[0-9]+\\]") (unpack fname)
    = Just "index"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::vec\\[[0-9]+\\]::from_elem\\[[0-9]+\\]") (unpack fname)
    = Just "vec_fromelem"

  | Just _ <- Regex.matchRegex (Regex.mkRegex "::ops\\[[0-9]+\\]::function\\[[0-9]+\\]::Fn\\[[0-9]+\\]::call\\[[0-9]+\\]") (unpack fname)
    = Just "call"

  -- TODO into_iter
  --    vec -> (vec, 0)
  -- TODO into_vec
  --    (vec, 0) -> vec
  -- TODO Iterator::map
  --    ((vec,0), closure) -> (closure of vec, 0)
  -- TODO Iterator::collect
  --    (vec, 0) -> vec
  -- TODO Fn::Call
  --    

  | otherwise = Nothing
