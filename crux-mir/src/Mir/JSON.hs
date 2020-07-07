{- |
Module           : Mir.JSON
Description      : JSON to Mir AST parser
License          : BSD3
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mir.JSON where

import Data.Aeson
import qualified Data.Aeson.Types  as Aeson
import qualified Data.HashMap.Lazy as HML
import qualified Data.Map.Strict   as Map
import qualified Data.Scientific   as Scientific

import Data.Word (Word64, Word8)
import Data.Bits
import qualified Data.ByteString as BS
import qualified Data.Char as Char
import Data.Text (Text,  unpack)
import qualified Data.Text as T
import qualified Data.Text.Read  as T
import Data.List
import qualified Data.Vector as V
import Control.Lens((^.),(&),(.~))

import Mir.DefId 
import Mir.Mir

import Debug.Trace

--------------------------------------------------------------------------------------
-- | FromJSON instances

-- Aeson is used for JSON deserialization


instance FromJSON BaseSize where
    parseJSON = withObject "BaseSize" $
                \t -> case HML.lookup "kind" t of
                        Just (String "Usize") -> pure USize
                        Just (String "U8") -> pure B8
                        Just (String "U16") -> pure B16
                        Just (String "U32") -> pure B32
                        Just (String "U64") -> pure B64
                        Just (String "U128") -> pure B128
                        Just (String "Isize") -> pure USize
                        Just (String "I8") -> pure B8
                        Just (String "I16") -> pure B16
                        Just (String "I32") -> pure B32
                        Just (String "I64") -> pure B64
                        Just (String "I128") -> pure B128
                        sz -> fail $ "unknown base size: " ++ show sz

instance FromJSON FloatKind where
    parseJSON = withObject "FloatKind" $ \t -> case HML.lookup "kind" t of
                                                 Just (String "F32") -> pure F32
                                                 Just (String "F64") -> pure F64
                                                 sz -> fail $ "unknown float type: " ++ show sz

instance FromJSON Substs where
    parseJSON v = do
      ml <- parseJSONList v
      case sequence ml of
        Just l  -> pure $ Substs l
        Nothing -> fail "invalid type argument found in substs"

instance FromJSON Ty where
    parseJSON = withText "Ty" $ \v -> case v of
        "nonty::Lifetime" -> pure TyLifetime
        "nonty::Const" -> pure TyConst
        _ -> pure $ TyInterned v

newtype InlineTy = InlineTy { getInlineTy :: Ty }

instance FromJSON InlineTy where
    parseJSON = withObject "InlineTy" $ \v -> InlineTy <$> case HML.lookup "kind" v of
      Just (String "Bool") -> pure TyBool
      Just (String "Char") -> pure TyChar
      Just (String "Int") -> TyInt <$> v .: "intkind"
      Just (String "Uint") -> TyUint <$> v .: "uintkind"
      Just (String "Tuple") -> TyTuple <$> v .: "tys"
      Just (String "Slice") -> TySlice <$> v .: "ty"
      Just (String "Array") -> do
        lit <- v .: "size"
        case lit of
          Constant _ (ConstInt (Usize i)) ->
             TyArray <$> v .: "ty" <*> pure (fromInteger i)
          _ -> fail $ "unsupported array size: " ++ show lit
      Just (String "Ref") ->  TyRef <$> v .: "ty" <*> v .: "mutability"
      Just (String "FnDef") -> TyFnDef <$> v .: "defid"
      Just (String "Adt") -> TyAdt <$> v .: "name" <*> v .: "orig_def_id" <*> v .: "substs"
      Just (String "Closure") -> TyClosure <$> v .: "upvar_tys"
      Just (String "Str") -> pure TyStr
      Just (String "FnPtr") -> TyFnPtr <$> v .: "signature"
      Just (String "Dynamic") -> TyDynamic <$> v .: "trait_id"
      Just (String "RawPtr") -> TyRawPtr <$> v .: "ty" <*> v .: "mutability"
      Just (String "Float") -> TyFloat <$> v .: "size"
      Just (String "Never") -> pure TyNever
      Just (String "Foreign") -> pure TyForeign
      r -> fail $ "unsupported ty: " ++ show r

instance FromJSON NamedTy where
    parseJSON = withObject "NamedTy" $ \v ->
        NamedTy <$> v .: "name" <*> (getInlineTy <$> v .: "ty")

instance FromJSON Instance where
    parseJSON = withObject "Instance" $ \v -> case HML.lookup "kind" v of
        Just (String "Item") -> Instance IkItem
            <$> v .: "def_id" <*> v .: "substs"
        Just (String "Intrinsic") -> Instance IkIntrinsic
            <$> v .: "def_id" <*> v .: "substs"
        Just (String "VtableShim") -> Instance IkVtableShim
            <$> v .: "def_id" <*> v .: "substs"
        Just (String "ReifyShim") -> Instance IkReifyShim
            <$> v .: "def_id" <*> v .: "substs"
        Just (String "FnPtrShim") -> Instance
            <$> (IkFnPtrShim <$> v .: "ty") <*> v .: "def_id" <*> v .: "substs"
        Just (String "Virtual") -> Instance
            <$> (IkVirtual <$> v .: "trait_id" <*> v .: "index") <*> v .: "item_id" <*> pure mempty
        Just (String "ClosureOnceShim") -> Instance IkClosureOnceShim
            <$> v .: "call_once" <*> v .: "substs"
        Just (String "DropGlue") -> Instance
            <$> (IkDropGlue <$> v .: "ty") <*> v .: "def_id" <*> v .: "substs"
        Just (String "CloneShim") -> Instance
            <$> (IkCloneShim <$> v .: "ty" <*> v .: "callees") <*> v .: "def_id" <*> v .: "substs"

instance FromJSON FnSig where
    parseJSON =
      withObject "FnSig" $ \v -> do
         let spread = return Nothing
         FnSig <$> v .: "inputs"
               <*> v .: "output"
               <*> v .: "abi"
               <*> spread
               
instance FromJSON Adt where
    parseJSON = withObject "Adt" $ \v -> Adt
        <$> v .: "name"
        <*> v .: "kind"
        <*> v .: "variants"
        <*> v .: "orig_def_id"
        <*> v .: "orig_substs"

instance FromJSON AdtKind where
    parseJSON x = case x of
        String "Struct" -> pure Struct
        String "Enum" -> pure Enum
        String "Union" -> pure Union
        _ -> fail $ "unsupported adt kind " ++ show x

instance FromJSON VariantDiscr where
    parseJSON = withObject "VariantDiscr" $ \v -> case HML.lookup "kind" v of
                                                    Just (String "Explicit") -> Explicit <$> v .: "name"
                                                    Just (String "Relative") -> Relative <$> v .: "index"
                                                    _ -> fail "unspported variant discriminator"

instance FromJSON CtorKind where
    parseJSON = withObject "CtorKind" $ \v -> case HML.lookup "kind" v of
                                                Just (String "Fn") -> pure FnKind
                                                Just (String "Const") -> pure ConstKind
                                                Just (String "Fictive") -> pure FictiveKind
                                                _ -> fail "unspported constructor kind"
instance FromJSON Variant where
    parseJSON = withObject "Variant" $ \v -> Variant <$> v .: "name" <*> v .: "discr" <*> v .: "fields" <*> v .: "ctor_kind"

instance FromJSON Field where
    parseJSON = withObject "Field" $ \v -> Field <$> v .: "name" <*> v .: "ty"

instance FromJSON Mutability where
    parseJSON = withObject "Mutability" $ \v -> case HML.lookup "kind" v of
                                                Just (String "MutMutable") -> pure Mut
                                                Just (String "Mut") -> pure Mut
                                                Just (String "MutImmutable") -> pure Immut
                                                Just (String "Not") -> pure Immut
                                                x -> fail $ "bad mutability: " ++ show x


instance FromJSON Var where
    parseJSON = withObject "Var" $ \v -> Var
        <$>  v .: "name"
        <*>  v .: "mut"
        <*>  v .: "ty"
        <*>  v .: "is_zst"

instance FromJSON Collection where
    parseJSON = withObject "Collection" $ \v -> do
      (fns    :: [Fn])        <- v .: "fns"
      (adts   :: [Adt])       <- v .: "adts"
      (traits :: [Trait])     <- v .: "traits"
      (statics :: [Static]  ) <- v .: "statics"
      (vtables :: [Vtable]  ) <- v .: "vtables"
      (intrinsics :: [Intrinsic]) <- v .: "intrinsics"
      (tys    :: [NamedTy])   <- v .: "tys"
      (roots :: [MethName])   <- v .: "roots"
      return $ Collection
        (foldr (\ x m -> Map.insert (x^.fname) x m)     Map.empty fns)
        (foldr (\ x m -> Map.insert (x^.adtname) x m)   Map.empty adts)
        (foldr (\ x m -> Map.insertWith (++) (x^.adtOrigDefId) [x] m) Map.empty adts)
        (foldr (\ x m -> Map.insert (x^.traitName) x m) Map.empty traits)
        (foldr (\ x m -> Map.insert (x^.sName) x m)     Map.empty statics)
        (foldr (\ x m -> Map.insert (x^.vtName) x m)    Map.empty vtables)
        (foldr (\ x m -> Map.insert (x^.intrName) x m)  Map.empty intrinsics)
        (foldr (\ x m -> Map.insert (x^.ntName) (x^.ntTy) m) Map.empty tys)
        roots


instance FromJSON Fn where
    parseJSON = withObject "Fn" $ \v -> do
      args <- v .: "args"
      let sig = FnSig <$> return (map typeOf args)
                      <*> v .: "return_ty"
                      <*> v .: "abi"
                      <*> v .: "spread_arg"

      Fn
        <$> v .: "name"
        <*> return args
        <*> sig        
        <*> v .: "body"

instance FromJSON Abi where
    parseJSON = withObject "Abi" $ \v -> case HML.lookup "kind" v of
        Just (String "Rust") -> pure RustAbi
        Just (String "RustIntrinsic") -> pure RustIntrinsic
        Just (String "RustCall") -> pure RustCall
        Just (String _) -> pure OtherAbi
        x -> fail $ "bad abi: " ++ show x
        
instance FromJSON BasicBlock where
    parseJSON = withObject "BasicBlock" $ \v -> BasicBlock
        <$> v .: "blockid"
        <*> v .: "block"

instance FromJSON BasicBlockData where
    parseJSON = withObject "BasicBlockData" $ \v -> BasicBlockData
        <$> v .: "data"
        <*> v .: "terminator"

instance FromJSON Statement where
    parseJSON = withObject "Statement" $ \v -> case HML.lookup "kind" v of
                             Just (String "Assign") ->  Assign <$> v.: "lhs" <*> v .: "rhs" <*> v .: "pos"
                             Just (String "SetDiscriminant") -> SetDiscriminant <$> v .: "lvalue" <*> v .: "variant_index"
                             Just (String "StorageLive") -> StorageLive <$> v .: "slvar"
                             Just (String "StorageDead") -> StorageDead <$> v .: "sdvar"
                             Just (String "Nop") -> pure Nop
                             k -> fail $ "kind not found for statement: " ++ show k


data RustcPlace = RustcPlace Var [PlaceElem]

instance FromJSON RustcPlace where
    parseJSON = withObject "Place" $ \v ->
        RustcPlace <$> v .: "var" <*> v .: "data"

instance FromJSON PlaceElem where
    parseJSON = withObject "PlaceElem" $ \v ->
      case HML.lookup "kind" v of
        Just (String "Deref") -> pure Deref
        Just (String "Field") -> PField <$> v .: "field" <*> v .: "ty"
        Just (String "Index") -> Index <$> v .: "op"
        Just (String "ConstantIndex") -> ConstantIndex <$> v .: "offset" <*> v .: "min_length" <*> v .: "from_end"
        Just (String "Subslice") -> Subslice <$> v .: "from" <*> v .: "to" <*> v .: "from_end"
        Just (String "Downcast") -> Downcast <$> v .: "variant"
        x -> fail ("bad PlaceElem: " ++ show x)

instance FromJSON Lvalue where
    parseJSON j = convert <$> parseJSON j
      where
        convert (RustcPlace base elems) = foldl LProj (LBase base) elems

instance FromJSON Rvalue where
    parseJSON = withObject "Rvalue" $ \v -> case HML.lookup "kind" v of
                                              Just (String "Use") -> Use <$> v .: "usevar"
                                              Just (String "Repeat") -> Repeat <$> v .: "op" <*> v .: "len"
                                              Just (String "Ref") ->  Ref <$> v .: "borrowkind" <*> v .: "refvar" <*> v .: "region"
                                              Just (String "AddressOf") ->  AddressOf <$> v .: "mutbl" <*> v .: "place"
                                              Just (String "Len") -> Len <$> v .: "lv"
                                              Just (String "Cast") -> Cast <$> v .: "type" <*> v .: "op" <*> v .: "ty"
                                              Just (String "BinaryOp") -> BinaryOp <$> v .: "op" <*> v .: "L" <*> v .: "R"
                                              Just (String "CheckedBinaryOp") -> CheckedBinaryOp <$> v .: "op" <*> v .: "L" <*> v .: "R"
                                              Just (String "NullaryOp") -> NullaryOp <$> v .: "op" <*> v .: "ty"
                                              Just (String "UnaryOp") -> UnaryOp <$> v .: "uop" <*> v .: "op"
                                              Just (String "Discriminant") -> Discriminant <$> v .: "val"
                                              Just (String "Aggregate") -> Aggregate <$> v .: "akind" <*> v .: "ops"
                                              k -> fail $ "unsupported RValue " ++ show k

instance FromJSON Terminator where
    parseJSON = withObject "Terminator" $ \v -> case HML.lookup "kind" v of
                                                  Just (String "Goto") -> Goto <$> v .: "target"
                                                  Just (String "SwitchInt") ->
                                                    let  q :: Aeson.Parser [Maybe Integer]
                                                         q = do
                                                               lmt <- v .: "values"
                                                               mapM (mapM convertIntegerText) lmt
                                                    in
                                                    SwitchInt <$> v .: "discr" <*> v .: "switch_ty" <*> q <*> v .: "targets" <*> v .: "pos"
                                                  Just (String "Resume") -> pure Resume
                                                  Just (String "Abort") -> pure Abort
                                                  Just (String "Return") -> pure Return
                                                  Just (String "Unreachable") -> pure Unreachable
                                                  Just (String "Drop") -> Drop <$> v .: "location" <*> v .: "target" <*> v .: "unwind" <*> v .: "drop_fn"
                                                  Just (String "DropAndReplace") -> DropAndReplace <$> v .: "location" <*> v .: "value" <*> v .: "target" <*> v .: "unwind" <*> v .: "drop_fn"
                                                  Just (String "Call") ->  Call <$> v .: "func" <*> v .: "args" <*> v .: "destination" <*> v .: "cleanup"
                                                  Just (String "Assert") -> Assert <$> v .: "cond" <*> v .: "expected" <*> v .: "msg" <*> v .: "target" <*> v .: "cleanup"
                                                  k -> fail $ "unsupported terminator" ++ show k

instance FromJSON Operand where
    parseJSON = withObject "Operand" $ \v -> case HML.lookup "kind" v of
                                               Just (String "Move") -> Move <$> v .: "data"
                                               Just (String "Copy") -> Copy <$> v .: "data"  
                                               Just (String "Constant") -> OpConstant <$> v .: "data"
                                               x -> fail ("base operand: " ++ show x)

instance FromJSON NullOp where
    parseJSON = withObject "NullOp" $ \v -> case HML.lookup "kind" v of
                                             Just (String "SizeOf") -> pure SizeOf
                                             Just (String "Box") -> pure Box
                                             x -> fail ("bad nullOp: " ++ show x)

instance FromJSON BorrowKind where
    parseJSON = withText "BorrowKind" $ \t ->
           if t == "Shared" then pure Shared
      else if t == "Unique" then pure Unique
      else if t == "Mut"    then pure Mutable
      -- s can be followed by "{ allow_two_phase_borrow: true }"
      else if T.isPrefixOf "Mut" t then pure Mutable
      else fail ("bad borrowKind: " ++ show t) 
       


      
instance FromJSON UnOp where
    parseJSON = withObject "UnOp" $ \v -> case HML.lookup "kind" v of
                                             Just (String "Not") -> pure Not
                                             Just (String "Neg") -> pure Neg
                                             x -> fail ("bad unOp: " ++ show x)
instance FromJSON BinOp where
    parseJSON = withObject "BinOp" $ \v -> case HML.lookup "kind" v of
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
                                             x -> fail ("bad binop: " ++ show x)


instance FromJSON VtableItem where
    parseJSON = withObject "VtableItem" $ \v ->
        VtableItem <$> v .: "def_id" <*> (v .: "item_id")

instance FromJSON Vtable where
    parseJSON = withObject "Vtable" $ \v ->
        Vtable <$> v .: "name" <*> v .: "items"

instance FromJSON CastKind where
    parseJSON = withObject "CastKind" $ \v -> case HML.lookup "kind" v of
                                               Just (String "Misc") -> pure Misc
                                               Just (String "Pointer(ReifyFnPointer)") -> pure ReifyFnPointer
                                               Just (String "Pointer(ClosureFnPointer(Normal))") -> pure ClosureFnPointer
                                               Just (String "Pointer(UnsafeFnPointer)") -> pure UnsafeFnPointer
                                               Just (String "Pointer(Unsize)") -> pure Unsize
                                               Just (String "Pointer(MutToConstPointer)") -> pure MutToConstPointer
                                               Just (String "UnsizeVtable") -> UnsizeVtable <$> v .: "vtable"
                                               x -> fail ("bad CastKind: " ++ show x)

instance FromJSON Constant where
    parseJSON = withObject "Literal" $ \v -> do
      ty <- v .: "ty"
      rend <- v .:? "rendered"
      init <- v .:? "initializer"
      case (rend, init) of
        (Just (RustcRenderedConst rend), _) ->
            pure $ Constant ty rend
        (Nothing, Just (RustcConstInitializer defid)) ->
            pure $ Constant ty $ ConstInitializer defid
        (Nothing, Nothing) ->
            fail $ "need either rendered value or initializer in constant literal"


data RustcConstInitializer = RustcConstInitializer DefId

instance FromJSON RustcConstInitializer where
    parseJSON = withObject "Initializer" $ \v ->
        RustcConstInitializer <$> v .: "def_id"

newtype RustcRenderedConst = RustcRenderedConst ConstVal

instance FromJSON RustcRenderedConst where
    parseJSON = withObject "RenderedConst" $ \v ->
      RustcRenderedConst <$> case HML.lookup "kind" v of
        Just (String "isize") -> do
            val <- convertIntegerText =<< v .: "val"
            pure $ ConstInt $ Isize val

        Just (String "int") -> do
            size :: Int <- v .: "size"
            val <- convertIntegerText =<< v .: "val"
            ConstInt <$> case size of
                1 -> pure $ I8 val
                2 -> pure $ I16 val
                4 -> pure $ I32 val
                8 -> pure $ I64 val
                16 -> pure $ I128 val
                _ -> fail $ "bad size " ++ show size ++ " for int literal"

        Just (String "usize") -> do
            val <- convertIntegerText =<< v .: "val"
            pure $ ConstInt $ Usize val

        Just (String "uint") -> do
            size :: Int <- v .: "size"
            val <- convertIntegerText =<< v .: "val"
            ConstInt <$> case size of
                1 -> pure $ U8 val
                2 -> pure $ U16 val
                4 -> pure $ U32 val
                8 -> pure $ U64 val
                16 -> pure $ U128 val
                _ -> fail $ "bad size " ++ show size ++ " for uint literal"

        Just (String "bool") -> do
            val :: String <- v .: "val"
            ConstBool <$> case val of
                "0" -> pure False
                "1" -> pure True
                _ -> fail $ "bad value " ++ show val ++ " for bool literal"

        Just (String "char") -> do
            val <- convertIntegerText =<< v .: "val"
            pure $ ConstChar $ Char.chr (fromInteger val)

        Just (String "float") -> do
            size :: Int <- v .: "size"
            val <- v .: "val"
            fk <- case size of
                4 -> pure F32
                8 -> pure F64
                _ -> fail $ "bad size " ++ show size ++ " for float literal"
            pure $ ConstFloat $ FloatLit fk (T.unpack val)

        Just (String "str") -> do
            val <- v .: "val"
            let f sci = case Scientific.toBoundedInteger sci of
                    Just b -> pure (b :: Word8)
                    Nothing -> fail $ "cannot read " ++ show sci
            bytes <- mapM (withScientific "byte" f) val
            return $ ConstStr $ BS.pack bytes

        Just (String "bstr") -> do
            val <- v .: "val"
            let f sci = case Scientific.toBoundedInteger sci of
                    Just b -> pure (ConstInt $ U8 $ toInteger (b :: Int))
                    Nothing -> fail $ "cannot read " ++ show sci
            bytes <- mapM (withScientific "byte" f) val
            return $ ConstArray $ V.toList bytes

        Just (String "struct") -> do
            fields <- map (\(RustcRenderedConst val) -> val) <$> v .: "fields"
            return $ ConstStruct fields
        Just (String "enum") -> do
            variant <- v .: "variant"
            fields <- map (\(RustcRenderedConst val) -> val) <$> v .: "fields"
            return $ ConstEnum variant fields

        Just (String "fndef") -> ConstFunction <$> v .: "def_id"
        Just (String "static_ref") -> ConstStaticRef <$> v .: "def_id"
        Just (String "zst") -> pure ConstZST
        Just (String "raw_ptr") -> do
            val <- convertIntegerText =<< v .: "val"
            return $ ConstRawPtr val

-- mir-json integers are expressed as strings of 128-bit unsigned values
-- for example, -1 is displayed as "18446744073709551615"
-- we need to parse this as a 128 unsigned bit Int value and then
-- cast it to a signed value
convertIntegerText :: Text -> Aeson.Parser Integer
convertIntegerText t = do
  case (T.signed T.decimal) t of
    Right ((i :: Integer), _) -> return i
    Left _       -> fail $ "Cannot parse Integer value: " ++ T.unpack t


instance FromJSON AggregateKind where
    parseJSON = withObject "AggregateKind" $ \v -> case HML.lookup "kind" v of
                                                     Just (String "Array") -> AKArray <$> v .: "ty"
                                                     Just (String "Tuple") -> pure AKTuple
                                                     Just (String "Closure") -> pure AKClosure
                                                     Just (String unk) -> fail $ "unimp: " ++ unpack unk
                                                     x -> fail ("bad AggregateKind: " ++ show x)

instance FromJSON Trait where
    parseJSON = withObject "Trait" $ \v -> do
      Trait <$> v .: "name"
            <*> v .: "items"

instance FromJSON TraitItem where
    parseJSON = withObject "TraitItem" $ \v ->
                case HML.lookup "kind" v of
                  Just (String "Method") -> do
                    TraitMethod <$> v .: "item_id" <*> v .: "signature"
                  Just (String unk) -> fail $ "unknown trait item type: " ++ unpack unk
                  Just x -> fail $ "Incorrect format of the kind field in TraitItem: " ++ show x
                  k -> fail $ "bad kind field in TraitItem " ++ show k


instance FromJSON Intrinsic where
    parseJSON = withObject "Intrinsic" $ \v ->
        Intrinsic <$> v .: "name" <*> v .: "inst"


instance FromJSON MirBody where
    parseJSON = withObject "MirBody" $ \v -> MirBody
        <$> v .: "vars"
        <*> v .: "blocks"

instance FromJSON Static where
  parseJSON = withObject "Static" $ \v -> do
    Static <$> v .: "name"
           <*> v .: "ty"
           <*> v .: "mutable"

           
--  LocalWords:  initializer supertraits deserialization impls
