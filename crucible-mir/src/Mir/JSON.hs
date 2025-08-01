{- |
Module           : Mir.JSON
Description      : JSON to Mir AST parser
License          : BSD3
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Mir.JSON where

import Data.Aeson
import qualified Data.Aeson.Types  as Aeson
import qualified Data.Map.Strict   as Map
import qualified Data.Scientific   as Scientific

import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.Char as Char
import Data.Text (Text,  unpack)
import qualified Data.Text as T
import qualified Data.Text.Read  as T
import qualified Data.Vector as V
import Data.Word (Word64)
import Control.Lens((^.))

#if MIN_VERSION_aeson(2,0,0)
import qualified Data.Aeson.Key as K (Key)
import qualified Data.Aeson.KeyMap as KM
#else
import qualified Data.HashMap.Lazy as HML
#endif

import Mir.DefId
import Mir.Mir

--------------------------------------------------------------------------------------
-- | FromJSON instances

-- Aeson is used for JSON deserialization


instance FromJSON BaseSize where
    parseJSON = withObject "BaseSize" $
                \t -> case lookupKM "kind" t of
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
    parseJSON = withObject "FloatKind" $ \t -> case lookupKM "kind" t of
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
    parseJSON = withObject "InlineTy" $ \v -> InlineTy <$> case lookupKM "kind" v of
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
      Just (String "Adt") -> TyAdt <$> v .: "name" <*> v .: "orig_def_id" <*> v .: "args"
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

instance FromJSON LangItem where
    parseJSON = withObject "LangItem" $ \v ->
        LangItem <$> v .: "orig_def_id" <*> v .: "name"

instance FromJSON Instance where
    parseJSON = withObject "Instance" $ \v -> case lookupKM "kind" v of
        Just (String "Item") -> Instance IkItem
            <$> v .: "def_id" <*> v .: "args"
        Just (String "Intrinsic") -> Instance IkIntrinsic
            <$> v .: "def_id" <*> v .: "args"
        Just (String "VtableShim") -> Instance IkVtableShim
            <$> v .: "def_id" <*> v .: "args"
        Just (String "ReifyShim") -> Instance IkReifyShim
            <$> v .: "def_id" <*> v .: "args"
        Just (String "FnPtrShim") -> Instance
            <$> (IkFnPtrShim <$> v .: "ty") <*> v .: "def_id" <*> v .: "args"
        Just (String "Virtual") -> Instance
            <$> (IkVirtual <$> v .: "trait_id" <*> v .: "index") <*> v .: "item_id" <*> pure mempty
        Just (String "ClosureOnceShim") -> Instance IkClosureOnceShim
            <$> v .: "call_once" <*> v .: "args"
        Just (String "DropGlue") -> Instance
            <$> (IkDropGlue <$> v .: "ty") <*> v .: "def_id" <*> v .: "args"
        Just (String "CloneShim") -> Instance
            <$> (IkCloneShim <$> v .: "ty" <*> v .: "callees") <*> v .: "def_id" <*> v .: "args"
        Just (String "ClosureFnPointerShim") -> Instance IkClosureFnPointerShim
            <$> v .: "call_mut" <*> pure mempty

instance FromJSON FnSig where
    parseJSON =
      withObject "FnSig" $ \v -> do
         FnSig <$> v .: "inputs"
               <*> v .: "output"
               <*> v .: "abi"

instance FromJSON Adt where
    parseJSON = withObject "Adt" $ \v -> Adt
        <$> v .: "name"
        <*> v .: "kind"
        <*> v .: "variants"
        <*> v .: "size"
        <*> v .: "repr_transparent"
        <*> v .: "orig_def_id"
        <*> v .: "orig_args"

instance FromJSON AdtKind where
    parseJSON = withObject "AdtKind" $ \v -> case lookupKM "kind" v of
        Just (String "Struct") -> pure Struct
        Just (String "Enum") -> Enum <$> v .: "discr_ty"
        Just (String "Union") -> pure Union
        mbKind -> fail $ "unsupported adt kind " ++ show mbKind

instance FromJSON VariantDiscr where
    parseJSON = withObject "VariantDiscr" $ \v -> case lookupKM "kind" v of
                                                    Just (String "Explicit") -> Explicit <$> v .: "name"
                                                    Just (String "Relative") -> Relative <$> v .: "index"
                                                    _ -> fail "unspported variant discriminator"

instance FromJSON CtorKind where
    parseJSON = withObject "CtorKind" $ \v -> case lookupKM "kind" v of
                                                Just (String "Fn") -> pure FnKind
                                                Just (String "Const") -> pure ConstKind
                                                _ -> fail "unspported constructor kind"
instance FromJSON Variant where
    parseJSON = withObject "Variant" $ \v ->
        Variant <$> v .: "name"
                <*> v .: "discr"
                <*> v .: "fields"
                <*> v .: "ctor_kind"
                <*> do  val <- v .:? "discr_value"
                        convertIntegerText `traverse` val
                <*> v .: "inhabited"

instance FromJSON Field where
    parseJSON = withObject "Field" $ \v -> Field <$> v .: "name" <*> v .: "ty"

instance FromJSON Mutability where
    parseJSON = withObject "Mutability" $ \v -> case lookupKM "kind" v of
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
      (version :: Word64)     <- v .: "version"
      (fns    :: [Fn])        <- v .: "fns"
      (adts   :: [Adt])       <- v .: "adts"
      (traits :: [Trait])     <- v .: "traits"
      (statics :: [Static]  ) <- v .: "statics"
      (vtables :: [Vtable]  ) <- v .: "vtables"
      (intrinsics :: [Intrinsic]) <- v .: "intrinsics"
      (tys    :: [NamedTy])   <- v .: "tys"
      (langItems :: [LangItem]) <- v .: "lang_items"
      (roots :: [MethName])   <- v .: "roots"
      return $ Collection
        version
        (foldr (\ x m -> Map.insert (x^.fname) x m)     Map.empty fns)
        (foldr (\ x m -> Map.insert (x^.adtname) x m)   Map.empty adts)
        (foldr (\ x m -> Map.insertWith (++) (x^.adtOrigDefId) [x] m) Map.empty adts)
        (foldr (\ x m -> Map.insert (x^.traitName) x m) Map.empty traits)
        (foldr (\ x m -> Map.insert (x^.sName) x m)     Map.empty statics)
        (foldr (\ x m -> Map.insert (x^.vtName) x m)    Map.empty vtables)
        (foldr (\ x m -> Map.insert (x^.intrName) x m)  Map.empty intrinsics)
        (foldr (\ x m -> Map.insert (x^.ntName) (x^.ntTy) m) Map.empty tys)
        (foldr (\ x m -> Map.insert (x^.liOrigDefId) (x^.liLangItemDefId) m) Map.empty langItems)
        roots


instance FromJSON Fn where
    parseJSON = withObject "Fn" $ \v -> do
      args <- v .: "args"

      origAbi <- v .: "abi"
      abi <- case origAbi of
        RustCall _ -> do
          spreadArg <- v .: "spread_arg"
          case spreadArg of
            Just i -> return $ RustCall (RcSpreadArg i)
            Nothing -> return $ RustCall RcNoSpreadArg
        _ -> return origAbi

      let sig = FnSig <$> return (map typeOf args)
                      <*> v .: "return_ty"
                      <*> return abi

      Fn
        <$> v .: "name"
        <*> return args
        <*> sig
        <*> v .: "body"

instance FromJSON Abi where
    parseJSON = withObject "Abi" $ \v -> case lookupKM "kind" v of
        Just (String "Rust") -> pure RustAbi
        Just (String "RustIntrinsic") -> pure RustIntrinsic
        -- For `RustCall`, defaut to `RcNoBody`.  The spread_arg info will be
        -- added while parsing the `Fn`, if this `Abi` is part of a `Fn`'s
        -- signature.
        Just (String "RustCall") -> pure $ RustCall RcNoBody
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
    parseJSON j =
      Statement
        <$> parseJSON j
        <*> withObject "Statement" (.: "pos") j

instance FromJSON StatementKind where
    parseJSON = withObject "StatementKind" $ \v -> do
      case lookupKM "kind" v of
        Just (String "Assign") ->  Assign <$> v.: "lhs" <*> v .: "rhs"
        Just (String "SetDiscriminant") -> SetDiscriminant <$> v .: "lvalue" <*> v .: "variant_index"
        Just (String "StorageLive") -> StorageLive <$> v .: "slvar"
        Just (String "StorageDead") -> StorageDead <$> v .: "sdvar"
        Just (String "Nop") -> pure Nop
        Just (String "Deinit") -> pure Deinit
        Just (String "Intrinsic") -> do
           kind <- v .: "intrinsic_kind"
           ndi <- case kind of
               "Assume" -> NDIAssume <$> v .: "operand"
               "CopyNonOverlapping" ->
                   NDICopyNonOverlapping <$> v .: "src"
                                         <*> v .: "dst"
                                         <*> v .: "count"
               _ -> fail $ "unknown Intrinsic kind" ++ kind

           return $ StmtIntrinsic ndi
        Just (String "ConstEvalCounter") -> pure ConstEvalCounter

        k -> fail $ "kind not found for statement: " ++ show k

data RustcPlace = RustcPlace Var [PlaceElem]

instance FromJSON RustcPlace where
    parseJSON = withObject "Place" $ \v ->
        RustcPlace <$> v .: "var" <*> v .: "data"

instance FromJSON PlaceElem where
    parseJSON = withObject "PlaceElem" $ \v ->
      case lookupKM "kind" v of
        Just (String "Deref") -> pure Deref
        Just (String "Field") -> PField <$> v .: "field" <*> v .: "ty"
        Just (String "Index") -> Index <$> v .: "op"
        Just (String "ConstantIndex") -> ConstantIndex <$> v .: "offset" <*> v .: "min_length" <*> v .: "from_end"
        Just (String "Subslice") -> Subslice <$> v .: "from" <*> v .: "to" <*> v .: "from_end"
        Just (String "Downcast") -> Downcast <$> v .: "variant"
        Just (String "Subtype") -> Subtype <$> v .: "ty"
        x -> fail ("bad PlaceElem: " ++ show x)

instance FromJSON Lvalue where
    parseJSON j = convert <$> parseJSON j
      where
        convert (RustcPlace base elems) = foldl LProj (LBase base) elems

instance FromJSON Rvalue where
    parseJSON = withObject "Rvalue" $ \v -> case lookupKM "kind" v of
                                              Just (String "Use") -> Use <$> v .: "usevar"
                                              Just (String "Repeat") -> Repeat <$> v .: "op" <*> v .: "len"
                                              Just (String "Ref") ->  Ref <$> v .: "borrowkind" <*> v .: "refvar" <*> v .: "region"
                                              Just (String "AddressOf") ->  AddressOf <$> v .: "mutbl" <*> v .: "place"
                                              Just (String "Len") -> Len <$> v .: "lv"
                                              Just (String "Cast") -> Cast <$> v .: "type" <*> v .: "op" <*> v .: "ty"
                                              Just (String "BinaryOp") -> BinaryOp <$> v .: "op" <*> v .: "L" <*> v .: "R"
                                              Just (String "NullaryOp") -> NullaryOp <$> v .: "op" <*> v .: "ty"
                                              Just (String "UnaryOp") -> UnaryOp <$> v .: "uop" <*> v .: "op"
                                              Just (String "Discriminant") -> Discriminant <$> v .: "val" <*> v .: "ty"
                                              Just (String "Aggregate") -> Aggregate <$> v .: "akind" <*> v .: "ops"
                                              Just (String "AdtAg") -> RAdtAg <$> v .: "ag"
                                              Just (String "ShallowInitBox") -> ShallowInitBox <$> v .: "ptr" <*> v .: "ty"
                                              Just (String "CopyForDeref") -> CopyForDeref <$> v .: "place"
                                              Just (String "ThreadLocalRef") -> ThreadLocalRef <$> v .: "def_id" <*> v .: "ty"
                                              k -> fail $ "unsupported RValue " ++ show k

instance FromJSON AdtAg where
    parseJSON = withObject "AdtAg" $ \v ->
        AdtAg <$> v .: "adt" <*> v .: "variant" <*> v .: "ops" <*> v .: "ty" <*> v .: "field"

instance FromJSON Terminator where
    parseJSON j =
      Terminator
        <$> parseJSON j
        <*> withObject "Terminator" (.: "pos") j

instance FromJSON TerminatorKind where
    parseJSON = withObject "TerminatorKind" $ \v -> do
      case lookupKM "kind" v of
        Just (String "Goto") -> Goto <$> v .: "target"
        Just (String "SwitchInt") ->
          let  q :: Aeson.Parser [Maybe Integer]
               q = do
                     lmt <- v .: "values"
                     mapM (mapM convertIntegerText) lmt
          in
          SwitchInt <$> v .: "discr" <*> v .: "switch_ty" <*> q <*> v .: "targets"
        Just (String "Resume") -> pure Resume
        Just (String "Abort") -> pure Abort
        Just (String "Return") -> pure Return
        Just (String "Unreachable") -> pure Unreachable
        Just (String "Drop") -> Drop <$> v .: "location" <*> v .: "target" <*> v .: "drop_fn"
        Just (String "Call") ->  Call <$> v .: "func" <*> v .: "args" <*> v .: "destination"
        Just (String "Assert") -> Assert <$> v .: "cond" <*> v .: "expected" <*> v .: "msg" <*> v .: "target"
        k -> fail $ "unsupported terminator kind" ++ show k

instance FromJSON Operand where
    parseJSON = withObject "Operand" $ \v -> case lookupKM "kind" v of
                                               Just (String "Move") -> Move <$> v .: "data"
                                               Just (String "Copy") -> Copy <$> v .: "data"
                                               Just (String "Constant") -> OpConstant <$> v .: "data"
                                               x -> fail ("base operand: " ++ show x)

instance FromJSON NullOp where
    parseJSON = withObject "NullOp" $ \v -> case lookupKM "kind" v of
                                             Just (String "SizeOf") -> pure SizeOf
                                             Just (String "AlignOf") -> pure AlignOf
                                             Just (String "UbChecks") -> pure UbChecks
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
    parseJSON = withObject "UnOp" $ \v -> case lookupKM "kind" v of
                                             Just (String "Not") -> pure Not
                                             Just (String "Neg") -> pure Neg
                                             Just (String "PtrMetadata") -> pure PtrMetadata
                                             x -> fail ("bad unOp: " ++ show x)
instance FromJSON BinOp where
    parseJSON = withObject "BinOp" $ \v ->
        case lookupKM "kind" v of
            Just (String "Add") -> pure Add
            Just (String "AddUnchecked") -> pure $ Unchecked Add
            Just (String "AddWithOverflow") -> pure $ WithOverflow Add
            Just (String "Sub") -> pure Sub
            Just (String "SubUnchecked") -> pure $ Unchecked Sub
            Just (String "SubWithOverflow") -> pure $ WithOverflow Sub
            Just (String "Mul") -> pure Mul
            Just (String "MulUnchecked") -> pure $ Unchecked Mul
            Just (String "MulWithOverflow") -> pure $ WithOverflow Mul
            Just (String "Div") -> pure Div
            Just (String "Rem") -> pure Rem
            Just (String "BitXor") -> pure BitXor
            Just (String "BitAnd") -> pure BitAnd
            Just (String "BitOr") -> pure BitOr
            Just (String "Shl") -> pure Shl
            Just (String "ShlUnchecked") -> pure $ Unchecked Shl
            Just (String "Shr") -> pure Shr
            Just (String "ShrUnchecked") -> pure $ Unchecked Shr
            Just (String "Eq") -> pure Beq
            Just (String "Lt") -> pure Lt
            Just (String "Le") -> pure Le
            Just (String "Ne") -> pure Ne
            Just (String "Ge") -> pure Ge
            Just (String "Gt") -> pure Gt
            Just (String "Offset") -> pure Offset
            Just (String "Cmp") -> pure Cmp
            x -> fail ("bad binop: " ++ show x)


instance FromJSON VtableItem where
    parseJSON = withObject "VtableItem" $ \v ->
        VtableItem <$> v .: "def_id" <*> (v .: "item_id")

instance FromJSON Vtable where
    parseJSON = withObject "Vtable" $ \v ->
        Vtable <$> v .: "name" <*> v .: "items"

instance FromJSON CastKind where
    parseJSON = withObject "CastKind" $ \v ->
        case lookupKM "kind" v of
            Just (String "PointerCoercion") ->
                let go = withObject "PointerCoercion" $ \v' ->
                        case lookupKM "kind" v' of
                            Just (String "ReifyFnPointer") -> pure ReifyFnPointer
                            Just (String "UnsafeFnPointer") -> pure UnsafeFnPointer
                            Just (String "MutToConstPointer") -> pure MutToConstPointer
                            Just (String "ArrayToPointer") -> pure Misc
                            Just (String "Unsize") -> pure Unsize
                            Just (String "ClosureFnPointer") ->
                              fail $ "bad PointerCastKind: ClosureFnPointer should be "
                                ++ "handled specially as a separate CastKind"
                            x -> fail ("bad PointerCastKind: " ++ show x)
                in v .: "cast" >>= go
            Just (String "UnsizeVtable") -> UnsizeVtable <$> v .: "vtable"
            Just (String "ClosureFnPointer") -> ClosureFnPointer <$> v .: "shim"
            -- TODO: actually plumb this information through if it is relevant
            -- instead of using Misc. See
            -- https://github.com/GaloisInc/crucible/issues/1223
            Just (String "PointerExposeProvenance") -> pure Misc
            Just (String "PointerWithExposedProvenance") -> pure Misc
            Just (String "DynStar") -> pure Misc
            Just (String "IntToInt") -> pure Misc
            Just (String "FloatToInt") -> pure Misc
            Just (String "FloatToFloat") -> pure Misc
            Just (String "IntToFloat") -> pure Misc
            Just (String "PtrToPtr") -> pure Misc
            Just (String "FnPtrToPtr") -> pure Misc
            Just (String "Transmute") -> pure Transmute
            x -> fail ("bad CastKind: " ++ show x)

instance FromJSON Constant where
    parseJSON = withObject "Literal" $ \v -> do
      ty <- v .: "ty"
      rend <- v .:? "rendered"
      init <- v .:? "initializer"
      case (rend, init) of
        (Just rend, _) ->
            pure $ Constant ty rend
        (Nothing, Just (RustcConstInitializer defid)) ->
            pure $ Constant ty $ ConstInitializer defid
        (Nothing, Nothing) ->
            fail $ "need either rendered value or initializer in constant literal"


data RustcConstInitializer = RustcConstInitializer DefId

instance FromJSON RustcConstInitializer where
    parseJSON = withObject "Initializer" $ \v ->
        RustcConstInitializer <$> v .: "def_id"

instance FromJSON ConstVal where
    parseJSON = withObject "ConstVal" $ \v ->
      case lookupKM "kind" v of
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

        Just (String "slice") -> do
            def_id <- v .: "def_id"
            len <- v.: "len"
            return $ ConstSliceRef def_id len

        Just (String "strbody") -> do
            elements <- v .: "elements"
            let f sci = case Scientific.toBoundedInteger sci of
                    Just b -> pure (b :: Word8)
                    Nothing -> fail $ "cannot read " ++ show sci
            bytes <- mapM (withScientific "byte" f) elements
            return $ ConstStrBody $ BS.pack bytes

        Just (String "struct") ->
            ConstStruct <$> v .: "fields"
        Just (String "enum") -> do
            variant <- v .: "variant"
            fields <- v .: "fields"
            return $ ConstEnum variant fields
        Just (String "union") ->
            pure ConstUnion

        Just (String "fndef") -> ConstFunction <$> v .: "def_id"
        Just (String "static_ref") -> ConstStaticRef <$> v .: "def_id"
        Just (String "zst") -> pure ConstZST
        Just (String "raw_ptr") -> do
            val <- convertIntegerText =<< v .: "val"
            return $ ConstRawPtr val

        Just (String "array") ->
            ConstArray <$> v .: "elements"

        Just (String "tuple") ->
            ConstTuple <$> v .: "elements"

        Just (String "closure") ->
            ConstClosure <$> v .: "upvars"

        Just (String "fn_ptr") ->
            ConstFnPtr <$> v .: "def_id"

        o -> do
            fail $ "parseJSON - bad rendered constant kind: " ++ show o

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
    parseJSON = withObject "AggregateKind" $ \v -> case lookupKM "kind" v of
                                                     Just (String "Array") -> AKArray <$> v .: "ty"
                                                     Just (String "Tuple") -> pure AKTuple
                                                     Just (String "Closure") -> pure AKClosure
                                                     Just (String "RawPtr") -> AKRawPtr <$> v .: "ty" <*> v .: "mutbl"
                                                     Just (String unk) -> fail $ "unimp: " ++ unpack unk
                                                     x -> fail ("bad AggregateKind: " ++ show x)

instance FromJSON Trait where
    parseJSON = withObject "Trait" $ \v -> do
      Trait <$> v .: "name"
            <*> v .: "items"

instance FromJSON TraitItem where
    parseJSON = withObject "TraitItem" $ \v ->
                case lookupKM "kind" v of
                  Just (String "Method") -> do
                    TraitMethod <$> v .: "item_id" <*> v .: "signature"
                  Just (String unk) -> fail $ "unknown trait item type: " ++ unpack unk
                  Just x -> fail $ "Incorrect format of the kind field in TraitItem: " ++ show x
                  k -> fail $ "bad kind field in TraitItem " ++ show k


instance FromJSON Intrinsic where
    parseJSON = withObject "Intrinsic" $ \v ->
        Intrinsic <$> v .: "name" <*> v .: "inst"


instance FromJSON MirBody where
    parseJSON = withObject "MirBody" $ \v -> do
        vars <- v .: "vars"
        blocks <- v .: "blocks"
        let blockMap = Map.fromList [(b ^. bbinfo, b ^. bbdata) | b <- blocks]
        return $ MirBody vars blocks blockMap

instance FromJSON Static where
  parseJSON = withObject "Static" $ \v -> do
    Static <$> v .: "name"
           <*> v .: "ty"
           <*> v .: "mutable"
           <*> v .:? "rendered"


--  LocalWords:  initializer supertraits deserialization impls

-- TODO: When the ecosystem widely uses aeson-2.0.0.0 or later, remove this CPP.
#if MIN_VERSION_aeson(2,0,0)
lookupKM :: K.Key -> KM.KeyMap Value -> Maybe Value
lookupKM = KM.lookup
#else
lookupKM :: Text -> HML.HashMap Text Value -> Maybe Value
lookupKM = HML.lookup
#endif
