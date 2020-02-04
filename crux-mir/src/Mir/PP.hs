{- A more compact pretty printer that looks more similar to Rust syntax -}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

module Mir.PP where

import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import           Data.Text (Text, unpack)
import qualified Data.Vector as V


import           Control.Lens((^.))
import           Text.PrettyPrint.ANSI.Leijen

import           Mir.Mir
import           Mir.DefId


-----------------------------------------------

-- format the AST suitable for an error message
-- unlike the default 'show' instance for 'Doc', this function
-- uses the full ribbon width for an 80 column layout
fmt :: Pretty a => a -> String
fmt x = displayS (renderPretty 1.0 80 (pretty x)) ""

pr_id :: DefId -> Doc
pr_id = pretty

pretty_fn1 :: Pretty a => String -> a -> Doc
pretty_fn1 str x = text str <> parens (pretty x)

pretty_fn2 :: (Pretty a,Pretty b) => String -> a -> b -> Doc
pretty_fn2 str x y = text str <> tupled [pretty x, pretty y]

pretty_fn3 :: (Pretty a,Pretty b,Pretty c) => String -> a -> b -> c -> Doc
pretty_fn3 str x y z = text str <> tupled [pretty x, pretty y, pretty z]

pretty_fn4 :: (Pretty a,Pretty b,Pretty c,Pretty d) => String -> a -> b -> c -> d -> Doc
pretty_fn4 str x y z w = text str <> tupled [pretty x, pretty y, pretty z, pretty w]


arrow :: Doc
arrow = text "->"

size_str :: BaseSize -> String
size_str B8   = "8"
size_str B16  = "16"
size_str B32  = "32"
size_str B64  = "64"
size_str B128 = "128"
size_str USize = "size"


instance Pretty Text where
  pretty = text . unpack
  
instance Pretty BaseSize where
    pretty = text . size_str

instance Pretty FloatKind where
    pretty F32 = text "f32"
    pretty F64 = text "f64"

instance Pretty Ty where
    pretty TyBool         = text "bool"
    pretty TyChar         = text "char"
    pretty (TyInt sz)     = text $ "i" ++ size_str sz
    pretty (TyUint sz)    = text $ "u" ++ size_str sz
    pretty (TyTuple tys)  = tupled (map pretty tys)
    pretty (TySlice ty)   = brackets (pretty ty)
    pretty (TyArray ty i) = brackets (pretty ty <> semi <+> int i)
    pretty (TyRef ty mutability) = text "&" <> pretty mutability <> pretty ty
    pretty (TyAdt _ origDefId tys)    = pr_id origDefId <> pretty tys
    pretty TyUnsupported         = text "Unsupported"
    pretty (TyParam i)           = text ("_" ++ show i)
    pretty (TyFnDef defId tys)   = text "fnDef" <+> pr_id defId <> pretty tys
    pretty (TyClosure tys)       = text "closure" <+> pretty tys
    pretty TyStr                 = text "str"
    pretty (TyFnPtr fnSig)       = pretty fnSig 
    pretty (TyDynamic trait preds) = text "dynamic" <+> pretty trait <+> pretty preds
    pretty (TyRawPtr ty mutability) = text "*" <> pretty mutability <+> pretty ty
    pretty (TyFloat floatKind) = pretty floatKind
    pretty (TyDowncast adt i)    = parens (pretty adt <+> text "as" <+> pretty i)
    pretty (TyProjection defId tys) = text "projection" <+> brackets (pr_id defId <> pretty tys)
    pretty TyNever = text "never"
    pretty TyLifetime = text "lifetime"
    pretty TyConst = text "const"
    pretty TyErased = text "erased"
    pretty (TyInterned s) = text $ unpack s

instance Pretty Adt where
   pretty (Adt nm kind vs origName origSubsts) =
    pretty kind <+> pretty nm <> brackets (pretty origName <+> pretty origSubsts)
        <> tupled (map pretty vs)

instance Pretty AdtKind where
  pretty = text . show

instance Pretty VariantDiscr where
  pretty (Explicit a) = pretty_fn1 "Explicit" a
  pretty (Relative a) = pretty_fn1 "Relative" a


instance Pretty CtorKind where
  pretty = text . show

instance Pretty Variant where
  pretty (Variant nm dscr flds knd) = pretty_fn4 "Variant" (pretty nm) dscr flds knd

instance Pretty Field where
    pretty (Field nm ty sbs) = pretty_fn3 "Field" (pretty nm) ty sbs

instance Pretty Mutability where
    pretty Mut   = text "mut " 
    pretty Immut = empty

instance Pretty Var where
    pretty (Var vn _vm _vty _vzst _vs _) = pretty vn

pretty_arg :: Var -> Doc
pretty_arg (Var vn _vm vty _vzst _vs _) =
  pretty vn <+> colon <+> pretty vty

pretty_temp :: Var -> Doc
pretty_temp (Var vn vm vty _vzst _vs _) =
  text "let" <+>
    (if vm == Mut then text "mut" else text "const")
    <+> pretty vn <+> colon <+> pretty vty <> semi

instance Pretty Predicate where
  pretty (TraitPredicate trait args) =
      pretty trait <> pretty args
  pretty (TraitProjection lhs ty) =
      pretty lhs <> text "=" <> pretty ty
  pretty (AutoTraitPredicate trait) =
      pretty trait
  pretty UnknownPredicate = text "UnknownPredicate"
  
instance Pretty Fn where
    pretty (Fn fname1 fargs1 fs fbody1 fstatics) =
      vcat $ [text "fn" <+> pretty fname1 <> pparams gens
            <> patys atys <+> tupled (map pretty_arg fargs1)
                      <+> arrow <+> pretty rty <+> ppreds preds <+> lbrace] 
            ++ (map pretty (V.toList fstatics)) 
            ++ [indent 3 (pretty fbody1),
                rbrace]
      where
        gens   = fs^.fsgenerics
        atys   = fs^.fsassoc_tys
        rty    = fs^.fsreturn_ty
        preds  = fs^.fspredicates

instance Pretty MirBody where
    pretty (MirBody mvs mbs) =
      vcat (map pretty_temp mvs ++
            map pretty      mbs)
    
instance Pretty BasicBlock where
    pretty (BasicBlock info dat) =
      vcat [
        pretty info <> colon <+> lbrace,
        indent 3 (pretty dat),
        rbrace
        ]

instance Pretty BasicBlockData where
    pretty (BasicBlockData bbds bbt) =
      vcat (map pretty bbds ++ [pretty bbt])


instance Pretty Statement where
    pretty (Assign lhs rhs _) = pretty lhs <+> equals <+> pretty rhs <> semi
    pretty (SetDiscriminant lhs rhs) =
      text "discr(" <> pretty lhs <> text ")" <+> equals <+> pretty rhs <> semi
    pretty (StorageLive l) = pretty_fn1 "StorageLive" l <> semi
    pretty (StorageDead l) = pretty_fn1 "StorageDead" l <> semi
    pretty Nop = text "nop" <> semi

instance Pretty PlaceBase where
    pretty (Local v)        = pretty v
    pretty (PStatic did _t) = pretty_fn1 "Static" did
    pretty (PPromoted p _t) = pretty p

instance Pretty Lvalue where
    pretty (LBase base) = pretty base
    pretty (LProj lv Deref) = text "*" <> pretty lv
    pretty (LProj lv (PField i _ty)) = pretty lv <> dot <> pretty i
    pretty (LProj lv (Index op))    = pretty lv <> brackets (pretty op)
    pretty (LProj lv (ConstantIndex co _cl ce)) =
      pretty lv <> brackets (if ce then empty else text "-" <> pretty co)
    pretty (LProj lv (Subslice f t)) =
      pretty lv <> brackets (pretty f <> dot <> dot <> pretty t)
    pretty (LProj lv (Downcast i)) =
      parens (pretty lv <+> text "as" <+> pretty i)

instance Pretty Rvalue where
    pretty (Use a) = pretty_fn1 "use" a
    pretty (Repeat a b) = brackets (pretty a <> semi <> pretty b) 
    pretty (Ref Shared b _c) = text "&" <> pretty b
    pretty (Ref Unique b _c) = text "&unique" <+> pretty b
    pretty (Ref Mutable b _c) = text "&mut" <+> pretty b
    pretty (Len a) = pretty_fn1 "len" a
    pretty (Cast a b c) = pretty_fn3 "Cast" a b c
    pretty (BinaryOp a b c) = pretty b <+> pretty a <+> pretty c
    pretty (CheckedBinaryOp a b c) = pretty b <+> pretty a <+> pretty c
    pretty (NullaryOp a _b) = pretty a
    pretty (UnaryOp a b) = pretty a <+> pretty b
    pretty (Discriminant a) = pretty_fn1 "Discriminant" a
    pretty (Aggregate a b) = pretty_fn2 "Aggregate" a b
    pretty (RAdtAg a) = pretty a

instance Pretty AdtAg where
  pretty (AdtAg (Adt nm _kind _vs _ _) i ops _) = pretty_fn3 "AdtAg" (pr_id nm) i ops


instance Pretty Terminator where
    pretty (Goto g) = pretty_fn1 "goto" g <> semi
    pretty (SwitchInt op ty vs bs) =
      text "switchint" <+> pretty op <+> colon <> pretty ty <+>
      pretty vs <+> arrow <+> pretty bs
    pretty Return = text "return;"
    pretty Abort = text "abort;"
    pretty Resume = text "resume;"
    pretty Unreachable = text "unreachable;"
    pretty (Drop _l _target _unwind) = text "drop;"
    pretty DropAndReplace{} = text "dropreplace;"
    pretty (Call f args (Just (lv,bb0)) bb1) =
      text "call" <> tupled ([pretty lv <+> text "="
                                       <+> pretty f <> tupled (map pretty args),
                             pretty bb0] ++ Maybe.maybeToList (fmap pretty bb1))
    pretty (Call f args Nothing  bb1 ) =
      text "call" <> tupled ([pretty f <> tupled (map pretty args)]
                             ++ Maybe.maybeToList (fmap pretty bb1))

      
    pretty (Assert op expect _msg target1 _cleanup) =
      text "assert" <+> pretty op <+> text "==" <+> pretty expect
                    <+> arrow <+> pretty target1



instance Pretty Operand where
    pretty (OpConstant c) = pretty c
    pretty (Move c) = pretty c
    pretty (Copy c) = pretty c

instance Pretty Constant where
    pretty (Constant _a b) = pretty b

instance Pretty NullOp where
    pretty SizeOf = text "sizeof"
    pretty Box    = text "box"

instance Pretty BorrowKind where
    pretty = text . show



instance Pretty UnOp where
    pretty Not = text "!"
    pretty Neg = text "-"

instance Pretty BinOp where
    pretty op = case op of
      Add -> text "+"
      Sub -> text "-"
      Mul -> text "*"
      Div -> text "/"
      Rem -> text "%"
      BitXor -> text "^"
      BitAnd -> text "&"
      BitOr -> text "|"
      Shl -> text "<<"
      Shr -> text ">>"
      Beq -> text "=="
      Lt -> text "<"
      Le -> text "<="
      Ne -> text "!="
      Ge -> text ">="
      Gt -> text ">"
      Offset -> text "Offset"

instance Pretty CastKind where
    pretty = text . show

instance Pretty Literal where
    pretty (Item a b)    = pretty_fn2 "Item" a b
    pretty (Value a)     = pretty a
    pretty (LitPromoted a) = pretty a

instance Pretty IntLit where
  pretty i = text $ case i of
    U8 i0 -> show i0
    U16 i0 -> show i0
    U32 i0 -> show i0
    U64 i0 -> show i0
    U128 i0 -> show i0
    Usize i0 -> show i0
    I8 i0 -> show i0
    I16 i0 -> show i0
    I32 i0 -> show i0
    I64 i0 -> show i0
    I128 i0 -> show i0
    Isize i0 -> show i0

instance Pretty FloatLit where
  pretty = text . show


instance Pretty Substs where
  pretty (Substs b) = langle <> hcat (punctuate comma (map pretty b)) <> rangle
  
instance Pretty ConstVal where
    pretty (ConstFloat i)   = pretty i
    pretty (ConstInt i)     = pretty i
    pretty (ConstStr i)     = char '\"' <> text (show i) <> char '\"'
    pretty (ConstByteStr i) = text (show i)
    pretty (ConstBool i)    = pretty i
    pretty (ConstChar i)    = pretty i
    pretty (ConstVariant i) = pr_id i
    pretty (ConstTuple cs)  = tupled (map pretty cs)
    pretty (ConstArray cs)     = list (map pretty cs)
    pretty (ConstRepeat cv i)  = brackets (pretty cv <> semi <+> int i)
    pretty (ConstFunction a b) = pr_id a <> pretty b
    pretty ConstStruct = text "ConstStruct"
    pretty (ConstInitializer a b) = pr_id a <> pretty b

instance Pretty AggregateKind where
    pretty (AKArray t) = brackets (pretty t)
    pretty AKTuple = text "tup"
    pretty (AKClosure defid args) = pretty defid <> pretty args

instance Pretty FnSig where
  pretty fs =
    pparams (fs^.fsgenerics) <>
    tupled (map pretty (fs^.fsarg_tys)) <+> arrow <+> pretty (fs^.fsreturn_ty)
                <+> ppreds (fs^.fspredicates)
                <+> patys  (fs^.fsassoc_tys)
                <+> brackets (pretty (fs^.fsabi))
                <+> maybeSpreadArg
    where
        maybeSpreadArg = case fs^.fsspreadarg of
            Nothing -> mempty
            Just i -> braces (text "spread_arg" <+> pretty i)

instance Pretty Abi where
    pretty a = pretty (show a)

instance Pretty TraitItem where
  pretty (TraitMethod name sig)
    = text "fn"    <+> pr_id name <> pretty sig <> semi
  pretty (TraitType name)         = text "name"  <+> pr_id name <> semi
  pretty (TraitConst name ty)     = text "const" <+> pr_id name <> colon <> pretty ty <> semi

instance Pretty Trait where
  pretty (Trait name items _supers params preds _numParams) =
    let ps = pparams params
    in                    
        vcat [text "trait" <+> pretty name <+> ps <+> ppreds preds <+> lbrace ,
              indent 3 (vcat (map pretty items)),
              rbrace]

instance Pretty TraitRef where
  pretty (TraitRef did (Substs (s:_))) = pr_id did <+> text "for" <+> pretty s
  pretty (TraitRef did s)              = pr_id did <+> text "for" <+> pretty s

instance Pretty Param where
  pretty (Param name) = pretty name

--instance Pretty AssocTy where
--  pretty (AssocTy (name, substs)) = pretty name <+> pretty substs

patys   :: [AssocTy] -> Doc
patys atys = if null atys then empty
  else encloseSep langle rangle  comma (map pretty atys)

-- don't allow line breaks in the middle of params
pparams :: [Param] -> Doc
pparams params = if null params then mempty
  else hcat $ [langle] ++ punctuate comma (map pretty params) ++ [rangle]

ppreds :: [Predicate] -> Doc
ppreds preds = if null preds then empty
  else text "where" <+> list (map pretty preds)

instance Pretty TraitImpl where
  pretty ti =
    vcat [text "impl" <> pparams (ti^.tiGenerics) <+> pretty (ti^.tiTraitRef)
               <+> ppreds (ti^.tiPredicates) <+> lbrace, 
          indent 3 (vcat (map pretty (ti^.tiItems))),
          rbrace]

instance Pretty TraitImplItem where
  pretty (TraitImplMethod nm timpls _params _preds sig)  =
    pretty nm <+> text "of type" <+> pretty sig <+>
       text "implements" <+> pretty timpls
  pretty (TraitImplType nm timpls _params _preds ty) =
    text "type" <+> pretty nm <+> pretty timpls <+> text "=" <+> pretty ty

instance Pretty Static where
  pretty (Static nm ty mut pf p) =
    pretty mut <+> pretty nm <+> text ":" <+> pretty ty <+> text "promoted from" <+> pretty pf <+> pretty p

instance Pretty Promoted where
  pretty (Promoted i) = text "{{promoted}}" <> brackets (pretty i)

instance Pretty Intrinsic where
  pretty (Intrinsic name inst) = pretty name <+> text "=" <+> pretty inst

instance Pretty Instance where
  pretty (Instance kind defid substs) = pretty kind <+> pretty defid <> text "<" <> pretty substs <> text ">"

instance Pretty InstanceKind where
  pretty x = text $ show x

instance Pretty Collection where
  pretty col =
    vcat ([text "FNs"] ++
          map pretty (Map.elems (col^.functions)) ++
          [text "ADTs"] ++
          map pretty (Map.elems (col^.adts)) ++
          [text "TRAITs"] ++
          map pretty (Map.elems (col^.traits)) ++
          [text "INTRINSICSs"] ++
          map pretty (Map.elems (col^.intrinsics)) ++
          [text "IMPLs"] ++
          map pretty (col^.impls) ++
          [text "STATICS"] ++
          map pretty (Map.elems (col^.statics)))
