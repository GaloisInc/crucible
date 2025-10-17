{- A more compact pretty printer that looks more similar to Rust syntax -}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Mir.PP where

import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe

import           Control.Lens((^.))
import           Prettyprinter
import           Prettyprinter.Render.String

import           Mir.Mir
import           Mir.DefId


-----------------------------------------------

-- format the AST suitable for an error message
-- unlike the default 'show' instance for 'Doc', this function
-- uses the full ribbon width for an 80 column layout
fmtDoc :: Doc ann -> String
fmtDoc x = renderString (layoutPretty opts x)
  where opts = LayoutOptions (AvailablePerLine 80 1.0)

-- format the AST suitable for an error message
-- unlike the default 'show' instance for 'Doc', this function
-- uses the full ribbon width for an 80 column layout
fmt :: Pretty a => a -> String
fmt x = fmtDoc (pretty x)

pr_id :: DefId -> Doc ann
pr_id = pretty

pretty_fn1 :: Pretty a => String -> a -> Doc ann
pretty_fn1 str x = pretty str <> parens (pretty x)

pretty_fn2 :: (Pretty a, Pretty b) => String -> a -> b -> Doc ann
pretty_fn2 str x y = pretty str <> tupled [pretty x, pretty y]

pretty_fn3 :: (Pretty a, Pretty b, Pretty c) => String -> a -> b -> c -> Doc ann
pretty_fn3 str x y z = pretty str <> tupled [pretty x, pretty y, pretty z]

pretty_fn4 :: (Pretty a, Pretty b, Pretty c, Pretty d) => String -> a -> b -> c -> d -> Doc ann
pretty_fn4 str x y z w = pretty str <> tupled [pretty x, pretty y, pretty z, pretty w]


arrow :: Doc ann
arrow = pretty "->"

size_str :: BaseSize -> String
size_str B8   = "8"
size_str B16  = "16"
size_str B32  = "32"
size_str B64  = "64"
size_str B128 = "128"
size_str USize = "size"


instance Pretty BaseSize where
    pretty = pretty . size_str

instance Pretty FloatKind where
    pretty F32 = pretty "f32"
    pretty F64 = pretty "f64"

instance Pretty Ty where
    pretty TyBool         = pretty "bool"
    pretty TyChar         = pretty "char"
    pretty (TyInt sz)     = pretty $ "i" ++ size_str sz
    pretty (TyUint sz)    = pretty $ "u" ++ size_str sz
    pretty (TyTuple tys)  = tupled (map pretty tys)
    pretty (TySlice ty)   = brackets (pretty ty)
    pretty (TyArray ty i) = brackets (pretty ty <> semi <+> pretty i)
    pretty (TyRef ty mutability) = pretty "&" <> pretty mutability <> pretty ty
    pretty (TyAdt _ origDefId tys)    = pr_id origDefId <> pretty tys
    pretty (TyFnDef defId)       = pretty "fnDef" <+> pr_id defId
    pretty (TyClosure tys)       = pretty "closure" <+> pretty tys
    pretty TyStr                 = pretty "str"
    pretty (TyFnPtr fnSig)       = pretty fnSig
    pretty (TyDynamic trait)     = pretty "dynamic" <+> pretty trait
    pretty (TyRawPtr ty Immut) = pretty "*const" <+> pretty ty
    pretty (TyRawPtr ty Mut)   = pretty "*mut" <+> pretty ty
    pretty (TyFloat floatKind) = pretty floatKind
    pretty (TyDowncast adt i)    = parens (pretty adt <+> pretty "as" <+> pretty i)
    pretty TyNever = pretty "never"
    pretty TyLifetime = pretty "lifetime"
    pretty TyConst = pretty "const"
    pretty TyForeign = pretty "foreign"
    pretty TyErased = pretty "erased"
    pretty (TyInterned s) = pretty s

instance Pretty Adt where
   pretty (Adt nm kind vs _size reprTransparent origName origSubsts) =
    (if reprTransparent then pretty "#[repr(transparent)]" else mempty) <+>
    pretty kind <+> pretty nm <> brackets (pretty origName <+> pretty origSubsts)
        <> tupled (map pretty vs)

instance Pretty AdtKind where
  pretty = viaShow

instance Pretty VariantDiscr where
  pretty (Explicit a) = pretty_fn1 "Explicit" a
  pretty (Relative a) = pretty_fn1 "Relative" a


instance Pretty CtorKind where
  pretty = viaShow

instance Pretty Variant where
  pretty (Variant nm dscr flds knd mbVal inh) =
    pretty "Variant" <>
      tupled [pretty nm, pretty dscr, pretty flds, pretty knd, pretty mbVal, pretty inh]

instance Pretty Field where
    pretty (Field nm ty) = pretty_fn2 "Field" nm ty

instance Pretty Mutability where
    pretty Mut   = pretty "mut "
    pretty Immut = mempty

instance Pretty Var where
    pretty (Var vn _vm _vty _vzst) = pretty vn

pretty_arg :: Var -> Doc ann
pretty_arg (Var vn _vm vty _vzst) =
  pretty vn <+> colon <+> pretty vty

pretty_temp :: Var -> Doc ann
pretty_temp (Var vn vm vty _vzst) =
  pretty "let" <+>
    (if vm == Mut then pretty "mut" else pretty "const")
    <+> pretty vn <+> colon <+> pretty vty <> semi

instance Pretty Fn where
    pretty (Fn fname1 fargs1 fs fbody1) =
      vcat $ [extern <> pretty "fn" <+> pretty fname1 <> tupled (map pretty_arg fargs1)
                  <+> arrow <+> pretty rty <+> lbrace]
            ++ [indent 3 (pretty fbody1),
                rbrace]
      where
        rty    = fs^.fsreturn_ty
        extern = case fs^.fsabi of
          RustAbi -> mempty
          abi -> pretty "extern" <+> viaShow abi <+> mempty

instance Pretty MirBody where
    pretty (MirBody mvs mbs _) =
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
  pretty stmt = pretty (stmt ^. stmtKind)

instance Pretty StatementKind where
    pretty (Assign lhs rhs) = pretty lhs <+> equals <+> pretty rhs <> semi
    pretty (SetDiscriminant lhs rhs) =
      pretty "discr(" <> pretty lhs <> pretty ")" <+> equals <+> pretty rhs <> semi
    pretty (StorageLive l) = pretty_fn1 "StorageLive" l <> semi
    pretty (StorageDead l) = pretty_fn1 "StorageDead" l <> semi
    pretty Nop = pretty "nop" <> semi
    pretty Deinit = pretty "DeInit"
    pretty (StmtIntrinsic (NDIAssume op)) =
      pretty "Intrinsic" <> brackets (pretty "Assume") <> parens (pretty op) <> semi
    pretty (StmtIntrinsic (NDICopyNonOverlapping o1 o2 o3)) =
      pretty "Intrinsic" <> brackets (pretty "CopyNonOverlapping")
                         <> tupled (pretty <$> [o1, o2, o3])
                         <> semi
    pretty ConstEvalCounter = pretty "ConstEvalCounter"

instance Pretty Lvalue where
    pretty (LBase base) = pretty base
    pretty (LProj lv Deref) = pretty "*" <> pretty lv
    pretty (LProj lv (PField i _ty)) = pretty lv <> dot <> pretty i
    pretty (LProj lv (Index op))    = pretty lv <> brackets (pretty op)
    pretty (LProj lv (ConstantIndex co _cl ce)) =
      pretty lv <> brackets (if ce then mempty else pretty "-" <> pretty co)
    pretty (LProj lv (Subslice f t False)) =
      pretty lv <> brackets (pretty f <> dot <> dot <> pretty t)
    pretty (LProj lv (Subslice f t True)) =
      pretty lv <> brackets (pretty "-" <> pretty f <> dot <> dot <> pretty "-" <> pretty t)
    pretty (LProj lv (Downcast i)) =
      parens (pretty lv <+> pretty "as" <+> pretty i)
    pretty (LProj lv (Subtype ty)) =
      parens (pretty lv <+> pretty "as subtype" <+> pretty ty)

instance Pretty Rvalue where
    pretty (Use a) = pretty_fn1 "use" a
    pretty (Repeat a b) = brackets (pretty a <> semi <> pretty b)
    pretty (Ref Shared b _c) = pretty "&" <> pretty b
    pretty (Ref Unique b _c) = pretty "&unique" <+> pretty b
    pretty (Ref Mutable b _c) = pretty "&mut" <+> pretty b
    pretty (AddressOf Immut b) = pretty "&raw" <+> pretty b
    pretty (AddressOf Mut b) = pretty "&raw mut" <+> pretty b
    pretty (Len a) = pretty_fn1 "len" a
    pretty (Cast a b c) = pretty_fn3 "Cast" a b c
    pretty (BinaryOp a b c) = pretty b <+> pretty a <+> pretty c
    pretty (NullaryOp a _b) = pretty a
    pretty (UnaryOp a b) = pretty a <+> pretty b
    pretty (Discriminant a b) = pretty_fn2 "Discriminant" a b
    pretty (Aggregate a b) = pretty_fn2 "Aggregate" a b
    pretty (RAdtAg a) = pretty a
    pretty (ShallowInitBox ptr ty) = pretty_fn2 "ShallowInitBox" ptr ty
    pretty (CopyForDeref lv) = pretty_fn1 "CopyForDeref" lv
    pretty (ThreadLocalRef a b) = pretty_fn2 "ThreadLocalRef" a b

instance Pretty AdtAg where
  pretty (AdtAg (Adt nm _kind _vs _ _ _ _) i ops _ optField) = case optField of
    Just field -> pretty_fn4 "AdtAg" nm i ops field
    Nothing -> pretty_fn3 "AdtAg" nm i ops

instance Pretty Terminator where
  pretty term = pretty (term ^. termKind)

instance Pretty TerminatorKind where
    pretty (Goto g) = pretty_fn1 "goto" g <> semi
    pretty (SwitchInt op ty vs bs) =
      pretty "switchint" <+> pretty op <+> colon <> pretty ty <+>
      pretty vs <+> arrow <+> pretty bs
    pretty Return = pretty "return;"
    pretty Abort = pretty "abort;"
    pretty Resume = pretty "resume;"
    pretty Unreachable = pretty "unreachable;"
    pretty (Drop l target dropFn) =
        pretty "drop" <+> pretty l <+> pretty "->" <+> pretty target <+> parens (viaShow dropFn) <> semi
    pretty (Call f args bb) =
      pretty "call" <> tupled ([pretty f <> tupled (map pretty args)]
                             ++ Maybe.maybeToList (fmap pretty bb))
    pretty (Assert op expect _msg target1) =
      pretty "assert" <+> pretty op <+> pretty "==" <+> pretty expect
                    <+> arrow <+> pretty target1
    pretty InlineAsm = pretty "inlineasm;"



instance Pretty Operand where
    pretty (OpConstant c) = pretty c
    pretty (Move c) = pretty c
    pretty (Copy c) = pretty c
    pretty (Temp c) = pretty c

instance Pretty Constant where
    pretty (Constant a b) =
      case (a, b) of
        -- We include two special cases for ConstZST that leverage its type to
        -- improve the pretty-printing:
        --
        -- - If the type is TyFnDef, then we pretty-print the function's DefId.
        --   (This is crucial to ensure that pretty-printing function
        --   applications reveals the name of the applied function.)
        --
        -- - Otherwise, we print <ZST: [ty]>, where [ty] is the pretty-printed
        --   type.
        --
        -- There is also a case for ConstZST in the `Pretty ConstVal` instance,
        -- but the output there (<ZST>) is much less informative, as it cannot
        -- take the type of the ConstZST into account.
        (TyFnDef defId, ConstZST) ->
          pr_id defId
        (_, ConstZST) ->
          pretty "<ZST:" <+> pretty a <> pretty ">"
        _ ->
          pretty b

instance Pretty NullOp where
    pretty SizeOf = pretty "sizeof"
    pretty AlignOf = pretty "alignof"
    pretty UbChecks = pretty "ub_checks"

instance Pretty BorrowKind where
    pretty = viaShow



instance Pretty UnOp where
    pretty Not = pretty "!"
    pretty Neg = pretty "-"
    pretty PtrMetadata = pretty "PtrMetadata"

instance Pretty BinOp where
    pretty op = case op of
      Add -> pretty "+"
      Sub -> pretty "-"
      Mul -> pretty "*"
      Div -> pretty "/"
      Rem -> pretty "%"
      BitXor -> pretty "^"
      BitAnd -> pretty "&"
      BitOr -> pretty "|"
      Shl -> pretty "<<"
      Shr -> pretty ">>"
      Beq -> pretty "=="
      Lt -> pretty "<"
      Le -> pretty "<="
      Ne -> pretty "!="
      Ge -> pretty ">="
      Gt -> pretty ">"
      Offset -> pretty "Offset"
      Cmp -> pretty "Cmp"
      Unchecked op' -> pretty op' <> pretty "!"
      WithOverflow op' -> pretty op' <> pretty "?"

instance Pretty VtableItem where
  pretty (VtableItem fn def) =
    vcat
      [ pretty "( " <+> pretty def
      , pretty "=>" <+> pretty fn <+> pretty ");"
      ]

instance Pretty Vtable where
  pretty (Vtable name items) =
    vcat [pretty "vtable" <+> pretty name <+> lbrace ,
          indent 3 (vcat (map pretty items)),
          rbrace]

instance Pretty CastKind where
    pretty = viaShow

instance Pretty IntLit where
  pretty i = pretty $ case i of
    U8 i0 -> i0
    U16 i0 -> i0
    U32 i0 -> i0
    U64 i0 -> i0
    U128 i0 -> i0
    Usize i0 -> i0
    I8 i0 -> i0
    I16 i0 -> i0
    I32 i0 -> i0
    I64 i0 -> i0
    I128 i0 -> i0
    Isize i0 -> i0

instance Pretty FloatLit where
  pretty = viaShow


instance Pretty Substs where
  pretty (Substs b) = langle <> hcat (punctuate comma (map pretty b)) <> rangle

instance Pretty ConstVal where
    pretty (ConstFloat i)   = pretty i
    pretty (ConstInt i)     = pretty i
    pretty (ConstStrBody i) = dquotes (viaShow i)
    pretty (ConstBool i)    = pretty i
    pretty (ConstChar i)    = pretty i
    pretty (ConstVariant i) = pr_id i
    pretty (ConstTuple cs)  = tupled (map pretty cs)
    pretty (ConstClosure us)   = pretty "closure" <> list (map pretty us)
    pretty (ConstArray cs)     = list (map pretty cs)
    pretty (ConstRepeat cv i)  = brackets (pretty cv <> semi <+> pretty i)
    pretty (ConstFunction a)   = pr_id a
    pretty (ConstInitializer a) = pr_id a
    pretty (ConstStaticRef a) = pretty "&" <> pr_id a
    pretty ConstZST =
      -- A ConstZST value represents a value with a zero-sized type, but we
      -- cannot know what type it is by looking at the value in isolation. Note
      -- that the `Pretty Constant` instance includes a special case for
      -- ConstZST that value along with its type for clarity. In practice, most
      -- ConstZSTs will be printed via the `Pretty Constant` instance, not the
      -- code below.
      pretty "<ZST>"
    pretty (ConstRawPtr a) = pretty a
    pretty (ConstStruct fs) = pretty "struct" <> list (map pretty fs)
    pretty (ConstEnum v fs) = pretty "enum" <> list ((pretty "variant" <+> pretty v) : map pretty fs)
    pretty ConstUnion = pretty "union"
    pretty (ConstSliceRef a _len) = pretty "&" <> pr_id a
    pretty (ConstFnPtr i)   = pretty "fn_ptr" <> brackets (pretty i)

instance Pretty AggregateKind where
    pretty (AKArray t) = brackets (pretty t)
    pretty AKTuple = pretty "tup"
    pretty AKClosure = pretty "closure"
    pretty (AKRawPtr t mutbl) = brackets (pretty (TyRawPtr t mutbl))

instance Pretty FnSig where
  pretty fs =
    tupled (map pretty (fs^.fsarg_tys)) <+> arrow <+> pretty (fs^.fsreturn_ty)
                <+> brackets (pretty (fs^.fsabi))

instance Pretty Abi where
    pretty = viaShow

instance Pretty TraitItem where
  pretty (TraitMethod name sig)
    = pretty "fn" <+> pr_id name <> pretty sig <> semi

instance Pretty Trait where
  pretty (Trait name items) =
    vcat [pretty "trait" <+> pretty name <+> lbrace ,
          indent 3 (vcat (map pretty items)),
          rbrace]

instance Pretty Static where
  pretty (Static nm ty mut mbConst) =
    pretty mut <+> pretty nm <+> pretty ":" <+> pretty ty <+>
    maybe mempty (\c -> pretty "=" <+> pretty c) mbConst

instance Pretty Intrinsic where
  pretty (Intrinsic name inst) = pretty name <+> pretty "=" <+> pretty inst

instance Pretty Instance where
  pretty (Instance kind defid substs) = pretty kind <+> pretty defid <> pretty "<" <> pretty substs <> pretty ">"

instance Pretty InstanceKind where
  pretty = viaShow

instance Pretty Collection where
  pretty col =
    vcat ([pretty "FNs"] ++
          map pretty (Map.elems (col^.functions)) ++
          [pretty "ADTs"] ++
          map pretty (Map.elems (col^.adts)) ++
          [pretty "TRAITs"] ++
          map pretty (Map.elems (col^.traits)) ++
          [pretty "VTABLEs"] ++
          map pretty (Map.elems (col^.vtables)) ++
          [pretty "INTRINSICSs"] ++
          map pretty (Map.elems (col^.intrinsics)) ++
          [pretty "STATICS"] ++
          map pretty (Map.elems (col^.statics)))
