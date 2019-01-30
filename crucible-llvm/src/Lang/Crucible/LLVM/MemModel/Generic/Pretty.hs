{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.MemModel.Generic.Pretty
  ( ppType
  , ppAlloc
  , ppAllocs
  , ppMem

  -- * Re-exports
  , ppPtr
  ) where

import qualified Data.Vector as V
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Value
import           Lang.Crucible.LLVM.MemModel.Pointer (ppPtr)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           What4.Interface (IsExpr, IsExprBuilder)

--------------------------------------------------------------------------------
-- Pretty printing


ppTermExpr
  :: forall sym. IsExprBuilder sym
  => LLVMVal sym
  -> Doc
ppTermExpr t = -- FIXME, do something with the predicate?
  case t of
    LLVMValZero _tp -> text "0"
    LLVMValUndef tp -> text "<undef : " <> text (show tp) <> text ">"
    LLVMValInt base off -> ppPtr @sym (LLVMPointer base off)
    LLVMValFloat _ v -> printSymExpr v
    LLVMValStruct v -> encloseSep lbrace rbrace comma v''
      where v'  = fmap (over _2 ppTermExpr) (V.toList v)
            v'' = map (\(fld,doc) ->
                        group (text "base+" <> text (show $ fieldOffset fld) <+> equals <+> doc))
                      v'
    LLVMValArray _tp v -> encloseSep lbracket rbracket comma v'
      where v' = ppTermExpr <$> V.toList v

-- | Pretty print type.
ppType :: StorageType -> Doc
ppType tp =
  case storageTypeF tp of
    Bitvector w -> text ('i': show (bytesToBits w))
    Float -> text "float"
    Double -> text "double"
    X86_FP80 -> text "long double"
    Array n etp -> brackets (text (show n) <+> char 'x' <+> ppType etp)
    Struct flds -> braces $ hsep $ punctuate (char ',') $ V.toList $ ppFld <$> flds
      where ppFld f = ppType (f^.fieldVal)

ppMerge :: IsExpr e
        => (v -> Doc)
        -> e tp
        -> [v]
        -> [v]
        -> Doc
ppMerge vpp c x y =
  indent 2 $
    text "Condition:" <$$>
    indent 2 (printSymExpr c) <$$>
    text "True Branch:"  <$$>
    indent 2 (vcat $ map vpp x) <$$>
    text "False Branch:" <$$>
    indent 2 (vcat $ map vpp y)

ppAlloc :: IsExprBuilder sym => MemAlloc sym -> Doc
ppAlloc (Alloc atp base sz mut _alignment loc) =
  text (show atp) <+> text (show base) <+> printSymExpr sz <+> text (show mut) <+> text loc
ppAlloc (MemFree base) =
  text "free" <+> printSymExpr base
ppAlloc (AllocMerge c x y) = do
  text "merge" <$$> ppMerge ppAlloc c x y

ppAllocs :: IsExprBuilder sym => [MemAlloc sym] -> Doc
ppAllocs xs = vcat $ map ppAlloc xs

ppWrite :: IsExprBuilder sym => MemWrite sym -> Doc
ppWrite (MemWrite d (MemCopy s l)) = do
  text "memcopy" <+> ppPtr d <+> ppPtr s <+> printSymExpr l
ppWrite (MemWrite d (MemSet v l)) = do
  text "memset" <+> ppPtr d <+> printSymExpr v <+> printSymExpr l
ppWrite (MemWrite d (MemStore v _ _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> ppTermExpr v
ppWrite (MemWrite d (MemArrayStore arr _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> printSymExpr arr
ppWrite (WriteMerge c x y) = do
  text "merge" <$$> ppMerge ppWrite c x y

ppMemChanges :: IsExprBuilder sym => MemChanges sym -> Doc
ppMemChanges (al,wl) =
  text "Allocations:" <$$>
  indent 2 (vcat (map ppAlloc al)) <$$>
  text "Writes:" <$$>
  indent 2 (vcat (map ppWrite wl))

ppMemState :: (MemChanges sym -> Doc) -> MemState sym -> Doc
ppMemState f (EmptyMem _ _ d) = do
  text "Base memory" <$$> indent 2 (f d)
ppMemState f (StackFrame _ _ d ms) = do
  text "Stack frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms
ppMemState f (BranchFrame _ _ d ms) = do
  text "Branch frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms

ppMem :: IsExprBuilder sym => Mem sym -> Doc
ppMem m = ppMemState ppMemChanges (m^.memState)
