-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.CFG.Reg
-- Description      : Provides a representation of Crucible programs using
--                    mutable registers rather than SSA.
-- Copyright        : (c) Galois, Inc 2014-2016
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines CFGs which feature mutable registers, in contrast
-- to the Core CFGs, which are in SSA form.  Register CFGs can be
-- translated into SSA registers using the SSAConversion module.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.Crucible.CFG.Reg
  ( -- * CFG
    CFG(..)
  , cfgInputTypes
  , cfgReturnType
  , SomeCFG(..)
  , Label(..)
  , LambdaLabel(..)
  , BlockID(..)
  , Reg(..)

    -- * Atoms
  , Atom(..)
  , AtomSource(..)
  , mkInputAtoms
  , AtomValue(..)
  , typeOfAtomValue

    -- * Values
  , Value(..)
  , typeOfValue
  , ValueSet

    -- * Blocks
  , Block
  , mkBlock
  , blockID
  , blockStmts
  , blockTerm
  , blockKnownInputs
  , blockAssignedValues

    -- * Statements
  , Stmt(..)
  , TermStmt(..)
  , termStmtInputs
  , termNextLabels

    -- * Expressions
  , Expr(..)
  , exprType

    -- * Re-exports
  , module Lang.Crucible.CFG.Common
  ) where

import qualified Data.Foldable as Fold
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Sequence (Seq)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Syntax (IsExpr(..))
import           Lang.Crucible.Types

-- | Print list of documents separated by commas and spaces.
commas :: [Doc] -> Doc
commas l = hcat (punctuate (comma <> char ' ') l)

------------------------------------------------------------------------
-- Label

-- | A label for a block that does not expect an input.
newtype Label s = Label { labelInt :: Int }

instance Eq (Label s) where
  Label i == Label j = i == j

instance Ord (Label s) where
  Label i `compare` Label j = i `compare` j

instance Show (Label s) where
  show (Label i) = '%' : show i

instance Pretty (Label s) where
  pretty = text . show

------------------------------------------------------------------------
-- LambdaLabel

-- | A label for a block that expects an argument of a specific type.
data LambdaLabel (s :: *) (tp :: CrucibleType)
   = LambdaLabel
      { lambdaInt :: !Int
        -- ^ Integer that uniquely identifies this label within the CFG.
      , lambdaAtom :: Atom s tp
        -- ^ The atom to store the output result in.
        --
        -- Note. This must be lazy to break a recursive cycle.
      }

instance Show (LambdaLabel s tp) where
  show l = '%' : show (lambdaInt l)

instance Pretty (LambdaLabel s tp) where
  pretty = text . show

------------------------------------------------------------------------
-- BlockID

-- | A label for a block is either a standard label, or a label expecting an input.
data BlockID (s :: *) where
  LabelID :: Label s -> BlockID s
  LambdaID :: LambdaLabel s tp -> BlockID s

instance Show (BlockID s) where
  show (LabelID l) = show l
  show (LambdaID l) = show l

instance Eq (BlockID s) where
  LabelID x == LabelID y = x == y
  LambdaID x == LambdaID y = lambdaInt x == lambdaInt y
  _ == _ = False

instance Ord (BlockID s) where
  LabelID  x `compare` LambdaID y = compare (labelInt x) (lambdaInt y)
  LabelID  x `compare` LabelID  y = compare x y
  LambdaID x `compare` LabelID  y = compare (lambdaInt x) (labelInt y)
  LambdaID x `compare` LambdaID y = compare (lambdaInt x) (lambdaInt y)

-----------------------------------------------------------------------
-- AtomSource

-- | Identifies what generated atom.
data AtomSource s tp
   = Assigned
     -- Input argument to function.  They are ordered before other blocks.
   | FnInput
     -- The value passed into a lambda label.  This must appear after
     -- other expressions.
   | LambdaArg !(LambdaLabel s tp)

------------------------------------------------------------------------
-- Atom

-- | An expression in the control flow graph with a unique identifier.
-- Unlike registers, atoms must be assigned exactly once.
data Atom s tp
   = Atom { atomPosition :: !Position
            -- ^ Position where register was declared (used for debugging).
          , atomId :: !Int
            -- ^ Unique identifier for atom.
          , atomSource :: !(AtomSource s tp)
            -- ^ Application used to defined expression.
          , typeOfAtom :: !(TypeRepr tp)
          }

mkInputAtoms :: forall s init . Position -> CtxRepr init -> Assignment (Atom s) init
mkInputAtoms p argTypes = Ctx.generate (Ctx.size argTypes) f
  where f :: Index init tp -> Atom s tp
        f i = Atom { atomPosition = p
                   , atomId = indexVal i
                   , atomSource = FnInput
                   , typeOfAtom = argTypes Ctx.! i
                   }

instance TestEquality (Atom s) where
  testEquality x y
    | atomId x == atomId y =
      case testEquality (typeOfAtom x) (typeOfAtom y) of
        Just Refl -> Just Refl
        Nothing -> error "Lang.Crucible.Generator.Atom testEquality: mismatched types!"
    | otherwise = Nothing

instance OrdF (Atom s) where
  compareF x y =
    case compare (atomId x) (atomId y) of
      LT -> LTF
      GT -> GTF
      EQ -> case testEquality (typeOfAtom x) (typeOfAtom y) of
              Just Refl -> EQF
              Nothing -> error "Lang.Crucible.Generator.Atom compareF: mismatched types!"

instance Show (Atom s tp) where
  show a = '$' : show (atomId a)

instance Pretty (Atom s tp) where
  pretty a = text (show a)

------------------------------------------------------------------------
-- Reg

-- | A mutable value in the control flow graph.
data Reg s tp
   = Reg { -- | Position where register was declared (used for debugging).
           regPosition :: !Position
           -- | Unique identifier for register.
         , regId :: !Int
           -- | Type of register.
         , typeOfReg :: !(TypeRepr tp)
         }

instance Pretty (Reg s tp) where
  pretty = text . show

instance Show (Reg s tp) where
  show r = 'r' : show (regId r)

instance ShowF (Reg s)

instance TestEquality (Reg s) where
  testEquality x y
    | regId x == regId y =
      case testEquality (typeOfReg x) (typeOfReg y) of
        Just Refl -> Just Refl
        Nothing -> error "Lang.Crucible.Generator.Reg testEquality: mismatched types!"
    | otherwise = Nothing

instance OrdF (Reg s) where
  compareF x y =
    case compare (regId x) (regId y) of
      LT -> LTF
      GT -> GTF
      EQ -> case testEquality (typeOfReg x) (typeOfReg y) of
              Just Refl -> EQF
              Nothing -> error "Lang.Crucible.Generator.Reg compareF: mismatched types!"

------------------------------------------------------------------------
-- Primitive operations

instance TestEquality (LambdaLabel s) where
  testEquality x y
    | lambdaInt x == lambdaInt y =
        case testEquality (typeOfAtom (lambdaAtom x)) (typeOfAtom (lambdaAtom y)) of
          Just Refl -> Just Refl
          Nothing   -> error "Lang.Crucible.LambdaLabel testEquality: type mismatch!"
    | otherwise = Nothing

instance OrdF (LambdaLabel s) where
  compareF x y
    | lambdaInt x < lambdaInt y = LTF
    | lambdaInt x == lambdaInt y =
        case testEquality (typeOfAtom (lambdaAtom x)) (typeOfAtom (lambdaAtom y)) of
          Just Refl -> EQF
          Nothing   -> error "Lang.Crucible.LambdaLabel testEquality: type mismatch!"
    | otherwise = GTF

------------------------------------------------------------------------
-- SomeValue and ValueSet

data Value s tp
   = RegValue  !(Reg s tp)
   | AtomValue !(Atom s tp)

instance TestEquality (Value s) where
  testEquality (RegValue  x) (RegValue y)  = testEquality x y
  testEquality (AtomValue x) (AtomValue y) = testEquality x y
  testEquality _ _ = Nothing

instance OrdF (Value s) where
  compareF (RegValue x) (RegValue y) = compareF x y
  compareF RegValue{} _ = LTF
  compareF _ RegValue{} = GTF
  compareF (AtomValue x) (AtomValue y) = compareF x y

instance Show (Value s tp) where
  show (RegValue  r) = show r
  show (AtomValue a) = show a

instance ShowF (Value s)

typeOfValue :: Value s tp -> TypeRepr tp
typeOfValue (RegValue r) = typeOfReg r
typeOfValue (AtomValue a) = typeOfAtom a

-- | A set of values
type ValueSet s = Set (Some (Value s))

------------------------------------------------------------------------
-- Expr

-- | An expression in RTL representation.
data Expr ext s tp
  = App !(App ext (Expr ext s) tp)
    -- ^ An application of an expression
  | AtomExpr !(Atom s tp)
    -- ^ An evaluated expession

instance PrettyExt ext => Pretty (Expr ext s tp) where
  pretty (App a) = ppApp pretty a
  pretty (AtomExpr a) = pretty a

instance PrettyExt ext => Show (Expr ext s tp) where
  show e = show (pretty e)

instance PrettyExt ext => ShowF (Expr ext s)

instance TypeApp (ExprExtension ext) => IsExpr (Expr ext s) where
  type ExprExt (Expr ext s) = ext
  app = App
  asApp (App x) = Just x
  asApp _ = Nothing

  -- exprType :: Expr s tp -> TypeRepr tp
  exprType (App a)          = appType a
  exprType (AtomExpr a)     = typeOfAtom a

instance IsString (Expr ext s StringType) where
  fromString s = App (TextLit (fromString s))



------------------------------------------------------------------------
-- AtomValue

-- | The value of an assigned atom.
data AtomValue ext s tp where
  -- Evaluate an expression
  EvalApp :: !(App ext (Atom s) tp) -> AtomValue ext s tp
  -- Read a value from a register
  ReadReg :: !(Reg s tp) -> AtomValue ext s tp
  -- Evaluate an extension statement
  EvalExt :: !(StmtExtension ext (Atom s) tp) -> AtomValue ext s tp
  -- Read from a global vlalue
  ReadGlobal :: !(GlobalVar tp) -> AtomValue ext s tp
  -- Read from a reference cell
  ReadRef :: !(Atom s (ReferenceType tp)) -> AtomValue ext s tp
  -- Create a fresh reference cell
  NewRef :: !(Atom s tp) -> AtomValue ext s (ReferenceType tp)
  -- Create a fresh empty reference cell
  NewEmptyRef :: !(TypeRepr tp) -> AtomValue ext s (ReferenceType tp)

  Call :: !(Atom s (FunctionHandleType args ret))
       -> !(Assignment (Atom s) args)
       -> !(TypeRepr ret)
       -> AtomValue ext s ret

instance PrettyExt ext => Pretty (AtomValue ext s tp) where
  pretty v =
    case v of
      EvalApp ap -> ppApp pretty ap
      EvalExt st -> ppApp pretty st
      ReadReg r -> pretty r
      ReadGlobal g -> text "global" <+> pretty g
      ReadRef r -> text "!" <> pretty r
      NewRef a -> text "newref" <+> pretty a
      NewEmptyRef tp -> text "emptyref" <+> pretty tp
      Call f args _ -> pretty f <> parens (commas (toListFC pretty args))

typeOfAtomValue :: (TypeApp (StmtExtension ext) , TypeApp (ExprExtension ext))
                => AtomValue ext s tp -> TypeRepr tp
typeOfAtomValue v =
  case v of
    EvalApp a -> appType a
    EvalExt stmt -> appType stmt
    ReadReg r -> typeOfReg r
    ReadGlobal r -> globalType r
    ReadRef r -> case typeOfAtom r of
                   ReferenceRepr tpr -> tpr
    NewRef a -> ReferenceRepr (typeOfAtom a)
    NewEmptyRef tp -> ReferenceRepr tp
    Call _ _ r -> r

-- | Fold over all values in an 'AtomValue'.
foldAtomValueInputs :: TraverseExt ext
                    => (forall x . Value s x -> b -> b)
                    -> AtomValue ext s tp -> b -> b
foldAtomValueInputs f (ReadReg r)     b = f (RegValue r) b
foldAtomValueInputs f (EvalExt stmt)  b = foldrFC (f . AtomValue) b stmt
foldAtomValueInputs _ (ReadGlobal _)  b = b
foldAtomValueInputs f (ReadRef r)     b = f (AtomValue r) b
foldAtomValueInputs _ (NewEmptyRef _) b = b
foldAtomValueInputs f (NewRef a)      b = f (AtomValue a) b
foldAtomValueInputs f (EvalApp app0)  b = foldApp (f . AtomValue) b app0
foldAtomValueInputs f (Call g a _)    b = f (AtomValue g) (foldrFC' (f . AtomValue) b a)

ppAtomBinding :: PrettyExt ext => Atom s tp -> AtomValue ext s tp -> Doc
ppAtomBinding a v = pretty a <+> text ":=" <+> pretty v

------------------------------------------------------------------------
-- Stmt

-- | Statement in control flow graph.
data Stmt ext s
   = forall tp . SetReg     !(Reg s tp)       !(Atom s tp)
   | forall tp . WriteGlobal  !(GlobalVar tp) !(Atom s tp)
   | forall tp . WriteRef !(Atom s (ReferenceType tp)) !(Atom s tp)
   | forall tp . DropRef  !(Atom s (ReferenceType tp))
   | forall tp . DefineAtom !(Atom s tp)      !(AtomValue ext s tp)
   | Print      !(Atom s StringType)
     -- | Assert that the given expression is true.
   | Assert !(Atom s BoolType) !(Atom s StringType)

instance PrettyExt ext => Pretty (Stmt ext s) where
  pretty s =
    case s of
      SetReg r e     -> pretty r <+> text ":=" <+> pretty e
      WriteGlobal g r  -> text "global" <+> pretty g <+> text ":=" <+> pretty r
      WriteRef r v -> text "ref" <+> pretty r <+> text ":=" <+> pretty v
      DropRef r    -> text "drop" <+> pretty r
      DefineAtom a v -> ppAtomBinding a v
      Print  v   -> text "print"  <+> pretty v
      Assert c m -> text "assert" <+> pretty c <+> pretty m

-- | Return local value assigned by this statement or @Nothing@ if this
-- does not modify a register.
stmtAssignedValue :: Stmt ext s -> Maybe (Some (Value s))
stmtAssignedValue s =
  case s of
    SetReg r _ -> Just (Some (RegValue r))
    DefineAtom a _ -> Just (Some (AtomValue a))
    WriteGlobal{} -> Nothing
    WriteRef{} -> Nothing
    DropRef{} -> Nothing
    Print{} -> Nothing
    Assert{} -> Nothing

-- | Fold all registers that are inputs tostmt.
foldStmtInputs :: TraverseExt ext => (forall x . Value s x -> b -> b) -> Stmt ext s -> b -> b
foldStmtInputs f s b =
  case s of
    SetReg _ e     -> f (AtomValue e) b
    WriteGlobal _ a  -> f (AtomValue a) b
    WriteRef r a -> f (AtomValue r) (f (AtomValue a) b)
    DropRef r    -> f (AtomValue r) b
    DefineAtom _ v -> foldAtomValueInputs f v b
    Print  e     -> f (AtomValue e) b
    Assert c m   -> f (AtomValue c) (f (AtomValue m) b)

------------------------------------------------------------------------
-- TermStmt

data TermStmt s (ret :: CrucibleType) where
  -- Jump to the given block.
  Jump :: !(Label s)
       -> TermStmt s ret
  -- Branch on condition.
  Br :: !(Atom s BoolType)
     -> !(Label s)
     -> !(Label s)
     -> TermStmt s ret
  -- Switch on whether this is a maybe value.
  MaybeBranch :: !(TypeRepr tp)
              -> !(Atom s (MaybeType tp))
              -> !(LambdaLabel s tp)
              -> !(Label s)
              -> TermStmt s ret

  -- Switch on a variant value.  Examine the tag of the variant
  -- and jump to the appropriate switch target.
  VariantElim :: !(CtxRepr varctx)
              -> !(Atom s (VariantType varctx))
              -> !(Ctx.Assignment (LambdaLabel s) varctx)
              -> TermStmt s ret

  -- Return from function.
  Return :: !(Atom s ret) -> TermStmt s ret

  -- End block with a tail call.
  TailCall :: !(Atom s (FunctionHandleType args ret))
           -> !(CtxRepr args)
           -> !(Ctx.Assignment (Atom s) args)
           -> TermStmt s ret

  -- Block ends because of a translation error.
  ErrorStmt :: !(Atom s StringType) -> TermStmt s ret

  -- Jump to the given block, and provide it the
  -- expression as input.
  Output :: !(LambdaLabel s tp)
         -> !(Atom s tp)
         -> TermStmt s ret

instance Pretty (TermStmt s ret) where
  pretty t0 =
    case t0 of
      Jump l -> text "jump" <+> pretty l
      Br c x y -> text "branch" <+> pretty c <+> pretty x <+> pretty y
      MaybeBranch _ c j n -> text "switchMaybe" <+> pretty c <+> pretty j <+> pretty n
      VariantElim _ e l ->
         text "switch" <+> pretty e <+> text "{" <$$>
           indent 2 (vcat (ppSwitch pp l)) <$$>
           indent 2 (text "}")
        where pp nm v = text nm <> text ":" <+> pretty v
      Return e -> text "return" <+> pretty e
      TailCall f _ a -> text "tail_call" <+> pretty f <> parens args
        where args = commas (toListFC pretty a)
      ErrorStmt e -> text "error" <+> pretty e
      Output l e -> text "output" <+> pretty l <+> pretty e


ppSwitch :: forall tgt ctx. (forall (tp :: CrucibleType). String -> tgt tp -> Doc) -> Ctx.Assignment tgt ctx -> [Doc]
ppSwitch pp asgn = forIndex (Ctx.size asgn) f mempty
  where f :: [Doc] -> Ctx.Index ctx (tp :: CrucibleType) -> [Doc]
        f rs idx = rs Prelude.++ [ pp (show (Ctx.indexVal idx)) (asgn Ctx.! idx)]

-- | Provide all registers in term stmt to fold function.
foldTermStmtAtoms :: (forall x . Atom s x -> b -> b)
                  -> TermStmt s ret
                  -> b
                  -> b
foldTermStmtAtoms f stmt0 b =
  case stmt0 of
    Jump _ -> b
    Output _ e -> f e b
    Br e _ _ -> f e b
    MaybeBranch _ e _ _ -> f e b
    VariantElim _ e _ -> f e b
    Return e -> f e b
    TailCall fn _ a -> f fn (foldrFC' f b a)
    ErrorStmt e -> f e b


-- | Returns set of registers appearing as inputs to terminal
-- statement.
termStmtInputs :: TermStmt s ret
               -> ValueSet s
termStmtInputs stmt = foldTermStmtAtoms (Set.insert . Some . AtomValue) stmt Set.empty


-- | Returns the next labels for the given block.  Error statements
-- have no next labels, while return/tail calls statements return Nothing.
termNextLabels :: TermStmt s ret
               -> Maybe [BlockID s]
termNextLabels s0 =
  case s0 of
    Jump l              -> Just [LabelID l]
    Output l _          -> Just [LambdaID l]
    Br _ x y            -> Just [LabelID x, LabelID y]
    MaybeBranch _ _ x y -> Just [LambdaID x, LabelID y]
    VariantElim _ _ s   -> Just $ toListFC LambdaID s
    Return _            -> Nothing
    TailCall{}          -> Nothing
    ErrorStmt _         -> Just []


------------------------------------------------------------------------
-- Block

-- | A basic block within a function.
data Block ext s (ret :: CrucibleType)
   = Block { blockID           :: !(BlockID s)
           , blockStmts        :: !(Seq (Posd (Stmt ext s)))
           , blockTerm         :: !(Posd (TermStmt s ret))
             -- | Registers that are known to be needed as inputs for this block.
             -- For the first block, this includes the function arguments.
             -- It also includes registers read by this block before they are
             -- assigned.
             -- It does not include the lambda reg for lambda blocks.
           , blockKnownInputs  :: !(ValueSet s)
             -- | Registers assigned by statements in block.
             -- This is a field so that it's value can be memoized.
           , blockAssignedValues :: !(ValueSet s)
           }

instance Eq (Block ext s ret) where
  x == y = blockID x == blockID y

instance Ord (Block ext s ret) where
  compare x y = compare (blockID x) (blockID y)

instance PrettyExt ext => Pretty (Block ext s ret) where
  pretty b = text (show (blockID b)) <$$> indent 2 stmts
    where stmts = vcat (pretty . pos_val <$> Fold.toList (blockStmts b)) <$$>
                  pretty (pos_val (blockTerm b))

mkBlock :: forall ext s ret
         . TraverseExt ext
        => BlockID s
        -> ValueSet s -- ^ Extra inputs to block (only non-empty for initial block)
        -> Seq (Posd (Stmt ext s))
        -> Posd (TermStmt s ret)
        -> Block ext s ret
mkBlock block_id inputs stmts term =
  Block { blockID    = block_id
        , blockStmts = stmts
        , blockTerm  = term
        , blockAssignedValues = assigned_values
        , blockKnownInputs  = all_input_values
        }
 where inputs_with_lambda =
         case block_id of
           LabelID{} -> inputs
           LambdaID l -> Set.insert (Some (AtomValue (lambdaAtom l))) inputs

       initState = (inputs_with_lambda, inputs)

       addUnassigned :: ValueSet s -> Value s x -> ValueSet s -> ValueSet s
       addUnassigned ar r s
         | Set.member (Some r) ar = s
         | otherwise = Set.insert (Some r) s

       all_input_values
         = foldTermStmtAtoms (addUnassigned assigned_values . AtomValue)
                             (pos_val term)
                             missing_values

       -- Function for inserting updating assigned regs, missing regs
       -- with statement.
       f :: (ValueSet s, ValueSet s) -> Posd (Stmt ext s) -> (ValueSet s, ValueSet s)
       f (ar, mr) s = (ar', mr')
         where ar' = case stmtAssignedValue (pos_val s) of
                       Nothing -> ar
                       Just  r -> Set.insert r ar
               mr' = foldStmtInputs (addUnassigned ar) (pos_val s) mr

       (assigned_values, missing_values) = Fold.foldl' f initState stmts

------------------------------------------------------------------------
-- CFG

-- | A CFG using registers instead of SSA form.
data CFG ext s init ret
   = CFG { cfgHandle :: !(FnHandle init ret)
         , cfgBlocks :: !([Block ext s ret])
         }

cfgInputTypes :: CFG ext s init ret -> CtxRepr init
cfgInputTypes g = handleArgTypes (cfgHandle g)

cfgReturnType :: CFG ext s init ret -> TypeRepr ret
cfgReturnType g = handleReturnType (cfgHandle g)

instance PrettyExt ext => Show (CFG ext s init ret) where
  show = show . pretty

instance PrettyExt ext => Pretty (CFG ext s init ret) where
  pretty g = do
    let nm = text (show (handleName (cfgHandle g)))
    let inputs = mkInputAtoms InternalPos (cfgInputTypes g)
    let args = commas $ toListFC pretty inputs
    pretty (cfgReturnType g) <+> nm <+> parens args <$$>
      vcat (pretty <$> cfgBlocks g)

------------------------------------------------------------------------
-- SomeCFG

-- | 'SomeCFG' is a CFG with an arbitrary parameter 's'.
data SomeCFG ext init ret = forall s . SomeCFG !(CFG ext s init ret)
