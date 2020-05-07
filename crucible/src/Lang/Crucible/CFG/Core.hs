{- |
Module           : Lang.Crucible.CFG.Core
Description      : SSA-based control flow graphs
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Define a SSA-based control flow graph data structure using a side-effect free
expression syntax.

Unlike usual SSA forms, we do not use phi-functions, but instead rely on an
argument-passing formulation for basic blocks.  In this form, concrete values
are bound to formal parameters instead of using phi-functions that switch
on the place from which you jumped.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Lang.Crucible.CFG.Core
  ( -- * CFG
    CFG(..)
  , SomeCFG(..)
  , HasSomeCFG(..)
  , AnyCFG(..)
  , ppCFG
  , ppCFG'
  , cfgArgTypes
  , cfgReturnType
  , CFGPostdom

    -- * Blocks
  , BlockMap
  , getBlock
  , extendBlockMap

  , BlockID(..)
  , extendBlockID
  , extendBlockID'

  , Block(..)
  , blockLoc
  , blockStmts
  , withBlockTermStmt
  , nextBlocks

    -- * Jump targets
  , JumpTarget(..)
  , extendJumpTarget
  , jumpTargetID
  , SwitchTarget(..)
  , switchTargetID
  , extendSwitchTarget

    -- * Statements
  , StmtSeq(..)
  , firstStmtLoc
  , stmtSeqTermStmt
  , Stmt(..)
  , ppStmt
  , nextStmtHeight

  , applyEmbeddingStmt

  , TermStmt(..)
  , termStmtNextBlocks

    -- * Expressions
  , Expr(..)
  , Reg(..)
  , extendReg
  , lastReg

    -- * Re-exports
  , module Lang.Crucible.Types
  , module Lang.Crucible.CFG.Common
  , module Data.Parameterized.Classes
  , module Data.Parameterized.Some
  ) where

import Control.Applicative
import Control.Lens
import Data.Bimap (Bimap)
import Data.Maybe (fromMaybe)
import Data.Kind (Type)
import Data.Parameterized.Classes
import Data.Parameterized.Map (Pair(..))
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.String
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import What4.Symbol

import Lang.Crucible.CFG.Common
import Lang.Crucible.CFG.Expr
import Lang.Crucible.FunctionHandle
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Types
import Lang.Crucible.Utils.PrettyPrint

#ifdef UNSAFE_OPS
-- We deliberately import Context.Unsafe as it is the only one that supports
-- the unsafe coerces between an index and its extension.
import Data.Parameterized.Context as Ctx hiding (Assignment)
import Data.Parameterized.Context.Unsafe as Ctx (Assignment)
import Unsafe.Coerce
#else
import Data.Parameterized.Context as Ctx
#endif

------------------------------------------------------------------------
-- Reg

-- | A temporary register identifier introduced during translation.
--   These are unique to the current function.  The `ctx` parameter
--   is a context containing the types of all the temporary registers
--   currently in scope, and the `tp` parameter indicates the type
--   of this register (which necessarily appears somewhere in `ctx`)
newtype Reg (ctx :: Ctx CrucibleType) (tp :: CrucibleType) = Reg { regIndex :: Ctx.Index ctx tp }
  deriving (Eq, TestEquality, Ord, OrdF)

instance Show (Reg ctx tp) where
  show (Reg i) = '$' : show (indexVal i)

instance ShowF (Reg ctx)

instance Pretty (Reg ctx tp) where
  pretty = text.show

instance ApplyEmbedding' Reg where
  applyEmbedding' ctxe r = Reg $ applyEmbedding' ctxe (regIndex r)

instance ExtendContext' Reg where
  extendContext' diff r = Reg $ extendContext' diff (regIndex r)

-- | Finds the value of the most-recently introduced register in scope.
lastReg :: KnownContext ctx => Reg (ctx ::> tp) tp
lastReg = Reg (nextIndex knownSize)

-- | Extend the set of registers in scope for a given register value
--   without changing its index or type.
extendReg :: Reg ctx tp -> Reg (ctx ::> r) tp
extendReg = Reg . extendIndex . regIndex

------------------------------------------------------------------------
-- Expr

-- | An expression is just an App applied to some registers.
newtype Expr ext (ctx :: Ctx CrucibleType) (tp :: CrucibleType)
      = App (App ext (Reg ctx) tp)

instance IsString (Expr ext ctx (StringType Unicode)) where
  fromString  = App . StringLit . fromString

instance PrettyApp (ExprExtension ext) => Pretty (Expr ext ctx tp) where
  pretty (App a) = ppApp pretty a

ppAssignment :: Assignment (Reg ctx) args -> [Doc]
ppAssignment = toListFC pretty

instance ( TraversableFC (ExprExtension ext)
         ) => ApplyEmbedding' (Expr ext) where
  applyEmbedding' ctxe (App e) = App (mapApp (applyEmbedding' ctxe) e)

instance ( TraversableFC (ExprExtension ext)
         ) => ExtendContext' (Expr ext) where
  extendContext' diff (App e) = App (mapApp (extendContext' diff) e)

------------------------------------------------------------------------
-- BlockID

-- | A `BlockID` uniquely identifies a block in a control-flow graph.
--   Each block has an associated context, indicating the formal arguments
--   it expects to find in registers from its calling locations.
newtype BlockID (blocks :: Ctx (Ctx CrucibleType)) (tp :: Ctx CrucibleType)
      = BlockID { blockIDIndex :: Ctx.Index blocks tp }
  deriving (Eq, Ord)

instance TestEquality (BlockID blocks) where
  testEquality (BlockID x) (BlockID y) = testEquality x y

instance OrdF (BlockID blocks) where
  compareF (BlockID x) (BlockID y) = compareF x y

instance Pretty (BlockID blocks tp) where
  pretty (BlockID i) = char '%' <> int (indexVal i)

instance Show (BlockID blocks ctx) where
  show (BlockID i) = '%' : show (indexVal i)

instance ShowF (BlockID blocks)

extendBlockID :: KnownDiff l r => BlockID l tp -> BlockID r tp
extendBlockID = BlockID . extendIndex . blockIDIndex

extendBlockID' :: Diff l r -> BlockID l tp -> BlockID r tp
extendBlockID' e = BlockID . extendIndex' e . blockIDIndex

------------------------------------------------------------------------
-- JumpTarget

-- | Target for jump and branch statements
data JumpTarget blocks ctx where
     JumpTarget :: !(BlockID blocks args)            -- BlockID to jump to
                -> !(CtxRepr args)                   -- expected argument types
                -> !(Assignment (Reg ctx) args) -- jump target actual arguments
                -> JumpTarget blocks ctx

instance Pretty (JumpTarget blocks ctx) where
  pretty (JumpTarget tgt _ a) = pretty tgt <> parens (commas (ppAssignment a))

jumpTargetID :: JumpTarget blocks ctx -> Some (BlockID blocks)
jumpTargetID (JumpTarget tgt _ _) = Some tgt

extendJumpTarget :: Diff blocks' blocks -> JumpTarget blocks' ctx -> JumpTarget blocks ctx
extendJumpTarget diff (JumpTarget b tps a) = JumpTarget (extendBlockID' diff b) tps a

instance ApplyEmbedding (JumpTarget blocks) where
  applyEmbedding ctxe (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (applyEmbedding' ctxe) args)

instance ExtendContext (JumpTarget blocks) where
  extendContext diff (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (extendContext' diff) args)

------------------------------------------------------------------------
-- SwitchTarget

-- | Target for a switch statement.
data SwitchTarget blocks ctx tp where
  SwitchTarget :: !(BlockID blocks (args ::> tp))   -- BlockID to jump to
               -> !(CtxRepr args)                   -- expected argument types
               -> !(Assignment (Reg ctx) args) -- switch target actual arguments
               -> SwitchTarget blocks ctx tp

switchTargetID :: SwitchTarget blocks ctx tp -> Some (BlockID blocks)
switchTargetID (SwitchTarget tgt _ _) = Some tgt

ppCase :: String -> SwitchTarget blocks ctx tp -> Doc
ppCase nm (SwitchTarget tgt _ a) =
  text nm <+> text "->" <+> pretty tgt <> parens (commas (ppAssignment a))

extendSwitchTarget :: Diff blocks' blocks
                   -> SwitchTarget blocks' ctx tp
                   -> SwitchTarget blocks ctx tp
extendSwitchTarget diff (SwitchTarget b tps a) =
    SwitchTarget (extendBlockID' diff b) tps a

instance ApplyEmbedding' (SwitchTarget blocks) where
  applyEmbedding' ctxe (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (applyEmbedding' ctxe) args)

instance ExtendContext' (SwitchTarget blocks) where
  extendContext' diff (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (extendContext' diff) args)


------------------------------------------------------------------------
-- Stmt

-- | A sequential statement that does not affect the
-- program location within the current block or leave the current
-- block.
data Stmt ext (ctx :: Ctx CrucibleType) (ctx' :: Ctx CrucibleType) where
  -- Assign the value of a register
  SetReg :: !(TypeRepr tp)
         -> !(Expr ext ctx tp)
         -> Stmt ext ctx (ctx ::> tp)

  -- Assign a register via an extension statement
  ExtendAssign :: !(StmtExtension ext (Reg ctx) tp)
               -> Stmt ext ctx (ctx ::> tp)

  -- Statement used for evaluating function calls
  CallHandle :: !(TypeRepr ret)                          -- The type of the return value(s)
             -> !(Reg ctx (FunctionHandleType args ret)) -- The function handle to call
             -> !(CtxRepr args)                          -- The expected types of the arguments
             -> !(Assignment (Reg ctx) args)             -- The actual arguments to the call
             -> Stmt ext ctx (ctx ::> ret)

  -- Print a message out to the console
  Print :: !(Reg ctx (StringType Unicode)) -> Stmt ext ctx ctx

  -- Read a global variable.
  ReadGlobal :: !(GlobalVar tp)
             -> Stmt ext ctx (ctx ::> tp)

  -- Write to a global variable.
  WriteGlobal :: !(GlobalVar tp)
              -> !(Reg ctx tp)
              -> Stmt ext ctx ctx

  -- Create a fresh constant
  FreshConstant :: !(BaseTypeRepr bt)
                -> !(Maybe SolverSymbol)
                -> Stmt ext ctx (ctx ::> BaseToType bt)

  -- Create a fresh floating-point constant
  FreshFloat :: !(FloatInfoRepr fi)
             -> !(Maybe SolverSymbol)
             -> Stmt ext ctx (ctx ::> FloatType fi)

  -- Allocate a new reference cell
  NewRefCell :: !(TypeRepr tp)
             -> !(Reg ctx tp)
             -> Stmt ext ctx (ctx ::> ReferenceType tp)

  -- Allocate a new, unassigned reference cell
  NewEmptyRefCell :: !(TypeRepr tp)
                  -> Stmt ext ctx (ctx ::> ReferenceType tp)

  -- Read the current value of a reference cell
  ReadRefCell :: !(Reg ctx (ReferenceType tp))
              -> Stmt ext ctx (ctx ::> tp)

  -- Write the current value of a reference cell
  WriteRefCell :: !(Reg ctx (ReferenceType tp))
               -> !(Reg ctx tp)
               -> Stmt ext ctx ctx

  -- Deallocate the storage associated with a reference cell
  DropRefCell  :: !(Reg ctx (ReferenceType tp))
               -> Stmt ext ctx ctx

  -- Assert a boolean condition.  If the condition fails, print the given string.
  Assert :: !(Reg ctx BoolType) -> !(Reg ctx (StringType Unicode)) -> Stmt ext ctx ctx

  -- Assume a boolean condition, remembering the given string as the 'reason' for this assumption.
  Assume :: !(Reg ctx BoolType) -> !(Reg ctx (StringType Unicode)) -> Stmt ext ctx ctx

------------------------------------------------------------------------
-- TermStmt

data TermStmt blocks (ret :: CrucibleType) (ctx :: Ctx CrucibleType) where
  -- Jump to the given jump target
  Jump :: !(JumpTarget blocks ctx)
       -> TermStmt blocks ret ctx

  -- Branch on condition.  If true, jump to the first jump target; otherwise
  -- jump to the second jump target.
  Br :: !(Reg ctx BoolType)
     -> !(JumpTarget blocks ctx)
     -> !(JumpTarget blocks ctx)
     -> TermStmt blocks ret ctx

  -- Switch on whether this is a maybe value.  Jump to the switch target if
  -- the maybe value is a "Some".  Otherwise (if "Nothing"), jump to the jump target.
  MaybeBranch :: !(TypeRepr tp)
              -> !(Reg ctx (MaybeType tp))
              -> !(SwitchTarget blocks ctx tp)
              -> !(JumpTarget blocks ctx)
              -> TermStmt blocks rtp ctx

  -- Switch on a variant value.  Examine the tag of the variant
  -- and jump to the appropriate switch target.
  VariantElim :: !(CtxRepr varctx)
              -> !(Reg ctx (VariantType varctx))
              -> !(Assignment (SwitchTarget blocks ctx) varctx)
              -> TermStmt blocks ret ctx

  -- Return from function, providing the return value(s).
  Return :: !(Reg ctx ret)
         -> TermStmt blocks ret ctx

  -- End block with a tail call.
  TailCall :: !(Reg ctx (FunctionHandleType args ret))
           -> !(CtxRepr args)
           -> !(Assignment (Reg ctx) args)
           -> TermStmt blocks ret ctx

  -- Block ends with an error.
  ErrorStmt :: !(Reg ctx (StringType Unicode)) -> TermStmt blocks ret ctx

#ifndef UNSAFE_OPS
extendTermStmt :: Diff blocks' blocks -> TermStmt blocks' ret ctx -> TermStmt blocks ret ctx
extendTermStmt diff (Jump tgt) = Jump (extendJumpTarget diff tgt)
extendTermStmt diff (Br c x y) = Br c (extendJumpTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (MaybeBranch tp c x y) =
  MaybeBranch tp c (extendSwitchTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (VariantElim ctx e asgn) =
  VariantElim ctx e (fmapFC (extendSwitchTarget diff) asgn)
extendTermStmt _diff (Return e) = Return e
extendTermStmt _diff (TailCall h tps args) = TailCall h tps args
extendTermStmt _diff (ErrorStmt e) = ErrorStmt e
#endif

-- | Return the set of possible next blocks from a TermStmt
termStmtNextBlocks :: TermStmt b ret ctx -> Maybe [Some (BlockID b)]
termStmtNextBlocks s0 =
  case s0 of
    Jump tgt             -> Just [ jumpTargetID tgt ]
    Br          _ x y    -> Just [ jumpTargetID x, jumpTargetID y ]
    MaybeBranch _ _ x y  -> Just [ switchTargetID x, jumpTargetID y ]
    VariantElim _ _ a    -> Just (toListFC switchTargetID a)
    Return      _        -> Nothing
    TailCall    _ _ _    -> Nothing
    ErrorStmt   _        -> Just []

instance Pretty (TermStmt blocks ret ctx) where
 pretty s =
  case s of
    Jump b   -> text "jump" <+> pretty b
    Br e x y -> text "br"  <+> pretty e <+> pretty x <+> pretty y
    MaybeBranch _ e j n ->
      text "maybeBranch" <+> pretty e <+> lbrace <$$>
        indent 2 (
          vcat [ ppCase "Just" j
               , text "Nothing ->" <+> pretty n
               ] <$$>
          rbrace)
    VariantElim _ e asgn ->
      let branches =
              [ f (show i) <> semi
              | i <- [(0::Int) .. ]
              | f <- toListFC (\tgt nm -> ppCase nm tgt) asgn
              ] in
      text "vswitch" <+> pretty e <+> lbrace <$$>
       indent 2 (vcat branches) <$$>
       rbrace
    Return e ->
      text "return"
       <+> pretty e
    TailCall h _ args ->
      text "tailCall"
       <+> pretty h
       <+> parens (commas (ppAssignment args))
    ErrorStmt msg ->
      text "error" <+> pretty msg


applyEmbeddingStmt :: forall ext ctx ctx' sctx.
                      TraverseExt ext =>
                      CtxEmbedding ctx ctx' ->
                      Stmt ext ctx sctx ->
                      Pair (Stmt ext ctx') (CtxEmbedding sctx)
applyEmbeddingStmt ctxe stmt =
  case stmt of
    SetReg tp e -> Pair (SetReg tp (applyEmbedding' ctxe e))
                        (extendEmbeddingBoth ctxe)

    ExtendAssign estmt ->
       Pair (ExtendAssign (fmapFC (Ctx.applyEmbedding' ctxe) estmt))
            (Ctx.extendEmbeddingBoth ctxe)

    CallHandle ret hdl tys args ->
      Pair (CallHandle ret (reg hdl) tys (fmapFC reg args))
           (extendEmbeddingBoth ctxe)

    Print str -> Pair (Print (reg str)) ctxe

    ReadGlobal var -> Pair (ReadGlobal var)
                           (extendEmbeddingBoth ctxe)

    WriteGlobal var r -> Pair (WriteGlobal var (reg r)) ctxe

    FreshConstant bt nm -> Pair (FreshConstant bt nm)
                                (Ctx.extendEmbeddingBoth ctxe)

    FreshFloat fi nm -> Pair (FreshFloat fi nm)
                             (Ctx.extendEmbeddingBoth ctxe)

    NewRefCell tp r -> Pair (NewRefCell tp (reg r))
                            (Ctx.extendEmbeddingBoth ctxe)
    NewEmptyRefCell tp -> Pair (NewEmptyRefCell tp)
                               (Ctx.extendEmbeddingBoth ctxe)
    ReadRefCell r     -> Pair (ReadRefCell (reg r))
                              (Ctx.extendEmbeddingBoth ctxe)
    WriteRefCell r r' -> Pair (WriteRefCell (reg r) (reg r')) ctxe
    DropRefCell r     -> Pair (DropRefCell (reg r)) ctxe
    Assert b str      -> Pair (Assert (reg b) (reg str)) ctxe
    Assume b str      -> Pair (Assume (reg b) (reg str)) ctxe
  where
    reg :: forall tp. Reg ctx tp -> Reg ctx' tp
    reg = applyEmbedding' ctxe


instance ApplyEmbedding (TermStmt blocks ret) where
  applyEmbedding :: forall ctx ctx'.
                    CtxEmbedding ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  applyEmbedding ctxe term =
    case term of
      Jump jt -> Jump (apC jt)
      Br b jtl jtr -> Br (apC' b) (apC jtl) (apC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (apC' b) (apC' swt) (apC jt)
      VariantElim repr r targets -> VariantElim repr (apC' r) (fmapFC apC' targets)
      Return r -> Return (apC' r)
      TailCall hdl tys args -> TailCall (apC' hdl) tys (fmapFC apC' args)
      ErrorStmt r -> ErrorStmt (apC' r)
    where
      apC' :: forall f v. ApplyEmbedding' f => f ctx v -> f ctx' v
      apC' = applyEmbedding' ctxe

      apC :: forall f. ApplyEmbedding  f => f ctx -> f ctx'
      apC  = applyEmbedding  ctxe

instance ExtendContext (TermStmt blocks ret) where
  extendContext :: forall ctx ctx'.
                    Diff ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  extendContext diff term =
    case term of
      Jump jt -> Jump (extC jt)
      Br b jtl jtr -> Br (extC' b) (extC jtl) (extC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (extC' b) (extC' swt) (extC jt)
      VariantElim repr r targets -> VariantElim repr (extC' r) (fmapFC extC' targets)
      Return r -> Return (extC' r)
      TailCall hdl tys args -> TailCall (extC' hdl) tys (fmapFC extC' args)
      ErrorStmt r -> ErrorStmt (extC' r)
    where
      extC' :: forall f v. ExtendContext' f => f ctx v -> f ctx' v
      extC' = extendContext' diff

      extC :: forall f. ExtendContext  f => f ctx -> f ctx'
      extC  = extendContext  diff


------------------------------------------------------------------------
-- StmtSeq

-- | A sequence of straight-line program statements that end with
--   a terminating statement (return, jump, etc).
data StmtSeq ext blocks (ret :: CrucibleType) ctx where
  ConsStmt :: !ProgramLoc
           -> !(Stmt ext ctx ctx')
           -> !(StmtSeq ext blocks ret ctx')
           -> StmtSeq ext blocks ret ctx
  TermStmt :: !ProgramLoc
           -> !(TermStmt blocks ret ctx)
           -> (StmtSeq ext blocks ret ctx)

-- | Return the location of a statement.
firstStmtLoc :: StmtSeq ext b r ctx -> ProgramLoc
firstStmtLoc (ConsStmt pl _ _) = pl
firstStmtLoc (TermStmt pl _) = pl

-- | A lens-like operation that gives one access to program location and term statement,
-- and allows the terminal statement to be replaced with an arbitrary sequence of
-- statements.
stmtSeqTermStmt :: Functor f
                => (forall ctx
                    . (ProgramLoc, TermStmt b ret ctx)
                    -> f (StmtSeq ext b' ret ctx))
                -> StmtSeq ext b ret args
                -> f (StmtSeq ext b' ret args)
stmtSeqTermStmt f (ConsStmt l s t) = ConsStmt l s <$> stmtSeqTermStmt f t
stmtSeqTermStmt f (TermStmt p t) = f (p, t)

ppReg :: Size ctx -> Doc
ppReg h = text "$" <> int (sizeInt h)

nextStmtHeight :: Size ctx -> Stmt ext ctx ctx' -> Size ctx'
nextStmtHeight h s =
  case s of
    SetReg{} -> incSize h
    ExtendAssign{} -> incSize h
    CallHandle{} -> incSize h
    Print{} -> h
    ReadGlobal{} -> incSize h
    WriteGlobal{} -> h
    FreshConstant{} -> Ctx.incSize h
    FreshFloat{} -> Ctx.incSize h
    NewRefCell{} -> Ctx.incSize h
    NewEmptyRefCell{} ->Ctx.incSize h
    ReadRefCell{} -> Ctx.incSize h
    WriteRefCell{} -> h
    DropRefCell{}  -> h
    Assert{} -> h
    Assume{} -> h

ppStmt :: PrettyExt ext => Size ctx -> Stmt ext ctx ctx' -> Doc
ppStmt r s =
  case s of
    SetReg _ e -> ppReg r <+> text "=" <+> pretty e
    ExtendAssign s' -> ppReg r <+> text "=" <+> ppApp pretty s'
    CallHandle _ h _ args ->
      ppReg r <+> text "= call"
              <+> pretty h <> parens (commas (ppAssignment args))
               <> text ";"
    Print msg -> ppFn "print" [ pretty msg ]
    ReadGlobal v -> text "read" <+> ppReg r <+> pretty v
    WriteGlobal v e -> text "write" <+> pretty v <+> pretty e
    FreshConstant bt nm -> ppReg r <+> text "=" <+> text "fresh" <+> pretty bt <+> maybe mempty (text . show) nm
    FreshFloat fi nm -> ppReg r <+> text "=" <+> text "fresh-float" <+> pretty fi <+> maybe mempty (text . show) nm
    NewRefCell _ e -> ppReg r <+> text "=" <+> ppFn "newref" [ pretty e ]
    NewEmptyRefCell tp -> ppReg r <+> text "=" <+> ppFn "emptyref" [ pretty tp ]
    ReadRefCell e -> ppReg r <+> text "= !" <> pretty e
    WriteRefCell r1 r2 -> pretty r1 <+> text ":=" <+> pretty r2
    DropRefCell r1 -> text "drop" <+> pretty r1
    Assert c e -> ppFn "assert" [ pretty c, pretty e ]
    Assume c e -> ppFn "assume" [ pretty c, pretty e ]

prefixLineNum :: Bool -> ProgramLoc -> Doc -> Doc
prefixLineNum True pl d = text "%" <+> ppNoFileName (plSourceLoc pl) <$$> d
prefixLineNum False _ d = d

ppStmtSeq :: PrettyExt ext => Bool -> Size ctx -> StmtSeq ext blocks ret ctx -> Doc
ppStmtSeq ppLineNum h (ConsStmt pl s r) =
  prefixLineNum ppLineNum pl (ppStmt h s) <$$>
  ppStmtSeq ppLineNum (nextStmtHeight h s) r
ppStmtSeq ppLineNum _ (TermStmt pl s) =
  prefixLineNum ppLineNum pl (pretty s)


#ifndef UNSAFE_OPS
extendStmtSeq :: Diff blocks' blocks -> StmtSeq ext blocks' ret ctx -> StmtSeq ext blocks ret ctx
extendStmtSeq diff (ConsStmt p s l) = ConsStmt p s (extendStmtSeq diff l)
extendStmtSeq diff (TermStmt p s) = TermStmt p (extendTermStmt diff s)
#endif


instance TraverseExt ext => ApplyEmbedding (StmtSeq ext blocks ret) where
  applyEmbedding ctxe (ConsStmt loc stmt rest) =
    case applyEmbeddingStmt ctxe stmt of
      Pair stmt' ctxe' -> ConsStmt loc stmt' (applyEmbedding ctxe' rest)
  applyEmbedding ctxe (TermStmt loc term) =
    TermStmt loc (applyEmbedding ctxe term)



------------------------------------------------------------------------
-- CFGPostdom

-- | Postdominator information about a CFG.  The assignment maps each block
--   to the postdominators of the given block.  The postdominators are ordered
--   with nearest postdominator first.
type CFGPostdom blocks = Assignment (Const [Some (BlockID blocks)]) blocks

emptyCFGPostdomInfo :: Size blocks -> CFGPostdom blocks
emptyCFGPostdomInfo sz = Ctx.replicate sz (Const [])


------------------------------------------------------------------------
-- Block

-- | A basic block within a function.
data Block ext (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType) ctx
   = Block { blockID        :: !(BlockID blocks ctx)
             -- ^ The unique identifier of this block
           , blockInputs    :: !(CtxRepr ctx)
             -- ^ The expected types of the formal arguments to this block
           , _blockStmts    :: !(StmtSeq ext blocks ret ctx)
             -- ^ The sequence of statements in this block
           }

blockStmts :: Simple Lens (Block ext b r c) (StmtSeq ext b r c)
blockStmts = lens _blockStmts (\b s -> b { _blockStmts = s })

-- | Return location of start of block.
blockLoc :: Block ext blocks ret ctx -> ProgramLoc
blockLoc b = firstStmtLoc (b^.blockStmts)

-- | Get the terminal statement of a basic block.  This is implemented
-- in a CPS style due to the block context.
withBlockTermStmt :: Block ext blocks ret args
                  -> (forall ctx . ProgramLoc -> TermStmt blocks ret ctx -> r)
                  -> r
withBlockTermStmt b f = getConst (stmtSeqTermStmt (Const . uncurry f) (b^.blockStmts))

nextBlocks :: Block ext b r a -> [Some (BlockID b)]
nextBlocks b =
  withBlockTermStmt b (\_ s -> fromMaybe [] (termStmtNextBlocks s))


blockInputCount :: Block ext blocks ret ctx -> Size ctx
blockInputCount b = size (blockInputs b)

ppBlock :: PrettyExt ext
        => Bool
           -- ^ Print line numbers.
        -> Bool
           -- ^ Print block args. Note that you can infer the number
           -- of block args from the first SSA temp register assigned
           -- to in the block: if the block has @n@ args, then the
           -- first register it assigns to will be @$n@.
        -> Maybe (CFGPostdom blocks)
           -- ^ Optionally print postdom info.
        -> Block ext blocks ret ctx
           -- ^ Block to print.
        -> Doc
ppBlock ppLineNumbers ppBlockArgs mPda b = do
  let stmts = ppStmtSeq ppLineNumbers (blockInputCount b) (b^.blockStmts)
  let mPostdom = flip fmap mPda $ \ pda ->
        let Const pd = pda ! blockIDIndex (blockID b)
        in if Prelude.null pd
           then text "% no postdom"
           else text "% postdom" <+> hsep (viewSome pretty <$> pd)
  let numArgs = lengthFC (blockInputs b)
  let argList = [ char '$' <> pretty n | n <- [0 .. numArgs-1] ]
  let args = encloseSep lparen rparen comma argList
  let block = pretty (blockID b) <>
              if ppBlockArgs then args else Text.PrettyPrint.ANSI.Leijen.empty
  let body = case mPostdom of
        Nothing -> stmts
        Just postdom -> stmts <$$> postdom
  block <$$> indent 2 body

instance PrettyExt ext => Show (Block ext blocks ret args) where
  show blk = show $ ppBlock False False Nothing blk

instance PrettyExt ext => ShowF (Block ext blocks ret)

#ifndef UNSAFE_OPS
extendBlock :: Block ext blocks ret ctx -> Block ext (blocks ::> new) ret ctx
extendBlock b =
  Block { blockID = extendBlockID (blockID b)
        , blockInputs = blockInputs b
        , _blockStmts = extendStmtSeq knownDiff (b^.blockStmts)
        }
#endif

------------------------------------------------------------------------
-- BlockMap

-- | A mapping from block indices to CFG blocks
type BlockMap ext blocks ret = Assignment (Block ext blocks ret) blocks

getBlock :: BlockID blocks args
         -> BlockMap ext blocks ret
         -> Block ext blocks ret args
getBlock (BlockID i) m = m Ctx.! i

extendBlockMap :: Assignment (Block ext blocks ret) b
               -> Assignment (Block ext (blocks ::> args) ret) b
#ifdef UNSAFE_OPS
extendBlockMap = unsafeCoerce
#else
extendBlockMap = fmapFC extendBlock
#endif
------------------------------------------------------------------------
-- CFG

-- | A CFG consists of:
--
-- * a function handle, uniquely identifying the function this CFG
-- implements;
--
-- * a block map, representing the main CFG data structure;
--
-- * and the identifier of the function entry point.
--
-- The @blocks@ type parameter maps each block identifier to the
-- formal arguments it expects.  The @init@ type parameter identifies
-- the formal arguments of the function represented by this control-flow graph,
-- which correspond to the formal arguments of the CFG entry point.
-- The @ret@ type parameter indicates the return type of the function.
data CFG (ext :: Type)
         (blocks :: Ctx (Ctx CrucibleType))
         (init :: Ctx CrucibleType)
         (ret :: CrucibleType)
   = CFG { cfgHandle :: FnHandle init ret
         , cfgBlockMap :: !(BlockMap ext blocks ret)
         , cfgEntryBlockID :: !(BlockID blocks init)
         , cfgBreakpoints :: !(Bimap BreakpointName (Some (BlockID blocks)))
         }

cfgArgTypes :: CFG ext blocks init ret -> CtxRepr init
cfgArgTypes g = handleArgTypes (cfgHandle g)

cfgReturnType :: CFG ext blocks init ret -> TypeRepr ret
cfgReturnType g = handleReturnType (cfgHandle g)

-- | Class for types that embed a CFG of some sort.
class HasSomeCFG f ext init ret | f -> ext, f -> init, f -> ret where
  getCFG :: f b -> SomeCFG ext init ret

instance PrettyExt ext => Show (CFG ext blocks init ret) where
  show g = show (ppCFG True g)

-- | Pretty print a CFG.
ppCFG :: PrettyExt ext
      => Bool -- ^ Flag indicates if we should print line numbers
      -> CFG ext blocks init ret
      -> Doc
ppCFG lineNumbers g = ppCFG' lineNumbers (emptyCFGPostdomInfo sz) g
  where sz = size (cfgBlockMap g)

-- | Pretty print CFG with postdom information.
ppCFG' :: PrettyExt ext
       => Bool -- ^ Flag indicates if we should print line numbers
       -> CFGPostdom blocks
       -> CFG ext blocks init ret
       -> Doc
ppCFG' lineNumbers pdInfo g = vcat (toListFC (ppBlock lineNumbers blockArgs (Just pdInfo)) (cfgBlockMap g))
  where blockArgs = False

-- | Control flow graph with some blocks.  This data type closes
--   existentially over the @blocks@ type parameter.
data SomeCFG ext (init :: Ctx CrucibleType) (ret :: CrucibleType) where
  SomeCFG :: CFG ext blocks init ret -> SomeCFG ext init ret

instance PrettyExt ext => Show (SomeCFG ext i r)
  where show cfg = case cfg of SomeCFG c -> show c

-- | Control flow graph.  This data type closes existentially
--   over all the type parameters.
data AnyCFG ext where
  AnyCFG :: CFG ext blocks init ret
         -> AnyCFG ext

instance PrettyExt ext => Show (AnyCFG ext) where
  show cfg = case cfg of AnyCFG c -> show c
