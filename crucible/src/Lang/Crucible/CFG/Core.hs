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
module Lang.Crucible.CFG.Core
  ( -- * CFG
    CFG(..)
  , SomeCFG(..)
  , HasSomeCFG(..)
  , AnyCFG(..)
  , ppCFG
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
  , extendBlock

    -- * Jump targets
  , JumpTarget(..)
  , extendJumpTarget
  , jumpTargetID
  , SwitchTarget(..)
  , switchTargetID
  , extendSwitchTarget
  , extendMSwitch

    -- * Statements
  , StmtSeq(..)
  , firstStmtLoc
  , extendStmtSeq
  , stmtSeqTermStmt
  , Stmt(..)
  , ppStmt

  , applyEmbeddingStmt

  , TermStmt(..)
  , termStmtNextBlocks
  , extendTermStmt

    -- * Expressions
  , Expr(..)
  , Reg(..)
  , extendReg
  , lastReg

    -- * Re-exports
  , CharVector
  , module Lang.Crucible.Types
  , module Lang.Crucible.CFG.Common
  , module Data.Parameterized.Classes
  , module Data.Parameterized.Some
  , module Lang.Crucible.Utils.ConstK
  ) where

import           Control.Applicative
import           Control.Lens
import           Data.Maybe
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (Pair(..))
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.String
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.MATLAB.CharVector (CharVector)
import           Lang.MATLAB.Utils.PrettyPrint

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.ConstK

#ifdef UNSAFE_OPS
import qualified Data.Coerce
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
  show (Reg i) = '$' : show (Ctx.indexVal i)

instance ShowF (Reg ctx)

instance Pretty (Reg ctx tp) where
  pretty = text.show

instance Ctx.ApplyEmbedding' Reg where
  applyEmbedding' ctxe r = Reg $ Ctx.applyEmbedding' ctxe (regIndex r)

instance Ctx.ExtendContext' Reg where
  extendContext' diff r = Reg $ Ctx.extendContext' diff (regIndex r)

-- | Finds the value of the most-recently introduced register in scope.
lastReg :: Ctx.KnownContext ctx => Reg (ctx ::> tp) tp
lastReg = Reg (Ctx.nextIndex Ctx.knownSize)

-- | Extend the set of registers in scope for a given register value
--   without changing its index or type.
extendReg :: Reg ctx tp -> Reg (ctx ::> r) tp
extendReg = Reg . Ctx.extendIndex . regIndex

#ifdef UNSAFE_OPS
instance CoercibleF (Reg ctx) where
  coerceF x = Data.Coerce.coerce x
#endif

------------------------------------------------------------------------
-- Expr

-- | An expression is just an App applied to some registers.
newtype Expr (ctx :: Ctx CrucibleType) (tp :: CrucibleType)
      = App (App (Reg ctx) tp)

instance IsString (Expr ctx StringType) where
  fromString  = App . TextLit . fromString

instance Pretty (Expr ctx tp) where
  pretty (App a) = ppApp pretty a

ppAssignment :: Ctx.Assignment (Reg ctx) args -> [Doc]
ppAssignment = toListFC pretty

instance Ctx.ApplyEmbedding' Expr where
  applyEmbedding' ctxe (App e) = App (mapApp (Ctx.applyEmbedding' ctxe) e)

instance Ctx.ExtendContext' Expr where
  extendContext' diff (App e) = App (mapApp (Ctx.extendContext' diff) e)

------------------------------------------------------------------------
-- BlockID

-- | A `BlockID` uniquely identifies a block in a control-flow graph.
--   Each block has an associated context, indicating the formal arguments
--   it expects to find in registers from its calling locations.
newtype BlockID (blocks :: Ctx (Ctx CrucibleType)) (tp :: Ctx CrucibleType)
      = BlockID { blockIDIndex :: Ctx.Index blocks tp }
  deriving ( Eq, Ord)

instance TestEquality (BlockID blocks) where
  testEquality (BlockID x) (BlockID y) = testEquality x y

instance OrdF (BlockID blocks) where
  compareF (BlockID x) (BlockID y) = compareF x y

instance Pretty (BlockID blocks tp) where
  pretty (BlockID i) = char '%' <> int (Ctx.indexVal i)

instance Show (BlockID blocks ctx) where
  show (BlockID i) = '%' : show (Ctx.indexVal i)

instance ShowF (BlockID blocks)

extendBlockID :: Ctx.KnownDiff l r => BlockID l tp -> BlockID r tp
extendBlockID = BlockID . Ctx.extendIndex . blockIDIndex

extendBlockID' :: Ctx.Diff l r -> BlockID l tp -> BlockID r tp
extendBlockID' e = BlockID . Ctx.extendIndex' e . blockIDIndex

------------------------------------------------------------------------
-- JumpTarget

-- | Target for jump and branch statements
data JumpTarget blocks ctx where
     JumpTarget :: !(BlockID blocks args)            -- BlockID to jump to
                -> !(CtxRepr args)                   -- expected argument types
                -> !(Ctx.Assignment (Reg ctx) args) -- jump target actual arguments
                -> JumpTarget blocks ctx

instance Pretty (JumpTarget blocks ctx) where
  pretty (JumpTarget tgt _ a) = pretty tgt <> parens (commas (ppAssignment a))

jumpTargetID :: JumpTarget blocks ctx -> Some (BlockID blocks)
jumpTargetID (JumpTarget tgt _ _) = Some tgt

extendJumpTarget :: Ctx.Diff blocks' blocks -> JumpTarget blocks' ctx -> JumpTarget blocks ctx
extendJumpTarget diff (JumpTarget b tps a) = JumpTarget (extendBlockID' diff b) tps a

instance Ctx.ApplyEmbedding (JumpTarget blocks) where
  applyEmbedding ctxe (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (Ctx.applyEmbedding' ctxe) args)

instance Ctx.ExtendContext (JumpTarget blocks) where
  extendContext diff (JumpTarget dest tys args) =
    JumpTarget dest tys (fmapFC (Ctx.extendContext' diff) args)

------------------------------------------------------------------------
-- SwitchTarget

-- | Target for a switch statement.
data SwitchTarget blocks ctx tp where
  SwitchTarget :: !(BlockID blocks (args ::> tp))   -- BlockID to jump to
               -> !(CtxRepr args)                   -- expected argument types
               -> !(Ctx.Assignment (Reg ctx) args) -- switch target actual arguments
               -> SwitchTarget blocks ctx tp

switchTargetID :: SwitchTarget blocks ctx tp -> Some (BlockID blocks)
switchTargetID (SwitchTarget tgt _ _) = Some tgt

ppCase :: String -> SwitchTarget blocks ctx tp -> Doc
ppCase nm (SwitchTarget tgt _ a) =
  text nm <+> text "->" <+> pretty tgt <> parens (commas (ppAssignment a))

extendSwitchTarget :: Ctx.Diff blocks' blocks
                   -> SwitchTarget blocks' ctx tp
                   -> SwitchTarget blocks ctx tp
extendSwitchTarget diff (SwitchTarget b tps a) =
    SwitchTarget (extendBlockID' diff b) tps a

instance Ctx.ApplyEmbedding' (SwitchTarget blocks) where
  applyEmbedding' ctxe (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (Ctx.applyEmbedding' ctxe) args)

instance Ctx.ExtendContext' (SwitchTarget blocks) where
  extendContext' diff (SwitchTarget dest tys args) =
    SwitchTarget dest tys (fmapFC (Ctx.extendContext' diff) args)


extendMSwitch :: Ctx.Diff blocks' blocks
              -> MSwitch (SwitchTarget blocks' ctx)
              -> MSwitch (SwitchTarget blocks ctx)
extendMSwitch diff = fmapF (extendSwitchTarget diff)

------------------------------------------------------------------------
-- Stmt

-- | A sequential statement that does not affect the
-- program location within the current block or leave the current
-- block.
data Stmt (ctx :: Ctx CrucibleType) (ctx' :: Ctx CrucibleType) where
  -- Assign the value of a register
  SetReg :: !(TypeRepr tp)
         -> !(Expr ctx tp)
         -> Stmt ctx (ctx ::> tp)

  -- Statement used for evaluating function calls
  CallHandle :: !(TypeRepr ret)                          -- The type of the return value(s)
             -> !(Reg ctx (FunctionHandleType args ret)) -- The function handle to call
             -> !(CtxRepr args)                          -- The expected types of the arguments
             -> !(Ctx.Assignment (Reg ctx) args)         -- The actual arguments to the call
             -> Stmt ctx (ctx ::> ret)

  -- Print a message out to the console
  Print :: !(Reg ctx StringType) -> Stmt ctx ctx

  -- Read a global variable.
  ReadGlobal :: !(GlobalVar tp)
             -> Stmt ctx (ctx ::> tp)

  -- Write to a global variable.
  WriteGlobal :: !(GlobalVar tp)
              -> !(Reg ctx tp)
              -> Stmt ctx ctx

  -- Allocate a new reference cell
  NewRefCell :: !(TypeRepr tp)
             -> !(Reg ctx tp)
             -> Stmt ctx (ctx ::> ReferenceType tp)

  -- Read the current value of a reference cell
  ReadRefCell :: !(Reg ctx (ReferenceType tp))
              -> Stmt ctx (ctx ::> tp)

  -- Write the current value of a reference cell
  WriteRefCell :: !(Reg ctx (ReferenceType tp))
               -> !(Reg ctx tp)
               -> Stmt ctx ctx

  -- Assert a boolean condition.  If the condition fails, print the given string.
  Assert :: !(Reg ctx BoolType) -> !(Reg ctx StringType) -> Stmt ctx ctx

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

  -- Switch on a Matlab value.  Examine the runtime type of the given
  -- dynamic expression and jump to the appropriate switch target.
  MSwitchStmt :: !(Reg ctx MatlabValueType)
              -> !(MSwitch (SwitchTarget blocks ctx))
              -> TermStmt blocks ret ctx

  -- Switch on a variant value.  Examine the tag of the variant
  -- and jump to the appropriate switch target.
  VariantElim :: !(CtxRepr varctx)
              -> !(Reg ctx (VariantType varctx))
              -> !(Ctx.Assignment (SwitchTarget blocks ctx) varctx)
              -> TermStmt blocks ret ctx

  -- Return from function, providing the return value(s).
  Return :: !(Reg ctx ret)
         -> TermStmt blocks ret ctx

  -- End block with a tail call.
  TailCall :: !(Reg ctx (FunctionHandleType args ret))
           -> !(CtxRepr args)
           -> !(Ctx.Assignment (Reg ctx) args)
           -> TermStmt blocks ret ctx

  -- Block ends with an error.
  ErrorStmt :: !(Reg ctx StringType) -> TermStmt blocks ret ctx

extendTermStmt :: Ctx.Diff blocks' blocks -> TermStmt blocks' ret ctx -> TermStmt blocks ret ctx
extendTermStmt diff (Jump tgt) = Jump (extendJumpTarget diff tgt)
extendTermStmt diff (Br c x y) = Br c (extendJumpTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (MaybeBranch tp c x y) =
  MaybeBranch tp c (extendSwitchTarget diff x) (extendJumpTarget diff y)
extendTermStmt diff (MSwitchStmt e s) =
  MSwitchStmt e (extendMSwitch diff s)
extendTermStmt diff (VariantElim ctx e asgn) =
  VariantElim ctx e (fmapFC (extendSwitchTarget diff) asgn)
extendTermStmt _diff (Return e) = Return e
extendTermStmt _diff (TailCall h tps args) = TailCall h tps args
extendTermStmt _diff (ErrorStmt e) = ErrorStmt e

-- | Return the set of possible next blocks from a TermStmt
termStmtNextBlocks :: TermStmt b ret ctx -> Maybe [Some (BlockID b)]
termStmtNextBlocks s0 =
  case s0 of
    Jump tgt             -> Just [ jumpTargetID tgt ]
    Br          _ x y    -> Just [ jumpTargetID x, jumpTargetID y ]
    MaybeBranch _ _ x y  -> Just [ switchTargetID x, jumpTargetID y ]
    VariantElim _ _ a    -> Just (toListFC switchTargetID a)
    MSwitchStmt _ s      -> Just (toListF switchTargetID s)
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
    MSwitchStmt e c ->
      text "switch" <+> pretty e <+> lbrace <$$>
       indent 2 (
         vcat ((<> semi) <$> ppMSwitch ppCase c) <$$>
         rbrace)
    Return e ->
      text "return"
       <+> pretty e
    TailCall h _ args ->
      text "tailCall"
       <+> pretty h
       <+> parens (commas (ppAssignment args))
    ErrorStmt msg ->
      text "error" <+> pretty msg


applyEmbeddingStmt :: forall ctx ctx' sctx.
                      Ctx.CtxEmbedding ctx ctx' -> Stmt ctx sctx
                      -> Pair (Stmt ctx') (Ctx.CtxEmbedding sctx)
applyEmbeddingStmt ctxe stmt =
  case stmt of
    SetReg tp e -> Pair (SetReg tp (Ctx.applyEmbedding' ctxe e))
                        (Ctx.extendEmbeddingBoth ctxe)

    CallHandle ret hdl tys args ->
      Pair (CallHandle ret (reg hdl) tys (fmapFC reg args))
           (Ctx.extendEmbeddingBoth ctxe)

    Print str -> Pair (Print (reg str)) ctxe

    ReadGlobal var -> Pair (ReadGlobal var)
                           (Ctx.extendEmbeddingBoth ctxe)

    WriteGlobal var r -> Pair (WriteGlobal var (reg r)) ctxe
    NewRefCell tp r -> Pair (NewRefCell tp (reg r))
                            (Ctx.extendEmbeddingBoth ctxe)
    ReadRefCell r     -> Pair (ReadRefCell (reg r))
                              (Ctx.extendEmbeddingBoth ctxe)
    WriteRefCell r r' ->  Pair (WriteRefCell (reg r) (reg r')) ctxe
    Assert b str      -> Pair (Assert (reg b) (reg str)) ctxe
  where
    reg :: forall tp. Reg ctx tp -> Reg ctx' tp
    reg = Ctx.applyEmbedding' ctxe


instance Ctx.ApplyEmbedding (TermStmt blocks ret) where
  applyEmbedding :: forall ctx ctx'.
                    Ctx.CtxEmbedding ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  applyEmbedding ctxe term =
    case term of
      Jump jt -> Jump (apC jt)
      Br b jtl jtr -> Br (apC' b) (apC jtl) (apC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (apC' b) (apC' swt) (apC jt)
      MSwitchStmt tm targets     -> MSwitchStmt (apC' tm) (fmapF apC' targets)
      VariantElim repr r targets -> VariantElim repr (apC' r) (fmapFC apC' targets)
      Return r -> Return (apC' r)
      TailCall hdl tys args -> TailCall (apC' hdl) tys (fmapFC apC' args)
      ErrorStmt r -> ErrorStmt (apC' r)
    where
      apC' :: forall f v. Ctx.ApplyEmbedding' f => f ctx v -> f ctx' v
      apC' = Ctx.applyEmbedding' ctxe

      apC :: forall f. Ctx.ApplyEmbedding  f => f ctx -> f ctx'
      apC  = Ctx.applyEmbedding  ctxe

instance Ctx.ExtendContext (TermStmt blocks ret) where
  extendContext :: forall ctx ctx'.
                    Ctx.Diff ctx ctx'
                    -> TermStmt blocks ret ctx
                    -> TermStmt blocks ret ctx'
  extendContext diff term =
    case term of
      Jump jt -> Jump (extC jt)
      Br b jtl jtr -> Br (extC' b) (extC jtl) (extC jtr)
      MaybeBranch tp b swt jt    -> MaybeBranch tp (extC' b) (extC' swt) (extC jt)
      MSwitchStmt tm targets     -> MSwitchStmt (extC' tm) (fmapF extC' targets)
      VariantElim repr r targets -> VariantElim repr (extC' r) (fmapFC extC' targets)
      Return r -> Return (extC' r)
      TailCall hdl tys args -> TailCall (extC' hdl) tys (fmapFC extC' args)
      ErrorStmt r -> ErrorStmt (extC' r)
    where
      extC' :: forall f v. Ctx.ExtendContext' f => f ctx v -> f ctx' v
      extC' = Ctx.extendContext' diff

      extC :: forall f. Ctx.ExtendContext  f => f ctx -> f ctx'
      extC  = Ctx.extendContext  diff


------------------------------------------------------------------------
-- StmtSeq

-- | A sequence of straight-line program statements that end with
--   a terminating statement (return, jump, etc).
data StmtSeq blocks (ret :: CrucibleType) ctx where
  ConsStmt :: !ProgramLoc
           -> !(Stmt ctx ctx')
           -> !(StmtSeq blocks ret ctx')
           -> StmtSeq blocks ret ctx
  TermStmt :: !ProgramLoc
           -> !(TermStmt blocks ret ctx)
           -> (StmtSeq blocks ret ctx)

-- | Return the location of a statement.
firstStmtLoc :: StmtSeq b r ctx -> ProgramLoc
firstStmtLoc (ConsStmt pl _ _) = pl
firstStmtLoc (TermStmt pl _) = pl

-- | A lens-like operation that gives one access to program location and term statement,
-- and allows the terminal statement to be replaced with an arbitrary sequence of
-- statements.
stmtSeqTermStmt :: Functor f
                => (forall ctx
                    . (ProgramLoc, TermStmt b ret ctx)
                    -> f (StmtSeq b' ret ctx))
                -> StmtSeq b ret args
                -> f (StmtSeq b' ret args)
stmtSeqTermStmt f (ConsStmt l s t) = ConsStmt l s <$> stmtSeqTermStmt f t
stmtSeqTermStmt f (TermStmt p t) = f (p, t)

ppReg :: Ctx.Size ctx -> Doc
ppReg h = text "$" <> int (Ctx.sizeInt h)

nextStmtHeight :: Ctx.Size ctx -> Stmt ctx ctx' -> Ctx.Size ctx'
nextStmtHeight h s =
  case s of
    SetReg{} -> Ctx.incSize h
    CallHandle{} -> Ctx.incSize h
    Print{} -> h
    ReadGlobal{} -> Ctx.incSize h
    WriteGlobal{} -> h
    NewRefCell{} -> Ctx.incSize h
    ReadRefCell{} -> Ctx.incSize h
    WriteRefCell{} -> h
    Assert{} -> h

ppStmt :: Ctx.Size ctx -> Stmt ctx ctx' -> Doc
ppStmt r s =
  case s of
    SetReg _ e -> ppReg r <+> text "=" <+> pretty e
    CallHandle _ h _ args ->
      ppReg r <+> text "= call"
              <+> pretty h <> parens (commas (ppAssignment args))
               <> text ";"
    Print msg -> ppFn "print" [ pretty msg ]
    ReadGlobal v -> text "read" <+> ppReg r <+> pretty v
    WriteGlobal v e -> text "write" <+> pretty v <+> pretty e
    NewRefCell _ e -> ppReg r <+> text "=" <+> ppFn "newref" [ pretty e ]
    ReadRefCell e -> ppReg r <+> text "= !" <> pretty e
    WriteRefCell r1 r2 -> pretty r1 <+> text ":=" <+> pretty r2
    Assert c e -> ppFn "assert" [ pretty c, pretty e]

prefixLineNum :: Bool -> ProgramLoc -> Doc -> Doc
prefixLineNum True pl d = text "%" <+> ppNoFileName (plSourceLoc pl) <$$> d
prefixLineNum False _ d = d

ppStmtSeq :: Bool -> Ctx.Size ctx -> StmtSeq blocks ret ctx -> Doc
ppStmtSeq ppLineNum h (ConsStmt pl s r) =
  prefixLineNum ppLineNum pl (ppStmt h s) <$$>
  ppStmtSeq ppLineNum (nextStmtHeight h s) r
ppStmtSeq ppLineNum _ (TermStmt pl s) =
  prefixLineNum ppLineNum pl (pretty s)


#ifdef UNSAFE_OPS
extendStmtSeq :: Ctx.Diff blocks' blocks -> StmtSeq blocks' ret ctx -> StmtSeq blocks ret ctx
extendStmtSeq _ s = Data.Coerce.coerce s
#else
extendStmtSeq :: Ctx.Diff blocks' blocks -> StmtSeq blocks' ret ctx -> StmtSeq blocks ret ctx
extendStmtSeq diff (ConsStmt p s l) = ConsStmt p s (extendStmtSeq diff l)
extendStmtSeq diff (TermStmt p s) = TermStmt p (extendTermStmt diff s)
#endif


instance Ctx.ApplyEmbedding (StmtSeq blocks ret) where
  applyEmbedding ctxe (ConsStmt loc stmt rest) =
    case applyEmbeddingStmt ctxe stmt of
      Pair stmt' ctxe' -> ConsStmt loc stmt' (Ctx.applyEmbedding ctxe' rest)
  applyEmbedding ctxe (TermStmt loc term) =
    TermStmt loc (Ctx.applyEmbedding ctxe term)



------------------------------------------------------------------------
-- CFGPostdom

-- | Postdominator information about a CFG.  The assignment maps each block
--   to the postdominators of the given block.  The postdominators are ordered
--   with nearest postdominator first.
type CFGPostdom blocks = Ctx.Assignment (ConstK [Some (BlockID blocks)]) blocks

emptyCFGPostdomInfo :: Ctx.Size blocks -> CFGPostdom blocks
emptyCFGPostdomInfo sz = Ctx.replicate sz (ConstK [])


------------------------------------------------------------------------
-- Block

-- | A basic block within a function.  Note: postdominators are precalculated.
data Block (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType) ctx
   = Block { blockID        :: !(BlockID blocks ctx)
             -- ^ The unique identifier of this block
           , blockInputs    :: !(CtxRepr ctx)
             -- ^ The expected types of the formal arguments to this block
           , _blockStmts    :: !(StmtSeq blocks ret ctx)
             -- ^ The sequence of statements in this block
           }

blockStmts :: Simple Lens (Block b r c) (StmtSeq b r c)
blockStmts = lens _blockStmts (\b s -> b { _blockStmts = s })

-- | Return location of start of block.
blockLoc :: Block blocks ret ctx -> ProgramLoc
blockLoc b = firstStmtLoc (b^.blockStmts)

-- | Get the terminal statement of a basic block.  This is implemented
-- in a CPS style due to the block context.
withBlockTermStmt :: Block blocks ret args
                  -> (forall ctx . ProgramLoc -> TermStmt blocks ret ctx -> r)
                  -> r
withBlockTermStmt b f = getConst (stmtSeqTermStmt (Const . uncurry f) (b^.blockStmts))

nextBlocks :: Block b r a -> [Some (BlockID b)]
nextBlocks b =
  withBlockTermStmt b (\_ s -> fromMaybe [] (termStmtNextBlocks s))


blockInputCount :: Block blocks ret ctx -> Ctx.Size ctx
blockInputCount b = Ctx.size (blockInputs b)

ppBlock :: Bool
           -- ^ Print line numbers.
        -> CFGPostdom blocks
        -> Block blocks ret ctx
           -- ^ Block to print.
        -> Doc
ppBlock ppLineNumbers pda b = do
  let stmts = ppStmtSeq ppLineNumbers (blockInputCount b) (b^.blockStmts)
  let ConstK pd = pda Ctx.! blockIDIndex (blockID b)
  let postdom
        | null pd = text "% no postdom"
        | otherwise = text "% postdom" <+> hsep (viewSome pretty <$> pd)
  pretty (blockID b) <$$> indent 2 (stmts <$$> postdom)

ppBlock' :: Bool
           -- ^ Print line numbers.
          -> Block blocks ret ctx
            -- ^ Block to print.
         -> Doc
ppBlock' ppLineNumbers b = do
  let stmts = ppStmtSeq ppLineNumbers (blockInputCount b) (b^.blockStmts)
  pretty (blockID b) <$$> indent 2 stmts

instance Show (Block blocks ret args) where
  show blk = show $ ppBlock' False blk

instance ShowF (Block blocks ret)

extendBlock :: Block blocks ret ctx -> Block (blocks ::> new) ret ctx
#ifdef UNSAFE_OPS
extendBlock b = Data.Coerce.coerce b
#else
extendBlock b =
  Block { blockID = extendBlockID (blockID b)
        , blockInputs = blockInputs b
        , _blockStmts = extendStmtSeq Ctx.knownDiff (b^.blockStmts)
        }
#endif

------------------------------------------------------------------------
-- BlockMap

-- | A mapping from block indices to CFG blocks
type BlockMap blocks ret = Ctx.Assignment (Block blocks ret) blocks

getBlock :: BlockID blocks args
         -> BlockMap blocks ret
         -> Block blocks ret args
getBlock (BlockID i) m = m Ctx.! i

extendBlockMap :: Ctx.Assignment (Block blocks ret) b
               -> Ctx.Assignment (Block (blocks ::> args) ret) b
#ifdef UNSAFE_OPS
extendBlockMap = Data.Coerce.coerce
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
-- the formal arguments of the function represetned by this control-flow graph,
-- which correspond to the formal arguments of the CFG entry point.
-- The @ret@ type parameter indicates the return type of the function.
data CFG (blocks :: Ctx (Ctx CrucibleType))
         (init :: Ctx CrucibleType)
         (ret :: CrucibleType)
   = CFG { cfgHandle :: FnHandle init ret
         , cfgBlockMap :: !(BlockMap blocks ret)
         , cfgEntryBlockID :: !(BlockID blocks init)
         }

cfgArgTypes :: CFG blocks init ret -> CtxRepr init
cfgArgTypes g = handleArgTypes (cfgHandle g)

cfgReturnType :: CFG blocks init ret -> TypeRepr ret
cfgReturnType g = handleReturnType (cfgHandle g)

-- | Class for types that embed a CFG of some sort.
class HasSomeCFG f init ret | f -> init, f -> ret where
  getCFG :: f b -> SomeCFG init ret

instance Show (CFG blocks init ret) where
  show g = show (ppCFG True g)

-- | Pretty print a CFG.
ppCFG :: Bool -- ^ Flag indicates if we should print line numbers
      -> CFG blocks init ret
      -> Doc
ppCFG lineNumbers g = ppCFG' lineNumbers (emptyCFGPostdomInfo sz) g
  where sz = Ctx.size (cfgBlockMap g)

-- | Pretty print CFG with postdom information.
ppCFG' :: Bool -- ^ Flag indicates if we should print line numbers
       -> CFGPostdom blocks
       -> CFG blocks init ret
       -> Doc
ppCFG' lineNumbers pdInfo g = vcat (toListFC (ppBlock lineNumbers pdInfo) (cfgBlockMap g))


-- | Control flow graph with some blocks.  This data type closes
--   existentially over the @blocks@ type parameter.
data SomeCFG (init :: Ctx CrucibleType) (ret :: CrucibleType) where
  SomeCFG :: CFG blocks init ret -> SomeCFG init ret

-- | Control flow graph.  This data type closes existentially
--   over all the type parameters.
data AnyCFG where
  AnyCFG :: CFG blocks init ret
         -> AnyCFG
