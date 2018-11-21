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
{-# LANGUAGE TypeApplications, AllowAmbiguousTypes #-}

-- TODO: temporary
{-# OPTIONS_GHC -fno-warn-unused-matches -fno-warn-name-shadowing #-}

module Lang.Crucible.CFG.Core
  ( -- * CFG
    CFG(..)
  , SomeCFG(..)
  , HasSomeCFG(..)
  , AnyCFG(..)
  , ppCFG
  , ppCFG'
  , cfgHandleName
  , cfgArgTypes
  , cfgReturnType
  , updateCFG
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

  
  , instantiateReg
  , instantiateCFG
  , instantiateCFGPostdom
  
    -- * Re-exports
  , module Lang.Crucible.Types
  , module Lang.Crucible.CFG.Common
  , module Data.Parameterized.Classes
  , module Data.Parameterized.Some
  ) where

import Control.Applicative
import Control.Lens
import Data.Maybe
import Data.Kind
import Data.Parameterized.Classes
import Data.Parameterized.Map (Pair(..))
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.String
import qualified Data.Vector as Vector
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))


import What4.ProgramLoc
import What4.Symbol

import Lang.Crucible.CFG.Common
import Lang.Crucible.CFG.Expr
import Lang.Crucible.FunctionHandle
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

instance IsString (Expr ext ctx StringType) where
  fromString  = App . TextLit . fromString

instance PrettyApp (ExprExtension ext) => Pretty (Expr ext ctx tp) where
  pretty (App a) = ppApp pretty a

ppAssignment :: Assignment (Reg ctx) args -> [Doc]
ppAssignment = toListFC pretty

instance TraversableFC (ExprExtension ext) => ApplyEmbedding' (Expr ext) where
  applyEmbedding' ctxe (App e) = App (mapApp (applyEmbedding' ctxe) e)

instance TraversableFC (ExprExtension ext) => ExtendContext' (Expr ext) where
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


-- Statement used for evaluating polymorphic function calls
--  CallPHandle :: (Instantiate subst args' ~ args,
--                  Instantiate subst ret' ~ ret) =>
--                !(TypeRepr ret)                                       -- The type of the return value(s)
--             -> !(Reg ctx (PolyType (FunctionHandleType args' ret'))) -- The function handle to call
--             -> CtxRepr subst                                         -- Type substitution to apply 
--             -> !(CtxRepr args)                                       -- The expected types of the arguments
--             -> !(Assignment (Reg ctx) args)                          -- The actual arguments to the call
--             -> Stmt ext ctx (ctx ::> ret)



  -- Print a message out to the console
  Print :: !(Reg ctx StringType) -> Stmt ext ctx ctx

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
  Assert :: !(Reg ctx BoolType) -> !(Reg ctx StringType) -> Stmt ext ctx ctx

  -- Assume a boolean condition, remembering the given string as the 'reason' for this assumption.
  Assume :: !(Reg ctx BoolType) -> !(Reg ctx StringType) -> Stmt ext ctx ctx


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
  ErrorStmt :: !(Reg ctx StringType) -> TermStmt blocks ret ctx

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

--    CallPHandle ret hdl targs tys args ->
--      Pair (CallPHandle ret (reg hdl) targs tys (fmapFC reg args))
--           (extendEmbeddingBoth ctxe)


    Print str -> Pair (Print (reg str)) ctxe

    ReadGlobal var -> Pair (ReadGlobal var)
                           (extendEmbeddingBoth ctxe)

    WriteGlobal var r -> Pair (WriteGlobal var (reg r)) ctxe

    FreshConstant bt nm -> Pair (FreshConstant bt nm)
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

{-
class InstantiateClass ty where
  instantiate :: CtxRepr subst -> ty -> Instantiate subst ty
type instance Instantiate subst (Ctx.Index ctx ty) = Ctx.Index (Instantiate subst ctx) (Instantiate subst ty)
instance InstantiateClass (Ctx.Index ctx ty) where
  instantiate idx = unsafeCoerce idx
type instance Instantiate subst (Reg ctx ty) = Reg (Instantiate subst ctx) (Instantiate subst ty)
instance InstantiateClass (Reg ctx ty) where
-}

-- Ctx.Index is just a number underneath
instantiateIndex :: CtxRepr subst -> Ctx.Index ctx ty -> Ctx.Index (Instantiate subst ctx) (Instantiate subst ty)
instantiateIndex subst idx = unsafeCoerce idx

instantiateReg :: forall subst ctx ty.
  CtxRepr subst -> Reg ctx ty -> Reg (Instantiate subst ctx) (Instantiate subst ty)
instantiateReg subst (Reg idx) = Reg (instantiateIndex subst idx)

--instantiatePolyReg :: forall subst ctx ty.
--  CtxRepr subst -> Reg ctx (PolyType ty) -> Reg (Instantiate subst ctx) (Instantiate subst ty)
--instantiatePolyReg subst (Reg idx) = Reg (instantiateIndex subst idx) where


instantiateBlockID :: CtxRepr subst -> BlockID blocks ctx
                 -> BlockID (Instantiate subst blocks) (Instantiate subst ctx)
instantiateBlockID subst (BlockID idx) = BlockID (instantiateIndex subst idx)
  
    
instantiateExpr :: CtxRepr subst -> Expr ext ctx tp -> Expr ext (Instantiate subst ctx) (Instantiate subst tp)
instantiateExpr subst (App app) = App (instantiateApp subst app)

instantiateApp :: forall subst ext ctx tp.
  CtxRepr subst -> App ext (Reg ctx) tp -> App ext (Reg (Instantiate subst ctx)) (Instantiate subst tp)
instantiateApp subst app = case app of
  ExtensionApp _ -> error "TODO: extension app"
  BaseIsEq bty r1 r2 -> BaseIsEq bty (instantiateReg subst r1) (instantiateReg subst r2)
  BaseIte bty r1 r2 r3 -> BaseIte bty (instantiateReg subst r1)
    (instantiateReg subst r2) (instantiateReg subst r3)
  EmptyApp -> EmptyApp
  PackAny ty reg   -> PackAny (instantiateRepr subst ty) (instantiateReg subst reg)
  UnpackAny ty reg -> UnpackAny (instantiateRepr subst ty) (instantiateReg subst reg)
  BoolLit b -> BoolLit b
  Not r1 -> Not (instantiateReg subst r1)
  And r1 r2 -> And (instantiateReg subst r1) (instantiateReg subst r2)
  Or r1 r2 -> Or (instantiateReg subst r1) (instantiateReg subst r2)
  BoolXor r1 r2 -> BoolXor (instantiateReg subst r1) (instantiateReg subst r2)
  NatLit n -> NatLit n
  NatLt  r1 r2 -> NatLt  (instantiateReg subst r1) (instantiateReg subst r2)
  NatLe  r1 r2 -> NatLe  (instantiateReg subst r1) (instantiateReg subst r2)
  NatAdd r1 r2 -> NatAdd (instantiateReg subst r1) (instantiateReg subst r2)
  NatSub r1 r2 -> NatSub (instantiateReg subst r1) (instantiateReg subst r2)
  NatMul r1 r2 -> NatMul (instantiateReg subst r1) (instantiateReg subst r2)
  NatDiv r1 r2 -> NatDiv (instantiateReg subst r1) (instantiateReg subst r2)
  NatMod r1 r2 -> NatMod (instantiateReg subst r1) (instantiateReg subst r2)

  IntLit n -> IntLit n
  IntLt  r1 r2 -> IntLt  (instantiateReg subst r1) (instantiateReg subst r2)
  IntLe  r1 r2 -> IntLe  (instantiateReg subst r1) (instantiateReg subst r2)
  IntNeg r1    -> IntNeg (instantiateReg subst r1)
  IntAdd r1 r2 -> IntAdd (instantiateReg subst r1) (instantiateReg subst r2)
  IntSub r1 r2 -> IntSub (instantiateReg subst r1) (instantiateReg subst r2)
  IntMul r1 r2 -> IntMul (instantiateReg subst r1) (instantiateReg subst r2)
  IntDiv r1 r2 -> IntDiv (instantiateReg subst r1) (instantiateReg subst r2)
  IntMod r1 r2 -> IntMod (instantiateReg subst r1) (instantiateReg subst r2)
  IntAbs r1    -> IntAbs (instantiateReg subst r1)

  RationalLit n -> RationalLit n
  RealLt  r1 r2 -> RealLt  (instantiateReg subst r1) (instantiateReg subst r2)
  RealLe  r1 r2 -> RealLe  (instantiateReg subst r1) (instantiateReg subst r2)
  RealNeg r1    -> RealNeg (instantiateReg subst r1)
  RealAdd r1 r2 -> RealAdd (instantiateReg subst r1) (instantiateReg subst r2)
  RealSub r1 r2 -> RealSub (instantiateReg subst r1) (instantiateReg subst r2)
  RealMul r1 r2 -> RealMul (instantiateReg subst r1) (instantiateReg subst r2)
  RealDiv r1 r2 -> RealDiv (instantiateReg subst r1) (instantiateReg subst r2)
  RealMod r1 r2 -> RealMod (instantiateReg subst r1) (instantiateReg subst r2)
  RealIsInteger r1 -> RealIsInteger (instantiateReg subst r1)

  FloatLit n    -> FloatLit n
  DoubleLit d   -> DoubleLit d
  FloatNaN fi   -> FloatNaN fi
  FloatPInf fi  -> FloatPInf fi
  FloatNInf fi  -> FloatNInf fi
  FloatPZero fi -> FloatPZero fi
  FloatNZero fi -> FloatNZero fi

  FloatNeg fi r1    -> FloatNeg fi (instantiateReg subst r1)
  FloatAbs fi r1    -> FloatAbs fi (instantiateReg subst r1)
  FloatSqrt fi rm r1  -> FloatSqrt fi rm (instantiateReg subst r1)
  FloatAdd fi rm r1 r2 -> FloatAdd fi rm (instantiateReg subst r1) (instantiateReg subst r2)
  FloatSub fi rm r1 r2 -> FloatSub fi rm (instantiateReg subst r1) (instantiateReg subst r2)
  FloatMul fi rm r1 r2 -> FloatMul fi rm (instantiateReg subst r1) (instantiateReg subst r2)
  FloatDiv fi rm r1 r2 -> FloatDiv fi rm (instantiateReg subst r1) (instantiateReg subst r2)
  FloatRem fi r1 r2 -> FloatRem fi (instantiateReg subst r1) (instantiateReg subst r2)
  FloatMin fi r1 r2 -> FloatMin fi (instantiateReg subst r1) (instantiateReg subst r2)
  FloatMax fi r1 r2 -> FloatMax fi (instantiateReg subst r1) (instantiateReg subst r2)
  FloatFMA fi rm r1 r2 r3 -> FloatFMA fi rm (instantiateReg subst r1) (instantiateReg subst r2) (instantiateReg subst r3)
  FloatLt  r1 r2 -> FloatLt  (instantiateReg subst r1) (instantiateReg subst r2)
  FloatLe  r1 r2 -> FloatLe  (instantiateReg subst r1) (instantiateReg subst r2)

  -- TODO: more floats

  JustValue ty r1 -> JustValue (instantiateRepr subst ty) (instantiateReg subst r1)
  NothingValue ty -> NothingValue (instantiateRepr subst ty) 
  FromJustValue ty r1 r2 -> FromJustValue (instantiateRepr subst ty) (instantiateReg subst r1) (instantiateReg subst r2)

  AddSideCondition bty r1 s r2 -> AddSideCondition bty (instantiateReg subst r1) s (instantiateReg subst r2)

  RollRecursive sr ctr r1 -> error "TODO"
  UnrollRecursive sr ctr r1 -> error "TODO"

  VectorLit ty v1 -> VectorLit  (instantiateRepr subst ty)
     (Vector.map (instantiateReg subst) v1)
  VectorReplicate ty r1 r2 -> VectorReplicate (instantiateRepr subst ty) (instantiateReg subst r1) (instantiateReg subst r2)
  VectorIsEmpty r1 -> VectorIsEmpty (instantiateReg subst r1)
  VectorSize r1 -> VectorSize (instantiateReg subst r1)
  VectorGetEntry ty r1 r2 -> VectorGetEntry (instantiateRepr subst ty) (instantiateReg subst r1) (instantiateReg subst r2)
  VectorSetEntry ty r1 r2 r3 ->
    VectorSetEntry  (instantiateRepr subst ty) (instantiateReg subst r1) (instantiateReg subst r2) (instantiateReg subst r3)
  VectorCons ty r1 r2 ->
    VectorCons  (instantiateRepr subst ty) (instantiateReg subst r1) (instantiateReg subst r2)


  HandleLit fh ->
    -- We need precondition that bare function handle literals in expressions do not contain any type parameters
    -- If this is true, we know that
    --    (Instantiate subst (FunctionHandleType args ret) ~ FunctionHandleType args ret)
    -- maybe we want to add this as a precondition to the HandleLit constructor?
    unsafeCoerce (HandleLit fh)

  Closure argTy retTy r1 tp r2 ->
    Closure (instantiateCtxRepr subst argTy) (instantiateRepr subst retTy)
            (instantiateReg subst r1) (instantiateRepr subst tp) (instantiateReg subst r2) 
  
  PolyHandleLit fh -> PolyHandleLit fh

  PolyInstantiate (ty :: TypeRepr (PolyType (FunctionHandleType args ret))) r1 (targs :: CtxRepr targs) ->
    case (axiom @subst @targs @ret, axiom @subst @targs @args) of
      (Refl, Refl) ->
        PolyInstantiate ty (instantiateReg subst r1) (instantiateCtxRepr subst targs)

  -- TODO: many missing here

  InjectVariant ctx idx r1 -> InjectVariant (instantiateCtxRepr subst ctx) (instantiateIndex subst idx)
    (instantiateReg subst r1)
  ProjectVariant ctx idx r1 -> ProjectVariant (instantiateCtxRepr subst ctx) (instantiateIndex subst idx)
    (instantiateReg subst r1) 

  MkStruct ctx args -> MkStruct (instantiateCtxRepr subst ctx) (instantiateArgs subst args)
  GetStruct r1 idx ty -> GetStruct (instantiateReg subst r1) (instantiateIndex subst idx) (instantiateRepr subst ty)
  SetStruct ctx r1 idx r2 -> SetStruct (instantiateCtxRepr subst ctx) (instantiateReg subst r1)
    (instantiateIndex subst idx) (instantiateReg subst r2)

axiom :: forall subst subst1 x. Instantiate subst (Instantiate subst1 x) :~: Instantiate (Instantiate subst subst1) x
axiom = unsafeCoerce Refl

instantiateStmt :: forall subst ext ctx ctx' .
  CtxRepr subst -> Stmt ext ctx ctx' -> Stmt ext (Instantiate subst ctx) (Instantiate subst ctx')
instantiateStmt subst (SetReg ty expr) = SetReg (instantiateRepr subst ty) (instantiateExpr subst expr)
instantiateStmt subst (ExtendAssign _ ) = error "TODO: extendAssign"
instantiateStmt subst (CallHandle ret reg argTys args) = 
  CallHandle (instantiateRepr subst ret)
             (instantiateReg subst reg)
             (instantiateCtxRepr subst argTys)
             (instantiateArgs subst args)
{-
instantiateStmt subst (CallPHandle ret (reg     :: Reg ctx (PolyType (FunctionHandleType args' ret')))
                        (subst1 :: CtxRepr subst1) argTys args) =
  case (axiom @subst @subst1 @args', axiom @subst @subst1 @ret') of
    (Refl, Refl) -> 
      (CallPHandle ret' reg' subst1' argTys' args') where
        ret'    = instantiateRepr subst ret
        reg'    = instantiateReg subst reg
        subst1' = instantiateCtxRepr subst subst1
        argTys' = instantiateCtxRepr subst argTys
        args'   = instantiateArgs    subst args
-}
instantiateStmt subst (Print reg) = Print (instantiateReg subst reg)
  --- NOTE need to know that the types of global variables are CLOSED
  --- i.e. that Instantiate subst ty ~ ty
instantiateStmt subst (ReadGlobal gv) = ReadGlobal (unsafeCoerce gv)
instantiateStmt subst (WriteGlobal gv reg) = WriteGlobal (unsafeCoerce gv) (instantiateReg subst reg)
instantiateStmt subst (FreshConstant bt ss) = FreshConstant bt ss
instantiateStmt subst (NewRefCell ty reg) = NewRefCell (instantiateRepr subst ty) (instantiateReg subst reg)
instantiateStmt subst (NewEmptyRefCell ty) = NewEmptyRefCell (instantiateRepr subst ty) 
instantiateStmt subst (ReadRefCell reg) = ReadRefCell (instantiateReg subst reg)
instantiateStmt subst (WriteRefCell reg1 reg2) = WriteRefCell (instantiateReg subst reg1)(instantiateReg subst reg2)
instantiateStmt subst (DropRefCell reg) = DropRefCell (instantiateReg subst reg)
instantiateStmt subst (Assert reg1 reg2) = Assert (instantiateReg subst reg1) (instantiateReg subst reg2)
instantiateStmt subst (Assume reg1 reg2) = Assume (instantiateReg subst reg1) (instantiateReg subst reg2)

instantiateTermStmt :: CtxRepr subst
                    -> TermStmt blocks ret ctx
                    -> TermStmt (Instantiate subst blocks) (Instantiate subst ret) (Instantiate subst ctx)
instantiateTermStmt subst (Jump target) = Jump (instantiateJumpTarget subst target)
instantiateTermStmt subst (Br reg jt1 jt2) = Br
  (instantiateReg subst reg)
  (instantiateJumpTarget subst jt1)
  (instantiateJumpTarget subst jt2)
instantiateTermStmt subst (MaybeBranch repr reg st1 jt2) =
  MaybeBranch (instantiateRepr subst repr)
              (instantiateReg subst reg)
              (instantiateSwitch subst st1)
              (instantiateJumpTarget subst jt2)
instantiateTermStmt subst (VariantElim repr reg switch) = VariantElim (instantiateCtxRepr subst repr) (instantiateReg subst reg)
  (instantiateSwitchMap subst switch)
instantiateTermStmt subst (Return reg) = Return (instantiateReg subst reg)
instantiateTermStmt subst (TailCall r1 ctx args) = TailCall (instantiateReg subst r1) (instantiateCtxRepr subst ctx)
  (instantiateArgs subst args)
instantiateTermStmt subst (ErrorStmt reg) = ErrorStmt (instantiateReg subst reg)

instantiateStmtSeq :: CtxRepr subst -> StmtSeq ext block ret ctx
                   -> StmtSeq ext (Instantiate subst block) (Instantiate subst ret) (Instantiate subst ctx)
instantiateStmtSeq subst (ConsStmt loc stmt sseq) = ConsStmt loc (instantiateStmt subst stmt) (instantiateStmtSeq subst sseq)
instantiateStmtSeq subst (TermStmt loc termstmt) = TermStmt loc (instantiateTermStmt subst termstmt)


instantiateBlock :: CtxRepr subst -> Block ext blocks ret ctx
                 -> Block ext (Instantiate subst blocks) (Instantiate subst ret) (Instantiate subst ctx)
instantiateBlock subst (Block id inputs stmts) = Block id' inputs' stmts' where
  id'     = instantiateBlockID subst id
  inputs' = instantiateCtxRepr subst inputs
  stmts'  = instantiateStmtSeq subst stmts

instantiateSwitch :: CtxRepr subst -> SwitchTarget blocks ctx tp
                  -> SwitchTarget (Instantiate subst blocks) (Instantiate subst ctx) (Instantiate subst tp)
instantiateSwitch subst (SwitchTarget bid argTys args)  =
  SwitchTarget (instantiateBlockID subst bid)
               (instantiateCtxRepr subst argTys)
               (instantiateArgs subst args)


instantiateJumpTarget :: CtxRepr subst -> JumpTarget blocks ctx
                  -> JumpTarget (Instantiate subst blocks) (Instantiate subst ctx) 
instantiateJumpTarget subst (JumpTarget bid argTys args)  =
  JumpTarget (instantiateBlockID subst bid)
               (instantiateCtxRepr subst argTys)
               (instantiateArgs subst args)

instantiateSwitchMap :: CtxRepr subst
  -> Assignment (SwitchTarget blocks ctx) args
  -> Assignment (SwitchTarget (Instantiate subst blocks) (Instantiate subst ctx)) (Instantiate subst args)
instantiateSwitchMap subst assign =
  case viewAssign assign of
    AssignEmpty -> Ctx.Empty
    AssignExtend bm b -> (instantiateSwitchMap subst bm) Ctx.:> (instantiateSwitch subst b)
instantiateArgs :: CtxRepr subst
  -> Assignment (Reg ctx) args
  -> Assignment (Reg (Instantiate subst ctx)) (Instantiate subst args)
instantiateArgs subst assign =
  case viewAssign assign of
    AssignEmpty -> Ctx.Empty
    AssignExtend bm b -> (instantiateArgs subst bm) Ctx.:> (instantiateReg subst b)

instantiateBlockMap :: CtxRepr subst
  -> Assignment (Block ext blocks' ret) blocks
  -> Assignment (Block ext (Instantiate subst blocks') (Instantiate subst ret)) (Instantiate subst blocks)
instantiateBlockMap subst assign =
  case viewAssign assign of
    AssignEmpty -> Ctx.Empty
    AssignExtend bm b -> (instantiateBlockMap subst bm) Ctx.:> (instantiateBlock subst b)


instantiatePostdomBlock :: forall subst blocks' b.
  CtxRepr subst -> Const [Some (BlockID blocks')] b -> 
  Const [Some (BlockID (Instantiate subst blocks'))] (Instantiate subst b)
instantiatePostdomBlock subst (Const x) =
  let  instSome :: Some (BlockID blocks') -> Some (BlockID (Instantiate subst blocks'))
       instSome (Some bid) = Some (instantiateBlockID subst bid)
  in
  Const (map instSome x)

instantiateCFGPostdom :: CtxRepr subst
                      -> Assignment (Const [Some (BlockID blocks')]) blocks
                      -> Assignment (Const [Some (BlockID (Instantiate subst blocks'))]) (Instantiate subst blocks)
instantiateCFGPostdom subst assign =
  case viewAssign assign of
    AssignEmpty -> Ctx.Empty
    AssignExtend bm b -> instantiateCFGPostdom subst bm Ctx.:> instantiatePostdomBlock subst b


instantiateCFG :: CtxRepr subst -> CFG ext blocks init ret
  -> CFG ext (Instantiate subst blocks) (Instantiate subst init) (Instantiate subst ret)
instantiateCFG subst (CFG handle blockMap entryBlockID) =
  ICFG handle subst (instantiateBlockMap subst blockMap) (instantiateBlockID subst entryBlockID)
instantiateCFG subst (ICFG subst' handle blockMap entryBlockID) = error "TODO"
  -- ICFG (instantiateCtxRepr subst subst') handle (error "TODO") (error "TODO")
  


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

--



ppReg :: Size ctx -> Doc
ppReg h = text "$" <> int (sizeInt h)

nextStmtHeight :: Size ctx -> Stmt ext ctx ctx' -> Size ctx'
nextStmtHeight h s =
  case s of
    SetReg{} -> incSize h
    ExtendAssign{} -> incSize h
    CallHandle{} -> incSize h
--    CallPHandle{} -> incSize h
    Print{} -> h
    ReadGlobal{} -> incSize h
    WriteGlobal{} -> h
    FreshConstant{} -> Ctx.incSize h
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
{-    CallPHandle _ h _targs _ args ->
      ppReg r <+> text "= callp"
              <+> pretty h <> langle <> rangle   --- TODO: print type arguments
              <> parens (commas (ppAssignment args))
              <> text ";"               -}
    Print msg -> ppFn "print" [ pretty msg ]
    ReadGlobal v -> text "read" <+> ppReg r <+> pretty v
    WriteGlobal v e -> text "write" <+> pretty v <+> pretty e
    FreshConstant bt nm -> ppReg r <+> text "=" <+> text "fresh" <+> pretty bt <+> maybe mempty (text . show) nm
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
--
-- Some CFGs may have polymorphic FnHandles. In that case, they can include
-- a type instantiation

data CFG (ext :: Type)
         (blocks :: Ctx (Ctx CrucibleType))
         (init :: Ctx CrucibleType)
         (ret :: CrucibleType)
     
   = CFG { cfgHandle :: (FnHandle init ret)
         , cfgBlockMap :: !(BlockMap ext blocks ret)
         , cfgEntryBlockID :: !(BlockID blocks init)
         }
     
   | forall subst init' ret'.
     (Instantiate subst init' ~ init, Instantiate subst ret' ~ ret) =>
     ICFG { 
            cfgIHandle :: (FnHandle init' ret')
          , cfgSubst :: !(CtxRepr subst)
          , cfgBlockMap :: !(BlockMap ext blocks ret)
          , cfgEntryBlockID :: !(BlockID blocks init)
         }

cfgHandleName :: CFG ext blocks init ret -> FunctionName
cfgHandleName (CFG h _ _) = handleName h
cfgHandleName (ICFG h _ _ _) = handleName h

cfgArgTypes :: CFG ext blocks init ret -> CtxRepr init
cfgArgTypes (CFG h _ _) = handleArgTypes h
cfgArgTypes (ICFG h s _ _) = instantiateCtxRepr s (handleArgTypes h)

cfgReturnType :: CFG ext blocks init ret -> TypeRepr ret
cfgReturnType (CFG h _ _) = handleReturnType h
cfgReturnType (ICFG h s _ _) = instantiateRepr s (handleReturnType h)

updateCFG :: (BlockMap ext blocks' ret) -> (BlockID blocks' init) -> CFG ext blocks init ret -> CFG ext blocks' init ret
updateCFG b m (CFG h _ _) = CFG h b m
updateCFG b m (ICFG h s _ _) = ICFG h s b m


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
