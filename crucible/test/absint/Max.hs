-- | A domain for tracking the maximum value a register can take
--
-- This is intentionally a very tall domain so that widening is
-- required.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Max (
  Max(..), SyntaxExt,
  maxDom,
  maxInterp
  ) where

import qualified Data.Parameterized.Context as PU

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import Lang.Crucible.Analysis.Fixpoint

data Max (tp :: C.CrucibleType) where
  Max :: Int -> Max tp

deriving instance Eq (Max tp)
deriving instance Show (Max tp)

instance C.ShowF Max

type Max' = Pointed Max

maxDom :: Domain Max'
maxDom = d
  where
    d = pointed j (==) (WTOWidening (> 10) w)
    j (Max i1) (Max i2) = Pointed (Max (max i1 i2))
    w _ _ = Top

type SyntaxExt = ()

maxInterp :: Interpretation SyntaxExt Max'
maxInterp = Interpretation { interpExpr = mExpr
                           , interpExt = undefined
                           , interpCall = mCall
                           , interpReadGlobal = mRdGlobal
                           , interpWriteGlobal = mWrGlobal
                           , interpBr = mBr
                           , interpMaybe = mMaybe
                           }

mExpr :: ScopedReg
        -> C.TypeRepr tp
        -> C.Expr ext ctx tp
        -> PointAbstraction blocks Max' ctx
        -> (Maybe (PointAbstraction blocks Max' ctx), Max' tp)
mExpr _sr _tr (C.App e) abstr =
  case e of
    C.IntLit i -> (Nothing, Pointed (Max (fromIntegral i)))
    C.IntAdd r1 r2 ->
      let a1 = lookupAbstractRegValue abstr r1
          a2 = lookupAbstractRegValue abstr r2
      in case (a1, a2) of
        (Pointed (Max m1), Pointed (Max m2)) -> (Nothing, Pointed (Max (m1 + m2)))
        _ -> (Nothing, Top)
    _ -> (Nothing, Top)

mCall :: C.CtxRepr args
        -> C.TypeRepr ret
        -> C.Reg ctx (C.FunctionHandleType args ret)
        -> Max' (C.FunctionHandleType args ret)
        -> PU.Assignment Max' args
        -> PointAbstraction blocks dom ctx
        -> (Maybe (PointAbstraction blocks Max' ctx), Max' ret)
mCall _ _ _ _ _ _ = (Nothing, Top)

mBr :: C.Reg ctx C.BoolType
      -> Max' C.BoolType
      -> C.JumpTarget blocks ctx
      -> C.JumpTarget blocks ctx
      -> PointAbstraction blocks Max' ctx
      -> (Maybe (PointAbstraction blocks Max' ctx), Maybe (PointAbstraction blocks Max' ctx))
mBr _ _ _ _ _ = (Nothing, Nothing)

mMaybe :: C.TypeRepr tp
         -> C.Reg ctx (C.MaybeType tp)
         -> Max' (C.MaybeType tp)
         -> PointAbstraction blocks Max' ctx
         -> (Maybe (PointAbstraction blocks Max' ctx), Max' tp, Maybe (PointAbstraction blocks Max' ctx))
mMaybe _ _ _ _ = (Nothing, Top, Nothing)

mWrGlobal :: C.GlobalVar tp -> C.Reg ctx tp -> PointAbstraction blocks Max' ctx -> Maybe (PointAbstraction blocks Max' ctx)
mWrGlobal _ _ _ = Nothing

mRdGlobal :: C.GlobalVar tp -> PointAbstraction blocks Max' ctx -> (Maybe (PointAbstraction blocks Max' ctx), Max' tp)
mRdGlobal _ _ = (Nothing, Top)
