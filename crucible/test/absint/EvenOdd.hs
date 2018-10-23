-- | A simple domain for tracking even-ness and odd-ness of values
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module EvenOdd (
  EvenOdd(..), EOExt,
  evenOddDom,
  evenOddInterp
  ) where

import qualified Data.Parameterized.Context as PU

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import Lang.Crucible.Analysis.Fixpoint

data EvenOdd (tp :: C.CrucibleType) where
  Even :: EvenOdd tp
  Odd :: EvenOdd tp

deriving instance Eq (EvenOdd tp)
deriving instance Show (EvenOdd tp)

instance C.ShowF EvenOdd

type EvenOdd' = Pointed EvenOdd

evenOddDom :: Domain EvenOdd'
evenOddDom = pointed j (==) WTO
  where
    j Even Odd = Top
    j Odd Even = Top
    j Even Even = Pointed Even
    j Odd Odd = Pointed Odd

type EOExt = ()

evenOddInterp :: Interpretation EOExt EvenOdd'
evenOddInterp = Interpretation { interpExpr = eoIExpr
                               , interpExt = undefined
                               , interpCall = eoICall
                               , interpReadGlobal = eoIRdGlobal
                               , interpWriteGlobal = eoIWrGlobal
                               , interpBr = eoIBr
                               , interpMaybe = eoIMaybe
                               }

eoIExpr :: ScopedReg
        -> C.TypeRepr tp
        -> C.Expr ext ctx tp
        -> PointAbstraction EvenOdd' ctx
        -> (Maybe (PointAbstraction EvenOdd' ctx), EvenOdd' tp)
eoIExpr _sr _tr (C.App e) abstr =
  case e of
    C.IntLit i -> (Nothing, if i `mod` 2 == 0 then Pointed Even else Pointed Odd)
    C.IntAdd r1 r2 ->
      let a1 = lookupAbstractRegValue abstr r1
          a2 = lookupAbstractRegValue abstr r2
      in case (a1, a2) of
        (Pointed Even, Pointed Even) -> (Nothing, Pointed Even)
        (Pointed Odd, Pointed Odd) -> (Nothing, Pointed Even)
        (Pointed Even, Pointed Odd) -> (Nothing, Pointed Odd)
        (Pointed Odd, Pointed Even) -> (Nothing, Pointed Odd)
        _ -> (Nothing, Top)
    _ -> (Nothing, Top)

eoICall :: C.CtxRepr args
        -> C.TypeRepr ret
        -> C.Reg ctx (C.FunctionHandleType args ret)
        -> EvenOdd' (C.FunctionHandleType args ret)
        -> PU.Assignment EvenOdd' args
        -> PointAbstraction dom ctx
        -> (Maybe (PointAbstraction EvenOdd' ctx), EvenOdd' ret)
eoICall _ _ _ _ _ _ = (Nothing, Top)

eoIBr :: C.Reg ctx C.BoolType
      -> EvenOdd' C.BoolType
      -> C.JumpTarget blocks ctx
      -> C.JumpTarget blocks ctx
      -> PointAbstraction EvenOdd' ctx
      -> (Maybe (PointAbstraction EvenOdd' ctx), Maybe (PointAbstraction EvenOdd' ctx))
eoIBr _ _ _ _ _ = (Nothing, Nothing)

eoIMaybe :: C.TypeRepr tp
         -> C.Reg ctx (C.MaybeType tp)
         -> EvenOdd' (C.MaybeType tp)
         -> PointAbstraction EvenOdd' ctx
         -> (Maybe (PointAbstraction EvenOdd' ctx), EvenOdd' tp, Maybe (PointAbstraction EvenOdd' ctx))
eoIMaybe _ _ _ _ = (Nothing, Top, Nothing)

eoIWrGlobal :: C.GlobalVar tp -> C.Reg ctx tp -> PointAbstraction EvenOdd' ctx -> Maybe (PointAbstraction EvenOdd' ctx)
eoIWrGlobal _ _ _ = Nothing

eoIRdGlobal :: C.GlobalVar tp -> PointAbstraction EvenOdd' ctx -> (Maybe (PointAbstraction EvenOdd' ctx), EvenOdd' tp)
eoIRdGlobal _ _ = (Nothing, Top)
