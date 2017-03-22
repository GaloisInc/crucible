{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}

module Lang.Crucible.Analysis.Taint where

import Lang.Crucible.Analysis.Fixpoint
import Lang.Crucible.Core

import qualified Data.Parameterized.Context as PU
import qualified Data.Parameterized.TraversableFC as PU
import qualified Data.Parameterized.Map as PM

import Control.Lens

data Tainted (tp :: CrucibleType) where
  Tainted :: Tainted tp
  Untainted :: Tainted tp
  deriving (Eq, Show)

join t1 t2 = if t1 == Tainted || t2 == Tainted then Tainted
             else Untainted

taintDomain :: Domain Tainted
taintDomain = Domain {domTop = Tainted
                     ,domBottom = Untainted
                     ,domJoin = join
                     ,domEq = (==)
                     ,domIter = WTO
                     }

taintInterp :: Interpretation Tainted
taintInterp = Interpretation {interpExpr = taintExpr
                             ,interpCall = taintCall
                             ,interpReadGlobal = taintReadGlobal
                             ,interpWriteGlobal = taintWriteGlobal
                             ,interpBr = taintBranch
                             ,interpMaybe = taintMaybe
                             }

taintExpr :: forall ctx tp. TypeRepr tp
          -> Expr ctx tp
          -> PointAbstraction Tainted ctx
          -> (Maybe (PointAbstraction Tainted ctx), Tainted tp)
taintExpr tyrepr (App expr) taintMap = case expr of
  EmptyApp -> puret Untainted
  
  IntLit _ -> puret Untainted
  IntAdd r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  
  RationalLit _ -> puret Untainted
  RealAdd r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  RealSub r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  RealMul r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  RealIte cr rt re -> puret $ depOnRegs [cr] taintMap `join` depOnRegs [rt, re] taintMap
  RealEq r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  RealLt r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
--  RealIsInteger r -> puret $ lookupAbstractRegValue taintMap r
  
  BVUndef _ -> puret Untainted
  BVLit _ _ -> puret Untainted
  BVEq _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVNot _ r -> puret $ lookupAbstractRegValue taintMap r
  BVAnd _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVOr _ r1 r2  -> puret $ depOnRegs [r1, r2] taintMap
  BVXor _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVAdd _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVSub _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVMul _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVUdiv _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVSdiv _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVUrem _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVSrem _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVUle  _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVSle  _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVUlt  _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVSlt  _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVShl  _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVAshr _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVLshr _ r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BVIte g _ r1 r2 -> puret $ depOnRegs [g] taintMap `join` depOnRegs [r1, r2] taintMap

  BoolLit _ -> puret Untainted
  Not r -> puret $ lookupAbstractRegValue taintMap r
  And r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  Or r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BoolXor r1 r2 -> puret $ depOnRegs [r1, r2] taintMap
  BoolIte g t e -> puret $ depOnRegs [g, t, e] taintMap
  TextLit _ -> puret Untainted
  MkStruct ctxrepr assignment -> error "TODO: handle MkStruct in taint analysis"

depOnRegs rs taintMap = foldl join Untainted $ map (lookupAbstractRegValue taintMap) rs
  
puret = (Nothing, )
    
taintCall :: forall ctx args ret. CtxRepr args
          -> TypeRepr ret
          -> Reg ctx (FunctionHandleType args ret)
          -> Tainted (FunctionHandleType args ret)
          -> PU.Assignment Tainted args
          -> PointAbstraction Tainted ctx
          -> (Maybe (PointAbstraction Tainted ctx), Tainted ret)
taintCall ctxRepr tyRepr funHandleReg funHandleTaint args ctxTaint = undefined

taintReadGlobal :: forall ctx tp. GlobalVar tp
                -> PointAbstraction Tainted ctx
                -> (Maybe (PointAbstraction Tainted ctx), Tainted tp)
taintReadGlobal var taintMap = case PM.lookup var $ taintMap ^. paGlobals of
  Nothing -> puret Untainted
  Just t  -> puret t

taintWriteGlobal :: forall ctx tp. GlobalVar tp
                 -> Reg ctx tp
                 -> PointAbstraction Tainted ctx
                 -> Maybe (PointAbstraction Tainted ctx)
taintWriteGlobal var reg taintMap =  let rt = lookupAbstractRegValue taintMap reg
                                     in  Just $ taintMap & paGlobals %~ PM.insert var rt

taintBranch :: forall blocks ctx. Reg ctx BoolType
            -> Tainted BoolType
            -> JumpTarget blocks ctx
            -> JumpTarget blocks ctx
            -> PointAbstraction Tainted ctx
            -> (Maybe (PointAbstraction Tainted ctx), Maybe (PointAbstraction Tainted ctx))
taintBranch _guardReg _guardTaint _then_ _else_ _taintMap  = (Nothing, Nothing) -- ^ We are not handling implicit flow

taintMaybe :: forall ctx tp. TypeRepr tp
           -> Reg ctx (MaybeType tp)
           -> Tainted (MaybeType tp)
           -> PointAbstraction Tainted ctx
           -> (Maybe (PointAbstraction Tainted ctx), Tainted tp, Maybe (PointAbstraction Tainted ctx))
taintMaybe = undefined
  
