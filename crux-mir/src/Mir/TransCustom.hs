{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}

module Mir.TransCustom(customOps) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.String as String
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V

import Control.Monad
import Control.Lens

import GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Peano
import Data.Parameterized.Some
import Data.Parameterized.WithRepr


-- crucible
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Substitution()
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.CFG.Reg as R

import qualified What4.ProgramLoc as PL



import qualified Mir.DefId as M
import           Mir.Mir
import qualified Mir.MirTy as M

import           Mir.PP (fmt)
import           Mir.Generator hiding (customOps)
import           Mir.Intrinsics
import           Mir.TransTy
import           Mir.Trans

import Debug.Trace

--------------------------------------------------------------------------------------------------------------------------
-- * Data structure manipulation for implementing primitives

-- ** options

-- | Construct an option::Some value
mkSome :: C.TypeRepr tp -> G.Expr MIR s tp -> G.Expr MIR s TaggedUnion
mkSome ty val =
   let tty  = C.StructRepr (Ctx.empty Ctx.:> ty) in
   let tval = G.App $ E.MkStruct (Ctx.empty Ctx.:> ty) (Ctx.empty Ctx.:> val) in
   G.App $ E.MkStruct (Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) 
                      (Ctx.empty Ctx.:> (S.app $ E.NatLit 1) Ctx.:> (S.app $ E.PackAny tty tval))

-- | Construct an option::None value
mkNone :: G.Expr MIR s TaggedUnion
mkNone =
  let ty  = C.StructRepr Ctx.empty in
  let val = S.app $ E.MkStruct Ctx.empty Ctx.empty in
  G.App $ E.MkStruct (Ctx.empty Ctx.:> C.NatRepr Ctx.:> C.AnyRepr) 
                     (Ctx.empty Ctx.:> (S.app $ E.NatLit 0) Ctx.:> (S.app $ E.PackAny ty val))

-- ** range

-- | Project the "start" component of a range::Range value
rangeStart :: C.TypeRepr ty -> R.Expr MIR s TaggedUnion -> MirGenerator h s ret (R.Expr MIR s ty)
rangeStart itemRepr r = do
   (MirExp C.AnyRepr tup) <- accessAggregate (MirExp taggedUnionRepr r) 1
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
   let strTy = C.StructRepr ctx
   let unp   = S.app $ E.FromJustValue strTy (S.app $ E.UnpackAny strTy tup)
                                     (String.fromString ("Bad Any unpack rangeStart:" ++ show strTy))
   let start = S.getStruct Ctx.i1of2 unp
   return start

-- | Project the "end" component of a range::Range value
rangeEnd :: C.TypeRepr ty -> R.Expr MIR s TaggedUnion -> MirGenerator h s ret (R.Expr MIR s ty)
rangeEnd itemRepr r = do
   (MirExp C.AnyRepr tup) <- accessAggregate (MirExp taggedUnionRepr r) 1
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
   let strTy = C.StructRepr ctx
   let unp   = S.app $ E.FromJustValue strTy (S.app $ E.UnpackAny strTy tup)
                                     (String.fromString ("Bad Any unpack rangeEnd:" ++ show strTy))
   let end   = S.getStruct Ctx.i2of2 unp
   return end

-- | Construct a range::Range value given start & end 
mkRange :: C.TypeRepr ty -> R.Expr MIR s ty -> R.Expr MIR s ty -> R.Expr MIR s TaggedUnion
mkRange itemRepr start end = 
   let ctx   = (Ctx.empty `Ctx.extend` itemRepr `Ctx.extend` itemRepr)
       strTy = C.StructRepr ctx
       y     = S.app $ E.PackAny strTy (S.app $ E.MkStruct ctx (Ctx.empty `Ctx.extend` start `Ctx.extend` end))
       j     = S.app $ E.MkStruct taggedUnionCtx (Ctx.empty `Ctx.extend` (S.litExpr 0) `Ctx.extend` y)
   in  j


--------------------------------------------------------------------------------------------------------------------------
-- *  Primitives & other custom stuff



customOps :: Map ExplodedDefId CustomRHS
customOps = Map.fromList [
                           slice_index_usize_get_unchecked
                         , slice_index_range_get_unchecked
                         , slice_index_usize_get_unchecked_mut
                         , slice_index_range_get_unchecked_mut

                         , type_id
                         , mem_swap
                         , add_with_overflow
                         , sub_with_overflow

                         -- CustomOps below this point have not been checked
                         -- for compatibility with new monomorphization.

                         , slice_len
                         , slice_is_empty
                         , slice_first
                         --, slice_get
                         --, slice_get_mut

                         --, slice_get_unchecked
                         --, slice_get_unchecked_mut


                         , str_len

                         --, ops_index
                         --, ops_index_mut

                         , into_iter
                         , iter_next
                         , iter_collect

                         , wrapping_mul
                         , wrapping_sub
                         , discriminant_value

                         , exit
                         , abort
                         , panicking_begin_panic
                         , panicking_panic


                         , integer_from_u8
                         , integer_from_i32
                         , integer_from_u64
                         , integer_as_u8
                         , integer_as_u64
                         , integer_shl
                         , integer_shr
                         , integer_bitand
                         , integer_bitor
                         , integer_add
                         , integer_sub
                         , integer_rem
                         , integer_eq
                         , integer_lt
                         ]


 
-----------------------------------------------------------------------------------------------------
-- ** Custom: Exit

exit :: (ExplodedDefId, CustomRHS)
exit = ((["std", "process"], "exit", []), \s ->
           Just (CustomOpExit $ \ops -> return "process::exit"))

abort :: (ExplodedDefId, CustomRHS)
abort = ((["core", "intrinsics"], "abort", []), \s ->
            Just (CustomOpExit $ \ops -> return "intrinsics::abort"))

panicking_begin_panic :: (ExplodedDefId, CustomRHS)
panicking_begin_panic = ((["std", "panicking"], "begin_panic", []), \s ->
            Just (CustomOpExit $  \ops -> return "panicking::begin_panic"))

panicking_panic :: (ExplodedDefId, CustomRHS)
panicking_panic = ((["core", "panicking"], "panic", []), \s ->
            Just (CustomOpExit $  \ops -> return "panicking::panic"))

-----------------------------------------------------------------------------------------------------
-- ** Custom: Index

-- TODO: these are trait implementations, so we should do what we did with the SliceIndex versions below
-- so that we can make dictionaries.

ops_index :: (ExplodedDefId, CustomRHS)
ops_index = ((["core", "ops", "index"], "Index", ["index"]), index_op )

ops_index_mut :: (ExplodedDefId, CustomRHS)
ops_index_mut = ((["core", "ops", "index"], "IndexMut", ["index_mut"]), index_op_mut )


{-
libcore/slice.rs includes the following impl that I don't know how to get through
rustc. So we implement by hand here.

    impl<T, I> Index<I> for [T]
    where I: SliceIndex<[T]>
    {
        type Output = I::Output;
        
        #[inline]
        fn index(&self, index: I) -> &I::Output {
            index.index(self)
        }
    }

    impl<T, I> IndexMut<I> for [T]
    where I: SliceIndex<[T]>
    {
        #[inline]
        fn index_mut(&mut self, index: I) -> &mut I::Output {
            index.index_mut(self)
        }
    }


-}

index_op :: Substs -> Maybe CustomOp
index_op (Substs [TySlice elTy, ii@(TyAdt _did _ss), iiOutput ]) =
    Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::index[0]")
                      -- TODO: third arg in substs should be iiOutput, but TyProj not removed
                  let substs = Substs [ii, TySlice elTy, TySlice elTy]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to index"
index_op _ = Nothing



index_op_mut :: Substs -> Maybe CustomOp
index_op_mut (Substs [TySlice elTy, ii@(TyAdt _did _ss), iiOutput ]) =
    Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::index_mut[0]")
                      -- TODO: third arg in substs should be iiOutput, but TyProj not removed
                  let substs = Substs [ii, TySlice elTy, TySlice elTy]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to index_mut"
index_op_mut _ = Nothing
--------------------------------------------------------------------------------------------------------------------------

-- ** Custom: wrapping_mul

-- TODO: this should return (a * b) mod 2N
-- however it does whatever Crucible does for BVMul
wrapping_mul :: (ExplodedDefId, CustomRHS)
wrapping_mul = ( (["core","num","{{impl}}"], "wrapping_mul", []),
   \ _substs -> Just $ CustomOp $ \ _opTys  ops ->
     case ops of 
       [MirExp aty a, MirExp bty b] ->
         
         case (aty, bty) of
           (C.BVRepr wa, C.BVRepr wb) | Just Refl <- testEquality wa wb -> do
               let sub = R.App $ E.BVMul wa a b 
               return (MirExp aty sub)
           (C.NatRepr, C.NatRepr) -> do
               let sub = R.App $ E.NatMul a b
               return (MirExp aty sub)               
           (_,_) -> mirFail $ "wrapping_mul: cannot call with types " ++ show aty ++ " and " ++ show bty

       _ -> mirFail $ "BUG: invalid arguments for wrapping_mul")


-- ** Custom: wrapping_sub

wrapping_sub :: (ExplodedDefId, CustomRHS)
wrapping_sub = ( (["core","num","{{impl}}"], "wrapping_sub", []),
   \ _substs -> Just $ CustomOp $ \ _opTys ops ->
     case ops of 
       [MirExp aty a, MirExp bty b] ->
         -- return (a - b) mod 2N  (this is the default behavior for BVSub)
         case (aty, bty) of
           (C.BVRepr wa, C.BVRepr wb) | Just Refl <- testEquality wa wb -> do
               let sub = R.App $ E.BVSub wa a b 
               return (MirExp aty sub)
           (C.NatRepr, C.NatRepr) -> do
               let sub = R.App $ E.NatSub a b
               return (MirExp aty sub)
           (_,_) -> mirFail $ "wrapping_sub: cannot call with types " ++ show aty ++ " and " ++ show bty

       _ -> mirFail $ "BUG: invalid arguments for wrapping_sub")

---------------------------------------------------------------------------------------
-- ** Custom ::intrinsics::discriminant_value

discriminant_value ::  (ExplodedDefId, CustomRHS)
discriminant_value = ((["core","intrinsics"],"discriminant_value", []),
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
      case (opTys,ops) of
        ([TyCustom (CEnum _adt _i)], [e]) -> return e
        ([_],[e]) -> do (MirExp C.NatRepr idx) <- accessAggregate e 0
                        return $ (MirExp knownRepr $ R.App (E.IntegerToBV (knownRepr :: NatRepr 64)
                                                                  (R.App (E.NatToInteger idx))))
        _ -> mirFail $ "BUG: invalid arguments for discriminant_value")

type_id ::  (ExplodedDefId, CustomRHS)
type_id = ((["core","intrinsics"],"type_id", []),
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
    -- TODO: keep a map from Ty to Word64, assigning IDs on first use of each type
    return $ MirExp knownRepr $ R.App (E.BVLit (knownRepr :: NatRepr 64) 0))

---------------------------------------------------------------------------------------
-- ** Custom: Iterator

-- TODO: should replace these with mir-lib implementations


into_iter :: (ExplodedDefId, CustomRHS)
into_iter = ((["core","iter","traits","collect"], "IntoIterator", ["into_iter"]),
    \(Substs subs) -> case subs of
       [ TyAdt defid (Substs [itemTy]) ]
         | defid == M.textId "::core[0]::ops[0]::range[0]::Range[0]"
         ->  Just $ CustomOp $ \_opTys [arg] -> return arg

       [ TyRef (TyArray itemTy size) Immut ]
         ->  Just $ CustomOp $ \_opTys [arg] -> do
             -- array iterator: a pair of the vector and the index
             -- this is not the implementation of "slice::Iter"
             -- but should be
             let x = buildTuple [arg, MirExp (C.NatRepr) (S.app $ E.NatLit 0)]
             let y = buildTuple [MirExp C.NatRepr (S.app $ E.NatLit 0), packAny x]
             return y
       _ -> Nothing)
               
      
iter_next :: (ExplodedDefId, CustomRHS)
iter_next = ((["core","iter","traits","iterator"],"Iterator", ["next"]), iter_next_op) where
  iter_next_op (Substs [TyAdt defid (Substs [itemTy])])
    | defid == M.textId "::core[0]::ops[0]::range[0]::Range[0]"  = Just (CustomOp (iter_next_op_range itemTy))
  iter_next_op (Substs [TyAdt defid (Substs [_,itemTy])])
    | defid == M.textId "::core[0]::slice[0]::Iter[0]" = Just (CustomOp (iter_next_op_array itemTy))
  iter_next_op (Substs [TyArray itemTy _len]) = Just (CustomOp (iter_next_op_array itemTy))
  iter_next_op _ = Nothing


iter_next_op_range :: forall h s ret. HasCallStack => Ty -> [Ty] -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_next_op_range itemTy _opTys ops =
    case ops of 
       [ MirExp (MirReferenceRepr tr) ii ]
         | Just Refl <- testEquality tr taggedUnionRepr
         -> do
             -- iterator is a struct of a "start" and "end" value of type 'itemTy'
             -- to increment the iterator, make sure the start < end and then
             tyToReprCont itemTy $ \itemRepr -> do

                r <- readMirRef tr ii
                start <- rangeStart itemRepr r
                end   <- rangeEnd   itemRepr r

                plus_one <- incrExp itemRepr start
                let good_ret = mkSome itemRepr start
                let bad_ret  = mkNone
                let  updateRange :: MirGenerator h s ret ()
                     updateRange = writeMirRef ii (mkRange itemRepr plus_one end)

                (MirExp C.BoolRepr boundsCheck)
                     <- evalBinOp Lt (arithType itemTy) (MirExp itemRepr start)
                                                          (MirExp itemRepr end)
                ret <- G.ifte boundsCheck
                           (updateRange >> return good_ret)
                           (return bad_ret)
                return (MirExp taggedUnionRepr ret)
       _ -> mirFail $ "BUG: invalid arguments for iter_next"


iter_next_op_array :: forall h s ret. HasCallStack => Ty -> [Ty] -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_next_op_array itemTy _opTys ops = 
    -- iterator is a reference to a struct containing (vec, pos of nat)
    -- if pos < size of vec, return (Some(vec[pos]) and update ref to (vec, pos+1)).
    -- otherwise return None  (and leave ref alone)
  case ops of
    [MirExp (MirReferenceRepr tp) iter_ref]
     | Just Refl <- testEquality tp taggedUnionRepr -> do
      tyToReprCont itemTy $ \ elemTy -> do
        adt <- readMirRef tp iter_ref
        let iter = S.getStruct Ctx.i2of2 adt   -- get the data value (we know that the tag is
        let ctx = Ctx.empty Ctx.:> (C.VectorRepr elemTy) Ctx.:> C.NatRepr
        let tr = (C.StructRepr ctx)
        let iter' = (S.app $ E.FromJustValue tr (S.app $ E.UnpackAny tr iter) (String.fromString ("Bad Any unpack: " ++ show tr)))
        let iter_vec = S.getStruct Ctx.i1of2 iter'
        let iter_pos = S.getStruct Ctx.i2of2 iter' 
        let is_good    = S.app $ E.NatLt iter_pos (S.app $ E.VectorSize iter_vec)

            good_ret_1 = mkSome elemTy (S.app $ E.VectorGetEntry elemTy iter_vec iter_pos)
            next_iter  = S.app $ E.MkStruct taggedUnionCtx
                            (Ctx.empty Ctx.:> (S.app $ E.NatLit 0) Ctx.:> (S.app $ E.PackAny (C.StructRepr ctx) tup))
            tup = G.App (E.MkStruct ctx (Ctx.empty Ctx.:> iter_vec Ctx.:> next_pos)) 
            next_pos = (S.app $ E.NatAdd iter_pos (S.app $ E.NatLit 1))


        ret <- withRepr taggedUnionRepr $ G.ifte is_good
                (do writeMirRef iter_ref next_iter
                    return good_ret_1)
                (return mkNone)
        return $ MirExp taggedUnionRepr ret
    _ -> mirFail $ "BUG: invalid args to iter_next_op_array " ++ show ops


iter_collect :: (ExplodedDefId, CustomRHS)
iter_collect = ((["core","iter","traits","iterator"],"Iterator", ["collect"]), \subst -> Just $ CustomOp $ iter_collect_op subst)

iter_collect_op ::  forall h s ret. HasCallStack => Substs -> [Ty] -> [MirExp s] -> MirGenerator h s ret (MirExp s)
iter_collect_op _subst _opTys ops =
   case ops of
     [ iter ] -> accessAggregate iter 0
     _ -> mirFail $ "BUG: invalid arguments to iter_collect"


-------------------------------------------------------------------------------------------------------
-- ** Custom: string operations
--
str_len :: (ExplodedDefId, CustomRHS)
str_len =
  ((["core","str","{{impl}}"], "len", [])
  , \subs -> case subs of
               (Substs []) -> Just $ CustomOp $ \ _optys  ops -> 
                 case ops of 
                    -- type of the structure is &str == TyStr ==> C.VectorRepr BV32
                   [MirExp (C.VectorRepr _) vec_e] -> do
                        return (MirExp C.NatRepr  (G.App $ E.VectorSize vec_e))
                   _ -> mirFail $ "BUG: invalid arguments to " ++ "string len"

               _ -> Nothing)


-------------------------------------------------------------------------------------------------------
-- ** Custom: slice impl functions
--
-- MOST of the operations below implement the following impl
-- the execption is get/get_mut, which is specialized to Range
{-
    impl<T>[T] {
        // must override
        pub const fn len(&self) -> usize {
            ....
        }

        pub const fn is_empty(&self) -> bool {
            self.len() == 0
        }

        pub fn first(&self) -> Option<&T> {
            self.get(0)
        }

    }
-}


slice_len :: (ExplodedDefId, CustomRHS)
slice_len =
  ((["core","slice","{{impl}}"], "len", [])
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys ops -> 
     case ops of 
     -- type of the structure is &mut[ elTy ]
       [MirExp (C.VectorRepr _) vec_e] -> do
            return (MirExp C.NatRepr  (G.App $ E.VectorSize vec_e))
       _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_len")

slice_is_empty :: (ExplodedDefId, CustomRHS)
slice_is_empty =
  ((["core","slice","{{impl}}"], "is_empty", [])
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys ops -> 
     case ops of 
     -- type of the structure is &mut[ elTy ]
       [MirExp (C.VectorRepr _) vec_e] -> do
            let sz = (G.App $ E.VectorSize vec_e)
            return (MirExp C.BoolRepr (G.App $ E.NatEq sz (G.App $ E.NatLit 0)))
       _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_is_empty")

slice_first :: (ExplodedDefId, CustomRHS)
slice_first =
  ((["core","slice","{{impl}}"], "first", [])
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys  ops -> 
     case ops of 
     -- type of the structure is &mut[ elTy ]
       [MirExp (C.VectorRepr elTy) vec_e] -> do
            return (MirExp elTy (G.App $ E.VectorGetEntry elTy vec_e (G.App $ E.NatLit 0)))
       _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_first")

{-  impl<T>[T] {

        pub fn get<I>(&self, index: I) -> Option<&I::Output>
        where I: SliceIndex<Self>
        {
            index.get(self)
        }
        
        pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
        where I: SliceIndex<Self>
        {
            index.get_mut(self)
        }
    }
-}

-- TODO: since this is a completely custom function, it is not in the collection at all
-- So the AT translation does not know to pass the third type argument for I::Output

slice_get_op :: Substs -> Maybe CustomOp
slice_get_op (Substs [tt, ii]) =
    Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::get[0]")
                      -- TODO: third arg in substs should be iiOutput, but TyProj not removed
                  let substs = Substs [ii, TySlice tt, TySlice tt]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to slice::SliceIndex::get"
slice_get_op _ = Nothing

slice_get_mut_op :: Substs -> Maybe CustomOp
slice_get_mut_op (Substs [tt, ii]) =
    Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::get_mut[0]")
                      -- TODO: third arg in substs should be iiOutput, but TyProj not removed
                  let substs = Substs [ii, TySlice tt, TySlice tt]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to slice::SliceIndex::get_mut"
slice_get_mut_op _ = Nothing


slice_get :: (ExplodedDefId, CustomRHS)
slice_get = ((["core","slice", "{{impl}}"],"get", []), slice_get_op)

slice_get_mut :: (ExplodedDefId, CustomRHS)
slice_get_mut = ((["core","slice", "{{impl}}"],"get_mut", []), slice_get_mut_op)


{---

impl<T> [T] {
   pub unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
        where I: SliceIndex<Self>
    {
        index.get_unchecked(self)
    }

   pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
        where I: SliceIndex<Self>
    {
        index.get_unchecked_mut(self)
    }

   // TODO!!!
   fn index_mut(self, slice: &mut [T]) -> &mut T {
        // N.B., use intrinsic indexing
	std::process::exit(0)
        //&mut (*slice)[self]
    }



}

--}


slice_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_get_unchecked = ((["core","slice", "{{impl}}"],"get_unchecked", []), slice_get_unchecked_op)

slice_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_get_unchecked_mut = ((["core","slice", "{{impl}}"],"get_unchecked_mut", []), slice_get_unchecked_mut_op)

slice_get_unchecked_op :: CustomRHS
slice_get_unchecked_op subs = case subs of
   (Substs [tt, ii])
     -> Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::get_unchecked[0]")
                  -- TODO: this is a real hack. We should find the ATs and look up the output type there
                  let out   = case ii of
                                TyUint USize -> tt
                                _ -> TySlice tt
                  let substs = Substs [ii, TySlice tt, out]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked"
   _ -> Nothing

slice_get_unchecked_mut_op :: CustomRHS
slice_get_unchecked_mut_op subs = case subs of
   (Substs [tt, ii])
     -> Just $ CustomMirOp $ \ ops -> do
             case ops of
               [op1, op2] -> do
                  let funid = (M.textId "core[0]::slice[0]::SliceIndex[0]::get_unchecked_mut[0]")
                  -- TODO: this is a real hack. We should find the ATs and look up the output type there
                  let out   = case ii of
                                TyUint USize -> tt
                                _ -> TySlice tt
                  let substs = Substs [ii, TySlice tt, out]
                  callExp funid substs [op2, op1] 
               _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut"
   _ -> Nothing

-------------------------------------------------------------------------------------------------------------------
{--
--
-- Some trait impls are difficult to define from 'slice.rs'. Instead, we "implement" them with std::process::exit
-- and then override those implementations with custom code here.
-- However, we 

impl<T> SliceIndex<[T]> for usize {
    type Output = T;
    unsafe fn get_unchecked(self, slice: &[T]) -> &T {
        &*slice.as_ptr().add(self)
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut [T]) -> &mut T {
        &mut *slice.as_mut_ptr().add(self)
    }

    fn index_mut(self, slice: &mut [T]) -> &mut T {
        // N.B., use intrinsic indexing
        //&mut (*slice)[self]
	slice_index_usize_index_mut(self,slice)
    }
}
--
--
impl<T> SliceIndex<[T]> for  core::ops::Range<usize> {

    unsafe fn get_unchecked(self, slice: &[T]) -> &[T] {
        std::process::exit(0)
        //from_raw_parts(slice.as_ptr().add(self.start), self.end - self.start)
    }

    //TODO

    unsafe fn get_unchecked_mut(self, slice: &mut [T]) -> &mut [T] {
        std::process::exit(0)
        //from_raw_parts_mut(slice.as_mut_ptr().add(self.start), self.end - self.start)
    }

fn slice_index_usize_get_unchecked<T>(sel: usize,  slice: &[T]) -> &T {
   std::process::exit(0)
}
fn slice_index_usize_get_unchecked_mut<T>(sel: usize,  slice: &mut[T]) -> &mut T {
   std::process::exit(0)

fn slice_index_usize_index_mut<T>(sel: usize,  slice: &mut[T]) -> &mut T {
   std::process::exit(0)
}

fn slice_index_range_get_unchecked<T>(sel: core::ops::Range<usize>,  slice: &[T]) -> &[T] {
   std::process::exit(0)
}
fn slice_index_range_get_unchecked_mut<T>(sel: core::ops::Range<usize>,  slice: &mut[T]) -> &mut [T] {
   std::process::exit(0)
}



--}

--slice_SliceIndex_get_unchecked :: (ExplodedDefId, CustomRHS)
--slice_SliceIndex_get_unchecked = ((["core","slice"],"SliceIndex", ["get_unchecked"]), slice_SliceIndex_get_unchecked_op)

slice_index_usize_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked = ((["core","slice","{{impl}}","get_unchecked"], "crucible_hook_usize", []), \subs ->
   case subs of
     (Substs [ elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
          case ops of
            [MirExp C.NatRepr ind, MirExp (C.VectorRepr el_tp) arr] -> do
                return $ (MirExp el_tp (S.app $ E.VectorGetEntry el_tp arr ind))
            [MirExp C.NatRepr ind, MirExp (MirSliceRepr el_tp) slice] -> do
                let ref   = S.getStruct (Ctx.natIndex @0) slice
                let start = S.getStruct (Ctx.natIndex @1) slice
                let ind'  = start S..+ ind
                arr <- readMirRef (C.VectorRepr el_tp) ref
                return $ (MirExp el_tp (S.app $ E.VectorGetEntry el_tp arr ind'))
            _ -> mirFail $ "BUG: invalid arguments to slice::SliceIndex::get_unchecked"
     _ -> Nothing)

slice_index_range_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked = ((["core","slice","{{impl}}","get_unchecked"], "crucible_hook_range", []), \subs ->
   case subs of
     (Substs [ elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
          case ops of
             [MirExp tr range_e, MirExp (C.VectorRepr ety) vec_e  ]
               | Just Refl <- testEquality tr taggedUnionRepr -> do
                start <- rangeStart C.NatRepr range_e
                stop  <- rangeEnd   C.NatRepr range_e
                v <- vectorCopy ety start stop vec_e
                return $ (MirExp (C.VectorRepr ety) v)

             [ MirExp tr range_e, MirExp (MirSliceRepr ty) vec_e] 
               | Just Refl <- testEquality tr taggedUnionRepr -> do
                start <- rangeStart C.NatRepr range_e
                stop  <- rangeEnd   C.NatRepr range_e 
                let newLen = (S.app $ E.NatSub stop start)
                let s1 = updateSliceLB  ty vec_e start
                let s2 = updateSliceLen ty s1    newLen
                return $ (MirExp (MirSliceRepr ty) s2)

             _ -> mirFail $ "BUG: invalid arguments to slice::SliceIndex::get_unchecked:" ++ show ops
     _ -> Nothing)



slice_index_usize_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked_mut = ((["core","slice","{{impl}}","get_unchecked_mut"], "crucible_hook_usize", []), \subs ->
   case subs of
     (Substs [ _elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
            case ops of

              [MirExp C.NatRepr ind, MirExp (MirSliceRepr el_tp) slice] -> do
                  let ref   = S.getStruct (Ctx.natIndex @0) slice
                  let start = S.getStruct (Ctx.natIndex @1) slice
                  let ind'  = start S..+ ind
                  ref <- subindexRef el_tp ref ind'
                  return $ (MirExp (MirReferenceRepr el_tp) ref)
              _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
     _ -> Nothing)

slice_index_range_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked_mut = ((["core","slice","{{impl}}","get_unchecked_mut"], "crucible_hook_range", []), \subs ->
   case subs of
     (Substs [ _elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
            case ops of

              [ MirExp tr range_e, MirExp (MirSliceRepr ty) vec_e] 
                 | Just Refl <- testEquality tr taggedUnionRepr -> do
                  start <- rangeStart C.NatRepr range_e
                  stop  <- rangeEnd   C.NatRepr range_e 
                  let newLen = (S.app $ E.NatSub stop start)
                  let s1 = updateSliceLB  ty vec_e start
                  let s2 = updateSliceLen ty s1    newLen
                  return $ (MirExp (MirSliceRepr ty) s2)

              _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
     _ -> Nothing)


--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: vec

-- A vector is an array tupled with a length, as an Adt
-- 

{-
vec_with_capacity :: (ExplodedDefId, CustomRHS)
vec_with_capacity =
  ((["alloc","vec"],"Vec", "with_capacity"),
  \subst -> Just $ CustomOp $ \optys _retTy ops -> do
     case ops of
       [ MirExp C.NatRepr capacity ] -> 
-}     




--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Integer

integerWidth = knownNat :: NatRepr 512

integer_from_u8 :: (ExplodedDefId, CustomRHS)
integer_from_u8 = ((["int512", "u8"], "from_prim", []), integerFromUnsigned)

integer_from_i32 :: (ExplodedDefId, CustomRHS)
integer_from_i32 = ((["int512", "i32"], "from_prim", []), integerFromSigned)

integer_from_u64 :: (ExplodedDefId, CustomRHS)
integer_from_u64 = ((["int512", "u64"], "from_prim", []), integerFromUnsigned)

integerFromSigned :: CustomRHS
integerFromSigned (Substs []) =
    let w' = integerWidth in
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w) int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w') (S.app $ E.BVSext w' w int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerFromSigned: " ++ show ops

integerFromUnsigned :: CustomRHS
integerFromUnsigned (Substs []) =
    let w' = integerWidth in
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w) int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w') (S.app $ E.BVZext w' w int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerFromUnsigned: " ++ show ops


integer_as_u8 :: (ExplodedDefId, CustomRHS)
integer_as_u8 = ((["int512", "u8"], "as_prim", []),
    integerAsUnsigned (knownNat :: NatRepr 8))

integer_as_u64 :: (ExplodedDefId, CustomRHS)
integer_as_u64 = ((["int512", "u64"], "as_prim", []),
    integerAsUnsigned (knownNat :: NatRepr 64))

integerAsUnsigned :: 1 <= w => NatRepr w -> CustomRHS
integerAsUnsigned w (Substs []) =
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w) (S.app $ E.BVTrunc w w' int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerAsUnsigned: " ++ show ops


integer_shl :: (ExplodedDefId, CustomRHS)
integer_shl = ((["int512"], "shl", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVShl w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shl: " ++ show ops
    )

integer_shr :: (ExplodedDefId, CustomRHS)
integer_shr = ((["int512"], "shr", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVLshr w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shr: " ++ show ops
    )

integer_bitand :: (ExplodedDefId, CustomRHS)
integer_bitand = ((["int512"], "bitand", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAnd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitand: " ++ show ops
    )

integer_bitor :: (ExplodedDefId, CustomRHS)
integer_bitor = ((["int512"], "bitor", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVOr w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitor: " ++ show ops
    )

integer_eq :: (ExplodedDefId, CustomRHS)
integer_eq = ((["int512"], "eq", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVEq w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_eq: " ++ show ops
    )

integer_lt :: (ExplodedDefId, CustomRHS)
integer_lt = ((["int512"], "lt", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVSlt w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_lt: " ++ show ops
    )

integer_add :: (ExplodedDefId, CustomRHS)
integer_add = ((["int512"], "add", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAdd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_add: " ++ show ops
    )

integer_sub :: (ExplodedDefId, CustomRHS)
integer_sub = ((["int512"], "sub", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSub w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_sub: " ++ show ops
    )

integer_rem :: (ExplodedDefId, CustomRHS)
integer_rem = ((["int512"], "rem", []), \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSrem w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_rem: " ++ show ops
    )




-- mem::swap is used pervasively (both directly and via mem::replace), but it
-- has a nasty unsafe implementation, with lots of raw pointers and
-- reintepreting casts.  Fortunately, it requires `T: Sized`, so it's almost
-- trivial to implement as a custom op.
mem_swap ::  (ExplodedDefId, CustomRHS)
mem_swap = ((["core","mem"],"swap", []),
    \ _substs -> Just $ CustomOp $ \ opTys ops -> case ops of
        [MirExp (MirReferenceRepr ty1) e1, MirExp (MirReferenceRepr ty2) e2]
          | Just Refl <- testEquality ty1 ty2 -> do
            val1 <- readMirRef ty1 e1
            val2 <- readMirRef ty2 e2
            writeMirRef e1 val2
            writeMirRef e2 val1
            return $ MirExp knownRepr $ R.App E.EmptyApp
        _ -> mirFail $ "bad arguments to mem_swap: " ++ show (opTys, ops)
    )

with_overflow_result ::
    C.TypeRepr ty ->
    E.App MIR (R.Expr MIR s) ty ->
    E.App MIR (R.Expr MIR s) C.BoolType ->
    MirExp s
with_overflow_result ty x b = buildTuple
    [ MirExp (C.MaybeRepr ty) $
        R.App $ E.JustValue ty $
        R.App $ x
    , MirExp (C.MaybeRepr C.BoolRepr) $
        R.App $ E.JustValue C.BoolRepr $
        R.App $ b
    ]

add_with_overflow ::  (ExplodedDefId, CustomRHS)
add_with_overflow = ((["core","intrinsics"],"add_with_overflow", []),
    \ _substs -> Just $ CustomOp $ \ opTys ops -> case (opTys, ops) of
        ([TyUint _, TyUint _], [MirExp (C.BVRepr w1) e1, MirExp (C.BVRepr w2) e2])
          | Just Refl <- testEquality w1 w2 -> do
            return $ with_overflow_result
                (C.BVRepr w1) (E.BVAdd w1 e1 e2) (E.BVCarry w1 e1 e2)
        _ -> mirFail $ "bad arguments to add_with_overflow: " ++ show (opTys, ops)
    )

sub_with_overflow ::  (ExplodedDefId, CustomRHS)
sub_with_overflow = ((["core","intrinsics"],"sub_with_overflow", []),
    \ _substs -> Just $ CustomOp $ \ opTys ops -> case (opTys, ops) of
        ([TyUint _, TyUint _], [MirExp (C.BVRepr w1) e1, MirExp (C.BVRepr w2) e2])
          | Just Refl <- testEquality w1 w2 -> do
            return $ with_overflow_result
                (C.BVRepr w1) (E.BVSub w1 e1 e2) (E.BVUlt w1 e1 e2)
        _ -> mirFail $ "bad arguments to add_with_overflow: " ++ show (opTys, ops)
    )



--------------------------------------------------------------------------------------------------------------------------




-- Type-indexed version of "1"
oneExp :: C.TypeRepr ty -> MirExp s
oneExp C.NatRepr    = MirExp C.NatRepr (S.litExpr 1)
oneExp (C.BVRepr w) = MirExp (C.BVRepr w) (R.App (E.BVLit w 1))
oneExp ty = error $ "oneExp: unimplemented for type " ++ show ty

-- Add one to an expression
incrExp :: C.TypeRepr ty -> R.Expr MIR s ty -> MirGenerator h s ret (R.Expr MIR s ty)
incrExp ty e = do res <- evalBinOp Add Nothing (MirExp ty e) (oneExp ty)
                  case res of 
                    (MirExp ty' e') | Just Refl <- testEquality ty ty'
                                    -> return e'
                    _ -> mirFail "BUG: incrExp should return same type"




performUntil :: R.Expr MIR s C.NatType -> (R.Reg s C.NatType -> MirGenerator h s ret ()) -> MirGenerator h s ret ()
performUntil n f = do -- perform (f i) for i = 0..n (not inclusive). f takes as input a nat register (but shouldn't increment it)
    ind <- G.newReg $ S.app $ E.NatLit 0
    G.while (PL.InternalPos, test n ind) (PL.InternalPos, (run_incr f) ind)

   where test :: R.Expr MIR s C.NatType -> R.Reg s C.NatType -> MirGenerator h s ret (R.Expr MIR s C.BoolType)
         test n r = do
             i <- G.readReg r
             return $ S.app $ E.NatLt i n

         run_incr :: (R.Reg s C.NatType -> MirGenerator h s ret ()) -> (R.Reg s C.NatType -> MirGenerator h s ret ())
         run_incr f = \r -> do
             f r
             i <- G.readReg r
             G.assignReg r (S.app $ E.NatAdd i (S.app $ E.NatLit 1))
