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

                         , mem_crucible_identity_transmute

                         , box_new

                         -- CustomOps below this point have not been checked
                         -- for compatibility with new monomorphization.

                         , slice_len
                         --, slice_is_empty
                         --, slice_first

                         , str_len

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
panicking_panic = ((["core", "panicking"], "panic", []), \s -> Just $ CustomOpExit $ \ops -> do
    name <- use $ currentFn . fname
    return $ "panicking::panic, called from " <> M.idText name
    )


-----------------------------------------------------------------------------------------------------
-- ** Custom: Box

-- Note that std::boxed::Box<T> gets custom translation in `TransTy.tyToRepr`.

box_new :: (ExplodedDefId, CustomRHS)
box_new = ( (["std","boxed","{{impl}}"], "new", []),
  \_substs -> Just $ CustomOp $ \ _opTys ops -> case ops of
    [MirExp tpr e] -> do
        r <- newMirRef tpr
        writeMirRef r e
        return $ MirExp (MirReferenceRepr tpr) r
  )


-----------------------------------------------------------------------------------------------------
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
           (UsizeRepr, UsizeRepr) -> do
               let sub = R.App $ usizeMul a b
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
           (UsizeRepr, UsizeRepr) -> do
               let sub = R.App $ usizeSub a b
               return (MirExp aty sub)
           (_,_) -> mirFail $ "wrapping_sub: cannot call with types " ++ show aty ++ " and " ++ show bty

       _ -> mirFail $ "BUG: invalid arguments for wrapping_sub")

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


---------------------------------------------------------------------------------------
-- ** Custom ::intrinsics::discriminant_value

discriminant_value ::  (ExplodedDefId, CustomRHS)
discriminant_value = ((["core","intrinsics"],"discriminant_value", []),
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
      case (opTys,ops) of
        ([TyRef (TyAdt nm args) Immut], [e]) -> do
            adt <- findAdt nm
            -- `&T` has the same representation as `T`, so we don't need to
            -- explicitly dereference.
            MirExp IsizeRepr e' <- enumDiscriminant adt args e
            return $ MirExp (C.BVRepr (knownRepr :: NatRepr 64)) $
                isizeToBv knownRepr R.App e'
        _ -> mirFail $ "BUG: invalid arguments for discriminant_value")

type_id ::  (ExplodedDefId, CustomRHS)
type_id = ((["core","intrinsics"],"type_id", []),
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
    -- TODO: keep a map from Ty to Word64, assigning IDs on first use of each type
    return $ MirExp knownRepr $ R.App (E.BVLit (knownRepr :: NatRepr 64) 0))

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


-- This is like normal mem::transmute, but requires source and target types to
-- have identical Crucible `TypeRepr`s.
mem_crucible_identity_transmute ::  (ExplodedDefId, CustomRHS)
mem_crucible_identity_transmute = ((["core","mem"],"crucible_identity_transmute", []),
    \ substs -> case substs of
      Substs [tyT, tyU] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e@(MirExp argTy _)]
          | Some retTy <- tyToRepr tyU
          , Just Refl <- testEquality argTy retTy -> return e
        _ -> mirFail $ "bad arguments to mem_crucible_identity_transmute: "
          ++ show (tyT, tyU, ops)
      _ -> Nothing
    )





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
                        return (MirExp UsizeRepr  (G.App $ vectorSizeUsize R.App vec_e))
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
  ((["core","slice","{{impl}}","len"], "crucible_slice_len_hook", [])
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys ops -> 
     case ops of 
     -- type of the structure is &mut[ elTy ]
       [MirExp (C.VectorRepr _) vec_e] -> do
            return (MirExp UsizeRepr (G.App $ vectorSizeUsize R.App vec_e))
       _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_len")

{-
slice_is_empty :: (ExplodedDefId, CustomRHS)
slice_is_empty =
  ((["core","slice","{{impl}}","is_empty"], "crucible_is_empty_hook", [])
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
-}

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

slice_index_usize_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked = ((["core","slice","{{impl}}","get_unchecked"], "crucible_hook_usize", []), \subs ->
   case subs of
     (Substs [ elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
          case ops of
            [MirExp UsizeRepr ind, MirExp (C.VectorRepr el_tp) arr] -> do
                return $ (MirExp el_tp (S.app $ vectorGetUsize el_tp R.App arr ind))
            [MirExp UsizeRepr ind, MirExp (MirSliceRepr el_tp) slice] -> do
                let ref   = S.getStruct (Ctx.natIndex @0) slice
                let start = S.getStruct (Ctx.natIndex @1) slice
                let ind'  = R.App $ usizeAdd start ind
                arr <- readMirRef (C.VectorRepr el_tp) ref
                return $ (MirExp el_tp (S.app $ vectorGetUsize el_tp R.App arr ind'))
            _ -> mirFail $ "BUG: invalid arguments to slice::SliceIndex::get_unchecked"
     _ -> Nothing)

slice_index_range_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked = ((["core","slice","{{impl}}","get_unchecked"], "crucible_hook_range", []), \subs ->
   case subs of
     (Substs [ elTy ])
       -> Just $ CustomOp $ \ optys ops -> do
          case ops of
             [ MirExp tr1 start, MirExp tr2 end, MirExp (C.VectorRepr ety) vec_e  ]
               | Just Refl <- testEquality tr1 UsizeRepr
               , Just Refl <- testEquality tr2 UsizeRepr
               -> do
                v <- vectorCopy ety start end vec_e
                return $ (MirExp (C.VectorRepr ety) v)

             [ MirExp tr1 start, MirExp tr2 end, MirExp (MirSliceRepr ty) vec_e] 
               | Just Refl <- testEquality tr1 UsizeRepr
               , Just Refl <- testEquality tr2 UsizeRepr
               -> do
                let newLen = (S.app $ usizeSub end start)
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

              [MirExp UsizeRepr ind, MirExp (MirSliceRepr el_tp) slice] -> do
                  let ref   = S.getStruct (Ctx.natIndex @0) slice
                  let start = S.getStruct (Ctx.natIndex @1) slice
                  let ind'  = R.App $ usizeAdd start ind
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

              [ MirExp tr1 start, MirExp tr2 end, MirExp (MirSliceRepr ty) vec_e] 
                | Just Refl <- testEquality tr1 UsizeRepr
                , Just Refl <- testEquality tr2 UsizeRepr
                -> do
                  let newLen = S.app $ usizeSub end start
                  let s1 = updateSliceLB  ty vec_e start
                  let s2 = updateSliceLen ty s1    newLen
                  return $ (MirExp (MirSliceRepr ty) s2)

              _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
     _ -> Nothing)

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


--------------------------------------------------------------------------------------------------------------------------




-- Type-indexed version of "1"
oneExp :: C.TypeRepr ty -> MirExp s
oneExp UsizeRepr    = MirExp UsizeRepr (R.App $ usizeLit 1)
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
