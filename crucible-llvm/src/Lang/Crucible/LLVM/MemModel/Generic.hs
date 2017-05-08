------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Generic
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.MemModel.Generic
  ( Mem
  , emptyMem
  , AllocType(..)
  , MemAlloc(..)
  , memAllocs
  , allocMem
  , allocAndWriteMem
  , readMem
  , isValidPointer
  , writeMem
  , copyMem
  , pushStackFrameMem
  , popStackFrameMem
  , freeMem
  , branchMem
  , branchAbortMem
  , mergeMem
  , ppMem
  , ppType
  , ppLLVMPtr
  ) where

import Control.Lens
import Control.Monad
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import Data.Monoid hiding ((<>))
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.Crucible.LLVM.MemModel.Common
import Lang.Crucible.LLVM.MemModel.Pointer
import Lang.Crucible.Solver.Interface
import Lang.Crucible.Solver.Partial
import Lang.MATLAB.Utils.Nat (Nat)

--import Debug.Trace as Debug

adrVar :: AddrDecomposeResult sym w -> Maybe Nat
adrVar Symbolic{} = Nothing
adrVar (ConcreteOffset v _ _) = Just v
adrVar (SymbolicOffset v _ _) = Just v

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Show)

-- | Stores writeable memory allocations.
data MemAlloc sym w
     -- | Allocation with given block ID and number of bytes.
   = Alloc AllocType Nat (SymBV sym w)
     -- | The merger of two allocations.
   | AllocMerge (Pred sym) [MemAlloc sym w] [MemAlloc sym w]

data MemWrite sym w
    -- | @MemCopy dst src len@ represents a copy from [src..src+len) to
    -- [dst..dst+len).
  = MemCopy (LLVMPtr sym w, AddrDecomposeResult sym w) (LLVMPtr sym w) (SymBV sym w, Maybe Integer)
    -- | Memstore is given address was written, value, and type of value.
  | MemStore (LLVMPtr sym w, AddrDecomposeResult sym w) (PartLLVMVal sym w) Type
    -- | The merger of two memories.
  | WriteMerge (Pred sym) [MemWrite sym w] [MemWrite sym w]

tgAddPtrC :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> LLVMPtr sym w -> Addr -> IO (LLVMPtr sym w)
tgAddPtrC sym w x y = ptrAdd sym w x =<< ptrConst sym w y

badLoad :: (IsBoolExprBuilder sym) => sym -> Type -> IO (Pred sym, PartLLVMVal sym w)
badLoad sym _tp = return (falsePred sym, Unassigned)

genPtrExpr :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
           -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
           -> PtrExpr
           -> IO (LLVMPtr sym w)
genPtrExpr sym w f@(load, store, _size) expr =
  case expr of
    PtrAdd pe ie -> do
      pe' <- genPtrExpr sym w f pe
      ie' <- genIntExpr sym w f ie
      ptrAdd sym w pe' ie'
    Load -> return load
    Store -> return store

genIntExpr :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
           -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
           -> IntExpr
           -> IO (SymBV sym w)
genIntExpr sym w f@(_load, _store, size) expr =
  case expr of
    PtrDiff e1 e2 -> do
      e1' <- genPtrExpr sym w f e1
      e2' <- genPtrExpr sym w f e2
      ptrDiff sym w e1' e2'
    IntAdd e1 e2 -> do
      e1' <- genIntExpr sym w f e1
      e2' <- genIntExpr sym w f e2
      bvAdd sym e1' e2'
    CValue i -> bvLit sym w i
    StoreSize -> return size

genCondVar :: (1 <= w, IsSymInterface sym)
              => sym -> NatRepr w
              -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
              -> Cond -> IO (Pred sym)
genCondVar sym w inst c =
  case c of
    PtrEq x y  -> join $ ptrEq sym w <$> genPtrExpr sym w inst x <*> genPtrExpr sym w inst y
    PtrLe x y  -> join $ ptrLe sym w <$> genPtrExpr sym w inst x <*> genPtrExpr sym w inst y
    IntEq x y  -> join $ bvEq sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    IntLe x y  -> join $ bvSle sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    And x y    -> join $ andPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y

genValueCtor :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> ValueCtor (PartLLVMVal sym w) -> IO (PartLLVMVal sym w)
genValueCtor sym w = foldTermM return (applyCtorFLLVMVal sym w)

applyView :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> PartLLVMVal sym w -> ValueView Type -> IO (PartLLVMVal sym w)
applyView sym w t = foldTermM (\_ -> return t) (applyViewFLLVMVal sym w)

-- | Join all conditions in fold together.
tgAll :: (IsBoolExprBuilder sym) => sym
      -> Getting (Dual (Endo (Pred sym -> IO (Pred sym)))) s (Pred sym)
      -> s
      -> IO (Pred sym)
tgAll sym fld = foldrMOf fld (andPred sym) (truePred sym)

tgMuxPair :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
          -> Pred sym
          -> (Pred sym, PartLLVMVal sym w)
          -> (Pred sym, PartLLVMVal sym w)
          -> IO (Pred sym, PartLLVMVal sym w)
tgMuxPair sym w c (xc,xt) (yc,yt) =
  (,) <$> itePred sym c xc yc
      <*> muxLLVMVal sym w c xt yt

evalValueCtor :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
              -> ValueCtor (Pred sym, PartLLVMVal sym w)
              -> IO (Pred sym, PartLLVMVal sym w)
evalValueCtor sym w vc =
   (,) <$> tgAll sym (traverse . _1) vc
       <*> genValueCtor sym w (snd <$> vc)

evalMuxValueCtor :: forall u sym w .
                    (1 <= w, IsSymInterface sym) => sym -> NatRepr w
                    -- Evaluation function
                 -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
                    -- Function for reading specific subranges.
                 -> (u -> IO (Pred sym, PartLLVMVal sym w))
                 -> Mux (ValueCtor u)
                 -> IO (Pred sym, PartLLVMVal sym w)
evalMuxValueCtor sym w _vf subFn (MuxVar v) =
  do v' <- traverse subFn v
     evalValueCtor sym w v'
evalMuxValueCtor sym w vf subFn (Mux c t1 t2) =
  do c' <- genCondVar sym w vf c
     t1' <- evalMuxValueCtor sym w vf subFn t1
     t2' <- evalMuxValueCtor sym w vf subFn t2
     tgMuxPair sym w c' t1' t2'

readMemCopy :: forall sym w .
               (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
            -> Type
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
            -> LLVMPtr sym w
            -> (SymBV sym w, Maybe Integer)
            -> (Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (Pred sym, PartLLVMVal sym w))
            -> IO (Pred sym, PartLLVMVal sym w)
readMemCopy sym w (l,ld) tp (d,dd) src (sz,szd) readPrev' = do
  let readPrev tp' p = readPrev' tp' . (p,) =<< ptrDecompose sym w p
  let varFn = (l, d, sz)
  case (ld, dd) of
    -- Offset if known
    (ConcreteOffset lv le lo, ConcreteOffset sv _ so)
      | lv == sv -> do
      let subFn :: RangeLoad Addr Addr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OutOfRange o tp') = do lv' <- natLit sym lv
                                        o' <- bvLit sym w (toInteger o)
                                        readPrev tp' (LLVMPtr lv' le o')
          subFn (InRange    o tp') = readPrev tp' =<< tgAddPtrC sym w src o
      case szd of
        Just csz -> do
          let s = R (fromInteger so) (fromInteger (so + csz))
          let vcr = rangeLoad (fromInteger lo) tp s
          evalValueCtor sym w =<< traverse subFn vcr
        _ ->
          evalMuxValueCtor sym w varFn subFn $
            fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' tp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: RangeLoad PtrExpr IntExpr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OutOfRange o tp') =
            readPrev tp' =<< genPtrExpr sym w varFn o
          subFn (InRange o tp') =
            readPrev tp' =<< ptrAdd sym w src =<< genIntExpr sym w varFn o
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      let mux0 | Just csz <- szd =
                   fixedSizeRangeLoad pref tp (fromInteger csz)
               | otherwise =
                   symbolicRangeLoad pref tp
      evalMuxValueCtor sym w varFn subFn mux0

readMemStore :: forall sym w .
               (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
               -- ^ The loaded address and information
            -> Type
               -- ^ The type we are reading.
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
               -- ^ The store we are reading from.
            -> PartLLVMVal sym w
               -- ^ The value that was stored.
            -> Type
               -- ^ The type of value that was written.
            -> (Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (Pred sym, PartLLVMVal sym w))
               -- ^ A callback function for when reading fails.
            -> IO (Pred sym, PartLLVMVal sym w)
readMemStore sym w (l,ld) ltp (d,dd) t stp readPrev' = do
  ssz <- bvLit sym w (toInteger (typeSize stp))
  let varFn = (l, d, ssz)
  let readPrev tp p = readPrev' tp . (p,) =<< ptrDecompose sym w p
  case (ld, dd) of
    -- Offset if known
    (ConcreteOffset lv le lo, ConcreteOffset sv _ so)
      | lv == sv -> do
      let subFn :: ValueLoad Addr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OldMemory o tp')   = do lv' <- natLit sym lv
                                         o' <- bvLit sym w (toInteger o)
                                         readPrev tp' (LLVMPtr lv' le o')
          subFn (LastStore v)       = (truePred sym,) <$> applyView sym w t v
          subFn (InvalidMemory tp') = badLoad sym tp'
      let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (Var stp)
      evalValueCtor sym w =<< traverse subFn vcr
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' ltp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: ValueLoad PtrExpr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OldMemory o tp')   = do
                     readPrev tp' =<< genPtrExpr sym w varFn o
          subFn (LastStore v)       = do
                     (truePred sym,) <$> applyView sym w t v
          subFn (InvalidMemory tp') = badLoad sym tp'
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      evalMuxValueCtor sym w varFn subFn $
        symbolicValueLoad pref ltp (Var stp)

readMem :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w
        -> LLVMPtr sym w
        -> Type
        -> Mem sym w
        -> IO (Pred sym, PartLLVMVal sym w)
readMem sym w l tp m = do
  ld <- ptrDecompose sym w l
  readMem' sym w (l,ld) tp (memWrites m)

-- | Read a value from memory given a list of writes.
--
-- This represents a predicate indicating if the read was successful, and the value
-- read (which may be anything if read was unsuccessful).
readMem' :: forall w sym . (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
            -- ^ Functions for primitive operations on addresses, propositions, and values.
         -> (LLVMPtr sym w, AddrDecomposeResult sym w)
            -- ^ Address we are reading along with information about how it was constructed.
         -> Type
            -- ^ The type to read from memory.
         -> [MemWrite sym w]
            -- ^ List of writes.
         -> IO (Pred sym, PartLLVMVal sym w)
readMem' sym _ _ tp [] = badLoad sym tp
readMem' sym w l tp (h:r) = do
  cache <- newIORef Map.empty
  let readPrev :: Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (Pred sym, PartLLVMVal sym w)
      readPrev tp' l' = do
        m <- readIORef cache
        case Map.lookup (tp',fst l') m of
          Just x -> return x
          Nothing -> do
            x <- readMem' sym w l' tp' r
            writeIORef cache $ Map.insert (tp',fst l') x m
            return x
  case h of
    MemCopy dst src sz -> do
      readMemCopy sym w l tp dst src sz readPrev
    MemStore dst v stp -> do
      readMemStore sym w l tp dst v stp readPrev
    WriteMerge c xr yr -> do
      join $ tgMuxPair sym w c
               <$> readMem' sym w l tp (xr++r)
               <*> readMem' sym w l tp (yr++r)

-- | A state of memory as of a stack push, branch, or merge.
data MemState d =
    -- | Represents initial memory and changes since then.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
    EmptyMem d
    -- | Represents a push of a stack frame,  and changes since that stack push.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | StackFrame d (MemState d)
    -- | Represents a push of a branch frame, and changes since that branch.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | BranchFrame d (MemState d)

memStateLastChanges :: Simple Lens (MemState d) d
memStateLastChanges f s0 =
  case s0 of
    EmptyMem l -> EmptyMem <$> f l
    StackFrame l s  -> flip StackFrame s  <$> f l
    BranchFrame l s -> flip BranchFrame s <$> f l

type MemChanges sym w = ([MemAlloc sym w], [MemWrite sym w])

prependChanges :: MemChanges sym w -> MemChanges sym w -> MemChanges sym w
prependChanges (xa,xw) (ya,yw) = (xa ++ ya, xw ++ yw)

muxChanges :: Pred sym -> MemChanges sym w -> MemChanges sym w -> MemChanges sym w
muxChanges c (xa,xw) (ya,yw) = ([AllocMerge c xa ya],[WriteMerge c xw yw])

data Mem sym w = Mem { _memState :: MemState (MemChanges sym w) }

memState :: Simple Lens (Mem sym w) (MemState ([MemAlloc sym w], [MemWrite sym w]))
memState = lens _memState (\s v -> s { _memState = v })

memChanges :: (MemChanges sym w -> [d]) -> Mem sym w -> [d]
memChanges f m = go (m^.memState)
  where go (EmptyMem l)      = f l
        go (StackFrame l s)  = f l ++ go s
        go (BranchFrame l s) = f l ++ go s

memAllocs :: Mem sym w -> [MemAlloc sym w]
memAllocs = memChanges fst

memWrites :: Mem sym w -> [MemWrite sym w]
memWrites = memChanges snd

memAddAlloc :: MemAlloc sym w -> Mem sym w -> Mem sym w
memAddAlloc x = memState . memStateLastChanges . _1 %~ (x:)

memAddWrite :: MemWrite sym w -> Mem sym w -> Mem sym w
memAddWrite x = memState . memStateLastChanges . _2 %~ (x:)

emptyChanges :: MemChanges sym w
emptyChanges = ([],[])

emptyMem :: Mem sym w
emptyMem = Mem { _memState = EmptyMem emptyChanges
               }

isAllocated' :: (IsBoolExprBuilder sym) => sym -> NatRepr w
                -- ^ Evaluation function that takes continuation
                -- for condition if previous check fails.
             -> (Nat -> SymBV sym w -> IO (Pred sym) -> IO (Pred sym))
             -> [MemAlloc sym w]
             -> IO (Pred sym)
isAllocated' sym _ _ [] = pure (falsePred sym)
isAllocated' sym w step (Alloc _ a asz:r) = do
  step a asz (isAllocated' sym w step r)
isAllocated' sym w step (AllocMerge c xr yr:r) =
  join $ itePred sym c
         <$> isAllocated' sym w step (xr ++ r)
         <*> isAllocated' sym w step (yr ++ r)


-- | @offsetisAllocated sym w b o sz m@ returns condition required to prove range
-- @[b+o..b+o+sz)@ lays within a single allocation in @m@.  This code assumes
-- @sz@ is non-zero, and @b+o@ does not overflow.
offsetIsAllocated :: (1 <= w, IsSymInterface sym)
                  => sym -> NatRepr w -> Nat -> LLVMPtr sym w -> SymBV sym w -> Mem sym w -> IO (Pred sym)
offsetIsAllocated sym w t o sz m = do
  (oc, LLVMPtr _ _ oe) <- ptrCheckedAdd sym w o sz
  let step a asz fallback
        | a == t = bvSle sym oe asz
        | otherwise = fallback
  andPred sym oc =<< isAllocated' sym w step (memAllocs m)

isAllocated :: (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w -> LLVMPtr sym w -> SymBV sym w -> Mem sym w -> IO (Pred sym)
isAllocated sym w p sz m = do
  ld <- ptrDecompose sym w p
  case ld of
    Symbolic{} -> do
      (oc, LLVMPtr base _ off) <- ptrCheckedAdd sym w p sz
      let step a asz fallback = do
            z <- bvLit sym w 0
            p1 <- natEq sym base =<< natLit sym a
            p2 <- join $ andPred sym <$> bvSle sym z off <*> bvSle sym off asz
            p3 <- andPred sym p1 p2
            orPred sym p3 =<< fallback
      andPred sym oc =<< isAllocated' sym w step (memAllocs m)
    ConcreteOffset t _ _ -> do
      offsetIsAllocated sym w t p sz m
    SymbolicOffset t _ _ -> do
      offsetIsAllocated sym w t p sz m


-- | @isValidPointer sym w b m@ returns condition required to prove range
--   that @p@ is a valid pointer in @m@.  This means that @p@ is in the
--   range of some allocation OR ONE PAST THE END of an allocation.  In other words
--   @p@ is a valid pointer if @b <= p <= b+sz@ for some allocation
--   at base @b@ of size @sz@.  Note that, even though @b+sz@ is outside the
--   allocation range of the allocation (loading through it will fail) it is
--   nonetheless a valid pointer value.  This strange special case is baked into
--   the C standard to allow certain common coding patterns to be defined.
isValidPointer :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w -> LLVMPtr sym w -> Mem sym w -> IO (Pred sym)
isValidPointer sym w p m = do
   sz <- ptrConst sym w 0
   isAllocated sym w p sz m
 -- NB We call isAllocated with a size of 0.  This is a violation of the usual rules, but gives
 -- precisely what we need for the valid pointer check.

writeMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtr sym w
         -> Type
         -> PartLLVMVal sym w
         -> Mem sym w
         -> IO (Pred sym, Mem sym w)
writeMem sym w p tp v m = do
  (,) <$> (do sz <- bvLit sym w (toInteger (typeEnd 0 tp))
              isAllocated sym w p sz m)
      <*> writeMem' sym w p tp v m

-- | Write memory without checking if it is allocated.
writeMem' :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w
          -> LLVMPtr sym w
          -> Type
          -> PartLLVMVal sym w
          -> Mem sym w
          -> IO (Mem sym w)
writeMem' sym w p tp v m = addWrite <$> ptrDecompose sym w p
  where addWrite pd = m & memAddWrite (MemStore (p,pd) v tp)

-- | Perform a mem copy.
copyMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtr sym w -- ^ Dest
         -> LLVMPtr sym w -- ^ Source
         -> SymBV sym w -- ^ Size
         -> Mem sym w
         -> IO (Pred sym, Mem sym w)
copyMem sym w dst src sz m = do
  (,) <$> (join $ andPred sym <$> isAllocated sym w dst sz m
                           <*> isAllocated sym w src sz m)
      <*> (do dstd <- ptrDecompose sym w dst
              szd <- ptrSizeDecompose sym w sz
              return $ m & memAddWrite (MemCopy (dst,dstd) src (sz,szd)))


-- | Allocate space for memory
allocMem :: AllocType -- ^ Type of allocation
         -> Nat -- ^ Block id for allocation
         -> SymBV sym w -- ^ Size
         -> Mem sym w
         -> Mem sym w
allocMem a b sz = memAddAlloc (Alloc a b sz)

-- | Allocate space for memory
allocAndWriteMem :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w
                 -> AllocType -- ^ Type of allocation
                 -> Nat -- ^ Block id for allocation
                 -> Type
                 -> PartLLVMVal sym w -- Value to write
                 -> Mem sym w
                 -> IO (Mem sym w)
allocAndWriteMem sym w a b tp v m = do
  sz <- bvLit sym w (toInteger (typeEnd 0 tp))
  base <- natLit sym b
  off <- bvLit sym w 0
  let p = LLVMPtr base sz off
  writeMem' sym w p tp v (m & memAddAlloc (Alloc a b sz))

pushStackFrameMem :: Mem sym w -> Mem sym w
pushStackFrameMem = memState %~ StackFrame emptyChanges

popStackFrameMem :: Mem sym w -> Mem sym w
popStackFrameMem m = m & memState %~ popf
  where popf (StackFrame (a,w) s) = s & memStateLastChanges %~ prependChanges c
          where c = (mapMaybe pa a, w)

        -- WARNING: The following code executes a stack pop underneath a branch
        -- frame.  This is necessary to get merges to work correctly
        -- when they propagate all the way to function returns.
        -- However, it is not clear that the following code is
        -- precisely correct because it may leave in place writes to
        -- memory locations that have just been popped off the stack.
        -- This does not appear to be causing problems for our
        -- examples, but may be a source of subtle errors.
        popf (BranchFrame (a,w) s) = BranchFrame c $ popf s
          where c = (mapMaybe pa a, w)

        popf _ = error "popStackFrameMem given unexpected memory"

        pa (Alloc StackAlloc _ _) = Nothing
        pa a@(Alloc HeapAlloc _ _) = Just a
        pa a@(Alloc GlobalAlloc _ _) = Just a
        pa (AllocMerge c x y) = Just (AllocMerge c (mapMaybe pa x) (mapMaybe pa y))

freeMem :: forall sym w
         . (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w
        -> LLVMPtr sym w -- ^ Base of allocation to free
        -> Mem sym w
        -> IO (Pred sym, Mem sym w)
freeMem sym w p m = do
  p' <- ptrDecompose sym w p
  freeMem' sym w p p' m

-- FIXME? This could perhaps be more efficient.  Right now we
-- will traverse almost the entire memory on every free, even
-- if we concretely find the corresponding allocation early.
freeMem' :: forall sym w
         . (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w
        -> LLVMPtr sym w
        -> AddrDecomposeResult sym w -- ^ Base of allocation to free
        -> Mem sym w
        -> IO (Pred sym, Mem sym w)
freeMem' sym w p p_decomp m = do
    (c, st') <- freeSt (m^.memState)
    return (c, m & memState .~ st')
 where
  freeAllocs :: [MemAlloc sym w] -> IO (Pred sym, [MemAlloc sym w])
  freeAllocs [] =
     return ( falsePred sym , [] )
  freeAllocs (a@(Alloc HeapAlloc b sz) : as) = do
     case p_decomp of
       ConcreteOffset p' _ poff
         | p' == b -> do
             let c = if poff == 0 then truePred sym else falsePred sym
             return (c, as)
         | otherwise -> do
             (c, as') <- freeAllocs as
             return (c, a : as')
       SymbolicOffset p' _ poff
         | p' == b -> do
             c <- bvEq sym poff =<< bvLit sym w 0
             return (c, as)
         | otherwise -> do
             (c, as') <- freeAllocs as
             return (c, a : as')
       _ -> do
         base <- natLit sym b
         off <- bvLit sym w 0
         eq <- ptrEq sym w p (LLVMPtr base sz off)
         (c, as') <- freeAllocs as
         c'  <- orPred sym eq c
         return (c', AllocMerge eq [] [a] : as')

  freeAllocs (a@(Alloc _ _ _) : as) = do
     (c, as') <- freeAllocs as
     return (c, a:as')
  freeAllocs (AllocMerge cm x y : as) = do
     (c1, x') <- freeAllocs x
     (c2, y') <- freeAllocs y
     c <- itePred sym cm c1 c2
     (c3, as') <- freeAllocs as
     c' <- orPred sym c c3
     return (c', AllocMerge cm x' y' : as')

  freeCh :: MemChanges sym w -> IO (Pred sym, MemChanges sym w)
  freeCh (a, w') = do
      (c,a') <- freeAllocs a
      return (c, (a', w'))

  freeSt :: MemState (MemChanges sym w)
         -> IO (Pred sym, MemState (MemChanges sym w))
  freeSt (StackFrame ch st) = do
            (c1,ch') <- freeCh ch
            (c2,st') <- freeSt st
            c <- orPred sym c1 c2
            return (c, StackFrame ch' st')
  freeSt (BranchFrame ch st) = do
            (c1,ch') <- freeCh ch
            (c2,st') <- freeSt st
            c <- orPred sym c1 c2
            return (c, BranchFrame ch' st')
  freeSt (EmptyMem ch) = do
            (c, ch') <- freeCh ch
            return (c, EmptyMem ch')


branchMem :: Mem sym w -> Mem sym w
branchMem = memState %~ BranchFrame emptyChanges

branchAbortMem :: Mem sym w -> Mem sym w
branchAbortMem = memState %~ popf
  where popf (BranchFrame c s) = s & memStateLastChanges %~ prependChanges c
        popf _ = error "branchAbortMem given unexpected memory"

mergeMem :: Pred sym -> Mem sym w -> Mem sym w -> Mem sym w
mergeMem c x y =
  case (x^.memState, y^.memState) of
    (BranchFrame a s, BranchFrame b _) ->
      let s' = s & memStateLastChanges %~ prependChanges (muxChanges c a b)
       in x & memState .~ s'
    _ -> error "mergeMem given unexpected memories"


--------------------------------------------------------------------------------
-- Pretty printing

ppLLVMPtr :: IsExprBuilder sym => LLVMPtr sym w -> Doc
ppLLVMPtr (LLVMPtr blk _ off) = parens $ blk_doc <> ", " <> off_doc
  where blk_doc = printSymExpr blk
        off_doc = printSymExpr off

ppPartTermExpr
  :: IsExprBuilder sym
  => PartExpr (Pred sym) (LLVMVal sym w)
  -> Doc
ppPartTermExpr Unassigned = text "<undef>"
ppPartTermExpr (PE _p t) = ppTermExpr t

ppTermExpr
  :: forall sym w . IsExprBuilder sym
  => LLVMVal sym w
  -> Doc
ppTermExpr t = -- FIXME, do something with the predicate?
  case t of
    LLVMValPtr base end off -> text "ptr" <> ppLLVMPtr (LLVMPtr base end off :: LLVMPtr sym w)
    LLVMValInt _x v -> printSymExpr v
    LLVMValReal v -> printSymExpr v
    LLVMValStruct v -> encloseSep lbrace rbrace comma v''
      where v'  = fmap (over _2 ppTermExpr) (V.toList v)
            v'' = map (\(fld,doc) ->
                        group (text "base+" <> text (show $ fieldOffset fld) <+> equals <+> doc))
                      v'
    LLVMValArray _tp v -> encloseSep lbracket rbracket comma v'
      where v' = ppTermExpr <$> V.toList v

-- | Pretty print type.
ppType :: Type -> Doc
ppType tp =
  case typeF tp of
    Bitvector w -> text ('i': show w)
    Float -> text "float"
    Double -> text "double"
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

ppAlloc :: IsExprBuilder sym => MemAlloc sym w -> Doc
ppAlloc (Alloc atp base sz) =
  text (show atp) <+> text (show base) <+> printSymExpr sz
ppAlloc (AllocMerge c x y) = do
  text "merge" <$$> ppMerge ppAlloc c x y

ppWrite :: IsExprBuilder sym => MemWrite sym w -> Doc
ppWrite (MemCopy (d,_) s (l,_)) = do
  text "memcopy" <+> ppLLVMPtr d <+> ppLLVMPtr s <+> printSymExpr l
ppWrite (MemStore (d,_) v _) = do
  char '*' <> ppLLVMPtr d <+> text ":=" <+> ppPartTermExpr v
ppWrite (WriteMerge c x y) = do
  text "merge" <$$> ppMerge ppWrite c x y

ppMemChanges :: IsExprBuilder sym => MemChanges sym w -> Doc
ppMemChanges (al,wl) =
  text "Allocations:" <$$>
  indent 2 (vcat (map ppAlloc al)) <$$>
  text "Writes:" <$$>
  indent 2 (vcat (map ppWrite wl))

ppMemState :: (d -> Doc) -> MemState d -> Doc
ppMemState f (EmptyMem d) = do
  text "Base memory" <$$> indent 2 (f d)
ppMemState f (StackFrame d ms) = do
  text "Stack frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms
ppMemState f (BranchFrame d ms) = do
  text "Branch frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms

ppMem :: IsExprBuilder sym => Mem sym w -> Doc
ppMem m = ppMemState ppMemChanges (m^.memState)
