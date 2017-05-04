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
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.MemModel.Generic where
{-
 ( Type
 , TypeF(..)
 , bitvectorType
 , floatType
 , doubleType
 , arrayType
 , mkStruct
 , typeF
 , typeEnd
 , Field
 , fieldVal ,fieldPad

 , ValueCtorF(..)
 , ViewF(..)

 , TermGenerator(..)
 , tgMuxPair
 , AddrDecomposeResult(..)

 , Mem
 , emptyMem
 , AllocType(..)
 , allocMem
 , allocAndWriteMem
 , readMem
 , isAllocated
 , isValidPointer
 , writeMem
 , writeMem'
 , copyMem
 , pushStackFrameMem
 , popStackFrameMem
 , branchMem
 , branchAbortMem
 , mergeMem
 , MemPrettyPrinter(..)
 , ppMem
 , ppType
 ) where
-}

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

--import Debug.Trace as Debug

adrVar :: AddrDecomposeResult t -> Maybe t
adrVar Symbolic{} = Nothing
adrVar (ConcreteOffset v _) = Just v
adrVar (SymbolicOffset v _) = Just v

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Show)

-- | Stores writeable memory allocations.
data MemAlloc p c
     -- | Allocation with given base and number of bytes.
   = Alloc AllocType p p
     -- | The merger of two allocations.
   | AllocMerge c [MemAlloc p c] [MemAlloc p c]

type MemAlloc' sym w = MemAlloc (LLVMPtrExpr' sym w) (Pred sym)

data MemWrite p c t
    -- | @MemCopy dst src len@ represents a copy from [src..src+len) to
    -- [dst..dst+len).
  = MemCopy (p,AddrDecomposeResult p) p (p,Maybe Integer)
    -- | Memstore is given address was written, value, and type of value.
  | MemStore (p,AddrDecomposeResult p) t Type
    -- | The merger of two memories.
  | WriteMerge c [MemWrite p c t] [MemWrite p c t]

tgAddPtrC :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> LLVMPtrExpr' sym w -> Addr -> IO (LLVMPtrExpr' sym w)
tgAddPtrC sym w x y = ptrAdd sym w x =<< ptrConst sym w y

tgApplyValueF :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> ValueF (LLVMPtrExpr' sym w) -> IO (LLVMPtrExpr' sym w)
tgApplyValueF sym w (Add x y) = ptrAdd sym w x y
tgApplyValueF sym w (Sub x y) = ptrSub sym w x y
tgApplyValueF sym w (CValue c) = ptrConst sym w (fromInteger c)

badLoad :: (IsBoolExprBuilder sym) => sym -> Type -> IO (Pred sym, PartLLVMVal sym w)
badLoad sym _tp = return (falsePred sym, Unassigned)

genValue :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> (v -> LLVMPtrExpr' sym w) -> Value v -> IO (LLVMPtrExpr' sym w)
genValue sym w f = foldTermM (return . f) (tgApplyValueF sym w)

genCondVar :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w -> (v -> (LLVMPtrExpr' sym w)) -> Cond v -> IO (Pred sym)
genCondVar sym w f c =
  case c of
    Eq x y  -> join $ ptrEq sym w <$> genValue sym w f x <*> genValue sym w f y
    Le x y  -> join $ ptrLe sym w <$> genValue sym w f x <*> genValue sym w f y
    And x y -> join $ andPred sym <$> genCondVar sym w f x <*> genCondVar sym w f y

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
                 -> (Var -> LLVMPtrExpr' sym w)
                    -- Function for reading specific subranges.
                 -> (u -> IO (Pred sym, PartLLVMVal sym w))
                 -> Mux (Cond Var) (ValueCtor u)
                 -> IO (Pred sym, PartLLVMVal sym w)
evalMuxValueCtor sym w vf subFn t =
  reduceMux (\c -> tgMuxPair sym w c)
    =<< muxLeaf (evalValueCtor sym w)
    =<< muxCond (genCondVar sym w vf)
    =<< muxLeaf (traverse subFn) t

readMemCopy :: forall sym w .
               (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w
            -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w))
            -> Type
            -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w))
            -> LLVMPtrExpr' sym w
            -> (LLVMPtrExpr' sym w, Maybe Integer)
            -> (Type -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w)) -> IO (Pred sym, PartLLVMVal sym w))
            -> IO (Pred sym, PartLLVMVal sym w)
readMemCopy sym w (l,ld) tp (d,dd) src (sz,szd) readPrev' = do
  let varFn :: Var -> LLVMPtrExpr' sym w
      varFn Load = l
      varFn Store = d
      varFn StoreSize = sz
  let readPrev tp' p = readPrev' tp' . (p,) =<< ptrDecompose sym w p
  case (ld, dd) of
    -- Offset if known
    ( ConcreteOffset lv lo
      , ConcreteOffset sv so
      )
      | sameAllocationUnit lv sv -> do
      let subFn :: RangeLoad Addr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OutOfRange o tp') = readPrev tp' =<< tgAddPtrC sym w lv o
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
      , not (sameAllocationUnit lv sv) -> readPrev' tp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: RangeLoad (Value Var) -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OutOfRange o tp') =
            readPrev tp' =<< genValue sym w varFn o
          subFn (InRange o tp') =
            readPrev tp' =<< ptrAdd sym w src =<< genValue sym w varFn o
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
            -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w))
               -- ^ The loaded address and information
            -> Type
               -- The type we are reading.
            -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w))
               -- ^ The store we are reading from.
            -> PartLLVMVal sym w
               -- ^ The value that was stored.
            -> Type
               -- ^ The type of value that was written.
            -> (Type -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w)) -> IO (Pred sym, PartLLVMVal sym w))
               -- ^ A callback function for when reading fails.
            -> IO (Pred sym, PartLLVMVal sym w)
readMemStore sym w (l,ld) ltp (d,dd) t stp readPrev' = do
  ssz <- ptrConst sym w (typeSize stp)
  let varFn :: Var -> LLVMPtrExpr' sym w
      varFn Load = l
      varFn Store = d
      varFn StoreSize = ssz
  let readPrev tp p = readPrev' tp . (p,) =<< ptrDecompose sym w p
  case (ld, dd) of
    -- Offset if known
    ( ConcreteOffset lv lo
      , ConcreteOffset sv so
      )
      | sameAllocationUnit lv sv -> do
      let subFn :: ValueLoad Addr -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OldMemory o tp')   = readPrev tp' =<< tgAddPtrC sym w lv o
          subFn (LastStore v)       = (truePred sym,) <$> applyView sym w t v
          subFn (InvalidMemory tp') = badLoad sym tp'
      let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (Var stp)
      evalValueCtor sym w =<< traverse subFn vcr
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , not (sameAllocationUnit lv sv) -> readPrev' ltp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: ValueLoad (Value Var) -> IO (Pred sym, PartLLVMVal sym w)
          subFn (OldMemory o tp')   = do
                     readPrev tp' =<< genValue sym w varFn o
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
        -> LLVMPtrExpr' sym w
        -> Type
        -> Mem' sym w
        -> IO (Pred sym, PartLLVMVal sym w)
readMem sym w l tp m = do
  ld <- ptrDecompose sym w l
  readMem' sym w (l,ld) tp (memWrites m)

-- | Read a value from memory given a list of writes.
--
-- This represents a predicate indicating if the read was successful, and the value
-- read (which may be anything if read was unsuccessful).
readMem' :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
            -- ^ Functions for primitive operations on addresses, propositions, and values.
         -> (LLVMPtrExpr' sym w, AddrDecomposeResult (LLVMPtrExpr' sym w))
            -- ^ Address we are reading along with information about how it was constructed.
         -> Type
            -- ^ The type to read from memory.
         -> [MemWrite (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w)]
            -- ^ List of writes.
         -> IO (Pred sym, (PartLLVMVal sym w))
readMem' sym _ _ tp [] = badLoad sym tp
readMem' sym w l tp (h:r) = do
  cache <- newIORef Map.empty
  let readPrev tp' l' = do
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

type MemChanges p c t = ([MemAlloc p c], [MemWrite p c t])

prependChanges :: MemChanges p c t -> MemChanges p c t -> MemChanges p c t
prependChanges (xa,xw) (ya,yw) = (xa ++ ya, xw ++ yw)

muxChanges :: c -> MemChanges p c t -> MemChanges p c t -> MemChanges p c t
muxChanges c (xa,xw) (ya,yw) = ([AllocMerge c xa ya],[WriteMerge c xw yw])

data Mem p c t = Mem { _memState :: MemState (MemChanges p c t)
                     }
type Mem' sym w = Mem (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w)

memState :: Simple Lens (Mem p c t) (MemState ([MemAlloc p c],[MemWrite p c t]))
memState = lens _memState (\s v -> s { _memState = v })

memChanges :: (MemChanges p c t -> [d]) -> Mem p c t -> [d]
memChanges f m = go (m^.memState)
  where go (EmptyMem l)      = f l
        go (StackFrame l s)  = f l ++ go s
        go (BranchFrame l s) = f l ++ go s

memAllocs :: Mem p c t -> [MemAlloc p c]
memAllocs = memChanges fst

memWrites :: Mem p c t -> [MemWrite p c t]
memWrites = memChanges snd

memAddAlloc :: MemAlloc p c -> Mem p c t -> Mem p c t
memAddAlloc x = memState . memStateLastChanges . _1 %~ (x:)

memAddWrite :: MemWrite p c t -> Mem p c t -> Mem p c t
memAddWrite x = memState . memStateLastChanges . _2 %~ (x:)

emptyChanges :: MemChanges p c t
emptyChanges = ([],[])

emptyMem :: Mem p c t
emptyMem = Mem { _memState = EmptyMem emptyChanges
               }

isAllocated' :: (IsBoolExprBuilder sym) => sym -> NatRepr w
                -- ^ Evaluation function that takes continuation
                -- for condition if previous check fails.
             -> (LLVMPtrExpr' sym w -> LLVMPtrExpr' sym w -> IO (Pred sym) -> IO (Pred sym))
             -> [MemAlloc' sym w]
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
                  => sym -> NatRepr w -> LLVMPtrExpr' sym w -> LLVMPtrExpr' sym w -> LLVMPtrExpr' sym w -> Mem (LLVMPtrExpr' sym w) (Pred sym) t -> IO (Pred sym)
offsetIsAllocated sym w t o sz m = do
  (oc, oe) <- ptrCheckedAdd sym w o sz
  let step a asz fallback
        | sameAllocationUnit t a = ptrLe sym w oe asz
            --Debug.trace "offsetIsAllocated: comparing <=" $ ptrLe sym w oe asz
        | otherwise = fallback
  andPred sym oc =<< isAllocated' sym w step (memAllocs m)

isAllocated :: (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w -> LLVMPtrExpr' sym w -> LLVMPtrExpr' sym w -> Mem (LLVMPtrExpr' sym w) (Pred sym) t -> IO (Pred sym)
isAllocated sym w p sz m = do
  ld <- ptrDecompose sym w p
  case ld of
    Symbolic{} -> do
      (oc,pe) <- ptrCheckedAdd sym w p sz
      let step a asz fallback =
            join $ orPred sym
              <$> (do ae <- ptrAdd sym w a asz
                      join $ andPred sym <$> ptrLe sym w a p <*> ptrLe sym w pe ae)
              <*> fallback
      andPred sym oc =<< isAllocated' sym w step (memAllocs m)
    ConcreteOffset t o0 -> do
      o <- ptrConst sym w (fromInteger o0)
      offsetIsAllocated sym w t o sz m
    SymbolicOffset t o -> do
      offsetIsAllocated sym w t o sz m


-- | @isValidPointer sym w b m@ returns condition required to prove range
--   that @p@ is a valid pointer in @m@.  This means that @p@ is in the
--   range of some allocation OR ONE PAST THE END of an allocation.  In other words
--   @p@ is a valid pointer if @b <= p <= b+sz@ for some allocation
--   at base @b@ of size @sz@.  Note that, even though @b+sz@ is outside the
--   allocation range of the allocation (loading through it will fail) it is
--   nonetheless a valid pointer value.  This strange special case is baked into
--   the C standard to allow certain common coding patterns to be defined.
isValidPointer :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w -> LLVMPtrExpr' sym w -> Mem (LLVMPtrExpr' sym w) (Pred sym) t -> IO (Pred sym)
isValidPointer sym w p m = do
   sz <- ptrConst sym w 0
   isAllocated sym w p sz m
 -- NB We call isAllocated with a size of 0.  This is a violation of the usual rules, but gives
 -- precisely what we need for the valid pointer check.

writeMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtrExpr' sym w
         -> Type
         -> t
         -> Mem (LLVMPtrExpr' sym w) (Pred sym) t
         -> IO (Pred sym, Mem (LLVMPtrExpr' sym w) (Pred sym) t)
writeMem sym w p tp v m = do
  (,) <$> (do sz <- ptrConst sym w (typeEnd 0 tp)
              isAllocated sym w p sz m)
      <*> writeMem' sym w p tp v m

-- | Write memory without checking if it is allocated.
writeMem' :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w
          -> LLVMPtrExpr' sym w
          -> Type
          -> t
          -> Mem (LLVMPtrExpr' sym w) (Pred sym) t
          -> IO (Mem (LLVMPtrExpr' sym w) (Pred sym) t)
writeMem' sym w p tp v m = addWrite <$> ptrDecompose sym w p
  where addWrite pd = m & memAddWrite (MemStore (p,pd) v tp)

-- | Perform a mem copy.
copyMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtrExpr' sym w -- ^ Dest
         -> LLVMPtrExpr' sym w -- ^ Source
         -> LLVMPtrExpr' sym w -- ^ Size
         -> Mem' sym w
         -> IO (Pred sym, Mem' sym w)
copyMem sym w dst src sz m = do
  (,) <$> (join $ andPred sym <$> isAllocated sym w dst sz m
                           <*> isAllocated sym w src sz m)
      <*> (do dstd <- ptrDecompose sym w dst
              szd <- ptrSizeDecompose sym w sz
              return $ m & memAddWrite (MemCopy (dst,dstd) src (sz,szd)))


-- | Allocate space for memory
allocMem :: AllocType -- ^ Type of allocation
         -> LLVMPtrExpr' sym w -- ^ Base for allocation
         -> LLVMPtrExpr' sym w -- ^ Size
         -> Mem' sym w
         -> Mem' sym w
allocMem a b sz = memAddAlloc (Alloc a b sz)

-- | Allocate space for memory
allocAndWriteMem :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w
                 -> AllocType -- ^ Type of allocation
                 -> LLVMPtrExpr' sym w -- ^ Base for allocation
                 -> Type
                 -> t -- Value to write
                 -> Mem (LLVMPtrExpr' sym w) (Pred sym) t
                 -> IO (Mem (LLVMPtrExpr' sym w) (Pred sym) t)
allocAndWriteMem sym w a b tp v m = do
  sz <- ptrConst sym w (typeEnd 0 tp)
  writeMem' sym w b tp v (m & memAddAlloc (Alloc a b sz))

pushStackFrameMem :: Mem p c t -> Mem p c t
pushStackFrameMem = memState %~ StackFrame emptyChanges

popStackFrameMem :: Mem p c t -> Mem p c t
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
        -> LLVMPtrExpr' sym w -- ^ Base of allocation to free
        -> Mem' sym w
        -> IO (Pred sym, Mem' sym w)
freeMem sym w p m = do
  p' <- ptrDecompose sym w p
  freeMem' sym w p p' m

-- FIXME? This could perhaps be more efficient.  Right now we
-- will traverse almost the entire memory on every free, even
-- if we concretely find the corresponding allocation early.
freeMem' :: forall sym w
         . (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w
        -> LLVMPtrExpr' sym w
        -> AddrDecomposeResult (LLVMPtrExpr' sym w) -- ^ Base of allocation to free
        -> Mem' sym w
        -> IO (Pred sym, Mem' sym w)
freeMem' sym w p p_decomp m = do
    (c, st') <- freeSt (m^.memState)
    return (c, m & memState .~ st')
 where
  freeAllocs :: [MemAlloc' sym w] -> IO (Pred sym, [MemAlloc' sym w])
  freeAllocs [] =
     return ( falsePred sym , [] )
  freeAllocs (a@(Alloc HeapAlloc base _) : as) = do
     base' <- ptrDecompose sym w base
     case (p_decomp, base') of
       (ConcreteOffset p' poff,
         ConcreteOffset b' boff)
           | sameAllocationUnit p' b' -> do
               let c = if poff == boff then truePred sym else falsePred sym
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (ConcreteOffset p' poff,
         SymbolicOffset b' boff)
           | sameAllocationUnit p' b' -> do
               c <- ptrEq sym w boff =<< ptrConst sym w (fromIntegral poff)
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (SymbolicOffset p' poff,
         ConcreteOffset b' boff)
           | sameAllocationUnit p' b' -> do
               c <- ptrEq sym w poff =<< ptrConst sym w (fromIntegral boff)
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (SymbolicOffset p' poff,
         SymbolicOffset b' boff)
           | sameAllocationUnit p' b' -> do
               c <- ptrEq sym w boff poff
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       _ -> do
         eq <- ptrEq sym w p base
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

  freeCh :: MemChanges (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w) -> IO (Pred sym, MemChanges (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w))
  freeCh (a, w') = do
      (c,a') <- freeAllocs a
      return (c, (a', w'))

  freeSt :: MemState (MemChanges (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w))
         -> IO (Pred sym, MemState (MemChanges (LLVMPtrExpr' sym w) (Pred sym) (PartLLVMVal sym w)))
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


branchMem :: Mem p c t -> Mem p c t
branchMem = memState %~ BranchFrame emptyChanges

branchAbortMem :: Mem p c t -> Mem p c t
branchAbortMem = memState %~ popf
  where popf (BranchFrame c s) = s & memStateLastChanges %~ prependChanges c
        popf _ = error "branchAbortMem given unexpected memory"

mergeMem :: c -> Mem p c t -> Mem p c t -> Mem p c t
mergeMem c x y =
  case (x^.memState, y^.memState) of
    (BranchFrame a s, BranchFrame b _) ->
      let s' = s & memStateLastChanges %~ prependChanges (muxChanges c a b)
       in x & memState .~ s'
    _ -> error "mergeMem given unexpected memories"


data MemPrettyPrinter p c t m =
  PP { ppPtr  :: Int -> p -> m Doc
     , ppCond :: Int -> c -> m Doc
     , ppTerm :: Int -> t -> m Doc
     }

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

ppMerge :: Monad m
        => MemPrettyPrinter p c t m
        -> (v -> m Doc)
        -> c
        -> [v]
        -> [v]
        -> m Doc
ppMerge pp vpp c x y = do
  cdoc <- ppCond pp 0 c
  xdoc <- traverse vpp x
  ydoc <- traverse vpp y
  return $ indent 2 $
    text "Condition:" <$$>
    indent 2 cdoc <$$>
    text "True Branch:"  <$$>
    indent 2 (vcat $ xdoc) <$$>
    text "False Branch:" <$$>
    indent 2 (vcat $ ydoc)

ppAlloc :: Monad m => MemPrettyPrinter p c t m -> MemAlloc p c -> m Doc
ppAlloc pp (Alloc atp base sz) = do
  basedoc <- ppPtr pp 10 base
  szdoc   <- ppPtr pp 10 sz
  return $
    text (show atp) <+> basedoc <+> szdoc
ppAlloc pp (AllocMerge c x y) = do
  mergeDoc <- ppMerge pp (ppAlloc pp) c x y
  return $
    text "merge" <$$> mergeDoc

ppWrite :: Monad m => MemPrettyPrinter p c t m -> MemWrite p c t -> m Doc
ppWrite pp (MemCopy (d,_) s (l,_)) = do
  ddoc <- ppPtr pp 10 d
  sdoc <- ppPtr pp 10 s
  ldoc <- ppPtr pp 10 l
  return $ text "memcopy" <+> ddoc <+> sdoc <+> ldoc
ppWrite pp (MemStore (d,_) v _) = do
  ddoc <- ppPtr pp 10 d
  vdoc <- ppTerm pp 10 v
  return $
    char '*' <> ddoc <+> text ":=" <+> vdoc
ppWrite pp (WriteMerge c x y) = do
  mergeDoc <- ppMerge pp (ppWrite pp) c x y
  return $ text "merge" <$$> mergeDoc

ppMemChanges :: Monad m => MemPrettyPrinter p c t m -> MemChanges p c t -> m Doc
ppMemChanges pp (al,wl) = do
  aldoc <- traverse (ppAlloc pp) al
  wldoc <- traverse (ppWrite pp) wl
  return $
    text "Allocations:" <$$>
    indent 2 (vcat aldoc) <$$>
    text "Writes:" <$$>
    indent 2 (vcat wldoc)

ppMemState :: Monad m => (d -> m Doc) -> MemState d -> m Doc
ppMemState f (EmptyMem d) = do
  ddoc <- f d
  return $ text "Base memory" <$$>
           indent 2 ddoc
ppMemState f (StackFrame d ms) = do
  ddoc  <- f d
  msdoc <- ppMemState f ms
  return $
    text "Stack frame" <$$>
    indent 2 ddoc <$$>
    msdoc

ppMemState f (BranchFrame d ms) = do
  ddoc <- f d
  msdoc <- ppMemState f ms
  return $
    text "Branch frame" <$$>
    indent 2 ddoc <$$>
    msdoc

ppMem :: Monad m => MemPrettyPrinter p c t m -> Mem p c t -> m Doc
ppMem pp m = ppMemState (ppMemChanges pp) (m^.memState)
