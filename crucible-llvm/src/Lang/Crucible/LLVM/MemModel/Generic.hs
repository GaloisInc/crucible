-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Generic
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

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
import Control.Monad.IO.Class
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import Data.Monoid hiding ((<>))
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Lang.Crucible.LLVM.MemModel.Common

--import Debug.Trace as Debug

-- | This provides a view of an address as a base + offset when possible.
data AddrDecomposeResult t
   = Symbolic t
   | ConcreteOffset t Integer
   | SymbolicOffset t t
  deriving (Show)

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

data MemWrite p c t
    -- | @MemCopy dst src len@ represents a copy from [src..src+len) to
    -- [dst..dst+len).
  = MemCopy (p,AddrDecomposeResult p) p (p,Maybe Integer)
    -- | Memstore is given address was written, value, and type of value.
  | MemStore (p,AddrDecomposeResult p) t Type
    -- | The merger of two memories.
  | WriteMerge c [MemWrite p c t] [MemWrite p c t]

-- | This provides functions for manipulating symbolic addresses, propositions, and
-- values.
data TermGenerator m p c t = TG {
         tgPtrWidth :: Size

       , tgPtrDecompose :: p -> m (AddrDecomposeResult p)
       , tgPtrSizeDecompose :: p -> m (Maybe Integer)

       , tgConstPtr :: Size -> m p
       , tgAddPtr :: p -> p -> m p
         -- | Adds two pointers, returning value along with condition
         -- that holds if arithmetic did not overflow.
       , tgCheckedAddPtr :: p -> p -> m (c,p)
       , tgSubPtr :: p -> p -> m p

       , tgFalse :: c
       , tgTrue :: c
       , tgPtrEq :: p -> p -> m c
       , tgPtrLe :: p -> p -> m c
       , tgAnd :: c -> c -> m c
       , tgOr  :: c -> c -> m c
       , tgMuxCond :: c -> c -> c -> m c

       , tgUndefValue :: Type -> m t
       , tgApplyCtorF  :: ValueCtorF t -> m t
       , tgApplyViewF  :: ViewF t -> m t
       , tgMuxTerm :: c -> Type -> t -> t -> m t
       }

tgAddPtrC :: Monad m => TermGenerator m p c t -> p -> Addr -> m p
tgAddPtrC tg x y = tgAddPtr tg x =<< tgConstPtr tg y

tgApplyValueF :: TermGenerator m p c t -> ValueF p -> m p
tgApplyValueF tg (Add x y) = tgAddPtr tg x y
tgApplyValueF tg (Sub x y) = tgSubPtr tg x y
tgApplyValueF tg (CValue c) = tgConstPtr tg (fromInteger c)

badLoad :: (Applicative m, Monad m) => TermGenerator m p c t -> Type -> m (c,t)
badLoad tg tp = (tgFalse tg,) <$> tgUndefValue tg tp

genValue :: (Applicative m, Monad m) => TermGenerator m p c t -> (v -> p) -> Value v -> m p
genValue tg f = foldTermM (return . f) (tgApplyValueF tg)

genCondVar :: (Applicative m, Monad m) => TermGenerator m p c t -> (v -> p) -> Cond v -> m c
genCondVar tg f c =
  case c of
    Eq x y  -> join $ tgPtrEq tg <$> genValue tg f x <*> genValue tg f y
    Le x y  -> join $ tgPtrLe tg <$> genValue tg f x <*> genValue tg f y
    And x y -> join $ tgAnd tg <$> genCondVar tg f x <*> genCondVar tg f y

genValueCtor :: (Applicative m, Monad m)
             => TermGenerator m p c t -> ValueCtor t -> m t
genValueCtor tg = foldTermM return (tgApplyCtorF tg)

applyView :: (Applicative m, Monad m)
          => TermGenerator m p c t -> t -> ValueView Type -> m t
applyView tg t = foldTermM (\_ -> return t) (tgApplyViewF tg)

-- | Join all conditions in fold together.
tgAll :: Monad m
      => TermGenerator m p c t
      -> Getting (Dual (Endo (c -> m c))) s c
      -> s
      -> m c
tgAll tg fld = foldrMOf fld (tgAnd tg) (tgTrue tg)

tgMuxPair :: Applicative m
          => TermGenerator m p c t
          -> c
          -> Type
          -> (c,t)
          -> (c,t)
          -> m (c,t)
tgMuxPair tg c tp (xc,xt) (yc,yt) =
  (,) <$> tgMuxCond tg c xc yc
      <*> tgMuxTerm tg c tp xt yt

evalValueCtor :: (Applicative m, Monad m )
              => TermGenerator m p c t
              -> ValueCtor (c,t)
              -> m (c,t)
evalValueCtor tg vc =
   (,) <$> tgAll tg (traverse . _1) vc
       <*> genValueCtor tg (snd <$> vc)

evalMuxValueCtor :: forall m u p c t .
                    (Applicative m, Monad m)
                 => TermGenerator m p c t
                    -- Type for value returned
                 -> Type
                    -- Evaluation function
                 -> (Var -> p)
                    -- Function for reading specific subranges.
                 -> (u -> m (c,t))
                 -> Mux (Cond Var) (ValueCtor u)
                 -> m (c,t)
evalMuxValueCtor tg tp vf subFn t =
  reduceMux (\c -> tgMuxPair tg c tp)
    =<< muxLeaf (evalValueCtor tg)
    =<< muxCond (genCondVar tg vf)
    =<< muxLeaf (traverse subFn) t

readMemCopy :: forall m p c t .
               (Applicative m, MonadIO m, Eq p)
            => TermGenerator m p c t
            -> (p, AddrDecomposeResult p)
            -> Type
            -> (p, AddrDecomposeResult p)
            -> p
            -> (p,Maybe Integer)
            -> (Type -> (p, AddrDecomposeResult p) -> m (c,t))
            -> m (c,t)
readMemCopy tg (l,ld) tp (d,dd) src (sz,szd) readPrev' = do
  let varFn :: Var -> p
      varFn Load = l
      varFn Store = d
      varFn StoreSize = sz
  let readPrev tp' p = readPrev' tp' . (p,) =<< tgPtrDecompose tg p
  case (ld, dd) of
    -- Offset if known
    ( ConcreteOffset lv lo
      , ConcreteOffset sv so
      )
      | lv == sv -> do
      let subFn :: RangeLoad Addr -> m (c,t)
          subFn (OutOfRange o tp') = readPrev tp' =<< tgAddPtrC tg lv o
          subFn (InRange    o tp') = readPrev tp' =<< tgAddPtrC tg src o
      case szd of
        Just csz -> do
          let s = R (fromInteger so) (fromInteger (so + csz))
          let vcr = rangeLoad (fromInteger lo) tp s
          evalValueCtor tg =<< traverse subFn vcr
        _ ->
          evalMuxValueCtor tg tp varFn subFn $
            fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' tp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: RangeLoad (Value Var) -> m (c,t)
          subFn (OutOfRange o tp') =
            readPrev tp' =<< genValue tg varFn o
          subFn (InRange o tp') =
            readPrev tp' =<< tgAddPtr tg src =<< genValue tg varFn o
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      let mux0 | Just csz <- szd =
                   fixedSizeRangeLoad pref tp (fromInteger csz)
               | otherwise =
                   symbolicRangeLoad pref tp
      evalMuxValueCtor tg tp varFn subFn mux0

readMemStore :: forall m p c t .
               (Applicative m, MonadIO m, Eq p)
            => TermGenerator m p c t
            -> (p,AddrDecomposeResult p)
               -- ^ The loaded address and information
            -> Type
               -- The type we are reading.
            -> (p,AddrDecomposeResult p)
               -- ^ The store we are reading from.
            -> t
               -- ^ The value that was stored.
            -> Type
               -- ^ The type of value that was written.
            -> (Type -> (p, AddrDecomposeResult p) -> m (c,t))
               -- ^ A callback function for when reading fails.
            -> m (c,t)
readMemStore tg (l,ld) ltp (d,dd) t stp readPrev' = do
  ssz <- tgConstPtr tg (typeSize stp)
  let varFn :: Var -> p
      varFn Load = l
      varFn Store = d
      varFn StoreSize = ssz
  let readPrev tp p = readPrev' tp . (p,) =<< tgPtrDecompose tg p
  case (ld, dd) of
    -- Offset if known
    ( ConcreteOffset lv lo
      , ConcreteOffset sv so
      )
      | lv == sv -> do
      let subFn :: ValueLoad Addr -> m (c,t)
          subFn (OldMemory o tp')   = readPrev tp' =<< tgAddPtrC tg lv o
          subFn (LastStore v)       = (tgTrue tg,) <$> applyView tg t v
          subFn (InvalidMemory tp') = badLoad tg tp'
      let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (Var stp)
      evalValueCtor tg =<< traverse subFn vcr
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' ltp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: ValueLoad (Value Var) -> m (c,t)
          subFn (OldMemory o tp')   = do
                     readPrev tp' =<< genValue tg varFn o
          subFn (LastStore v)       = do
                     (tgTrue tg,) <$> applyView tg t v
          subFn (InvalidMemory tp') = badLoad tg tp'
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      evalMuxValueCtor tg ltp varFn subFn $
        symbolicValueLoad pref ltp (Var stp)

readMem :: (Applicative m, MonadIO m, Eq p, Ord p)
        => TermGenerator m p c t
        -> p
        -> Type
        -> Mem p c t
        -> m (c,t)
readMem tg l tp m = do
  ld <- tgPtrDecompose tg l
  readMem' tg (l,ld) tp (memWrites m)

-- | Read a value from memory given a list of writes.
--
-- This represents a predicate indicating if the read was successful, and the value
-- read (which may be anything if read was unsuccessful).
readMem' :: (Applicative m, MonadIO m, Ord p)
         => TermGenerator m p c t
            -- ^ Functions for primitive operations on addresses, propositions, and values.
         -> (p, AddrDecomposeResult p)
            -- Address we are reading along with information about how it was constructed.
         -> Type
            -- The type to read from memory.
         -> [MemWrite p c t]
            -- List of writes.
         -> m (c,t)
readMem' tg _ tp [] = badLoad tg tp
readMem' tg l tp (h:r) = do
  cache <- liftIO $ newIORef Map.empty
  let readPrev tp' l' = do
        m <- liftIO $ readIORef cache
        case Map.lookup (tp',fst l') m of
          Just x -> return x
          Nothing -> do
            x <- readMem' tg l' tp' r
            liftIO $ writeIORef cache $ Map.insert (tp',fst l') x m
            return x
  case h of
    MemCopy dst src sz -> do
      readMemCopy tg l tp dst src sz readPrev
    MemStore dst v stp -> do
      readMemStore tg l tp dst v stp readPrev
    WriteMerge c xr yr -> do
      join $ tgMuxPair tg c tp
               <$> readMem' tg l tp (xr++r)
               <*> readMem' tg l tp (yr++r)

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

isAllocated' :: (Applicative m, Monad m)
             => TermGenerator m p c t
                -- ^ Evaluation function that takes continuation
                -- for condition if previous check fails.
             -> (p -> p -> m c -> m c)
             -> [MemAlloc p c]
             -> m c
isAllocated' tg _ [] = pure (tgFalse tg)
isAllocated' tg step (Alloc _ a asz:r) = do
  step a asz (isAllocated' tg step r)
isAllocated' tg step (AllocMerge c xr yr:r) =
  join $ tgMuxCond tg c
         <$> isAllocated' tg step (xr ++ r)
         <*> isAllocated' tg step (yr ++ r)


-- | @offsetisAllocated tg b o sz m@ returns condition required to prove range
-- @[b+o..b+o+sz)@ lays within a single allocation in @m@.  This code assumes
-- @sz@ is non-zero, and @b+o@ does not overflow.
offsetIsAllocated :: (Applicative m, Monad m, Eq p)
                  => TermGenerator m p c t -> p -> p -> p -> Mem p c t -> m c
offsetIsAllocated tg t o sz m = do
  (oc, oe) <- tgCheckedAddPtr tg o sz
  let step a asz fallback
        | t == a = tgPtrLe tg oe asz
            --Debug.trace "offsetIsAllocated: comparing <=" $ tgPtrLe tg oe asz
        | otherwise = fallback
  tgAnd tg oc =<< isAllocated' tg step (memAllocs m)

isAllocated :: (Applicative m, Monad m, Eq p)
            => TermGenerator m p c t -> p -> p -> Mem p c t -> m c
isAllocated tg p sz m = do
  ld <- tgPtrDecompose tg p
  case ld of
    Symbolic{} -> do
      (oc,pe) <- tgCheckedAddPtr tg p sz
      let step a asz fallback =
            join $ tgOr tg
              <$> (do ae <- tgAddPtr tg a asz
                      join $ tgAnd tg <$> tgPtrLe tg a p <*> tgPtrLe tg pe ae)
              <*> fallback
      tgAnd tg oc =<< isAllocated' tg step (memAllocs m)
    ConcreteOffset t o0 -> do
      o <- tgConstPtr tg (fromInteger o0)
      offsetIsAllocated tg t o sz m
    SymbolicOffset t o -> do
      offsetIsAllocated tg t o sz m


-- | @isValidPointer tg b m@ returns condition required to prove range
--   that @p@ is a valid pointer in @m@.  This means that @p@ is in the
--   range of some allocation OR ONE PAST THE END of an allocation.  In other words
--   @p@ is a valid pointer if @b <= p <= b+sz@ for some allocation
--   at base @b@ of size @sz@.  Note that, even though @b+sz@ is outside the
--   allocation range of the allocation (loading through it will fail) it is
--   nonetheless a valid pointer value.  This strange special case is baked into
--   the C standard to allow certain common coding patterns to be defined.
isValidPointer :: (Applicative m, Monad m, Eq p)
        => TermGenerator m p c t -> p -> Mem p c t -> m c
isValidPointer tg p m = do
   sz <- tgConstPtr tg 0
   isAllocated tg p sz m
 -- NB We call isAllocated with a size of 0.  This is a violation of the usual rules, but gives
 -- precicely what we need for the valid pointer check.

writeMem :: (Applicative m, Monad m, Eq p)
         => TermGenerator m p c t
         -> p
         -> Type
         -> t
         -> Mem p c t
         -> m (c,Mem p c t)
writeMem tg p tp v m = do
  (,) <$> (do sz <- tgConstPtr tg (typeEnd 0 tp)
              isAllocated tg p sz m)
      <*> writeMem' tg p tp v m

-- | Write memory without checking if it is allocated.
writeMem' :: (Applicative m, Monad m, Eq p)
          => TermGenerator m p c t
          -> p
          -> Type
          -> t
          -> Mem p c t
          -> m (Mem p c t)
writeMem' tg p tp v m = addWrite <$> tgPtrDecompose tg p
  where addWrite pd = m & memAddWrite (MemStore (p,pd) v tp)

-- | Perform a mem copy.
copyMem :: (Applicative m, Monad m, Eq p)
         => TermGenerator m p c t
         -> p -- ^ Dest
         -> p -- ^ Source
         -> p -- ^ Size
         -> Mem p c t
         -> m (c,Mem p c t)
copyMem tg dst src sz m = do
  (,) <$> (join $ tgAnd tg <$> isAllocated tg dst sz m
                           <*> isAllocated tg src sz m)
      <*> (do dstd <- tgPtrDecompose tg dst
              szd <- tgPtrSizeDecompose tg sz
              return $ m & memAddWrite (MemCopy (dst,dstd) src (sz,szd)))


-- | Allocate space for memory
allocMem :: AllocType -- ^ Type of allocation
         -> p -- ^ Base for allocation
         -> p -- ^ Size
         -> Mem p c t
         -> Mem p c t
allocMem a b sz = memAddAlloc (Alloc a b sz)

-- | Allocate space for memory
allocAndWriteMem :: (Applicative m, Monad m, Eq p)
                 => TermGenerator m p c t
                 -> AllocType -- ^ Type of allocation
                 -> p -- ^ Base for allocation
                 -> Type
                 -> t -- Value to write
                 -> Mem p c t
                 -> m (Mem p c t)
allocAndWriteMem tg a b tp v m = do
  sz <- tgConstPtr tg (typeEnd 0 tp)
  writeMem' tg b tp v (m & memAddAlloc (Alloc a b sz))

pushStackFrameMem :: Mem p c t -> Mem p c t
pushStackFrameMem = memState %~ StackFrame emptyChanges

popStackFrameMem :: Mem p c t -> Mem p c t
popStackFrameMem m = m & memState %~ popf
  where popf (StackFrame (a,w) s) = s & memStateLastChanges %~ prependChanges c
          where c = (mapMaybe pa a, w)

        -- WARNING: The following code executes a stack pop underneith a branch
        -- frame.  This is necessary to get merges to work correctly
        -- when they propigate all the way to function returns.
        -- However, it is not clear that the following code is
        -- precicely correct because it may leave in place writes to
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

freeMem :: forall m p c t
         . (Applicative m, Monad m, Eq p)
        => TermGenerator m p c t
        -> p -- ^ Base of allocation to free
        -> Mem p c t
        -> m (c, Mem p c t)
freeMem tg p m = do
  p' <- tgPtrDecompose tg p
  freeMem' tg p p' m

-- FIXME? This could perhaps be more efficent.  Right now we
-- will traverse almost the entire memory on every free, even
-- if we concretely find the corresponding allocation early.
freeMem' :: forall m p c t
         . (Applicative m, Monad m, Eq p)
        => TermGenerator m p c t
        -> p
        -> AddrDecomposeResult p -- ^ Base of allocation to free
        -> Mem p c t
        -> m (c, Mem p c t)
freeMem' tg p p_decomp m = do
    (c, st') <- freeSt (m^.memState)
    return (c, m & memState .~ st')
 where
  freeAllocs :: [MemAlloc p c] -> m (c, [MemAlloc p c])
  freeAllocs [] =
     return ( tgFalse tg , [] )
  freeAllocs (a@(Alloc HeapAlloc base _) : as) = do
     base' <- tgPtrDecompose tg base
     case (p_decomp, base') of
       (ConcreteOffset p' poff,
         ConcreteOffset b' boff)
           | p' == b' -> do
               let c = if poff == boff then tgTrue tg else tgFalse tg
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (ConcreteOffset p' poff,
         SymbolicOffset b' boff)
           | p' == b' -> do
               c <- tgPtrEq tg boff =<< tgConstPtr tg (fromIntegral poff)
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (SymbolicOffset p' poff,
         ConcreteOffset b' boff)
           | p' == b' -> do
               c <- tgPtrEq tg poff =<< tgConstPtr tg (fromIntegral boff)
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       (SymbolicOffset p' poff,
         SymbolicOffset b' boff)
           | p' == b' -> do
               c <- tgPtrEq tg boff poff
               return (c, as)
           | otherwise -> do
                (c, as') <- freeAllocs as
                return (c, a : as')
       _ -> do
         eq <- tgPtrEq tg p base
         (c, as') <- freeAllocs as
         c'  <- tgOr tg eq c
         return (c', AllocMerge eq [] [a] : as')

  freeAllocs (a@(Alloc _ _ _) : as) = do
     (c, as') <- freeAllocs as
     return (c, a:as')
  freeAllocs (AllocMerge cm x y : as) = do
     (c1, x') <- freeAllocs x
     (c2, y') <- freeAllocs y
     c <- tgMuxCond tg cm c1 c2
     (c3, as') <- freeAllocs as
     c' <- tgOr tg c c3
     return (c', AllocMerge cm x' y' : as')

  freeCh :: MemChanges p c t -> m (c, MemChanges p c t)
  freeCh (a, w) = do
      (c,a') <- freeAllocs a
      return (c, (a', w))

  freeSt :: MemState (MemChanges p c t)
         -> m (c, MemState (MemChanges p c t))
  freeSt (StackFrame ch st) = do
            (c1,ch') <- freeCh ch
            (c2,st') <- freeSt st
            c <- tgOr tg c1 c2
            return (c, StackFrame ch' st')
  freeSt (BranchFrame ch st) = do
            (c1,ch') <- freeCh ch
            (c2,st') <- freeSt st
            c <- tgOr tg c1 c2
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
