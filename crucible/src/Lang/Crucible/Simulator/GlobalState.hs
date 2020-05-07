{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lang.Crucible.Simulator.GlobalState
  ( SymGlobalState
  , emptyGlobals
  , GlobalEntry(..)
  , insertGlobal
  , lookupGlobal
  , insertRef
  , lookupRef
  , dropRef
  , updateRef
  , globalPushBranch
  , globalAbortBranch
  , globalMuxFn
  ) where

import           Control.Applicative ((<|>))
import           Control.Monad.Trans.Class (lift)
import           Data.Functor.Identity
import           Data.Kind

import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF

import           What4.Interface
import           What4.Partial

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap

-- | As a map element, type @GlobalEntry sym tp@ models the contents
-- of a 'GlobalVar', which is always defined.
newtype GlobalEntry (sym :: Type) (tp :: CrucibleType) =
  GlobalEntry { globalEntryValue :: RegValue sym tp }

-- | Type @RefCellContents sym tp@ models the contents of a @RefCell@,
-- which holds a partial value. A @RefCell@ not found in the map is
-- considered to represent the 'Unassigned' value.
data RefCellContents (sym :: Type) (tp :: CrucibleType)
  = RefCellContents !(Pred sym) !(RegValue sym tp)

-- | Type @RefCellUpdate sym tp@ models an update to the contents of a
-- @RefCell@. The value @RefCellUpdate Unassigned@ represents the
-- deletion of a @RefCell@.
newtype RefCellUpdate (sym :: Type) (tp :: CrucibleType) =
  RefCellUpdate (PartExpr (Pred sym) (RegValue sym tp))

------------------------------------------------------------------------
-- GlobalTable

data GlobalTable f g =
  GlobalTable
  { globalVars :: !(MapF.MapF GlobalVar f)
  , globalRefs :: !(MapF.MapF RefCell g)
  }

updateGlobalVars ::
  (MapF.MapF GlobalVar v -> MapF.MapF GlobalVar v) ->
  GlobalTable v r -> GlobalTable v r
updateGlobalVars f (GlobalTable vs rs) = GlobalTable (f vs) rs

updateGlobalRefs ::
  (MapF.MapF RefCell r -> MapF.MapF RefCell r) ->
  GlobalTable v r -> GlobalTable v r
updateGlobalRefs f (GlobalTable vs rs) = GlobalTable vs (f rs)

-- | The empty set of global variable updates.
emptyGlobalTable :: GlobalTable v r
emptyGlobalTable = GlobalTable MapF.empty MapF.empty

-- | Take the union of two sets of updates, preferring elements from
-- the first set when duplicate keys are encountered.
mergeGlobalTable :: GlobalTable v r -> GlobalTable v r -> GlobalTable v r
mergeGlobalTable (GlobalTable vs1 rs1) (GlobalTable vs2 rs2) =
  GlobalTable (MapF.union vs1 vs2) (MapF.union rs1 rs2)

-- | Maps from global variables and global references to their values.
type GlobalContents sym = GlobalTable (GlobalEntry sym) (RefCellContents sym)

-- | A collection of updates to the global variables and global
-- references that have happened since a branch push.
type GlobalUpdates sym = GlobalTable (GlobalEntry sym) (RefCellUpdate sym)

-- | Apply a set of updates to the contents of global memory.
-- @GlobalVar@s cannot be deleted, so we just merge the @GlobalVar@
-- maps, preferring entries from the first argument. When merging the
-- @RefCell@ maps, a @RefCellUpdate Unassigned@ entry causes the
-- corresponding entry in the old map to be deleted.
applyGlobalUpdates :: forall sym . GlobalUpdates sym -> GlobalContents sym -> GlobalContents sym
applyGlobalUpdates (GlobalTable vs1 rs1) (GlobalTable vs2 rs2) =
  GlobalTable (MapF.union vs1 vs2) (runIdentity (MapF.mergeWithKeyM both left Identity rs1 rs2))
  where
    upd :: forall tp. RefCellUpdate sym tp -> Maybe (RefCellContents sym tp)
    upd (RefCellUpdate Unassigned) = Nothing
    upd (RefCellUpdate (PE p e)) = Just (RefCellContents p e)

    both :: forall tp. RefCell tp -> RefCellUpdate sym tp -> RefCellContents sym tp -> Identity (Maybe (RefCellContents sym tp))
    both _ u _ = Identity (upd u)

    left :: MapF.MapF RefCell (RefCellUpdate sym) -> Identity (MapF.MapF RefCell (RefCellContents sym))
    left m = Identity (MapF.mapMaybe upd m)

------------------------------------------------------------------------
-- GlobalFrames

-- | The state of global memory as a stack of changes separated by
-- branch pushes. The second parameter of 'BranchFrame' caches
-- the combined view of memory as of the previous branch push.
data GlobalFrames (sym :: Type) =
    InitialFrame !(GlobalContents sym)
  | BranchFrame !(GlobalUpdates sym) (GlobalContents sym) !(GlobalFrames sym)

-- | The depth of this value represents the number of symbolic
-- branches currently pending. We use this primarily as a sanity check
-- to help find bugs where we fail to match up calls to
-- 'globalPushBranch' with 'globalAbortBranch'/'globalMuxFn'.
globalPendingBranches :: GlobalFrames sym -> Int
globalPendingBranches (InitialFrame _) = 0
globalPendingBranches (BranchFrame _ _ gf) = 1 + globalPendingBranches gf

-- | The empty set of global variable bindings.
emptyGlobalFrames :: GlobalFrames sym
emptyGlobalFrames = InitialFrame emptyGlobalTable

------------------------------------------------------------------------
-- GlobalTable

-- | A map from global variables to their value.
data SymGlobalState (sym :: Type) =
  GlobalState
  { globalFrames :: !(GlobalFrames sym)
    -- ^ The stack of updates to global memory, separated by branch
    -- pushes. This field only contains values with ordinary crucible
    -- types (i.e. not intrinsic), which do not have mux operations
    -- that require branch push notifications.
  , globalIntrinsics :: !(GlobalContents sym)
    -- ^ The set of updates since initialization to vars and refs that
    -- have intrinsic or "any" types, which must be notified of
    -- branch pushes.
  }

-- | The empty set of global variable bindings.
emptyGlobals :: SymGlobalState sym
emptyGlobals = GlobalState emptyGlobalFrames emptyGlobalTable

-- | Test whether this type could be an intrinsic type, which must be
-- notified of branch pushes and aborts.
needsNotification :: TypeRepr tp -> Bool
needsNotification tr =
  case tr of
    IntrinsicRepr{} -> True
    AnyRepr -> True
    _ -> False

-- | Lookup a global variable in the state.
lookupGlobal :: GlobalVar tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupGlobal g gst
  | needsNotification (globalType g) =
      globalEntryValue <$> MapF.lookup g (globalVars (globalIntrinsics gst))
  | otherwise =
      globalEntryValue <$> go (globalFrames gst)
  where
    -- We never have to search more than one level deep, because the
    -- 'BranchFrame' constructor caches the combined contents of the
    -- rest of the 'GlobalFrames'.
    go (InitialFrame c) = MapF.lookup g (globalVars c)
    go (BranchFrame u c _) = MapF.lookup g (globalVars u) <|> MapF.lookup g (globalVars c)

-- | Set the value of a global in the state, or create a new global variable.
insertGlobal ::
  GlobalVar tp ->
  RegValue sym tp ->
  SymGlobalState sym ->
  SymGlobalState sym
insertGlobal g v gst
  | needsNotification (globalType g) =
      gst{ globalIntrinsics = updateGlobalVars (MapF.insert g x) (globalIntrinsics gst) }
  | otherwise =
      gst{ globalFrames = upd (globalFrames gst) }
  where
    x = GlobalEntry v
    upd (InitialFrame c) = InitialFrame (updateGlobalVars (MapF.insert g x) c)
    upd (BranchFrame u c gf) = BranchFrame (updateGlobalVars (MapF.insert g x) u) c gf
    -- NOTE: While global variables can be updated within branches, it
    -- should probably be forbidden to create a new global variable in
    -- a branch. However, we don't check for this currently. (An error
    -- will happen later when merging the branches if the set of
    -- global variables does not match.)

-- | Look up the value of a reference cell in the state.
lookupRef :: RefCell tp -> SymGlobalState sym -> PartExpr (Pred sym) (RegValue sym tp)
lookupRef r gst
  | needsNotification (refType r) = post $ MapF.lookup r (globalRefs (globalIntrinsics gst))
  | otherwise = go (globalFrames gst)
  where
    -- We never have to search more than one level deep, because the
    -- 'BranchFrame' constructor caches the combined contents of the
    -- rest of the 'GlobalFrames'.
    post = maybe Unassigned (\(RefCellContents p e) -> PE p e)
    go (InitialFrame c) = post $ MapF.lookup r (globalRefs c)
    go (BranchFrame u c _) =
      case MapF.lookup r (globalRefs u) of
        Just (RefCellUpdate pe) -> pe
        Nothing -> post $ MapF.lookup r (globalRefs c)

-- | Set the value of a reference cell in the state.
insertRef ::
  IsExprBuilder sym =>
  sym ->
  RefCell tp ->
  RegValue sym tp ->
  SymGlobalState sym ->
  SymGlobalState sym
insertRef sym r v = updateRef r (PE (truePred sym) v)

-- | Write a partial value to a reference cell in the state.
updateRef ::
  -- IsExprBuilder sym =>
  RefCell tp ->
  PartExpr (Pred sym) (RegValue sym tp) ->
  SymGlobalState sym ->
  SymGlobalState sym
updateRef r pe gst
  | needsNotification (refType r) =
      gst{ globalIntrinsics = updateGlobalRefs ins (globalIntrinsics gst) }
  | otherwise =
      gst{ globalFrames = upd (globalFrames gst) }
  where
    ins =
      case pe of
        Unassigned -> MapF.delete r
        PE p e -> MapF.insert r (RefCellContents p e)
    upd (InitialFrame c) = InitialFrame (updateGlobalRefs ins c)
    upd (BranchFrame u c gf) =
      BranchFrame (updateGlobalRefs (MapF.insert r (RefCellUpdate pe)) u) c gf

-- | Reset a reference cell to the uninitialized state. @'dropRef' r@ is
-- equivalent to @'updateRef' r 'Unassigned'@.
dropRef :: RefCell tp -> SymGlobalState sym -> SymGlobalState sym
dropRef r = updateRef r Unassigned

-- | Mark a branch point in the global state. Later calls to
-- 'globalMuxFn' will assume that the input states are identical up
-- until the most recent branch point.
globalPushBranch ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  SymGlobalState sym ->
  IO (SymGlobalState sym)
globalPushBranch sym iTypes (GlobalState gf (GlobalTable vs rs)) =
  do -- Notify intrinsic-typed vars and refs of the branch push.
     vs' <- MapF.traverseWithKey
            (\v (GlobalEntry e) ->
              GlobalEntry <$> pushBranchForType sym iTypes (globalType v) e)
            vs
     rs' <- MapF.traverseWithKey
            (\r (RefCellContents p e) ->
              RefCellContents p <$> pushBranchForType sym iTypes (refType r) e)
            rs
     --loc <- getCurrentProgramLoc sym
     --putStrLn $ unwords ["PUSH BRANCH:", show d, show $ plSourceLoc loc]
     let gf' = BranchFrame emptyGlobalTable cache gf
     return (GlobalState gf' (GlobalTable vs' rs'))
  where
    cache =
      case gf of
        InitialFrame c -> c
        BranchFrame u c _ -> applyGlobalUpdates u c

-- | Merge a set of updates into the outermost frame of a stack of global frames.
abortBranchFrame :: GlobalUpdates sym -> GlobalFrames sym -> GlobalFrames sym
abortBranchFrame u (InitialFrame c) = InitialFrame (applyGlobalUpdates u c)
abortBranchFrame u (BranchFrame u' c gf) = BranchFrame (mergeGlobalTable u u') c gf

-- | Remove the most recent branch point marker, and thus cancel the
-- effect of the most recent 'globalPushBranch'.
globalAbortBranch ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  SymGlobalState sym ->
  IO (SymGlobalState sym)

globalAbortBranch sym iTypes (GlobalState (BranchFrame u _ gf) (GlobalTable vs rs)) =
  do -- Notify intrinsic-typed vars and refs of the branch abort.
     vs' <- MapF.traverseWithKey
            (\v (GlobalEntry e) ->
              GlobalEntry <$> abortBranchForType sym iTypes (globalType v) e)
            vs
     rs' <- MapF.traverseWithKey
            (\r (RefCellContents p e) ->
              RefCellContents p <$> abortBranchForType sym iTypes (refType r) e)
            rs
     --loc <- getCurrentProgramLoc sym
     --putStrLn $ unwords ["ABORT BRANCH:", show (d-1), show $ plSourceLoc loc]
     let gf' = abortBranchFrame u gf
     return (GlobalState gf' (GlobalTable vs' rs'))

globalAbortBranch sym _ (GlobalState (InitialFrame _) _) =
  do loc <- getCurrentProgramLoc sym
     panic "GlobalState.globalAbortBranch"
       [ "Attempting to commit global changes at branch depth 0"
       , "*** Location: " ++ show (plSourceLoc loc)
       ]

muxPartialRegForType ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  TypeRepr tp ->
  MuxFn (Pred sym) (PartExpr (Pred sym) (RegValue sym tp))
muxPartialRegForType sym iteFns tp =
  mergePartial sym (\c u v -> lift $ muxRegForType sym iteFns tp c u v)

-- | A symbolic mux function for @GlobalContents@.
muxGlobalContents ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  MuxFn (Pred sym) (GlobalContents sym)
muxGlobalContents sym iteFns c (GlobalTable vs1 rs1) (GlobalTable vs2 rs2) =
  do vs' <- MapF.mergeWithKeyM muxEntry checkNullMap checkNullMap vs1 vs2
     rs' <- MapF.mergeWithKeyM muxRef refLeft refRight rs1 rs2
     return (GlobalTable vs' rs')
  where
    muxEntry :: GlobalVar tp
             -> GlobalEntry sym tp
             -> GlobalEntry sym tp
             -> IO (Maybe (GlobalEntry sym tp))
    muxEntry g (GlobalEntry u) (GlobalEntry v) =
      Just . GlobalEntry <$> muxRegForType sym iteFns (globalType g) c u v

    muxRef :: RefCell tp
           -> RefCellContents sym tp
           -> RefCellContents sym tp
           -> IO (Maybe (RefCellContents sym tp))
    muxRef r (RefCellContents pu u) (RefCellContents pv v) =
      do uv <- muxRegForType sym iteFns (refType r) c u v
         p <- itePred sym c pu pv
         return . Just $ RefCellContents p uv

    -- Make a partial value undefined unless the given predicate holds.
    restrictRefCellContents :: Pred sym -> RefCellContents sym tp -> IO (RefCellContents sym tp)
    restrictRefCellContents p1 (RefCellContents p2 x) =
      do p' <- andPred sym p1 p2
         return (RefCellContents p' x)

    refLeft :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
    refLeft m = traverseF (restrictRefCellContents c) m

    refRight :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
    refRight m =
      do cnot <- notPred sym c
         traverseF (restrictRefCellContents cnot) m

    -- Sets of global variables are required to be the same in both branches.
    checkNullMap :: MapF.MapF GlobalVar (GlobalEntry sym)
                 -> IO (MapF.MapF GlobalVar (GlobalEntry sym))
    checkNullMap m
      | MapF.null m = return m
      | otherwise =
        panic "GlobalState.globalMuxFn"
                [ "Different global variables in each branch." ]

data EitherOrBoth f g (tp :: k) =
  JustLeft (f tp) | Both (f tp) (g tp) | JustRight (g tp)

-- | A symbolic mux function for @GlobalUpdates@. For cases where a
-- pre-existing value is updated only on one side, we require a
-- @GlobalContents@ to look up the previous value to use in place of
-- the missing update.
muxGlobalUpdates ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  GlobalContents sym ->
  MuxFn (Pred sym) (GlobalUpdates sym)
muxGlobalUpdates sym iteFns (GlobalTable vs0 rs0) c (GlobalTable vs1 rs1) (GlobalTable vs2 rs2) =
  do -- Zip together the two maps of globals.
     vs3 <- MapF.mergeWithKeyM
            (\_ x y -> return (Just (Both x y)))
            (traverseF (return . JustLeft))
            (traverseF (return . JustRight))
            vs1 vs2
     vs' <- MapF.mergeWithKeyM
            (\k x0 e ->
              Just <$>
              case e of
                JustLeft x1 -> muxEntry k x1 x0 -- use old value x0 for right side
                JustRight x2 -> muxEntry k x0 x2 -- use old value x0 for left side
                Both x1 x2 -> muxEntry k x1 x2)
            (\_ -> return MapF.empty) -- old values updated on neither side are excluded from merged updates
            (MapF.traverseWithKey $ \k e ->
              case e of
                JustLeft _ -> panicNull -- panic if there is no old value
                JustRight _ -> panicNull -- panic if there is no old value
                Both x1 x2 -> muxEntry k x1 x2)
            vs0
            vs3

     -- Zip together the two maps of references.
     rs3 <- MapF.mergeWithKeyM
            (\_ x y -> return (Just (Both x y)))
            (traverseF (return . JustLeft))
            (traverseF (return . JustRight))
            rs1 rs2
     rs' <- MapF.mergeWithKeyM
            (\k (RefCellContents p e) eb ->
              let x0 = RefCellUpdate (PE p e) in
              Just <$>
              case eb of
                JustLeft x1 -> muxRef k x1 x0 -- use old value x0 for right side
                JustRight x2 -> muxRef k x0 x2 -- use old value x0 for left side
                Both x1 x2 -> muxRef k x1 x2)
            (\_ -> return MapF.empty) -- old values updated on neither side are excluded from merged updates
            (MapF.traverseWithKey $ \k e ->
              case e of
                JustLeft x1 -> muxRef k x1 undef -- x1 was newly-created on left side, undefined on right
                JustRight x2 -> muxRef k undef x2 -- x2 was newly-created on right side, undefined on left
                Both x1 x2 -> muxRef k x1 x2)
            rs0
            rs3
     return (GlobalTable vs' rs')
  where
    undef :: forall tp. RefCellUpdate sym tp
    undef = RefCellUpdate Unassigned

    muxEntry :: GlobalVar tp
             -> GlobalEntry sym tp
             -> GlobalEntry sym tp
             -> IO (GlobalEntry sym tp)
    muxEntry g (GlobalEntry u) (GlobalEntry v) =
      GlobalEntry <$> muxRegForType sym iteFns (globalType g) c u v

    muxRef :: RefCell tp
           -> RefCellUpdate sym tp
           -> RefCellUpdate sym tp
           -> IO (RefCellUpdate sym tp)
    muxRef r (RefCellUpdate pe1) (RefCellUpdate pe2) =
      RefCellUpdate <$> muxPartialRegForType sym iteFns (refType r) c pe1 pe2

    panicNull =
      panic "GlobalState.globalMuxFn"
            [ "Different global variables in each branch." ]

-- | Compute a symbolic if-then-else on two global states. The
-- function assumes that the two states were identical up until the
-- most recent branch point marked by 'globalPushBranch'. This most
-- recent branch point marker is also popped from the stack.
globalMuxFn ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  MuxFn (Pred sym) (SymGlobalState sym)

globalMuxFn sym iteFns cond
  (GlobalState (BranchFrame u1 cache1 gf1) s1)
  (GlobalState (BranchFrame u2 _cache2 gf2) s2)
  | globalPendingBranches gf1 == globalPendingBranches gf2 =
    -- We assume gf1 is in fact equal to gf2, which should be the case
    -- if we've followed the appropriate branching discipline.
    do u3 <- muxGlobalUpdates sym iteFns cache1 cond u1 u2
       s3 <- muxGlobalContents sym iteFns cond s1 s2
       --let gf' = updateFrame (mergeGlobalUpdates x') gf1
       let gf3 =
             case gf1 of
               InitialFrame c' -> InitialFrame (applyGlobalUpdates u3 c')
               BranchFrame u' c' gf' -> BranchFrame (mergeGlobalTable u3 u') c' gf'
       return (GlobalState gf3 s3)

globalMuxFn sym _ _ (GlobalState gf1 _) (GlobalState gf2 _) =
  do loc <- getCurrentProgramLoc sym
     panic "GlobalState.globalMuxFn"
           [ "Attempting to merge global states of incorrect branch depths:"
           , " *** Depth 1:  " ++ show (globalPendingBranches gf1)
           , " *** Depth 2:  " ++ show (globalPendingBranches gf2)
           , " *** Location: " ++ show (plSourceLoc loc)
           ]
