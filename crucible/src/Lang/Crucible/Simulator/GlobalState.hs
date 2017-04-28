{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Simulator.GlobalState
  ( SymGlobalState(..)
  , emptyGlobals
  , GlobalEntry(..)
  , insertGlobal
  , lookupGlobal
  , insertRef
  , lookupRef
  , globalPushBranch
  , globalAbortBranch
  , globalMuxFn
  ) where

import qualified Data.Parameterized.Map as MapF

import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Interface

type MuxFn p v = p -> v -> v -> IO v


newtype GlobalEntry (sym :: *) (tp :: CrucibleType) = GlobalEntry { globalEntryValue :: RegValue sym tp }

------------------------------------------------------------------------
-- SymGlobalState

-- | A map from global variables to their value.
--   The integer value is the number of symbolic branches
--   currently pending.  We use this primarily as a sanity check
--   to help find bugs where we fail to match up calls to
--   globalPushBranch with globalAbortBranch/globalMuxFn
data SymGlobalState (sym :: *) =
  GlobalState
  { _globalPendingBranches :: Int
  , globalMap             :: MapF.MapF GlobalVar (GlobalEntry sym)
  , globalReferenceMap    :: MapF.MapF RefCell (GlobalEntry sym)
  }

-- | The empty set of global variable bindings
emptyGlobals :: SymGlobalState sym
emptyGlobals = GlobalState 0 MapF.empty MapF.empty

-- | Lookup a global in the state
lookupGlobal :: GlobalVar tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupGlobal g gst = globalEntryValue <$> MapF.lookup g (globalMap gst)

-- | Set the value of a global in the state.
insertGlobal :: GlobalVar tp
             -> RegValue sym tp
             -> SymGlobalState sym
             -> SymGlobalState sym
insertGlobal g v gst = gst{ globalMap = MapF.insert g (GlobalEntry v) (globalMap gst) }

-- | Lookup the value of a reference cell in the state
lookupRef :: RefCell tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupRef r gst = globalEntryValue <$> MapF.lookup r (globalReferenceMap gst)

-- | Set the value of a reference cell in the state
insertRef :: RefCell tp
          -> RegValue sym tp
          -> SymGlobalState sym
          -> SymGlobalState sym
insertRef r v gst =
   gst{ globalReferenceMap = MapF.insert r (GlobalEntry v) (globalReferenceMap gst) }

globalPushBranch :: forall sym
                  . IsSymInterface sym
                 => sym
                 -> IntrinsicTypes sym
                 -> SymGlobalState sym
                 -> IO (SymGlobalState sym)
globalPushBranch sym iTypes (GlobalState d g refs) = do
  g' <- MapF.traverseWithKey
         (\v e -> GlobalEntry <$>
                   pushBranchForType sym iTypes
                     (globalType v)
                     (globalEntryValue e))
         g
  refs' <- MapF.traverseWithKey
            (\r e -> GlobalEntry <$>
                     pushBranchForType sym iTypes
                       (refType r)
                       (globalEntryValue e))
           refs

  --loc <- getCurrentProgramLoc sym
  --putStrLn $ unwords ["PUSH BRANCH:", show d, show $ plSourceLoc loc]
  return (GlobalState (d+1) g' refs')

globalAbortBranch :: forall sym
                . IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> SymGlobalState sym
               -> IO (SymGlobalState sym)
globalAbortBranch sym iTypes (GlobalState d g refs)
  | d > 0 = do
      g' <- MapF.traverseWithKey
             (\v e -> GlobalEntry <$>
                       abortBranchForType sym iTypes
                         (globalType v)
                         (globalEntryValue e))
             g
      refs' <- MapF.traverseWithKey
                (\r e -> GlobalEntry <$>
                       abortBranchForType sym iTypes
                         (refType r)
                         (globalEntryValue e))
                refs

      --loc <- getCurrentProgramLoc sym
      --putStrLn $ unwords ["ABORT BRANCH:", show (d-1), show $ plSourceLoc loc]
      return (GlobalState (d-1) g' refs')

  | otherwise = do
      loc <- getCurrentProgramLoc sym
      fail $ unwords
         ["Attempting to commit global changes at incorrect branch depth"
         , show d
         , show $ plSourceLoc loc
         ]

globalMuxFn :: forall sym
             . IsSymInterface sym
             => sym
             -> IntrinsicTypes sym
             -> MuxFn (Pred sym) (SymGlobalState sym)
globalMuxFn sym iteFns c (GlobalState dx x refs_x) (GlobalState dy y refs_y)
 | dx > 0 && dx == dy = do
      GlobalState (dx - 1) <$> MapF.mergeWithKeyM muxEntry checkNullMap checkNullMap x y
                           <*> MapF.mergeWithKeyM muxRef return return refs_x refs_y

    where muxEntry :: GlobalVar tp
                   -> GlobalEntry sym tp
                   -> GlobalEntry sym tp
                   -> IO (Maybe (GlobalEntry sym tp))
          muxEntry g (GlobalEntry u) (GlobalEntry v) =
            Just . GlobalEntry <$> muxRegForType sym iteFns (globalType g) c u v

          muxRef :: RefCell tp
                 -> GlobalEntry sym tp
                 -> GlobalEntry sym tp
                 -> IO (Maybe (GlobalEntry sym tp))
          muxRef r (GlobalEntry u) (GlobalEntry v) =
            Just . GlobalEntry <$> muxRegForType sym iteFns (refType r) c u v

          checkNullMap :: MapF.MapF GlobalVar (GlobalEntry sym)
                       -> IO (MapF.MapF GlobalVar (GlobalEntry sym))
          checkNullMap m
            | MapF.null m = return m
            | otherwise = fail "Different global variables in each branch."

globalMuxFn sym _ _ (GlobalState dx _ _) (GlobalState dy _ _) = do
  loc <- getCurrentProgramLoc sym
  fail $ unwords
     ["Attempting to merge global states of incorrect branch depths:"
     , show dx
     , show dy
     , show $ plSourceLoc loc
     ]
