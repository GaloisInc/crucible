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
  , dropRef
  , updateRef
  , globalPushBranch
  , globalAbortBranch
  , globalMuxFn
  ) where

import           Data.Kind
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF

import           What4.Interface
import           What4.Partial
import           What4.ProgramLoc

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic(panic)

newtype GlobalEntry (sym :: Type) (tp :: CrucibleType) = GlobalEntry { globalEntryValue :: RegValue sym tp }
data RefCellContents (sym :: Type) (tp :: CrucibleType)
  = RefCellContents !(Pred sym) !(RegValue sym tp)

------------------------------------------------------------------------
-- SymGlobalState

-- | A map from global variables to their value.
--   The integer value is the number of symbolic branches
--   currently pending.  We use this primarily as a sanity check
--   to help find bugs where we fail to match up calls to
--   globalPushBranch with globalAbortBranch/globalMuxFn
data SymGlobalState (sym :: Type) =
  GlobalState
  { _globalPendingBranches :: Int
  , globalMap             :: MapF.MapF GlobalVar (GlobalEntry sym)
  , globalReferenceMap    :: MapF.MapF RefCell (RefCellContents sym)
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
lookupRef :: RefCell tp -> SymGlobalState sym -> PartExpr (Pred sym) (RegValue sym tp)
lookupRef r gst =
  maybe Unassigned (\(RefCellContents p x) -> PE p x) $ MapF.lookup r (globalReferenceMap gst)

-- | Set the value of a reference cell in the state
insertRef :: IsExprBuilder sym
          => sym
          -> RefCell tp
          -> RegValue sym tp
          -> SymGlobalState sym
          -> SymGlobalState sym
insertRef sym r v gst =
   let x = RefCellContents (truePred sym) v in
   gst{ globalReferenceMap = MapF.insert r x (globalReferenceMap gst) }


updateRef ::
  IsExprBuilder sym =>
  RefCell tp ->
  PartExpr (Pred sym) (RegValue sym tp) ->
  SymGlobalState sym ->
  SymGlobalState sym
updateRef r Unassigned gst =
  gst{ globalReferenceMap = MapF.delete r (globalReferenceMap gst) }
updateRef r (PE p x) gst =
  gst{ globalReferenceMap = MapF.insert r (RefCellContents p x) (globalReferenceMap gst) }

dropRef :: RefCell tp
        -> SymGlobalState sym
        -> SymGlobalState sym
dropRef r gst =
   gst{ globalReferenceMap = MapF.delete r (globalReferenceMap gst) }

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
            (\r (RefCellContents p e) ->
                   do e' <- pushBranchForType sym iTypes
                              (refType r) e
                      return (RefCellContents p e'))
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
                (\r (RefCellContents p e) ->
                      do e' <- abortBranchForType sym iTypes
                                  (refType r) e
                         return (RefCellContents p e'))
                refs

      --loc <- getCurrentProgramLoc sym
      --putStrLn $ unwords ["ABORT BRANCH:", show (d-1), show $ plSourceLoc loc]
      return (GlobalState (d-1) g' refs')

  | otherwise = do
      loc <- getCurrentProgramLoc sym
      panic "GlobalState.globalAbortBranch"
            [ "Attempting to commit global changes at incorrect branch depth"
            , "*** Depth:    " ++ show d
            , "*** Location: " ++ show (plSourceLoc loc)
            ]

globalMuxFn :: forall sym
             . IsSymInterface sym
             => sym
             -> IntrinsicTypes sym
             -> MuxFn (Pred sym) (SymGlobalState sym)
globalMuxFn sym iteFns c (GlobalState dx x refs_x) (GlobalState dy y refs_y)
 | dx > 0 && dx == dy = do
      GlobalState (dx - 1) <$> MapF.mergeWithKeyM muxEntry checkNullMap checkNullMap x y
                           <*> MapF.mergeWithKeyM muxRef refLeft refRight refs_x refs_y

    where muxEntry :: GlobalVar tp
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

          refLeft :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
          refLeft m = traverseF f m
           where f :: RefCellContents sym tp -> IO (RefCellContents sym tp)
                 f (RefCellContents p z) =
                      do p' <- andPred sym c p
                         return $ RefCellContents p' z

          refRight :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
          refRight m = do cnot <- notPred sym c; traverseF (f cnot) m
           where f :: Pred sym -> RefCellContents sym tp -> IO (RefCellContents sym tp)
                 f cnot (RefCellContents p z) =
                      do p' <- andPred sym cnot p
                         return $ RefCellContents p' z

          checkNullMap :: MapF.MapF GlobalVar (GlobalEntry sym)
                       -> IO (MapF.MapF GlobalVar (GlobalEntry sym))
          checkNullMap m
            | MapF.null m = return m
            | otherwise =
              panic "GlobalState.globalMuxFn"
                      [ "Different global variables in each branch." ]

globalMuxFn sym _ _ (GlobalState dx _ _) (GlobalState dy _ _) =
  do loc <- getCurrentProgramLoc sym
     panic "GlobalState.globalMuxFn"
           [ "Attempting to merge global states of incorrect branch depths:"
           , " *** Depth 1:  " ++ show dx
           , " *** Depth 2:  " ++ show dy
           , " *** Location: " ++ show (plSourceLoc loc)
           ]
