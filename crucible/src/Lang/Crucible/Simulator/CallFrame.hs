-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.CallFrame
-- Description      : Data structure for call frames in the simulator
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Call frames are used to record information about suspended stack
-- frames when functions are called.
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.CallFrame
  ( -- * CrucibleBranchTarget
    CrucibleBranchTarget(..)
  , ppBranchTarget
    -- * Call frame
  , CallFrame(..)
  , mkCallFrame
  , mkBlockFrame
  , framePostdomMap
  , frameBlockMap
  , frameHandle
  , frameReturnType
  , frameBlockID
  , frameRegs
  , frameStmts
  , framePostdom
  , frameProgramLoc
  , setFrameBlock
  , setFrameBreakpointPostdomInfo
  , extendFrame
  , updateFrame
  , mergeCallFrame
    -- * SomeHandle
  , SomeHandle(..)
    -- * Simulator frames
  , SimFrame(..)
  , CrucibleLang
  , OverrideLang
  , FrameRetType
  , OverrideFrame(..)
  , override
  , overrideHandle
  , overrideRegMap
  , overrideSimFrame
  , crucibleSimFrame
  , fromCallFrame
  , fromReturnFrame
  , frameFunctionName
  ) where

import           Control.Lens
import           Data.Kind
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface ( Pred )

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.ProgramLoc ( ProgramLoc )
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap


------------------------------------------------------------------------
-- CrucibleBranchTarget

-- | A 'CrucibleBranchTarget' identifies a program location that is a
--   potential join point.  Each label is a merge point, and there is
--   an additional implicit join point at function returns.
data CrucibleBranchTarget f (args :: Maybe (Ctx CrucibleType)) where
   BlockTarget  ::
     !(BlockID blocks args) ->
     CrucibleBranchTarget (CrucibleLang blocks r) ('Just args)
   ReturnTarget ::
     CrucibleBranchTarget f 'Nothing

instance TestEquality (CrucibleBranchTarget f) where
  testEquality (BlockTarget x) (BlockTarget y) =
    case testEquality x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  testEquality ReturnTarget ReturnTarget  = Just Refl
  testEquality _ _ = Nothing

ppBranchTarget :: CrucibleBranchTarget f args -> String
ppBranchTarget (BlockTarget b) = "merge: " ++ show b
ppBranchTarget ReturnTarget = "return"


------------------------------------------------------------------------
-- CallFrame

-- | A call frame for a crucible block.
data CallFrame sym ext blocks ret args
   = forall initialArgs.
     CallFrame
     { _frameCFG        :: CFG ext blocks initialArgs ret
       -- ^ Handle to control flow graph for the current frame.
     , _framePostdomMap :: !(CFGPostdom blocks)
       -- ^ Post-dominator map for control flow graph associated with this
       -- function.
     , _frameBlockID    :: !(Some (BlockID blocks))
     , _frameRegs      :: !(RegMap sym args)
     , _frameStmts     :: !(StmtSeq ext blocks ret args)
     , _framePostdom   :: !(Some (CrucibleBranchTarget (CrucibleLang blocks ret)))
     }

frameBlockMap :: CallFrame sym ext blocks ret ctx -> BlockMap ext blocks ret
frameBlockMap CallFrame { _frameCFG = g } = cfgBlockMap g

frameHandle :: CallFrame sym ext blocks ret ctx -> SomeHandle
frameHandle CallFrame { _frameCFG = g } = SomeHandle (cfgHandle g)

frameReturnType :: CallFrame sym ext blocks ret ctx -> TypeRepr ret
frameReturnType CallFrame { _frameCFG = g } = cfgReturnType g

framePostdomMap :: Simple Lens (CallFrame sym ext blocks ret ctx) (CFGPostdom blocks)
framePostdomMap = lens _framePostdomMap (\s x -> s{ _framePostdomMap = x })

frameBlockID :: Simple Lens (CallFrame sym ext blocks ret ctx) (Some (BlockID blocks))
frameBlockID = lens _frameBlockID (\s v -> s { _frameBlockID = v })

-- | List of statements to execute next.
frameStmts :: Simple Lens (CallFrame sym ext blocks ret ctx) (StmtSeq ext blocks ret ctx)
frameStmts = lens _frameStmts (\s v -> s { _frameStmts = v })
{-# INLINE frameStmts #-}

frameRegs :: Simple Lens (CallFrame sym ext blocks ret args) (RegMap sym args)
frameRegs = lens _frameRegs (\s v -> s { _frameRegs = v })

-- | List of statements to execute next.
framePostdom :: Simple Lens (CallFrame sym ext blocks ret ctx) (Some (CrucibleBranchTarget (CrucibleLang blocks ret)))
framePostdom = lens _framePostdom (\s v -> s { _framePostdom = v })

-- | Create a new call frame.
mkCallFrame :: CFG ext blocks init ret
               -- ^ Control flow graph
            -> CFGPostdom blocks
               -- ^ Post dominator information.
            -> RegMap sym init
               -- ^ Initial arguments
            -> CallFrame sym ext blocks ret init
mkCallFrame g = mkBlockFrame g (cfgEntryBlockID g)

-- | Create a new call frame.
mkBlockFrame ::
  CFG ext blocks init ret {- ^  Control flow graph -} ->
  BlockID blocks args {- ^ Entry point -} ->
  CFGPostdom blocks {- ^ Post dominator information -} ->
  RegMap sym args {- ^ Initial arguments -} ->
  CallFrame sym ext blocks ret args
mkBlockFrame g bid@(BlockID block_id) pdInfo args = do
  let b = cfgBlockMap g Ctx.! block_id
  let pds = getConst $ pdInfo Ctx.! block_id
  CallFrame { _frameCFG   = g
            , _framePostdomMap = pdInfo
            , _frameBlockID  = Some bid
            , _frameRegs     = args
            , _frameStmts    = b^.blockStmts
            , _framePostdom  = mkFramePostdom pds
            }

mkFramePostdom :: [Some (BlockID blocks)] -> Some (CrucibleBranchTarget (CrucibleLang blocks ret))
mkFramePostdom [] = Some ReturnTarget
mkFramePostdom (Some i:_) = Some (BlockTarget i)


-- | Return program location associated with frame.
frameProgramLoc :: CallFrame sym ext blocks ret ctx -> ProgramLoc
frameProgramLoc cf = firstStmtLoc (cf^.frameStmts)

setFrameBlock :: BlockID blocks args
              -> RegMap sym args
              -> CallFrame sym ext blocks ret ctx
              -> CallFrame sym ext blocks ret args
setFrameBlock bid@(BlockID block_id) args f = f'
    where b = frameBlockMap f Ctx.! block_id
          pds = getConst $ (f^.framePostdomMap.ixF block_id)
          f' = f { _frameBlockID = Some bid
                 , _frameRegs =  args
                 , _frameStmts = b^.blockStmts
                 , _framePostdom = mkFramePostdom pds
                 }

setFrameBreakpointPostdomInfo ::
  [BreakpointName] ->
  CallFrame sym ext blocks ret ctx ->
  CallFrame sym ext blocks ret ctx
setFrameBreakpointPostdomInfo breakpoints f = case f of
  CallFrame{ _frameCFG = g, _frameBlockID = Some (BlockID block_id) } -> do
    let pdInfo = breakpointPostdomInfo g breakpoints
    f { _framePostdomMap = pdInfo
      , _framePostdom  = mkFramePostdom (getConst $ pdInfo Ctx.! block_id)
      }

updateFrame :: RegMap sym ctx'
            -> BlockID blocks ctx
            -> StmtSeq ext blocks ret ctx'
            -> CallFrame sym ext blocks ret ctx
            -> CallFrame sym ext blocks ret ctx'
updateFrame r b s f = f { _frameBlockID = Some  b, _frameRegs = r, _frameStmts = s }

-- | Extend frame with new register.
extendFrame :: TypeRepr tp
            -> RegValue sym tp
            -> StmtSeq ext blocks ret (ctx ::> tp)
            -> CallFrame sym ext blocks ret ctx
            -> CallFrame sym ext blocks ret (ctx ::> tp)
extendFrame tp v s f = f { _frameRegs = assignReg tp v (_frameRegs f)
                         , _frameStmts = s
                         }

mergeCallFrame :: IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> MuxFn (Pred sym) (CallFrame sym ext blocks ret args)
mergeCallFrame s iteFns p xcf ycf = do
  r <- mergeRegs s iteFns p (_frameRegs xcf) (_frameRegs ycf)
  return $ xcf { _frameRegs = r }


------------------------------------------------------------------------
-- CrucibleLang

-- | Nominal type for identifying override frames.
data CrucibleLang (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType)

------------------------------------------------------------------------
-- OverrideLang

-- | Nominal type for identifying override frames.
data OverrideLang (ret :: CrucibleType)

------------------------------------------------------------------------
-- OverrideFrame

-- | Frame in call to override.
data OverrideFrame sym (ret :: CrucibleType) args
   = OverrideFrame { _override :: !FunctionName
                   , _overrideHandle :: !SomeHandle
                   , _overrideRegMap :: !(RegMap sym args)
                     -- ^ Arguments to override.
                   }

override :: Simple Lens (OverrideFrame sym ret args) FunctionName
override = lens _override (\o x -> o{ _override = x })

overrideHandle :: Simple Lens (OverrideFrame sym ret args) SomeHandle
overrideHandle = lens _overrideHandle (\o x -> o { _overrideHandle = x })

overrideRegMap :: Lens (OverrideFrame sym ret args) (OverrideFrame sym ret args')
                       (RegMap sym args) (RegMap sym args')
overrideRegMap = lens _overrideRegMap (\o x -> o{ _overrideRegMap = x })

------------------------------------------------------------------------
-- SimFrame

{- An alternate idea we could try to save a few indirections...
type family SimFrame sym ext l args :: * where
  SimFrame sym ext (OverrideLang ret)        ('Just args) = OverrideFrame sym ret args
  SimFrame sym ext (CrucibleLang blocks ret) ('Just args) = CallFrame sym ext blocks ret args
  SimFrame sym ext (CrucibleLang blocks ret) ('Nothing)   = RegEntry sym ret
-}

type family FrameRetType (f :: Type) :: CrucibleType where
  FrameRetType (CrucibleLang b r) = r
  FrameRetType (OverrideLang r) = r

data SimFrame sym ext l (args :: Maybe (Ctx CrucibleType)) where
  -- | Custom code to execute, typically for "overrides"
  OF :: !(OverrideFrame sym ret args)
     -> SimFrame sym ext (OverrideLang ret) ('Just args)

  -- | We are executing some Crucible instructions
  MF :: !(CallFrame sym ext blocks ret args)
     -> SimFrame sym ext (CrucibleLang blocks ret) ('Just args)

  -- | We should return this value.
  RF :: !FunctionName {- Function we are returning from -}
     -> !(RegEntry sym (FrameRetType f))
     -> SimFrame sym ext f 'Nothing


overrideSimFrame :: Lens (SimFrame sym ext (OverrideLang r) ('Just args))
                         (SimFrame sym ext (OverrideLang r') ('Just args'))
                         (OverrideFrame sym r args)
                         (OverrideFrame sym r' args')
overrideSimFrame f (OF g) = OF <$> f g

crucibleSimFrame :: Lens (SimFrame sym ext (CrucibleLang blocks r) ('Just args))
                         (SimFrame sym ext (CrucibleLang blocks' r') ('Just args'))
                         (CallFrame sym ext blocks r args)
                         (CallFrame sym ext blocks' r' args')
crucibleSimFrame f (MF c) = MF <$> f c


fromCallFrame :: SimFrame sym ext (CrucibleLang b r) ('Just a)
              -> CallFrame sym ext b r a
fromCallFrame (MF x) = x

fromReturnFrame :: SimFrame sym ext f 'Nothing
                -> RegEntry sym (FrameRetType f)
fromReturnFrame (RF _ x) = x

frameFunctionName :: Getter (SimFrame sym ext f a) FunctionName
frameFunctionName = to $ \case
  OF f -> f^.override
  MF f -> case frameHandle f of SomeHandle h -> handleName h
  RF n _ -> n
