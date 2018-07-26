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
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.CallFrame
  ( -- * CrucibleBranchTarget
    CrucibleBranchTarget(..)
  , ppBranchTarget
    -- * Call frame
  , CallFrame
  , mkCallFrame
  , frameBlockMap
  , framePostdomMap
  , frameHandle
  , frameReturnType
  , frameRegs
  , frameStmts
  , framePostdom
  , frameProgramLoc
  , setFrameBlock
  , extendFrame
  , updateFrame
  , mergeCallFrame
    -- * SomeHandle
  , SomeHandle(..)
  ) where

import           Control.Lens
import qualified Data.Parameterized.Context as Ctx

import           What4.ProgramLoc ( ProgramLoc )
import           What4.Interface ( Pred )

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Backend


------------------------------------------------------------------------
-- CrucibleBranchTarget

-- | A 'CrucibleBranchTarget' identifies a program location that is a
--   potential join point.  Each label is a merge point, and there is
--   an additional implicit join point at function returns.
data CrucibleBranchTarget blocks (args :: Maybe (Ctx CrucibleType)) where
   BlockTarget  ::
     !(BlockID blocks args) ->
     CrucibleBranchTarget blocks ('Just args)
   ReturnTarget ::
     CrucibleBranchTarget blocks 'Nothing

instance TestEquality (CrucibleBranchTarget blocks) where
  testEquality (BlockTarget x) (BlockTarget y) =
    case testEquality x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  testEquality (ReturnTarget ) (ReturnTarget ) = Just Refl
  testEquality _ _ = Nothing

ppBranchTarget :: CrucibleBranchTarget blocks args -> String
ppBranchTarget (BlockTarget b) = "merge: " ++ show b
ppBranchTarget ReturnTarget = "return"


------------------------------------------------------------------------
-- CallFrame

-- | A call frame for a crucible block.
data CallFrame sym ext blocks ret args
   = CallFrame
     { frameHandle     :: SomeHandle
       -- ^ Handle to control flow graph for the current frame.
     , frameBlockMap   :: !(BlockMap ext blocks ret)
       -- ^ Block map for current control flow graph.
     , framePostdomMap :: !(CFGPostdom blocks)
       -- ^ Post-dominator map for control flow graph associated with this
       -- function.
     , frameReturnType :: !(TypeRepr ret)
     , _frameRegs      :: !(RegMap sym args)
     , _frameStmts     :: !(StmtSeq ext blocks ret args)
     , _framePostdom   :: !(Some (CrucibleBranchTarget blocks))
     }

-- | List of statements to execute next.
frameStmts :: Simple Lens (CallFrame sym ext blocks ret ctx) (StmtSeq ext blocks ret ctx)
frameStmts = lens _frameStmts (\s v -> s { _frameStmts = v })
{-# INLINE frameStmts #-}

frameRegs :: Simple Lens (CallFrame sym ext blocks ret args) (RegMap sym args)
frameRegs = lens _frameRegs (\s v -> s { _frameRegs = v })

-- | List of statements to execute next.
framePostdom :: Simple Lens (CallFrame sym ext blocks ret ctx) (Some (CrucibleBranchTarget blocks))
framePostdom = lens _framePostdom (\s v -> s { _framePostdom = v })

-- | Create a new call frame.
mkCallFrame :: CFG ext blocks init ret
               -- ^ Control flow graph
            -> CFGPostdom blocks
               -- ^ Post dominator information.
            -> RegMap sym init
               -- ^ Initial arguments
            -> CallFrame sym ext blocks ret init
mkCallFrame g pdInfo args = do
  let BlockID block_id = cfgEntryBlockID g
  let b = cfgBlockMap g Ctx.! block_id
  let pds = getConst $ pdInfo Ctx.! block_id
  CallFrame { frameHandle   = SomeHandle (cfgHandle g)
            , frameBlockMap = cfgBlockMap g
            , framePostdomMap = pdInfo
            , frameReturnType = cfgReturnType g
            , _frameRegs     = args
            , _frameStmts   = b^.blockStmts
            , _framePostdom = mkFramePostdom pds
            }

mkFramePostdom :: [Some (BlockID blocks)] -> Some (CrucibleBranchTarget blocks)
mkFramePostdom [] = Some ReturnTarget
mkFramePostdom (Some i:_) = Some (BlockTarget i)


-- | Return program location associated with frame.
frameProgramLoc :: CallFrame sym ext blocks ret ctx -> ProgramLoc
frameProgramLoc cf = firstStmtLoc (cf^.frameStmts)

setFrameBlock :: BlockID blocks args
              -> RegMap sym args
              -> CallFrame sym ext blocks ret ctx
              -> CallFrame sym ext blocks ret args
setFrameBlock (BlockID block_id) args f = f'
    where b = frameBlockMap f Ctx.! block_id
          pds = getConst $ framePostdomMap f Ctx.! block_id
          f' = f { _frameRegs =  args
                 , _frameStmts = b^.blockStmts
                 , _framePostdom = mkFramePostdom pds
                 }

updateFrame :: RegMap sym ctx'
            -> StmtSeq ext blocks ret ctx'
            -> CallFrame sym ext blocks ret ctx
            -> CallFrame sym ext blocks ret ctx'
updateFrame r s f = f { _frameRegs = r, _frameStmts = s }

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
