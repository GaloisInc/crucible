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
  ( -- * Call frame
    CallFrame
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
  , mergeCallFrame
    -- * SomeHandle
  , SomeHandle(..)
  ) where

import           Control.Lens
import           Data.Hashable
import           Data.Maybe
import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc ( ProgramLoc )
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Interface ( Pred, IsExprBuilder )

------------------------------------------------------------------------
-- SomeHandle

-- | A function handle is a reference to a function in a given
-- run of the simulator.  It has a set of expected arguments and return type.
data SomeHandle where
   SomeHandle :: !(FnHandle args ret) -> SomeHandle

instance Eq SomeHandle where
  SomeHandle x == SomeHandle y = isJust (testEquality (handleID x) (handleID y))

instance Hashable SomeHandle where
  hashWithSalt s (SomeHandle x) = hashWithSalt s (handleID x)

instance Show SomeHandle where
  show (SomeHandle h) = show (handleName h)


------------------------------------------------------------------------
-- CallFrame

-- | A call frame for a crucible block.
data CallFrame sym ext blocks ret args
   = CallFrame { frameHandle     :: SomeHandle
                 -- ^ Handle to control flow graph for the current frame.
               , frameBlockMap   :: !(BlockMap ext blocks ret)
                 -- ^ Block map for current control flow graph.
               , framePostdomMap :: !(CFGPostdom blocks)
                 -- ^ Post-dominator map for control flow graph associated with this
                 -- function.
               , frameReturnType :: !(TypeRepr ret)
               , _frameRegs      :: !(RegMap sym args)
               , _frameStmts     :: !(StmtSeq ext blocks ret args)
               , _framePostdom   :: !(Maybe (Some (BlockID blocks)))
               }

-- | List of statements to execute next.
frameStmts :: Simple Lens (CallFrame sym ext blocks ret ctx) (StmtSeq ext blocks ret ctx)
frameStmts = lens _frameStmts (\s v -> s { _frameStmts = v })
{-# INLINE frameStmts #-}

frameRegs :: Simple Lens (CallFrame sym ext blocks ret args) (RegMap sym args)
frameRegs = lens _frameRegs (\s v -> s { _frameRegs = v })

-- | List of statements to execute next.
framePostdom :: Simple Lens (CallFrame sym ext blocks ret ctx) (Maybe (Some (BlockID blocks)))
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
  let pd = getConst $ pdInfo Ctx.! block_id
  CallFrame { frameHandle   = SomeHandle (cfgHandle g)
            , frameBlockMap = cfgBlockMap g
            , framePostdomMap = pdInfo
            , frameReturnType = cfgReturnType g
            , _frameRegs     = args
            , _frameStmts   = b^.blockStmts
            , _framePostdom = listToMaybe pd
            }

-- | Return program location associated with frame.
frameProgramLoc :: CallFrame sym ext blocks ret ctx -> ProgramLoc
frameProgramLoc cf = firstStmtLoc (cf^.frameStmts)

setFrameBlock :: BlockID blocks args
              -> RegMap sym args
              -> CallFrame sym ext blocks ret ctx
              -> CallFrame sym ext blocks ret args
setFrameBlock (BlockID block_id) args f = f'
    where b = frameBlockMap f Ctx.! block_id
          Const pd = framePostdomMap f Ctx.! block_id
          f' = f { _frameRegs =  args
                 , _frameStmts = b^.blockStmts
                 , _framePostdom  = listToMaybe pd
                 }

-- | Extend frame with new register.
extendFrame :: TypeRepr tp
            -> RegValue sym tp
            -> StmtSeq ext blocks ret (ctx ::> tp)
            -> CallFrame sym ext blocks ret ctx
            -> CallFrame sym ext blocks ret (ctx ::> tp)
extendFrame tp v s f = f { _frameRegs = assignReg tp v (_frameRegs f)
                         , _frameStmts = s
                         }

mergeCallFrame :: IsExprBuilder sym
               => sym
               -> IntrinsicTypes sym
               -> MuxFn (Pred sym) (CallFrame sym ext blocks ret args)
mergeCallFrame s iteFns p xcf ycf = do
  r <- mergeRegs s iteFns p (_frameRegs xcf) (_frameRegs ycf)
  return $ xcf { _frameRegs = r }
