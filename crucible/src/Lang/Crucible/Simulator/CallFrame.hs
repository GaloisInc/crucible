-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.CallFrame
-- Description      : Data structure for call frames in the simulator
-- Copyright        : (c) Galois, Inc 2014
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

import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc ( ProgramLoc )
import           Lang.Crucible.Simulator.ExecutionTree ( MuxFn )
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Interface ( Pred, IsSymInterface )

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

-- | Call frame for simulator.
data CallFrame sym blocks ret args
   = CallFrame { frameHandle :: SomeHandle
               , frameBlockMap :: !(BlockMap blocks ret)
               , framePostdomMap :: !(CFGPostdom blocks)
               , frameReturnType :: !(TypeRepr ret)
               , frameRegs     :: !(RegMap sym args)
               , _frameStmts   :: !(StmtSeq blocks ret args)
               , _framePostdom :: !(Maybe (Some (BlockID blocks)))
               }

-- | List of statements to execute next.
frameStmts :: Simple Lens (CallFrame sym blocks ret ctx) (StmtSeq blocks ret ctx)
frameStmts = lens _frameStmts (\s v -> s { _frameStmts = v })
{-# INLINE frameStmts #-}

-- | List of statements to execute next.
framePostdom :: Simple Lens (CallFrame sym blocks ret ctx) (Maybe (Some (BlockID blocks)))
framePostdom = lens _framePostdom (\s v -> s { _framePostdom = v })

-- | Create a new call frame.
mkCallFrame :: CFG blocks init ret
               -- ^ Control flow graph
            -> CFGPostdom blocks
               -- ^ Post dominator information.
            -> RegMap sym init
               -- ^ Initial arguments
            -> CallFrame sym blocks ret init
mkCallFrame g pdInfo args = do
  let BlockID block_id = cfgEntryBlockID g
  let b = cfgBlockMap g Ctx.! block_id
  let ConstK pd = pdInfo Ctx.! block_id
  CallFrame { frameHandle   = SomeHandle (cfgHandle g)
            , frameBlockMap = cfgBlockMap g
            , framePostdomMap = pdInfo
            , frameReturnType = cfgReturnType g
            , frameRegs     = args
            , _frameStmts   = b^.blockStmts
            , _framePostdom = listToMaybe pd
            }

-- | Return program location associated with frame.
frameProgramLoc :: CallFrame sym blocks ret ctx -> ProgramLoc
frameProgramLoc cf = firstStmtLoc (cf^.frameStmts)

setFrameBlock :: BlockID blocks args
              -> RegMap sym args
              -> CallFrame sym blocks ret ctx
              -> CallFrame sym blocks ret args
setFrameBlock (BlockID block_id) args f = f'
    where b = frameBlockMap f Ctx.! block_id
          ConstK pd = framePostdomMap f Ctx.! block_id
          f' = f { frameRegs =  args
                 , _frameStmts = b^.blockStmts
                 , _framePostdom  = listToMaybe pd
                 }

-- | Extend frame with new register.
extendFrame :: TypeRepr tp
            -> RegValue sym tp
            -> StmtSeq blocks ret (ctx ::> tp)
            -> CallFrame sym blocks ret ctx
            -> CallFrame sym blocks ret (ctx ::> tp)
extendFrame tp v s f = f { frameRegs = assignReg tp v (frameRegs f)
                         , _frameStmts = s
                         }

mergeCallFrame :: IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> MuxFn (Pred sym) (CallFrame sym blocks ret args)
mergeCallFrame s iteFns p xcf ycf = do
  r <- mergeRegs s iteFns p (frameRegs xcf) (frameRegs ycf)
  return $ xcf { frameRegs = r }
