{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.StateCtx
-- Description      : Defines the shape of the Sally state type, as a parameterized context
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.StateCtx
  ( StateCtx,
    flattenCtx,
    globalIndexToStateIndex,
    makeCurrentBlockIndex,
    makeHasReturnedIndex,
  )
where

import qualified Data.Parameterized.Context as Ctx
import Lang.Crucible.ModelChecker.AsBaseType
import Lang.Crucible.Types
import Prelude hiding (init)

flattenCtx ::
  Ctx.Assignment (Ctx.Assignment f) blocks ->
  Ctx.Assignment f (CtxFlatten blocks)
flattenCtx ctxs =
  case Ctx.viewAssign ctxs of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctxs' ctx -> flattenCtx ctxs' Ctx.<++> ctx

-- using prefix <+> only because of a hlint bug
type BlocksGlobInitCtx blocks globCtx init =
  (Ctx.<+>)
    (AsBaseTypes (CtxFlatten blocks))
    ((Ctx.<+>) (AsBaseTypes globCtx) (AsBaseTypes init))

type StateCtx blocks globCtx init =
  BlocksGlobInitCtx blocks globCtx init
    Ctx.::> BaseBoolType
    Ctx.::> BaseIntegerType

blocksSize ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size (CtxFlatten blocks)
blocksSize blocks =
  case Ctx.viewAssign blocks of
    Ctx.AssignEmpty -> Ctx.zeroSize
    Ctx.AssignExtend rest size -> Ctx.addSize (blocksSize rest) size

blocksGlobInitCtxSize ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size globCtx ->
  Ctx.Size init ->
  Ctx.Size (BlocksGlobInitCtx blocks globCtx init)
blocksGlobInitCtxSize blocks globCtx init =
  asBaseTypesSize (blocksSize blocks) `Ctx.addSize` (asBaseTypesSize globCtx `Ctx.addSize` asBaseTypesSize init)

makeHasReturnedIndex ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size globCtx ->
  Ctx.Size init ->
  Ctx.Index (StateCtx blocks globCtx init) BaseBoolType
makeHasReturnedIndex blocks globCtx init =
  Ctx.skipIndex (Ctx.lastIndex (Ctx.incSize (blocksGlobInitCtxSize blocks globCtx init)))

makeCurrentBlockIndex ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size globCtx ->
  Ctx.Size init ->
  Ctx.Index (StateCtx blocks globCtx init) BaseIntegerType
makeCurrentBlockIndex blocks globCtx init =
  Ctx.lastIndex (Ctx.incSize (Ctx.incSize (blocksGlobInitCtxSize blocks globCtx init)))

leftIndex ::
  Ctx.Size r ->
  Ctx.Index l tp ->
  Ctx.Index ((Ctx.<+>) l r) tp
leftIndex sr il =
  Ctx.extendIndex' (Ctx.appendDiff sr) il

rightIndex ::
  Ctx.Size l ->
  Ctx.Size r ->
  Ctx.Index r tp ->
  Ctx.Index ((Ctx.<+>) l r) tp
rightIndex sl sr ir =
  case Ctx.viewIndex sr ir of
    Ctx.IndexViewInit i -> Ctx.skipIndex (rightIndex sl (Ctx.decSize sr) i)
    Ctx.IndexViewLast s -> Ctx.lastIndex (Ctx.incSize (Ctx.addSize sl s))

flattenSize ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size (CtxFlatten blocks)
flattenSize a =
  case Ctx.viewAssign a of
    Ctx.AssignEmpty -> Ctx.zeroSize
    Ctx.AssignExtend b s -> Ctx.addSize (flattenSize b) s

globalIndexToStateIndex ::
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Size globCtx ->
  Ctx.Size init ->
  Ctx.Index globCtx tp ->
  Ctx.Index (StateCtx blocks globCtx init) (AsBaseType' tp)
globalIndexToStateIndex blocks globCtx init globIndex =
  let blocks' = asBaseTypesSize (flattenSize blocks)
   in let globCtx' = asBaseTypesSize globCtx
       in let init' = asBaseTypesSize init
           in let globIndex' = asBaseTypesIndex globCtx globIndex
               in Ctx.skipIndex (Ctx.skipIndex (rightIndex blocks' (Ctx.addSize globCtx' init') (leftIndex init' globIndex')))
