------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.SSAConversion
-- Description      : Allows converting from RTL to SSA representation.
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides a function for converting from the RTL to SSA
-- Crucible representation.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.CFG.SSAConversion
  ( toSSA
  ) where

import           Control.Exception (assert)
import           Control.Lens ((&))
import           Control.Monad.State.Strict
import           Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import qualified Data.Foldable as Fold
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (isJust, fromMaybe)
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Type.Equality
import qualified Text.PrettyPrint.ANSI.Leijen as Pretty

import           Lang.Crucible.Analysis.Reachable
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName (FunctionName)
import           Lang.Crucible.ProgramLoc


#ifdef UNSAFE_OPS
-- We deliberately import Context.Unsafe as it is the only one that supports
-- the unsafe coerces between an index and its extension.
import           Data.Parameterized.Context.Unsafe as Ctx (Assignment)
import           Data.Parameterized.Context as Ctx hiding (Assignment)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Unsafe.Coerce
#else
import           Data.Parameterized.Context as Ctx
#endif

------------------------------------------------------------------------
-- Utilities

-- | Given a list of pairs returns a map that maps each value appearing
-- in the first element to the second element in the set of pairs
-- containing it.
nextSetMap :: (Ord x, Ord y) => [(x,y)] -> Map x (Set y)
nextSetMap l = execState (traverse go l) Map.empty
  where go (x,y) = modify $ Map.insertWith Set.union x (Set.singleton y)

------------------------------------------------------------------------
-- Input

-- | An input is a wrapper around a value that also knows if the
-- value was obtained as the output from a previous block.
--
-- * The first argument is true if the value was created from a previous block
-- * The second is the value itself.
data Input s
   = Input { inputGeneratedPrev :: !Bool
             -- ^ Stores true if the value was created from a previous block.
           , inputValue :: !(Some (Value s))
           }

instance Show (Input s) where
  showsPrec p r = showsPrec p (inputValue r)

instance Eq (Input s) where
  x == y = inputValue x == inputValue y

isOutputFromBlock :: BlockID s -> Some (Value s) -> Bool
isOutputFromBlock (LambdaID l) (Some (AtomValue a))
  | LambdaArg l' <- atomSource a = isJust (testEquality l l')
isOutputFromBlock _ _ = False

mkInput :: BlockID s -> Some (Value s) -> Input s
mkInput b v = Input { inputGeneratedPrev = isOutputFromBlock b v
                    , inputValue = v
                    }

instance Ord (Input s) where
  -- LambdaArg introduced in this block should be last.
  compare x y =
    case (inputGeneratedPrev x, inputGeneratedPrev y) of
      (True,  True ) -> assert (inputValue x == inputValue y) EQ
      (True,  False) -> GT
      (False, True ) -> LT
      (False, False) -> compare (inputValue x) (inputValue y)

------------------------------------------------------------------------
-- BlockInput

data BlockInput ext s blocks ret args
  = BInput { binputID         :: !(C.BlockID blocks args)
             -- | Arguments expected by block.
           , binputArgs       :: !(Assignment (Value s) args)
           , binputStmts      :: !(Seq (Posd (Stmt ext s)))
           , binputTerm       :: !(Posd (ExtendedTermStmt s blocks ret))
           }

-- The Breakpoint non-terminator statement becomes a jump during SSA conversion.
-- This datatype temporarily adds breakpoint as a terminator statement.
data ExtendedTermStmt s blocks ret where
  BaseTermStmt :: TermStmt s ret -> ExtendedTermStmt s blocks ret
  BreakStmt :: JumpInfo s blocks -> ExtendedTermStmt s blocks ret

type BlockInputAssignment ext s blocks ret
   = Assignment (BlockInput ext s blocks ret)

extBlockInputAssignment ::
  BlockInputAssignment ext s blocks ret a ->
  BlockInputAssignment ext s (blocks ::> tp) ret a
extBlockInput ::
  BlockInput ext s blocks ret args ->
  BlockInput ext s (blocks ::> tp) ret arg
extBreakpoints ::
  Bimap BreakpointName (Some (C.BlockID blocks)) ->
  Bimap BreakpointName (Some (C.BlockID (blocks ::> tp)))
#ifdef UNSAFE_OPS
extBlockInputAssignment = unsafeCoerce

extBlockInput = unsafeCoerce

extBreakpoints = unsafeCoerce
#else
extBlockInputAssignment = fmapFC extBlockInput

extBlockInput bi = bi { binputID = C.extendBlockID (binputID bi) }

extBreakpoints = Bimap.mapR (mapSome C.extendBlockID)
#endif

------------------------------------------------------------------------
-- inferRegAssignment

inferRegAssignment :: Set (Input s)
                   -> Some (Assignment (Value s))
inferRegAssignment s = Ctx.fromList (inputValue <$> Set.toList s)

------------------------------------------------------------------------
-- JumpInfo

data JumpInfo s blocks where
  JumpInfo :: C.BlockID blocks types
           -> C.CtxRepr types
           -> Assignment (Value s) types
           -> JumpInfo s blocks


emptyJumpInfoMap :: JumpInfoMap s blocks
lookupJumpInfo :: Label s -> JumpInfoMap s blocks -> Maybe (JumpInfo s blocks)
insertJumpInfo :: Label s -> JumpInfo s blocks -> JumpInfoMap s blocks -> JumpInfoMap s blocks

#ifdef UNSAFE_OPS
type JumpInfoMap s blocks = Map (Label s) (JumpInfo s blocks)

extJumpInfoMap :: JumpInfoMap s blocks -> JumpInfoMap s (blocks ::> args)
extJumpInfoMap = unsafeCoerce


emptyJumpInfoMap = Map.empty
lookupJumpInfo = Map.lookup
insertJumpInfo = Map.insert

#else
data JumpInfoMap s blocks
  = forall blocks'.
     JumpInfoMap
     { _jimDiff :: !(Diff blocks' blocks)
     , _jimMap  :: !(Map (Label s) (JumpInfo s blocks'))
     , _jimThunk :: Map (Label s) (JumpInfo s blocks) -- NB! don't make this strict
     }

emptyJumpInfoMap = JumpInfoMap noDiff Map.empty Map.empty

extJumpInfoMap :: JumpInfoMap s blocks -> JumpInfoMap s (blocks ::> args)
extJumpInfoMap (JumpInfoMap diff mp _) =
  let diff' = extendRight diff
   in JumpInfoMap diff' mp (fmap (extJumpInfo diff') mp)

lookupJumpInfo l (JumpInfoMap diff mp _) = fmap (extJumpInfo diff) (Map.lookup l mp)
--lookupJumpInfo l mp = Map.lookup l (jimThunk mp)

insertJumpInfo l ji (JumpInfoMap _ _ thk) =
    let mp = Map.insert l ji thk
     in JumpInfoMap noDiff mp mp

-- | Extend jump target
extJumpInfo :: Diff blocks' blocks -> JumpInfo s blocks' -> JumpInfo s blocks
extJumpInfo diff (JumpInfo b typs a) = JumpInfo (C.extendBlockID' diff b) typs a
#endif


------------------------------------------------------------------------
-- SwitchInfo

data SwitchInfo s blocks tp where
  SwitchInfo :: C.BlockID blocks (args ::> tp)
             -> C.CtxRepr args
             -> Assignment (Value s) args
             -> SwitchInfo s blocks tp

emptySwitchInfoMap :: SwitchInfoMap s blocks

insertSwitchInfo   :: LambdaLabel s tp
                   -> SwitchInfo s blocks tp
                   -> SwitchInfoMap s blocks
                   -> SwitchInfoMap s blocks
lookupSwitchInfo   :: LambdaLabel s tp -> SwitchInfoMap s blocks -> Maybe (SwitchInfo s blocks tp)

#ifdef UNSAFE_OPS
{-
instance CoercibleF (SwitchInfo s blocks) where
  coerceF x = Data.Coerce.coerce x
-}

newtype SwitchInfoMap s blocks = SwitchInfoMap (MapF (LambdaLabel s) (SwitchInfo s blocks))

emptySwitchInfoMap = SwitchInfoMap MapF.empty

extSwitchInfoMap   :: SwitchInfoMap s blocks
                   -> SwitchInfoMap s (blocks ::> args)
extSwitchInfoMap = unsafeCoerce

insertSwitchInfo l si (SwitchInfoMap m) = SwitchInfoMap (MapF.insert l si m)
lookupSwitchInfo l (SwitchInfoMap m) = MapF.lookup l m

#else
newtype SwitchInfoMap s blocks =
  SwitchInfoMap (Map (Some (LambdaLabel s)) (SomeSwitchInfo s blocks))
data SomeSwitchInfo s blocks = forall tp. SomeSwitchInfo (C.TypeRepr tp) (SwitchInfo s blocks tp)

mapSomeSI :: (forall tp. SwitchInfo s b tp -> SwitchInfo s b' tp) -> SomeSwitchInfo s b -> SomeSwitchInfo s b'
mapSomeSI f (SomeSwitchInfo tp si) = SomeSwitchInfo tp (f si)

emptySwitchInfoMap = SwitchInfoMap Map.empty

extSwitchInfoMap   :: SwitchInfoMap s blocks
                   -> SwitchInfoMap s (blocks ::> args)
extSwitchInfoMap (SwitchInfoMap m) =
   SwitchInfoMap $ fmap (mapSomeSI extSwitchInfo) m

insertSwitchInfo l si (SwitchInfoMap m) =
   SwitchInfoMap $ Map.insert (Some l) (SomeSwitchInfo (typeOfAtom (lambdaAtom l)) si) m

lookupSwitchInfo l (SwitchInfoMap m) =
   case Map.lookup (Some l) m of
      Nothing -> Nothing
      Just (SomeSwitchInfo tr si) -> Just $
         case testEquality tr (typeOfAtom (lambdaAtom l)) of
             Just Refl -> si
             Nothing   -> error "Lang.Crucible.SSAConversion.lookupSwitchInfo: type mismatch!"

-- | Extend switch target
extSwitchInfo :: SwitchInfo s blocks tp -> SwitchInfo s (blocks::>args) tp
extSwitchInfo (SwitchInfo b typs a) = SwitchInfo (C.extendBlockID b) typs a
#endif

extBlockInfo ::
  BlockInfo ext s ret blocks ->
  BlockInput ext s (blocks ::> args) ret args ->
  BlockInfo ext s ret (blocks ::> args)
extBlockInfo bi binput = do
  let blocks' = extBlockInputAssignment $ biBlocks bi
  let jump_info' = extJumpInfoMap $ biJumpInfo bi
  let switch_info' = extSwitchInfoMap $ biSwitchInfo bi
  let breakpoints' = extBreakpoints $ biBreakpoints bi
  BI { biBlocks = extend blocks' binput
     , biJumpInfo = jump_info'
     , biSwitchInfo = switch_info'
     , biBreakpoints = breakpoints'
     }

------------------------------------------------------------------------
-- PredMap

newtype PredMap ext s ret = PredMap (Map (BlockID s) [Block ext s ret])

instance Show (PredMap ext s ret) where
  show (PredMap m) = show (fmap blockID <$> m)

-- | Return labels that may jump to given label.
getPredecessorLabels :: BlockID s -> PredMap ext s ret -> [Block ext s ret]
getPredecessorLabels l (PredMap m) = fromMaybe [] (Map.lookup l m)

-- | Maps each block to the set of blocks that jump to it.
blockPredMap :: [Block ext s ret] -> PredMap ext s ret
blockPredMap l = PredMap (Set.toList <$> nextSetMap pairs)
  where pairs = [ (n, b)
                | b <- l
                , n <- fromMaybe [] (termNextLabels (pos_val (blockTerm b)))
                ]

------------------------------------------------------------------------
-- BlockInputMap

type BlockInputMap s = Map (BlockID s) (Set (Input s))

-- | Return inputs expected by block.
inputsForBlock :: Block ext s ret
               -> Set (Input s)
inputsForBlock b = Set.map (mkInput (blockID b)) (blockKnownInputs b)

-- | Define map that maps labels to the set of registers they need.
initialInputMap :: [Block ext s ret] -> BlockInputMap s
initialInputMap blocks = Map.fromList $
  [ (blockID b, inputsForBlock b)
  | b <- blocks
  ]

-- | Return map that stores arguments needed by each block.
completeInputs :: forall ext s ret . [Block ext s ret] -> BlockInputMap s
completeInputs blocks = do
  let block_map =  Map.fromList [ (blockID b, b) | b <- blocks ]
  -- pred_map maps each label to its predecessors.
  let pred_map = blockPredMap blocks
  let go :: Set (BlockID s) -- Set of blocks to revisit.
         -> BlockInputMap s
            -- Map from block labels to arguments corresponding block needs at end.
         -> BlockInputMap s
      go s0 input_map =
        case Set.maxView s0 of
          Nothing -> input_map
          Just (next_label, rest_labels) -> do
            let Just inputs = Map.lookup next_label input_map

            let resolve_pred :: [Block ext s ret]
                             -> Set (BlockID s)
                             -> BlockInputMap s
                             -> BlockInputMap s
                resolve_pred [] s m = go s m
                resolve_pred (prev_block:r) s m = do
                  let prev_label = blockID prev_block
                  -- Get list of inputs already computed for block.
                  let Just prev_inputs = Map.lookup prev_label m
                  -- Compute the inputs needed at the start of prev_block
                  let new_inputs = Set.map (mkInput (blockID prev_block))
                                 $ (`Set.difference` blockAssignedValues prev_block)
                                 $ Set.map inputValue inputs
                  let all_inputs = Set.union prev_inputs new_inputs
                  if Set.isSubsetOf new_inputs prev_inputs then
                    resolve_pred r s m
                  else do
                    let m' = Map.insert prev_label all_inputs m
                    resolve_pred r (Set.insert prev_label s)  m'
            let prev_blocks = getPredecessorLabels next_label pred_map
            resolve_pred prev_blocks rest_labels input_map
  -- Compute arguments to each block.
  go (Map.keysSet block_map) (initialInputMap blocks)

------------------------------------------------------------------------
-- Infer information about SSA.

-- | Information that is statically inferred from the block structure.
data BlockInfo ext s ret blocks
   = BI { biBlocks      :: !(Assignment (BlockInput ext s blocks ret) blocks)
        , biJumpInfo    :: !(JumpInfoMap s blocks)
        , biSwitchInfo  :: !(SwitchInfoMap s blocks)
        , biBreakpoints :: !(Bimap BreakpointName (Some (C.BlockID blocks)))
        }

-- | This infers the information given a set of blocks.
inferBlockInfo :: forall ext s ret . [Block ext s ret] -> Some (BlockInfo ext s ret)
inferBlockInfo blocks = seq input_map $ resolveBlocks bi0 blocks
  where input_map = completeInputs blocks
        bi0 = BI { biBlocks = empty
                 , biJumpInfo = emptyJumpInfoMap
                 , biSwitchInfo = emptySwitchInfoMap
                 , biBreakpoints = Bimap.empty
                 }
        resolveBlocks ::
          BlockInfo ext s ret blocks ->
          [Block ext s ret] ->
          Some (BlockInfo ext s ret)
        resolveBlocks bi [] = Some bi
        resolveBlocks bi (b:rest) = do
          let sz = size (biBlocks bi)
          let untyped_id = blockID b
          let Just inputs = Map.lookup untyped_id input_map
          case inferRegAssignment inputs of
            Some ra -> do
              let crepr = fmapFC typeOfValue ra
              case untyped_id of
                LabelID l -> do
                  let block_id = C.BlockID (nextIndex sz)
                  let block_term = (blockTerm b) { pos_val = BaseTermStmt $ pos_val $ blockTerm b }
                  let binput = BInput { binputID = block_id
                                      , binputArgs    = ra
                                      , binputStmts   = blockStmts b
                                      , binputTerm    = block_term
                                      }
                  let bi' = extBlockInfo bi binput
                  let ji = JumpInfo block_id crepr ra
                  let bi'' = bi' { biJumpInfo = insertJumpInfo l ji (biJumpInfo bi') }
                  splitLastBlockInputOnBreakpoints bi'' rest
                LambdaID l -> do
                  let block_id = C.BlockID (nextIndex sz)
                  let lastArg = AtomValue (lambdaAtom l)
                  let block_term = (blockTerm b) { pos_val = BaseTermStmt $ pos_val $ blockTerm b }
                  let binput = BInput { binputID = block_id
                                      , binputArgs = ra :> lastArg
                                      , binputStmts = blockStmts b
                                      , binputTerm = block_term
                                      }
                  let bi' = extBlockInfo bi binput
                  let si = SwitchInfo block_id crepr ra
                  let bi'' = bi' { biSwitchInfo = insertSwitchInfo l si (biSwitchInfo bi') }
                  splitLastBlockInputOnBreakpoints bi'' rest
        splitLastBlockInputOnBreakpoints ::
          BlockInfo ext s ret blocks ->
          [Block ext s ret] ->
          Some (BlockInfo ext s ret)
        splitLastBlockInputOnBreakpoints bi rest
          | first_binputs :> last_binput <- biBlocks bi
          , (first_stmts, break_stmt Seq.:<| last_stmts) <-
              Seq.breakl isBreakpoint (binputStmts last_binput)
          , Breakpoint nm args <- pos_val break_stmt = do
            let block_id = C.BlockID $ nextIndex $ size $ biBlocks bi

            let first_binputs' = extBlockInputAssignment $ first_binputs

            let jump_info = JumpInfo block_id (fmapFC typeOfValue args) args
            let last_binput' = (extBlockInput last_binput)
                  { binputStmts = first_stmts
                  , binputTerm = break_stmt { pos_val = BreakStmt jump_info }
                  }

            let new_binput = (extBlockInput last_binput)
                  { binputID = block_id
                  , binputArgs = args
                  , binputStmts = last_stmts
                  }

            let new_breakpoints = do
                  let try_new_breakpoints = Bimap.tryInsert nm (Some block_id) $
                        extBreakpoints $ biBreakpoints bi
                  if Bimap.pairMember (nm, (Some block_id)) try_new_breakpoints
                    then try_new_breakpoints
                    else error $ "Duplicate breakpoint: " ++ show nm
            let bi' = BI
                  { biBlocks = first_binputs' :> last_binput' :> new_binput
                  , biJumpInfo = extJumpInfoMap $ biJumpInfo bi
                  , biSwitchInfo = extSwitchInfoMap $ biSwitchInfo bi
                  , biBreakpoints = new_breakpoints
                  }
            splitLastBlockInputOnBreakpoints bi' rest
        splitLastBlockInputOnBreakpoints bi rest = resolveBlocks bi rest
        isBreakpoint :: Posd (Stmt ext s) -> Bool
        isBreakpoint = \case
          Posd _ Breakpoint{} -> True
          _ -> False


------------------------------------------------------------------------
-- Translates from RTL with inference information to SSA.

data MaybeF f tp where
  JustF :: f tp -> MaybeF f tp
  NothingF :: MaybeF f tp

-- | Map each core SSA binding to the expression that generated it if it
-- was generated by an expression.
type RegExprs ext ctx = Assignment (MaybeF (C.Expr ext ctx)) ctx

#ifdef UNSAFE_OPS

extendRegExprs :: MaybeF (C.Expr ext ctx) tp -> RegExprs ext ctx -> RegExprs ext (ctx ::> tp)
extendRegExprs r e = unsafeCoerce (e :> r)

-- | Maps values in mutable representation to the current value in the SSA form.
newtype TypedRegMap s ctx = TypedRegMap { _typedRegMap :: MapF (Value s) (C.Reg ctx) }

-- | Resolve a register
resolveReg :: TypedRegMap s ctx -> Value s tp -> C.Reg ctx tp
resolveReg (TypedRegMap m) r = fromMaybe (error msg) (MapF.lookup r m)
  where msg = "Cannot find (unsafe) reg value " ++ show r ++ " "
              ++ "in TypedRegMap: " ++ (show m)

-- | Resolve an atom
resolveAtom :: TypedRegMap s ctx -> Atom s tp -> C.Reg ctx tp
resolveAtom (TypedRegMap m) r = fromMaybe (error msg) (MapF.lookup (AtomValue r) m)
  where msg = "Cannot find (unsafe) atom value " ++ show r ++ "."

regMapFromAssignment :: forall s args
                      . Assignment (Value s) args
                     -> TypedRegMap s args
regMapFromAssignment a = TypedRegMap $ forIndex (size a) go MapF.empty
  where go :: MapF (Value s) (C.Reg args)
           -> Index args tp
           -> MapF (Value s) (C.Reg args)
        go m i = MapF.insert (a ! i) (C.Reg i) m

extendRegMap :: TypedRegMap s ctx
             -> TypedRegMap s (ctx ::> tp)
extendRegMap = unsafeCoerce

-- | Assign existing register to atom in typed RegMap.
bindValueReg
    :: Value s tp
    -> C.Reg ctx tp
    -> TypedRegMap s ctx
    -> TypedRegMap s ctx
bindValueReg r cr (TypedRegMap m) = TypedRegMap $ MapF.insert r cr m

#else

extendRegExprs :: MaybeF (C.Expr ext ctx) tp -> RegExprs ext ctx -> RegExprs ext (ctx ::> tp)
extendRegExprs r e = fmapFC ext e :> ext r
 where ext :: MaybeF (C.Expr ctx) tp' -> MaybeF (C.Expr (ctx ::> tp)) tp'
       ext NothingF  = NothingF
       ext (JustF (C.App app)) = JustF (C.App (C.mapApp C.extendReg app))

data SomeReg ctx where
   SomeReg :: C.TypeRepr tp -> C.Reg ctx tp -> SomeReg ctx

newtype TypedRegMap s ctx = TypedRegMap { _typedRegMap :: Map (Some (Value s)) (SomeReg ctx) }

-- | Resolve a register
resolveReg :: TypedRegMap s ctx -> Value s tp -> C.Reg ctx tp
resolveReg (TypedRegMap m) r = creg
  where creg = case Map.lookup (Some r) m of
                 Nothing -> error msg
                 Just (SomeReg tr r') ->
                    case testEquality tr (typeOfValue r) of
                       Nothing -> error msg
                       Just Refl -> r'

        msg = "Cannot find (safe) reg value " ++ show r

-- | Resolve an atom
resolveAtom :: TypedRegMap s ctx -> Atom s tp -> C.Reg ctx tp
resolveAtom m a = resolveReg m (AtomValue a)

regMapFromAssignment :: forall s args
                      . Assignment (Value s) args
                     -> TypedRegMap s args
regMapFromAssignment a = TypedRegMap $ forIndex (size a) go Map.empty
  where go :: Map (Some (Value s)) (SomeReg args)
           -> Index args tp
           -> Map (Some (Value s)) (SomeReg args)
        go m i =
             let r = a ! i
              in Map.insert (Some r) (SomeReg (typeOfValue r) (C.Reg i)) m

extendRegMap :: TypedRegMap s ctx
             -> TypedRegMap s (ctx ::> tp)
extendRegMap (TypedRegMap m) =
  TypedRegMap $ fmap (\(SomeReg tr x) -> SomeReg tr (C.extendReg x)) m

-- | Assign existing register to atom in typed RegMap.
bindValueReg
    :: Value s tp
    -> C.Reg ctx tp
    -> TypedRegMap s ctx
    -> TypedRegMap s ctx
bindValueReg r cr (TypedRegMap m) =
  TypedRegMap $ Map.insert (Some r) (SomeReg (typeOfValue r) cr) m

#endif

-- | Assign new register to value in typed reg map.
assignRegister
    :: Value s tp
    -> Size ctx
    -> TypedRegMap s ctx
    -> TypedRegMap s (ctx ::> tp)
assignRegister r sz m =
  bindValueReg r (C.Reg (nextIndex sz)) (extendRegMap m)

copyValue
    :: Value s tp -- ^ Assign
    -> Value s tp
    -> TypedRegMap s ctx
    -> TypedRegMap s ctx
copyValue r r' m = bindValueReg r (resolveReg m r') m


resolveJumpTarget :: BlockInfo ext s ret blocks
                  -> TypedRegMap s ctx
                  -> Label s
                  -> C.JumpTarget blocks ctx
resolveJumpTarget bi reg_map next_lbl = do
  case lookupJumpInfo next_lbl (biJumpInfo bi) of
    Nothing -> error "Could not find label in resolveJumpTarget"
    Just (JumpInfo next_id types inputs) -> do
      let args = fmapFC (resolveReg reg_map) inputs
      C.JumpTarget next_id types args

-- | Resolve a lambda label into a typed jump target.
resolveLambdaAsJump :: BlockInfo ext s ret blocks
                    -> TypedRegMap s ctx
                    -> LambdaLabel s tp
                    -> C.Reg ctx tp
                    -> C.JumpTarget blocks ctx
resolveLambdaAsJump bi reg_map next_lbl output =
  case lookupSwitchInfo next_lbl (biSwitchInfo bi) of
    Nothing -> error "Could not find label in resolveLambdaAsJump"
    Just (SwitchInfo block_id types inputs) -> do
      let types' = types :> typeOfAtom (lambdaAtom next_lbl)
      let args = fmapFC (resolveReg reg_map) inputs
      let args' = args `extend` output
      C.JumpTarget block_id types' args'

-- | Resolve a lambda label into a typed switch target.
resolveLambdaAsSwitch :: BlockInfo ext s ret blocks
                      -> TypedRegMap s ctx
                      -> LambdaLabel s tp
                      -> C.SwitchTarget blocks ctx tp
resolveLambdaAsSwitch bi reg_map next_lbl =
  case lookupSwitchInfo next_lbl (biSwitchInfo bi) of
    Nothing -> error "Could not find label in resolveLambdaAsSwitch"
    Just (SwitchInfo block_id types inputs) -> do
      let args = fmapFC (resolveReg reg_map) inputs
      C.SwitchTarget block_id types args

-- | Resolve an untyped terminal statement to a typed one.
resolveTermStmt :: BlockInfo ext s ret blocks
                -> TypedRegMap s ctx
                -> RegExprs ext ctx
                   -- ^ Maps registers to associated expressions.
                -> ExtendedTermStmt s blocks ret
                -> C.TermStmt blocks ret ctx
resolveTermStmt bi reg_map bindings (BaseTermStmt t0) =
  case t0 of
    Jump l -> C.Jump (resolveJumpTarget bi reg_map l)

    Br c x y -> do
      let c_r = resolveAtom reg_map c
      case bindings ! C.regIndex c_r of
        JustF (C.App (C.BoolLit True))  -> C.Jump (resolveJumpTarget bi reg_map x)
        JustF (C.App (C.BoolLit False)) -> C.Jump (resolveJumpTarget bi reg_map y)
        _ -> C.Br c_r
                  (resolveJumpTarget bi reg_map x)
                  (resolveJumpTarget bi reg_map y)
    MaybeBranch tp e j n -> do
      let e_r = resolveAtom reg_map e
      case bindings ! C.regIndex e_r of
        JustF (C.App (C.JustValue _ je)) -> C.Jump (resolveLambdaAsJump bi reg_map j je)
        JustF (C.App (C.NothingValue _)) -> C.Jump (resolveJumpTarget bi reg_map n)
        _ -> C.MaybeBranch tp
                           e_r
                           (resolveLambdaAsSwitch bi reg_map j)
                           (resolveJumpTarget bi reg_map n)

    VariantElim ctx e s -> do
      let e_r = resolveAtom reg_map e
      case bindings ! C.regIndex e_r of
        JustF (C.App (C.InjectVariant _ idx x)) ->
          C.Jump (resolveLambdaAsJump bi reg_map (s Ctx.! idx) x)
        _ -> C.VariantElim ctx e_r (fmapFC (resolveLambdaAsSwitch bi reg_map) s)

    Return e -> C.Return (resolveAtom reg_map e)
    TailCall f ctx args -> do
      C.TailCall (resolveAtom reg_map f) ctx (fmapFC (resolveAtom reg_map) args)
    ErrorStmt e -> C.ErrorStmt (resolveAtom reg_map e)

    Output l e -> C.Jump (resolveLambdaAsJump bi reg_map l (resolveAtom reg_map e))
resolveTermStmt _ reg_map _ (BreakStmt (JumpInfo next_id types inputs)) = do
  let args = fmapFC (resolveReg reg_map) inputs
  C.Jump $ C.JumpTarget next_id types args

#ifdef UNSAFE_OPS
type AppRegMap ext ctx = MapF (C.App ext (C.Reg ctx)) (C.Reg ctx)

appRegMap_extend :: AppRegMap ext ctx -> AppRegMap ext (ctx ::> tp)
appRegMap_extend = unsafeCoerce

appRegMap_insert :: ( TraversableFC (C.ExprExtension ext)
                    , OrdFC (C.ExprExtension ext)
                    )
                 => C.App ext (C.Reg ctx) tp
                 -> C.Reg (ctx ::> tp) tp
                 -> AppRegMap ext ctx
                 -> AppRegMap ext (ctx ::> tp)
appRegMap_insert k v m = MapF.insert (fmapFC C.extendReg k) v (appRegMap_extend m)

appRegMap_lookup :: ( OrdFC (C.ExprExtension ext)
                    )
                 => C.App ext (C.Reg ctx) tp
                 -> AppRegMap ext ctx
                 -> Maybe (C.Reg ctx tp)
appRegMap_lookup = MapF.lookup

appRegMap_empty :: AppRegMap ext ctx
appRegMap_empty = MapF.empty
#else
type AppRegMap ext ctx = Map (Some (C.App ext (C.Reg ctx))) (SomeReg ctx)

appRegMap_extend :: AppRegMap ext ctx -> AppRegMap ext (ctx ::> tp)
appRegMap_extend = Map.fromList . fmap f . Map.toList
 where f (Some app, SomeReg tp reg) = (Some (C.mapApp C.extendReg app), SomeReg tp (C.extendReg reg))

appRegMap_insert :: OrdFC (C.ExprExtension ext)
                 => C.App ext (C.Reg ctx) tp
                 -> C.Reg (ctx::>tp) tp
                 -> AppRegMap ext ctx
                 -> AppRegMap ext (ctx ::> tp)
appRegMap_insert k v m =
  Map.insert (Some (C.mapApp C.extendReg k)) (SomeReg (C.appType k) v) (appRegMap_extend m)

appRegMap_lookup :: C.App ext (C.Reg ctx) tp
                 -> AppRegMap ext ctx
                 -> Maybe (C.Reg ctx tp)
appRegMap_lookup app m =
  case Map.lookup (Some app) m of
     Nothing -> Nothing
     Just (SomeReg tp r)
        | Just Refl <- testEquality tp (C.appType app) -> Just r
     _ -> error "appRegMap_lookup: impossible!"


appRegMap_empty :: AppRegMap ext ctx
appRegMap_empty = Map.empty

#endif

-- | Resolve a list of statements to a typed list.
resolveStmts :: C.IsSyntaxExtension ext
             => FunctionName
             -> BlockInfo ext s ret blocks
             -> Size ctx
             -> TypedRegMap s ctx
             -> RegExprs ext ctx
                -- ^ Maps registers back to the expression that generated them (if any)
             -> AppRegMap ext ctx
                -- ^ Maps applications to register that stores their value.
                -- Used to eliminate redundant operations.
             -> [Posd (Stmt ext s)]
             -> Posd (ExtendedTermStmt s blocks ret)
             -> C.StmtSeq ext blocks ret ctx
resolveStmts nm bi _ reg_map bindings _ [] (Posd p t) = do
  C.TermStmt (mkProgramLoc nm p)
             (resolveTermStmt bi reg_map bindings t)
resolveStmts nm bi sz reg_map bindings appMap (Posd p s0:rest) t = do
  let pl = mkProgramLoc nm p
  case s0 of
    SetReg r a -> do
      let reg_map' = reg_map & copyValue (RegValue r) (AtomValue a)
      resolveStmts nm bi sz reg_map' bindings appMap rest t
    WriteGlobal v a -> do
      C.ConsStmt pl
                 (C.WriteGlobal v (resolveAtom reg_map a))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)
    WriteRef r a -> do
      C.ConsStmt pl
                 (C.WriteRefCell (resolveAtom reg_map r) (resolveAtom reg_map a))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)
    DropRef r -> do
      C.ConsStmt pl
                 (C.DropRefCell (resolveAtom reg_map r))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)
    DefineAtom a av -> do
      case av of
        ReadReg r -> do
          let reg_map' = reg_map & copyValue (AtomValue a) (RegValue r)
          resolveStmts nm bi sz reg_map' bindings appMap rest t
        EvalExt estmt -> do
          let estmt' = fmapFC (resolveAtom reg_map) estmt
          let sz' = incSize sz
          let reg_map'  = reg_map & assignRegister (AtomValue a) sz
          -- No expression to associate with this value.
          let bindings' = bindings & extendRegExprs NothingF
          -- No App to memoize in this case.
          let appMap'   = appMap   & appRegMap_extend
          C.ConsStmt pl
                     (C.ExtendAssign estmt')
                     (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)
        ReadGlobal v -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          -- No expression to associate with this value.
          let bindings' = bindings & extendRegExprs NothingF
          -- No App to memoize in this case.
          let appMap'   = appMap   & appRegMap_extend
          C.ConsStmt pl
                     (C.ReadGlobal v)
                     (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)
        NewRef v -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          -- No expression to associate with this value.
          let bindings' = bindings & extendRegExprs NothingF
          -- No App to memoize in this case.
          let appMap'   = appMap   & appRegMap_extend
          -- Resolve the atom
          let v' = resolveAtom reg_map v
          C.ConsStmt pl
                     (C.NewRefCell (typeOfAtom v) v')
                     (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)
        NewEmptyRef tp -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          -- No expression to associate with this value.
          let bindings' = bindings & extendRegExprs NothingF
          -- No App to memoize in this case.
          let appMap'   = appMap   & appRegMap_extend
          -- Resolve the atom
          C.ConsStmt pl
                     (C.NewEmptyRefCell tp)
                     (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)
        ReadRef r -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          -- No expression to associate with this value.
          let bindings' = bindings & extendRegExprs NothingF
          -- No App to memoize in this case.
          let appMap'   = appMap   & appRegMap_extend
          -- Resolve the atom
          let r' = resolveAtom reg_map r
          C.ConsStmt pl
                     (C.ReadRefCell r')
                     (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)
        EvalApp (fmapFC (resolveAtom reg_map) -> e)
          | Just cr <- appRegMap_lookup e appMap -> do
            let reg_map' = bindValueReg (AtomValue a) cr reg_map
            resolveStmts nm bi sz reg_map' bindings appMap rest t
          | otherwise -> do
            let e' = C.App e
            let sz' = incSize sz
            let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
            let bindings' = bindings & extendRegExprs (JustF e')
            let appMap'   = appMap   & appRegMap_insert e (C.Reg (nextIndex sz))
            let stmt = C.SetReg (typeOfAtom a) e'
            C.ConsStmt pl stmt (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)

        FreshConstant bt cnm -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          let bindings' = bindings & extendRegExprs NothingF
          let appMap'   = appMap   & appRegMap_extend
          let stmt = C.FreshConstant bt cnm
          C.ConsStmt pl stmt (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)

        FreshFloat fi cnm -> do
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          let bindings' = bindings & extendRegExprs NothingF
          let appMap'   = appMap   & appRegMap_extend
          let stmt = C.FreshFloat fi cnm
          C.ConsStmt pl stmt (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)

        Call h args _ -> do
          let return_type = typeOfAtom a
          let h' = resolveAtom reg_map h
          let arg_types = fmapFC typeOfAtom args
          let args' = fmapFC (resolveAtom reg_map) args
          let stmt = C.CallHandle return_type h' arg_types args'
          let sz' = incSize sz
          let reg_map'  = reg_map  & assignRegister (AtomValue a) sz
          let bindings' = bindings & extendRegExprs NothingF
          let appMap'   = appMap   & appRegMap_extend
          C.ConsStmt pl stmt (resolveStmts nm bi sz' reg_map' bindings' appMap' rest t)

    Print e -> do
      C.ConsStmt pl
                 (C.Print (resolveAtom reg_map e))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)
    Assert c m ->
      C.ConsStmt pl
                 (C.Assert (resolveAtom reg_map c)
                           (resolveAtom reg_map m))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)

    Assume c m ->
      C.ConsStmt pl
                 (C.Assume (resolveAtom reg_map c)
                           (resolveAtom reg_map m))
                 (resolveStmts nm bi sz reg_map bindings appMap rest t)

    -- breakpoint statements are eliminated during the inferBlockInfo phase
    Breakpoint{} -> error $
      "Unexpected breakpoint at position " ++ show p ++ ": " ++ show (Pretty.pretty s0)

data SomeBlockMap ext ret where
  SomeBlockMap ::
    Ctx.Index blocks tp ->
    Bimap BreakpointName (Some (C.BlockID blocks)) ->
    C.BlockMap ext blocks ret ->
    SomeBlockMap ext ret

resolveBlockMap :: forall ext s ret
                 . C.IsSyntaxExtension ext
                => FunctionName
                -> Label s
                -> [Block ext s ret]
                -> SomeBlockMap ext ret
resolveBlockMap nm entry blocks = do
  let resolveBlock :: BlockInfo ext s ret blocks
                   -> BlockInput ext s blocks ret args
                   -> C.Block ext blocks ret args
      resolveBlock bi bin = do
        let sz = size (binputArgs bin)
        let regs = regMapFromAssignment (binputArgs bin)
        let regExprs = Ctx.replicate sz NothingF
        let appMap = appRegMap_empty
        let stmts = Fold.toList $ binputStmts bin
        let term = binputTerm bin
        C.Block { C.blockID = binputID bin
                , C.blockInputs = fmapFC typeOfValue (binputArgs bin)
                , C._blockStmts = resolveStmts nm bi sz regs regExprs appMap stmts term
                }
  case inferBlockInfo blocks of
    Some bi ->
      case lookupJumpInfo entry (biJumpInfo bi) of
        Nothing -> error "Missing initial block."
        Just (JumpInfo (C.BlockID idx) _ _) ->
          SomeBlockMap idx (biBreakpoints bi) $
            fmapFC (resolveBlock bi) (biBlocks bi)

------------------------------------------------------------------------
-- SomeCFG

-- | Convert a CFG in RTL form into a Core CFG in SSA form.
--
-- This prunes the CFG so that only reachable blocks are returned.
toSSA :: C.IsSyntaxExtension ext
      => CFG ext s init ret
      -> C.SomeCFG ext init ret
toSSA g = do
  let h = cfgHandle g
  let initTypes = cfgInputTypes g
  let entry = cfgEntryLabel g
  let blocks = cfgBlocks g
  case resolveBlockMap (handleName h) entry blocks of
    SomeBlockMap idx breakpoints block_map -> do
          let b = block_map ! idx
          case C.blockInputs b `testEquality` initTypes of
            Nothing -> error $
              "Input block type " ++ show (C.blockInputs b)
              ++ " does not match expected " ++ show initTypes
              ++ ":\nwhile SSA converting function " ++ show h
            Just Refl -> do
              let g' = C.CFG { C.cfgHandle = h
                             , C.cfgBlockMap = block_map
                             , C.cfgEntryBlockID = C.BlockID idx
                             , C.cfgBreakpoints = breakpoints
                             }
              reachableCFG g'
