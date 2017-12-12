{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Mir.Pass (
    passId,
    passRemoveStorage,
    passRemoveBoxNullary,
    passCollapseRefs,
    passMutRefArgs
) where

import Mir.Mir
import Control.Monad.State.Lazy
import Data.List
import Control.Monad.Reader
import Data.Maybe (catMaybes)
import Control.Lens hiding (op)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import System.IO.Unsafe

-- mir utitiles
--
--
--

isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) ||  isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = foldl (\acc t -> acc || isMutRefTy t) False ts
isMutRefTy (TyCustom (BoxTy t)) = isMutRefTy t
isMutRefTy _ = False

class IsMutTagged a where
    isMutTagged :: a -> Bool

instance IsMutTagged Operand where
    isMutTagged (Consume (Tagged _ "mutchange")) = True
    isMutTagged _ = False

instance IsMutTagged Lvalue where
    isMutTagged (Tagged _ "mutchange") = True
    isMutTagged _ = False

removeTags :: [Operand] -> [Operand]
removeTags = map (\(Consume ( Tagged lv _)) -> Consume lv)

isMutRefVar :: Var -> Bool
isMutRefVar (Var _ _ t _ _) = isMutRefTy t

changeTyToImmut :: Ty -> Ty
changeTyToImmut (TyRef c _) =  (TyRef c Immut)
changeTyToImmut t = t

--
--other utils
ints_list :: Int -> [Int]
ints_list 0 = [0]
ints_list i | i > 0 = (ints_list (i - 1)) ++ [i]
            | i < 0 = error "bad intslist"
--

type Pass = [Fn] -> [Fn]

passId :: Pass
passId fns = fns

-- Pass for rewriting mutref args to be returned outside; i.e., if I have a function f(x : T1, y : &mut T2, z : T3, w : &mut T4) -> T5, it will be transformed into a function which returns (T5, T2, T4). All function calls are also transformed to handle this. This is done purely at the MIR "syntax" level.

-- The algorithm is imperative -- everything is basically modified in place.

data RewriteFnSt = RFS { --  state internal to function translation.
    _fn_name :: T.Text,
    _ctr :: Int, -- counter for fresh variables
    _immut_arguments :: Map.Map T.Text Var, -- arguments to the function which don't need to be tampered with
    -- vvv arguments of the form &mut T (or variations thereof.) The translation creates a dummy variable for each one. The dummy variable is the second. fst will end up in internals, snd will end up in arguments
    _mut_argpairs :: Map.Map T.Text (Var, Var),
    _ret_ty :: Ty,
    _internals :: Map.Map T.Text Var, -- local variables
    _blocks :: Map.Map T.Text BasicBlockData,
    _dummyret :: Maybe Var, -- this is where the original return value goes, which will later be aggregated with the mutref values
    _fnargsmap :: Map.Map T.Text [Ty], -- maps argument names to their types in the function signature
    _fnsubstitutions :: Map.Map Lvalue Lvalue -- any substitutions which need to take place. all happen at the end
    }

fnSubstitutions :: Simple Lens RewriteFnSt (Map.Map Lvalue Lvalue)
fnSubstitutions = lens _fnsubstitutions (\s v -> s { _fnsubstitutions = v })

fnName :: Simple Lens (RewriteFnSt) T.Text
fnName = lens _fn_name (\s v -> s { _fn_name = v })

dummy_ctr :: Simple Lens (RewriteFnSt) Int
dummy_ctr = lens _ctr (\s v -> s { _ctr = v })

fnImmutArguments :: Simple Lens (RewriteFnSt) (Map.Map T.Text Var)
fnImmutArguments = lens _immut_arguments (\s v -> s { _immut_arguments = v })

fnArgsMap :: Simple Lens (RewriteFnSt) (Map.Map T.Text [Ty])
fnArgsMap = lens _fnargsmap (\s v -> s { _fnargsmap = v })

fnMutArgPairs :: Simple Lens (RewriteFnSt) (Map.Map T.Text (Var, Var))
fnMutArgPairs = lens _mut_argpairs (\s v -> s { _mut_argpairs = v })

fnDummyRet :: Simple Lens RewriteFnSt (Maybe Var)
fnDummyRet = lens _dummyret (\s v -> s { _dummyret = v})

fnRet_ty :: Simple Lens (RewriteFnSt) Ty
fnRet_ty = lens _ret_ty (\s v -> s { _ret_ty = v })

fnInternals :: Simple Lens (RewriteFnSt) (Map.Map T.Text Var)
fnInternals = lens _internals (\s v -> s { _internals = v })

fnBlocks :: Simple Lens (RewriteFnSt) (Map.Map T.Text BasicBlockData)
fnBlocks = lens _blocks (\s v -> s { _blocks = v })

newCtr :: State RewriteFnSt Int
newCtr = do
    c <- use dummy_ctr
    dummy_ctr .= (c + 1)
    return (c + 1)

newDummyBlock :: T.Text -> BasicBlockData -> State RewriteFnSt BasicBlock
newDummyBlock prev_name bbd = do
    blocks <- use fnBlocks
    let name = T.pack $ (T.unpack prev_name) ++ "d"
    fnBlocks .= Map.insert name bbd blocks
    return (BasicBlock name bbd)

mkDummyInternal :: Ty -> State RewriteFnSt Var
mkDummyInternal ty = do
    internals <- use fnInternals
    let dummyvar = (Var "_dummyret" Immut ty "scopedum" "<dummy pos>")
    fnInternals .= Map.insert "_dummyret" dummyvar internals
    return dummyvar

newInternal :: Ty -> State RewriteFnSt Var
newInternal ty = do
    ctr <- newCtr
    let new_name = T.pack $ "_vd" ++ (show ctr)
        new_var =  (Var new_name Immut ty "scopedum" "<dummy pos>")
    internals <- use fnInternals
    fnInternals .= Map.insert new_name new_var internals
    return new_var

removeReturnVar :: [Var] -> [Var]
removeReturnVar [] = []
removeReturnVar (v:vs) = case v of
                           (Var "_0" _ _ _ _) -> vs
                           _ -> v : (removeReturnVar vs)

findReturnVar :: [Var] -> Var
findReturnVar [] = error "return var not found!"
findReturnVar (v:vs) = case v of
                         (Var "_0" _ _ _ _) -> v
                         _ -> findReturnVar vs

modifyVarTy :: Var -> Ty -> Var
modifyVarTy (Var a b c d p) e = Var a b e d p


vars_to_map :: [Var] -> Map.Map T.Text Var
vars_to_map vs = Map.fromList $ map (\v -> (_varname v, v)) vs

mutref_to_immut :: Var -> Var
mutref_to_immut (Var vn vm vty vsc vp) = Var (T.pack $ (T.unpack vn) ++ "d") vm (changeTyToImmut vty) vsc vp

-- buildRewriteSt
-- build initial rewrite state

buildRewriteSt :: Fn -> [Fn] -> RewriteFnSt
buildRewriteSt (Fn fname fargs fretty (MirBody internals blocks)) fns =
    let (mut_args, immut_args) = partition (isMutRefTy . typeOf) fargs
        immut_map = vars_to_map immut_args
        mutpairmap = Map.map (\v -> (v, mutref_to_immut v)) (vars_to_map mut_args)
        fnmap = Map.fromList $ map (\(Fn fn fa _ _) -> (fn, map typeOf fa)) fns in
    RFS fname 0 immut_map mutpairmap fretty (vars_to_map internals) (Map.fromList $ map (\bb -> (_bbinfo bb, _bbdata bb)) blocks) Nothing fnmap Map.empty

-- insertMutvarsIntoInternals
-- put all x's into internals, where (x,y) are the mutarg pairs (x is old mut, y is new immut dummy)

insertMutvarsIntoInternals :: State RewriteFnSt ()
insertMutvarsIntoInternals = do
    mutargpairs <- use fnMutArgPairs
    forM_ (Map.toList mutargpairs) $ \(vname, (vmut, vimmut)) -> do
        internals <- use fnInternals
        fnInternals .= Map.insert vname vmut internals

-- modifyAssignEntryBlock
-- insert statements x := y where x is mut ref arg (will be internal), y is corresponding dummy into first block
modifyAssignEntryBlock :: State RewriteFnSt ()
modifyAssignEntryBlock = do
    blocks <- use fnBlocks
    mutpairs <- use fnMutArgPairs
    let (BasicBlockData entry_stmts ei) = case Map.lookup (T.pack "bb0") blocks of
                        Just b -> b
                        Nothing -> error "entry block not found"

        new_asgns = Map.elems $ Map.map (\(vmut, vimmut) -> Assign (Local vmut) (Use $ Consume $ Local vimmut) "<dummy pos>") mutpairs
        new_bbd = BasicBlockData (new_asgns ++ entry_stmts) ei
    fnBlocks .= Map.insert (T.pack "bb0") new_bbd blocks

-- modifyRetData
-- new fretty = (old fretty, x_1, .., x_n) where x_i are mutref types
-- make _0 be new fretty
-- make _dummyret be old fretty
-- replace _0 with _dummyret in blocks

modifyRetData :: State RewriteFnSt ()
modifyRetData = do
    old_fretty <- use fnRet_ty
    mutpairs <- use fnMutArgPairs
    internals <- use fnInternals
    let new_fretty = TyTuple $ [old_fretty] ++ (map (_varty . snd) (Map.elems mutpairs))
    fnRet_ty .= new_fretty

    let (Just retvar) =  Map.lookup "_0" internals
    fnInternals .= Map.insert "_0" (modifyVarTy retvar new_fretty) internals

    dummy_ret <- mkDummyInternal old_fretty
    fnDummyRet .= Just (dummy_ret)

    blocks <- use fnBlocks
    fnBlocks .= replaceVar retvar dummy_ret blocks

-- make statement _0 := (_dummyret, x_1, x_2, ..) where x_i are internalized mutable argument
mkPreReturnAssgn :: State RewriteFnSt Statement
mkPreReturnAssgn = do
    mutpairs <- use fnMutArgPairs
    internals <- use fnInternals
    let muts = Map.elems $ Map.map fst mutpairs
    Just dummyret <- use fnDummyRet
    let (Just retvar) = Map.lookup "_0" internals
    return $ Assign (Local retvar) (Aggregate AKTuple $  [Consume (Local dummyret)] ++ (map (Consume . Local) muts)) "<dummy pos>"

processReturnBlock_ :: BasicBlockData -> State RewriteFnSt BasicBlockData
processReturnBlock_ (BasicBlockData stmts Return) = do
    snew <- mkPreReturnAssgn
    return (BasicBlockData (stmts ++ [snew]) Return)

processReturnBlock_ v = return v

-- processReturnBlocks :
    --  last statement before return becomes _0 := (_dummyret, x_1, x_2, ..) where x_i are the internalized mutable arguments
processReturnBlocks :: State RewriteFnSt ()
processReturnBlocks = do
    blocks <- use fnBlocks
    newblocks <- mapM processReturnBlock_ blocks
    fnBlocks .= newblocks

-- for the example above where f is taken from returning T5 to (T5, T2, T4), mkFnCallVars creates the dummy variable for receiving the (T5, T2, T4)-value, as well as the corresponding destructures.

mkFnCallVars :: Lvalue -> [Ty] -> State RewriteFnSt (Var, (Lvalue, [Lvalue]))
mkFnCallVars orig_dest mut_tys = do
    let type_list = [typeOf orig_dest] ++ mut_tys
        type_of_new = TyTuple type_list
    v <- newInternal type_of_new
    let destructures = zipWith (\ind ty -> LProjection (LvalueProjection (Local v) (PField ind ty))) (ints_list ((length type_list) - 1)) type_list
    return (v, (head destructures, tail destructures))

    --  for each function call:
    --     Call(f, args, (ret_lv, dest)) ->
    --      v := newVar (mkCorrespondingTuple args ret_lv) -- mkCorrespondingTuple args ret_lv = (lv_type, (mut args tupl))
    --      call(f, args, (Local v, B))
    --      where B := newDummyBlock $
    --          destructure v to (orig_return, (mutargs_changed))
    --          assign ret_lv to orig_return
    --          assign args to mutargs_changed
    --          jump to dest
processFnCall_ :: BasicBlockInfo -> BasicBlockData -> State RewriteFnSt ()
processFnCall_ bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean))
    | Just _ <- isCustomFunc (funcNameofOp cfunc) = processCustomFnCall bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean))
    | otherwise = do
        fnargsmap <- use fnArgsMap
        let (mut_cargs, immut_cargs) = sort_mutrefs cargs fnargsmap (funcNameofOp cfunc)
        if (null mut_cargs) then do
            return ()
        else do
            do_mutrefarg_trans bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean)) mut_cargs

   where sort_mutrefs :: [Operand] -> Map.Map T.Text [Ty] -> T.Text -> ([Operand], [Operand])
         sort_mutrefs args fnmap fname = case Map.lookup fname fnmap of
                                           Just tys -> go args tys
                                           Nothing -> error $ "fn not found: " ++ (show fname)

         go :: [Operand] -> [Ty] -> ([Operand], [Operand])
         go [] [] = ([], [])
         go (o:os) (t:ts) = case (isMutRefTy t) of
                              True -> let (a,b) = go os ts in (o:a, b)
                              False -> let (a,b) = go os ts in (a, o:b)

         processCustomFnCall :: BasicBlockInfo -> BasicBlockData -> State RewriteFnSt ()
         processCustomFnCall bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean))
          | Just "vec_asmutslice" <- isCustomFunc (funcNameofOp cfunc),
          [op] <- cargs = do -- collapse return var into input.
              fnsubs <- use fnSubstitutions
              fnSubstitutions .= Map.insert dest_lv (lValueofOp op) fnsubs
          | Just "iter_next" <- isCustomFunc (funcNameofOp cfunc), [op] <- cargs = do -- op acts like a mutref.
            do_mutrefarg_trans bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean)) [op]

          | otherwise = return ()

         do_mutrefarg_trans :: BasicBlockInfo -> BasicBlockData -> [Operand] -> State RewriteFnSt ()
         do_mutrefarg_trans bbi (BasicBlockData stmts (Call cfunc cargs (Just (dest_lv, dest_block)) cclean)) mut_cargs = do
            (v, (v0, vrest)) <- mkFnCallVars dest_lv $ map typeOf mut_cargs
            newb <- newDummyBlock bbi $ BasicBlockData
                ([Assign dest_lv (Use $ Consume v0) "<dummy pos>"] ++
                 (zipWith (\c v -> Assign (lValueofOp c) (Use $ Consume v) "<dummy pos>") mut_cargs vrest))
                (Goto dest_block)

            blocks <- use fnBlocks
            fnBlocks .= Map.insert bbi (BasicBlockData stmts (Call cfunc cargs (Just (Local v, _bbinfo newb)) cclean)) blocks
processFnCall_ _ _ = return ()

processFnCalls :: State RewriteFnSt ()
processFnCalls = do
    blocks <- use fnBlocks
    forM_ (Map.toList blocks) $ \(k,v) -> do
        processFnCall_ k v

-- use the state to recover the transformed function
extractFn :: State RewriteFnSt Fn
extractFn = do
    immut_args <- use fnImmutArguments
    mut_argpairs <- use fnMutArgPairs
    ret_ty <- use fnRet_ty
    internals <- use fnInternals
    blocks <- use fnBlocks
    fname <- use fnName
    fsubs <- use fnSubstitutions

    let blocks_ = replaceList (Map.toList fsubs) blocks

    let fnargs = (Map.elems immut_args) ++ (Map.elems $ Map.map snd mut_argpairs)
        fnblocks = map (\(k,v) -> BasicBlock k v) (Map.toList blocks_)
    return $ Fn fname fnargs ret_ty (MirBody (Map.elems internals) fnblocks)


-- if there are no mutref args, then the body of the function doesn't need to change
needsToBeTransformed :: State RewriteFnSt Bool
needsToBeTransformed = do
    mutargpairs <- use fnMutArgPairs
    return $ not $  Map.null mutargpairs

rewriteMutRefArgFn :: State RewriteFnSt Fn
rewriteMutRefArgFn = do
    b <- needsToBeTransformed
    if b then do
        modifyAssignEntryBlock
        modifyRetData
        processReturnBlocks
        insertMutvarsIntoInternals
    else do
        return ()
    processFnCalls
    extractFn

passRewriteMutRefArg :: Pass
passRewriteMutRefArg fns = map (\fn -> evalState (rewriteMutRefArgFn) (buildRewriteSt fn fns)) fns

passRemoveBoxNullary :: Pass
passRemoveBoxNullary fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (map removeBoxNullary blocks))) fns

removeBoxNullary :: BasicBlock -> BasicBlock
removeBoxNullary (BasicBlock bbi (BasicBlockData stmts term)) =
    let stmts' = filter (\stmt -> case stmt of
                Assign _ (NullaryOp Box _) _ -> False
                _ -> True) stmts
    in BasicBlock bbi (BasicBlockData stmts' term)


mapTransClosure :: Ord a => Map.Map a a -> Map.Map a a
mapTransClosure m = Map.map (\v -> mapIterate m v) m
    where mapIterate m v = case (Map.lookup v m) of
                             Just g -> mapIterate m g
                             Nothing -> v

passCollapseRefs :: Pass
passCollapseRefs fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (pcr_ blocks))) fns

pcr_ :: [BasicBlock] -> [BasicBlock]
pcr_ bs = evalState (pcr bs) (Map.empty)

registerStmt :: Statement -> State (Map.Map Lvalue Lvalue) ()
registerStmt stmt = do
    refmap <- get
    case stmt of
      Assign lv rv _ ->
          if (Map.notMember lv refmap) then
              case (typeOf lv) of
                  TyRef _ _ ->
                      case rv of
                        Use op ->
                            do {put $ Map.insert lv (lValueofOp op) refmap}
                        Ref _ l _ -> do
                            put $ Map.insert lv l refmap
                  _ -> return ()
          else return ()
      _ -> return ()

pcr :: [BasicBlock] -> State (Map.Map Lvalue Lvalue) [BasicBlock]
pcr bbs = do
    forM_ bbs $ \(BasicBlock bbi (BasicBlockData stmts term)) ->
        forM_ stmts registerStmt

    refmap <- get
    let refmap_ = mapTransClosure refmap
    return $ replaceList (Map.toList refmap_) bbs

passMutRefArgs :: Pass
passMutRefArgs = passRewriteMutRefArg . passCollapseRefs

-- remove storageDead / storageAlive calls
passRemoveStorage :: Pass
passRemoveStorage fns = map (\(Fn a b c (MirBody d blocks)) -> Fn a b c (MirBody d (prs_ blocks))) fns

prs_ :: [BasicBlock] -> [BasicBlock]
prs_ bbs = map prs bbs

prs :: BasicBlock -> BasicBlock
prs (BasicBlock bbi (BasicBlockData stmts t)) =
    let ns = filter (\stmt -> case stmt of
                    StorageLive _ -> False
                    StorageDead _ -> False
                    _ -> True) stmts in
    (BasicBlock bbi (BasicBlockData ns t))

exists :: (a -> Bool) -> [a] -> Bool
exists p xs = case findIndex p xs of
                Just _ -> True
                Nothing -> False

forall :: (a -> Bool) -> [a] -> Bool
forall p xs = not $ exists (not . p) xs

is_branch :: Terminator -> Bool
is_branch term = case term of
                   SwitchInt _ _ _ _ -> True
                   _ -> False


is_return_block :: BasicBlock -> Bool
is_return_block (BasicBlock bbi (BasicBlockData stmts term)) = (term == Return)

-- for each function, if it returns a mutable reference, and if the return is statically known to be one of the arguments, perform the corresponding substitution

type MrrsSt = Map.Map T.Text (Maybe Int) -- if component is set, the function returns a mutable reference, and needs to be fused while calling. the integer argument is which argument is the return

build_mrrs_st :: [Fn] -> MrrsSt
build_mrrs_st fns = Map.fromList $ map (\fn -> (_fname fn, mut_info fn fns)) fns

-- determine whether the function statically returns a mutref of an argument. this is true (at least) when there are no switches in the body, and any functions called are themselves static.
mut_info :: Fn -> [Fn] ->  Maybe Int
mut_info fn fns =
    case (is_static_mut_return fns fn) of
                True -> Just (retrieve_static_mut_return fn)
                False -> Nothing

is_static_mut_return :: [Fn] -> Fn -> Bool
is_static_mut_return fns fn =
    case fn of
      Fn fname fargs fretty (MirBody internals fblocks) ->
          case exists (\(BasicBlock _ (BasicBlockData _ term)) -> is_branch term) fblocks of
            True -> False
            False ->
                forall (\(BasicBlock _ (BasicBlockData _ term)) -> (not . is_bad_call) term) fblocks

   where is_bad_call :: Terminator -> Bool
         is_bad_call term = case term of
                              Call fname _ _ _ ->
                                  case find (\(Fn n _ t _) -> n == (funcNameofOp fname)) fns of
                                    Just call_fn | isMutRefTy (_freturn_ty call_fn) -> (not . (is_static_mut_return fns)) call_fn
                                    _ -> False
                              _ -> False

retrieve_static_mut_return :: Fn -> Int
retrieve_static_mut_return (Fn fname fargs fretty (MirBody internals blocks)) =
    error "unimplemented" -- find most recent arg index assigned to return variable. the code is guaranteed to be straightline by now, so we can just iterate backwards through the blocks.


passMutRefReturnStatic :: Pass
passMutRefReturnStatic fns = map (\fn -> runReader (mrrs fn) (build_mrrs_st fns)) fns

mrrs :: Fn -> Reader MrrsSt Fn
mrrs (Fn fname fargs fretty (MirBody d blocks)) = do
    mrrs_map <- ask
    let subs = catMaybes $ map (\(BasicBlock bbi (BasicBlockData stmts term)) -> get_sub term mrrs_map) blocks

    return $ Fn fname fargs fretty (MirBody d (replaceList subs blocks))

   where
       get_sub :: Terminator -> Map.Map T.Text (Maybe Int) -> Maybe (Lvalue, Lvalue)
       get_sub term mrrs_map = case term of
         Call opfunc opargs (Just (dest_lv,dest_bbi)) cleanup ->
             case Map.lookup (funcNameofOp opfunc) mrrs_map of
               Just (Just i) -> Just ((dest_lv, lValueofOp $ opargs !! i))
               _ -> Nothing
         _ -> Nothing
