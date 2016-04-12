{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.SBVParser
  ( loadSBV
  , parseSBVPgm
  , UnintMap
  , Typ(..)
  , typOf
  ) where

import Prelude hiding (mapM)

import Control.Monad.State hiding (mapM)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (mapM)

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm
import qualified SAWScript.SBVModel as SBV

type NodeCache s = Map SBV.NodeId (SharedTerm s)

parseSBV :: SharedContext s -> NodeCache s -> SBV.SBV -> IO (Nat, SharedTerm s)
parseSBV sc _ (SBV.SBV size (Left num)) =
    do t <- scBvConst sc (fromInteger size) num
       return (fromInteger size, t)
parseSBV _ nodes (SBV.SBV size (Right nodeid)) =
    case Map.lookup nodeid nodes of
      Just t -> return (fromIntegral size, t)
      Nothing -> fail "parseSBV"

type UnintMap s = String -> Typ -> Maybe (SharedTerm s)

parseSBVExpr :: SharedContext s -> UnintMap s -> NodeCache s ->
                Nat -> SBV.SBVExpr -> IO (SharedTerm s)
parseSBVExpr sc _unint nodes _size (SBV.SBVAtom sbv) =
    liftM snd $ parseSBV sc nodes sbv
parseSBVExpr sc unint nodes size (SBV.SBVApp operator sbvs) =
    case operator of
      SBV.BVAdd -> binop scBvAdd sbvs
      SBV.BVSub -> binop scBvSub sbvs
      SBV.BVMul -> binop scBvMul sbvs
      SBV.BVDiv _loc -> binop (error "bvDiv") sbvs
      SBV.BVMod _loc -> binop (error "bvMod") sbvs
      SBV.BVPow -> binop (error "bvPow") sbvs
      SBV.BVIte ->
          case sbvs of
            [sbv1, sbv2, sbv3] ->
                do (_size1, arg1) <- parseSBV sc nodes sbv1
                   (_size2, arg2) <- parseSBV sc nodes sbv2
                   (_size3, arg3) <- parseSBV sc nodes sbv3
                   -- assert size1 == 1 && size2 == size && size3 == size
                   s <- scBitvector sc size
                   cond <- scBv1ToBool sc arg1
                   scIte sc s cond arg2 arg3
            _ -> fail "parseSBVExpr: wrong number of arguments for if-then-else"
      SBV.BVShl -> shiftop scBvShiftL sbvs
      SBV.BVShr -> shiftop scBvShiftR sbvs
      SBV.BVRol -> shiftop scBvRotateL sbvs
      SBV.BVRor -> shiftop scBvRotateR sbvs
      SBV.BVExt hi lo | lo >= 0 && hi >= lo ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   unless (size == fromInteger (hi + 1 - lo)) (fail $ "parseSBVExpr BVExt: size mismatch " ++ show (size, hi, lo))
                   b <- scBoolType sc
                   s1 <- scNat sc (size1 - 1 - fromInteger hi)
                   s2 <- scNat sc size
                   s3 <- scNat sc (fromInteger lo)
                   -- SBV indexes bits starting with 0 = lsb.
                   scSlice sc b s1 s2 s3 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for extract"
      SBV.BVExt{} -> fail "parseSBVExpr: BVExt bad arguments"
      SBV.BVAnd -> binop scBvAnd sbvs
      SBV.BVOr  -> binop scBvOr  sbvs
      SBV.BVXor -> binop scBvXor sbvs
      SBV.BVNot ->
          case sbvs of
            [sbv1] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   s1 <- scNat sc size1
                   unless (size == size1) (fail $ "parseSBVExpr BVNot: size mismatch " ++ show (size, size1))
                   scBvNot sc s1 arg1
            _ -> fail "parseSBVExpr: wrong number of arguments for Not"
      SBV.BVEq  -> binrel scBvEq  sbvs
      SBV.BVGeq -> binrel scBvUGe sbvs
      SBV.BVLeq -> binrel scBvULe sbvs
      SBV.BVGt  -> binrel scBvUGt sbvs
      SBV.BVLt  -> binrel scBvULt sbvs
      SBV.BVApp ->
          case sbvs of
            [sbv1, sbv2] ->
                do (size1, arg1) <- parseSBV sc nodes sbv1
                   (size2, arg2) <- parseSBV sc nodes sbv2
                   s1 <- scNat sc size1
                   s2 <- scNat sc size2
                   unless (size == size1 + size2) (fail $ "parseSBVExpr BVApp: size mismatch " ++ show (size, size1, size2))
                   b <- scBoolType sc
                   -- SBV append takes the most-significant argument
                   -- first, as SAWCore does.
                   scAppend sc b s1 s2 arg1 arg2
            _ -> fail "parseSBVExpr: wrong number of arguments for append"
      SBV.BVLkUp indexSize resultSize ->
          do (size1 : inSizes, arg1 : args) <- liftM unzip $ mapM (parseSBV sc nodes) sbvs
             -- unless (2 ^ indexSize == length args) $ putStrLn "parseSBVExpr BVLkUp: list size not a power of 2"
             unless (size1 == fromInteger indexSize && all (== (fromInteger resultSize)) inSizes)
                        (fail $ "parseSBVExpr BVLkUp: size mismatch")
             e <- scBitvector sc (fromInteger resultSize)
             scMultiMux sc (fromInteger indexSize) e arg1 args
      SBV.BVUnint _loc _codegen (name, irtyp) ->
          do let typ = parseIRType irtyp
             t <- case unint name typ of
               Just t -> return t
               Nothing ->
                   do putStrLn ("WARNING: unknown uninterpreted function " ++ show (name, typ, size))
                      putStrLn ("Using Prelude." ++ name)
                      scGlobalDef sc (mkIdent preludeName name)
             args <- mapM (parseSBV sc nodes) sbvs
             let inSizes = map fst args
                 (TFun inTyp outTyp) = typ
             unless (sum (typSizes inTyp) == sum (map fromIntegral inSizes)) $ do
               putStrLn ("ERROR parseSBVPgm: input size mismatch in " ++ name)
               print inTyp
               print inSizes
             argument <- combineOutputs sc inTyp args
             result <- scApply sc t argument
             results <- splitInputs sc outTyp result
             let outSizes = typSizes outTyp
             -- Append bitvector components of result value in lsb order
             scAppendAll sc (reverse (zip results outSizes))
    where
      -- | scMkOp :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
      binop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size1 == size && size2 == size) (fail $ "parseSBVExpr binop: size mismatch " ++ show (size, size1, size2))
             s <- scNat sc size
             scMkOp sc s arg1 arg2
      binop _ _ = fail "parseSBVExpr: wrong number of arguments for binop"
      -- | scMkRel :: (x :: Nat) -> bitvector x -> bitvector x -> Bool;
      binrel scMkRel [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size == 1 && size1 == size2) (fail $ "parseSBVExpr binrel: size mismatch " ++ show (size, size1, size2))
             s <- scNat sc size1
             t <- scMkRel sc s arg1 arg2
             scBoolToBv1 sc t
      binrel _ _ = fail "parseSBVExpr: wrong number of arguments for binrel"
      -- | scMkOp :: (x :: Nat) -> bitvector x -> Nat -> bitvector x;
      shiftop scMkOp [sbv1, sbv2] =
          do (size1, arg1) <- parseSBV sc nodes sbv1
             (size2, arg2) <- parseSBV sc nodes sbv2
             unless (size1 == size) (fail "parseSBVExpr shiftop: size mismatch")
             s1 <- scNat sc size1
             s2 <- scNat sc size2
             c <- scBool sc False
             boolTy <- scBoolType sc
             scMkOp s1 boolTy s2 c arg1 arg2
      shiftop _ _ = fail "parseSBVExpr: wrong number of arguments for binop"
      scBvShiftL n ty w c v amt = scGlobalApply sc "Prelude.bvShiftL" [n, ty, w, c, v, amt]
      scBvShiftR n ty w c v amt = scGlobalApply sc "Prelude.bvShiftR" [n, ty, w, c, v, amt]
      scBvRotateL n ty w _ v amt = scGlobalApply sc "Prelude.bvRotateL" [n, ty, w, v, amt]
      scBvRotateR n ty w _ v amt = scGlobalApply sc "Prelude.bvRotateR" [n, ty, w, v, amt]

----------------------------------------------------------------------

data SBVAssign = SBVAssign SBV.Size SBV.NodeId SBV.SBVExpr
  deriving Show
data SBVInput = SBVInput SBV.Size SBV.NodeId
  deriving Show
type SBVOutput = SBV.SBV

partitionSBVCommands :: [SBV.SBVCommand] -> ([SBVAssign], [SBVInput], [SBVOutput])
partitionSBVCommands = foldr select ([], [], [])
    where
      select cmd (assigns, inputs, outputs) =
          case cmd of
            SBV.Decl _ (SBV.SBV _ (Left _)) _ ->
                error "invalid SBV command: ground value on lhs"
            SBV.Decl _ (SBV.SBV size (Right nodeid)) Nothing ->
                (assigns, SBVInput size nodeid : inputs, outputs)
            SBV.Decl _ (SBV.SBV size (Right nodeid)) (Just expr) ->
                (SBVAssign size nodeid expr : assigns, inputs, outputs)
            SBV.Output sbv ->
                (assigns, inputs, sbv : outputs)

-- TODO: Should I use a state monad transformer?
parseSBVAssign :: SharedContext s -> UnintMap s -> NodeCache s -> SBVAssign -> IO (NodeCache s)
parseSBVAssign sc unint nodes (SBVAssign size nodeid expr) =
    do term <- parseSBVExpr sc unint nodes (fromInteger size) expr
       return (Map.insert nodeid term nodes)

----------------------------------------------------------------------

data Typ
  = TBool
  | TFun Typ Typ
  | TVec SBV.Size Typ
  | TTuple [Typ]
  | TRecord [(String, Typ)]

instance Show Typ where
  show TBool = "."
  show (TFun t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TVec size t) = "[" ++ show size ++ "]" ++ show t
  show (TTuple ts) = "(" ++ intercalate "," (map show ts) ++ ")"
  show (TRecord fields) = "{" ++ intercalate "," (map showField fields) ++ "}"
    where showField (s, t) = s ++ ":" ++ show t

parseIRType :: SBV.IRType -> Typ
parseIRType (SBV.TApp "." []) = TBool
parseIRType (SBV.TApp "->" [a, b]) = TFun (parseIRType a) (parseIRType b)
parseIRType (SBV.TApp ":" [SBV.TInt n, a]) = TVec n (parseIRType a)
parseIRType (SBV.TApp c ts)
  | c == "(" ++ replicate (length ts - 1) ',' ++ ")" = TTuple (map parseIRType ts)
parseIRType (SBV.TRecord fields) =
    TRecord [ (name, parseIRType t) | (name, SBV.Scheme [] [] [] t) <- fields ]
parseIRType t = error ("parseIRType: " ++ show t)

typSizes :: Typ -> [SBV.Size]
typSizes TBool = [1]
typSizes (TTuple ts) = concatMap typSizes ts
typSizes (TVec n TBool) = [n]
typSizes (TVec n t) = concat (replicate (fromIntegral n) (typSizes t))
typSizes (TRecord fields) = concatMap (typSizes . snd) fields
typSizes (TFun _ _) = error "typSizes: not a first-order type"

scTyp :: SharedContext s -> Typ -> IO (SharedTerm s)
scTyp sc TBool = scBoolType sc
scTyp sc (TFun a b) =
    do s <- scTyp sc a
       t <- scTyp sc b
       scFun sc s t
scTyp sc (TVec n TBool) =
    do scBitvector sc (fromInteger n)
scTyp sc (TVec n t) =
    do ty <- scTyp sc t
       ntm <- scNat sc (fromInteger n)
       scVecType sc ntm ty
scTyp sc (TTuple as) =
    do ts <- mapM (scTyp sc) as
       scTupleType sc ts
scTyp sc (TRecord fields) =
    do let am = Map.fromList fields
       tm <- mapM (scTyp sc) am
       scRecordType sc tm

-- | projects all the components out of the input term
-- TODO: rename to splitInput?
splitInputs :: SharedContext s -> Typ -> SharedTerm s -> IO [SharedTerm s]
splitInputs _sc TBool x = return [x]
splitInputs sc (TTuple ts) x =
    do xs <- mapM (\i -> scTupleSelector sc x i) [1 .. length ts]
       yss <- sequence (zipWith (splitInputs sc) ts xs)
       return (concat yss)
splitInputs _ (TVec _ TBool) x = return [x]
splitInputs sc (TVec n t) x =
    do nt <- scNat sc (fromIntegral n)
       idxs <- mapM (scNat sc . fromIntegral) [0 .. (n - 1)]
       ty <- scTyp sc t
       xs <- mapM (scAt sc nt ty x) idxs
       yss <- mapM (splitInputs sc t) xs
       return (concat yss)
splitInputs _ (TFun _ _) _ = error "splitInputs TFun: not a first-order type"
splitInputs sc (TRecord fields) x =
    do let (names, ts) = unzip fields
       xs <- mapM (scRecordSelect sc x) names
       yss <- sequence (zipWith (splitInputs sc) ts xs)
       return (concat yss)

----------------------------------------------------------------------

-- | Combines outputs into a data structure according to Typ
combineOutputs :: forall s. SharedContext s -> Typ -> [(Nat, SharedTerm s)]
               -> IO (SharedTerm s)
combineOutputs sc ty xs0 =
    do (z, ys) <- runStateT (go ty) xs0
       unless (null ys) (fail $ "combineOutputs: too many outputs: " ++
                                show (length ys) ++ " remaining")
       return z
    where
      pop :: StateT [(Nat, SharedTerm s)] IO (Nat, SharedTerm s)
      pop = do xs <- get
               case xs of
                 [] -> fail "combineOutputs: too few outputs"
                 y : ys -> put ys >> return y
      go :: Typ -> StateT [(Nat, SharedTerm s)] IO (SharedTerm s)
      go TBool =
          do (_, x) <- pop
             lift (scBv1ToBool sc x)
      go (TTuple ts) =
          do xs <- mapM go ts
             lift (scTuple sc xs)
      -- | SBV files may encode values of type '[n]Bool' in one of two
      -- ways: as a single n-bit word, or as a list of n 1-bit words.
      go (TVec n TBool) =
          do (n', x) <- pop
             case () of
               () | n' == fromIntegral n -> return x
                  | n' == 1 ->
                    do (sizes, xs) <- fmap unzip $ replicateM (fromIntegral n - 1) pop
                       unless (all (== 1) sizes) $
                         fail $ "combineOutputs: can't read SBV bitvector: " ++
                                show sizes ++ " doesn't equal " ++ show n
                       -- Append 1-bit words, lsb first (TODO: is this right?)
                       lift $ scAppendAll sc $ reverse [ (t, 1) | t <- x : xs ]
                  | otherwise -> fail $ "combineOutputs: can't read SBV bitvector from " ++
                                        show n' ++ " arguments"
      go (TVec n t) =
          do xs <- replicateM (fromIntegral n) (go t)
             ety <- lift (scTyp sc t)
             lift (scVector sc ety xs)
      go (TRecord fields) =
          do let (names, ts) = unzip fields
             xs <- mapM go ts
             lift (scRecord sc (Map.fromList (zip names xs)))
      go (TFun _ _) =
          fail "combineOutputs: not a first-order type"

----------------------------------------------------------------------

parseSBVPgm :: SharedContext s -> UnintMap s -> SBV.SBVPgm -> IO (SharedTerm s)
parseSBVPgm sc unint (SBV.SBVPgm (_version, irtype, revcmds, _vcs, _warnings, _uninterps)) =
    do let (TFun inTyp outTyp) = parseIRType irtype
       let cmds = reverse revcmds
       let (assigns, inputs, outputs) = partitionSBVCommands cmds
       let inSizes = [ size | SBVInput size _ <- inputs ]
       let inNodes = [ node | SBVInput _ node <- inputs ]
       -- putStrLn ("inTyp: " ++ show inTyp)
       --putStrLn ("outTyp: " ++ show outTyp)
       --putStrLn ("inSizes: " ++ show inSizes)
       unless (typSizes inTyp == inSizes) (fail "parseSBVPgm: input size mismatch")
       inputType <- scTyp sc inTyp
       inputVar <- scLocalVar sc 0
       inputTerms <- splitInputs sc inTyp inputVar
       --putStrLn "processing..."
       let nodes0 = Map.fromList (zip inNodes inputTerms)
       nodes <- foldM (parseSBVAssign sc unint) nodes0 assigns
       --putStrLn "collecting output..."
       outputTerms <- mapM (parseSBV sc nodes) outputs
       outputTerm <- combineOutputs sc outTyp outputTerms
       scLambda sc "x" inputType outputTerm

----------------------------------------------------------------------
-- New SharedContext operations; should eventually move to SharedTerm.hs.

-- | bv1ToBool :: bitvector 1 -> Bool
-- bv1ToBool x = bvAt 1 Bool 1 x (bv 1 0)
scBv1ToBool :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scBv1ToBool sc x =
    do n0 <- scNat sc 0
       n1 <- scNat sc 1
       b <- scBoolType sc
       bv <- scBvNat sc n1 n0
       scBvAt sc n1 b n1 x bv

-- | boolToBv1 :: Bool -> bitvector 1
scBoolToBv1 :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scBoolToBv1 sc x =
    do b <- scBoolType sc
       scSingle sc b x

-- see if it's the same error
scMultiMux :: SharedContext s -> Nat -> SharedTerm s
           -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scMultiMux sc iSize e i args = do
    vec <- scVector sc e args 
    w <- scNat sc iSize    
    m <- scNat sc (fromIntegral (length args))
    scBvAt sc m e w vec i

scAppendAll :: SharedContext s -> [(SharedTerm s, Integer)] -> IO (SharedTerm s)
scAppendAll _ [] = error "scAppendAll: unimplemented"
scAppendAll _ [(x, _)] = return x
scAppendAll sc ((x, size1) : xs) =
    do let size2 = sum (map snd xs)
       b <- scBoolType sc
       s1 <- scNat sc (fromInteger size1)
       s2 <- scNat sc (fromInteger size2)
       y <- scAppendAll sc xs
       scAppend sc b s1 s2 x y

typOf :: SBV.SBVPgm -> Typ
typOf (SBV.SBVPgm (_, irtype, _, _, _, _)) = parseIRType irtype

loadSBV :: FilePath -> IO SBV.SBVPgm
loadSBV = SBV.loadSBV
