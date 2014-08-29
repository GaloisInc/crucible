{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : jhendrix
-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.SBVModel where

import Data.Binary
import Data.List(sortBy)
import Control.Monad (liftM, liftM2, liftM3)
import System.IO (openBinaryFile, IOMode(..), hClose)
import qualified Data.ByteString.Lazy as B

-- Auxiliary Cryptol types
type Major = Int
type Minor = Int
data Version = Version Major Minor deriving Show
type TyCon = String
type Name = String
data Loc = Loc String Int{-line-} Int{-col-}
         | LocPrim String
         | LocDefault String
         | LocExpr
         | LocInternal
         | LocNone
         deriving Show
data Scheme a = Scheme [String] [a] [Predicate a] (Type a) deriving Show

schemeType :: Scheme a -> Type a
schemeType (Scheme _ _ _ t) = t

embedScheme :: Type a -> Scheme a
embedScheme t = Scheme [] [] [] t
data Predicate a
    = PredEq    (Type a) (Type a) (Maybe (Predicate a)) [Loc]
    | PredSubst a (Type a)                              [Loc]
    | PredGrEq  (Type a) (Type a)                       [Loc]
    | PredFin (Type a)                                  [Loc]
    | PredImplied (Predicate a)
    deriving Show
data Type a
    = TVar a
    | TInt Integer
    | TApp TyCon [Type a]
    | TRecord [(Name, Scheme a)]
    deriving Show
type IRTyVar  = TyVar Int
data TyVar a
  = TyVar { tyvarName :: a, tyvarKind :: Kind
          , tyvarIgnorable :: Bool, tyvarDefaultable :: Bool }
   deriving Show
type IRType   = Type IRTyVar
data Kind
    = KStar
    | KSize
    | KShape
    deriving Show
-- SBV programs
type Size      = Integer
type GroundVal = Integer
type NodeId    = Int
data SBV = SBV !Size !(Either GroundVal NodeId) deriving Show
data SBVCommand = Decl   CtrlPath !SBV (Maybe SBVExpr)
                | Output !SBV
                deriving Show
data Operator = BVAdd | BVSub | BVMul | BVDiv Loc | BVMod Loc | BVPow
              | BVIte
              | BVShl | BVShr | BVRol | BVRor
              | BVExt !Integer !Integer  -- hi lo
              | BVAnd | BVOr | BVXor | BVNot
              | BVEq  | BVGeq | BVLeq | BVGt | BVLt
              | BVApp   -- append
              -- following is not essential, but simplifies lookups
              | BVLkUp !Integer !Integer -- index size, result size
              -- Uninterpreted constants
              | BVUnint Loc [(String, String)] (String, IRType) -- loc, code-gen info, name/type
              deriving Show
data SBVExpr = SBVAtom !SBV
             | SBVApp  !Operator ![SBV]
             deriving Show
type CtrlPath = [Either SBV SBV]
type VC = ( CtrlPath    -- path to the VC
          , SBVExpr     -- stipulated trap; need to prove this expr is not true
          , String)     -- associated error message
data SBVPgm = SBVPgm (Version, IRType, [SBVCommand], [VC]
                     , [String] -- warnings
                     , [((String, Loc), IRType, [(String, String)])] -- uninterpeted functions and code
                     )
            deriving Show
-- make it an instance of Binary
instance Binary Loc where
  put (Loc s i j)    = putWord8 0 >> put s >> put i >> put j
  put (LocPrim s)    = putWord8 1 >> put s
  put (LocDefault s) = putWord8 2 >> put s
  put LocExpr        = putWord8 3
  put LocInternal    = putWord8 4
  put LocNone        = putWord8 5
  get = do tag <- getWord8
           case tag of
             0 -> liftM3 Loc get get get
             1 -> liftM LocPrim get
             2 -> liftM LocDefault get
             3 -> return LocExpr
             4 -> return LocInternal
             5 -> return LocNone
             n -> error $ "Binary.Loc: " ++ show n
instance Binary Version where
   put (Version ma mi) = put ma >> put mi
   get = liftM2 Version get get
instance Binary SBVPgm where
  put (SBVPgm cmds) = put cmds
  get = liftM SBVPgm get

-- only monomorphic types supported below
sortUnder :: (Ord b) => (a -> b) -> [a] -> [a]
sortUnder f = sortBy (\a b -> compare (f a) (f b))

instance Binary IRType where
  put (TInt i)      = putWord8 0 >> put i
  put (TApp t ts)   = putWord8 1 >> put t >> put ts
  put (TRecord nss) = putWord8 2 >> put [(n, schemeType s) | (n, s) <- sortUnder fst nss]
  put TVar{} = error $ "internal: put not defined on TVar"
  get = do tag <- getWord8
           case tag of
             0 -> liftM TInt get
             1 -> liftM2 TApp get get
             2 -> do nts <- get
                     return (TRecord [(n, embedScheme t) | (n, t) <- nts])
             n -> error $ "Binary.IRType: " ++ show n
instance Binary SBV where
  put (SBV i esn) = put i >> put esn
  get             = liftM2 SBV get get
instance Binary SBVCommand where
  put (Decl path v mbe) = putWord8 0 >> put path >> put v >> put mbe
  put (Output v)        = putWord8 1 >> put v
  get = do tag <- getWord8
           case tag of
             0 -> liftM3 Decl get get get
             1 -> liftM  Output get
             n -> error $ "Binary.SBVCommand: " ++ show n
instance Binary SBVExpr where
  put (SBVAtom s)   = putWord8 0 >> put s
  put (SBVApp o es) = putWord8 1 >> put o >> put es
  get = do tag <- getWord8
           case tag of
             0 -> liftM  SBVAtom get
             1 -> liftM2 SBVApp  get get
             n -> error $ "Binary.SBVExpr: " ++ show n
instance Binary Operator where
   put BVAdd = putWord8 0
   put BVSub = putWord8 1
   put BVMul = putWord8 2
   put (BVDiv l) = putWord8 3 >> put l
   put (BVMod l) = putWord8 4 >> put l
   put BVPow = putWord8 5
   put BVIte = putWord8 6
   put BVShl = putWord8 7
   put BVShr = putWord8 8
   put BVRol = putWord8 9
   put BVRor = putWord8 10
   put (BVExt hi lo) = putWord8 11 >> put hi >> put lo
   put BVAnd = putWord8 12
   put BVOr  = putWord8 13
   put BVXor = putWord8 14
   put BVNot = putWord8 15
   put BVEq  = putWord8 16
   put BVGeq = putWord8 17
   put BVLeq = putWord8 18
   put BVGt  = putWord8 19
   put BVLt  = putWord8 20
   put BVApp = putWord8 21
   put (BVLkUp i r) = putWord8 22 >> put i >> put r
   put (BVUnint l cgs nt) = putWord8 23 >> put l >> put cgs >> put nt
   get = do tag <- getWord8
            case tag of
              0 -> return BVAdd
              1 -> return BVSub
              2 -> return BVMul
              3 -> liftM BVDiv get
              4 -> liftM BVMod get
              5 -> return BVPow
              6 -> return BVIte
              7 -> return BVShl
              8 -> return BVShr
              9 -> return BVRol
              10 -> return BVRor
              11 -> liftM2 BVExt get get
              12 -> return BVAnd
              13 -> return BVOr
              14 -> return BVXor
              15 -> return BVNot
              16 -> return BVEq
              17 -> return BVGeq
              18 -> return BVLeq
              19 -> return BVGt
              20 -> return BVLt
              21 -> return BVApp
              22 -> liftM2 BVLkUp get get
              23 -> liftM3 BVUnint get get get
              n  -> error $ "Binary.Operator: " ++ show n
loadSBV :: FilePath -> IO SBVPgm
loadSBV f = do
        h <- openBinaryFile f ReadMode
        pgm <- B.hGetContents h
        B.length pgm `seq` hClose h   -- oh, the horror..
        return (decode pgm)
