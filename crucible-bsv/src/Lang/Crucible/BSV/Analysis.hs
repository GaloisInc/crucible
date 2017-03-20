{-# LANGUAGE BangPatterns #-}

-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.BSV.Analysis
-- Description      : This module performs compile-time analysis of BSV
--                    packages, such as type identifier resolution and typechecking.
-- Copyright        : (c) Galois, Inc 2017
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3


module Lang.Crucible.BSV.Analysis where

import           Data.Map (Map)
import qualified Data.Map as Map

import Lang.BSV.AST

type TypeEnv = Map Ident Typedef

typedefIdent :: Typedef -> Ident
typedefIdent (TypedefSynonym _ pt) = typedefName pt
typedefIdent (TypedefEnum _ nm) = nm
typedefIdent (TypedefStruct _ pt)  = typedefName pt
typedefIdent (TypedefUnion _ pt)  = typedefName pt

processTypedef :: Typedef -> TypeEnv -> TypeEnv
processTypedef td env =
   case Map.lookup nm env of
     Nothing -> Map.insert nm td env
     Just _ -> error $ "Multiple definitions of type constructor: " ++ nm
 where nm = typedefIdent td

processTypedefs :: [PackageStmt] -> TypeEnv -> TypeEnv
processTypedefs [] !env = env
processTypedefs (Typedef td _derives : ss) !env = -- FIXME handle derives?
  processTypedefs ss (processTypedef td env)
processTypedefs (_s : ss) !env =
  processTypedefs ss env

normalizeType :: TypeEnv -> Type -> Type
normalizeType env tp@(TypeCon nm args) =
  case Map.lookup nm env of
    Just (TypedefSynonym def proto) -> substTyVars proto args def
    Just _ -> tp
    Nothing -> error $ "Unknown type constructor: " ++ nm
normalizeType _env tp = tp

mapFst :: (a -> a') -> (a,b) -> (a',b)
mapFst f (x,y) = (f x, y)

substTyVars :: TypeProto
            -> [Type]
            -> Type
            -> Type
substTyVars proto args = sub
  where
    env = Map.fromList $ zip (map fst (typedefFormals proto)) args
    sub (TypeVar nm) = case Map.lookup nm env of
                         Just x  -> x
                         Nothing -> error $ "Unbound type variable: " ++ show nm
    sub (TypeSizeOf xs) = TypeSizeOf $! map sub xs
    sub (TypeCon nm xs) = TypeCon nm $! map sub xs
    sub (TypeFun fp)    = TypeFun
                            fp{ funResultType = sub (funResultType fp)
                              , funFormals    = map (mapFst sub) (funFormals fp)
                              }
    sub (TypeNat n)     = TypeNat n
    sub (TypeBit bs)    = TypeBit bs