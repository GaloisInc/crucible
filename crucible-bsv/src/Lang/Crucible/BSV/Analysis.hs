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

initialTypeEnv :: TypeEnv
initialTypeEnv = Map.fromList $
  map f
  [ "Vector"
  , "Integer"
  , "Bit"
  , "Int"
  , "UInt"
  , "Action"
  , "Array"
  ]
 where f x = (x, TypedefPrim x)

typedefIdent :: Typedef -> Ident
typedefIdent (TypedefSynonym _ pt) = typedefName pt
typedefIdent (TypedefEnum _ nm) = nm
typedefIdent (TypedefStruct _ pt)  = typedefName pt
typedefIdent (TypedefUnion _ pt)  = typedefName pt
typedefIdent (TypedefPrim nm)     = nm

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
  case applyTypes env nm args of
    Just tp' -> normalizeType env tp'
    Nothing  -> tp
normalizeType env tp@(TypeVar nm) =
  case applyTypes env nm [] of
    Just tp' -> normalizeType env tp'
    Nothing  -> tp
normalizeType _env tp = tp


applyTypes :: TypeEnv
           -> Ident
           -> [Type]
           -> Maybe Type
applyTypes env nm args =
  case Map.lookup nm env of
    Just (TypedefSynonym def proto) -> Just $! substTyVars proto args def
    Just _ -> Nothing
    Nothing -> error $ "Unknown type constructor: " ++ nm

mapFst :: (a -> a') -> (a,b) -> (a',b)
mapFst f (x,y) = (f x, y)

substTyVars :: TypeProto
            -> [Type]
            -> Type
            -> Type
substTyVars proto args =
    if length args == length (typedefFormals proto)
      then sub
      else error $ unwords ["Type consturctor argument mismatch", show proto, show args]
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
