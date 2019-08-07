{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE OverloadedStrings #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-unticked-promoted-constructors #-}

module Mir.GenericOps where

import qualified Data.ByteString as B
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Vector(Vector)
import qualified Data.Vector as V

import Control.Monad.Except(MonadError(..))
import Control.Lens((^.),(&),(%~), makeLenses)

import Mir.DefId
import Mir.Mir
import Mir.PP(fmt)
import Text.PrettyPrint.ANSI.Leijen(Doc,(<+>),text,pretty,vcat)

import GHC.Generics
import GHC.Stack

import Debug.Trace

--------------------------------------------------------------------------------------
-- For associated types pass

data ATDict = ATDict { atd_dict :: Map DefId (Substs -> Maybe Ty), atd_doc :: [Doc] }


data ATInfo = ATInfo {
     _atStart :: Integer    -- ^ index to start renaming
   , _atNum   :: Integer    -- ^ number of ATs to insert
   , _atDict  :: ATDict     -- ^ mapping for AssocTys
   , _atCol   :: Collection -- ^ collection
   , _atMeths :: Map MethName (FnSig,Trait)
       -- ^ declared types of trait methods, plus params and AssocTys from the trait
   }

makeLenses ''ATInfo

--------------------------------------------------------------------------------------
--
-- Generic operations over MIR AST
--

-- 
-- These syntax-directed operations are defined via GHC.Generics so
-- that they can automatically adapt to changes in the Mir AST.
--
-- 
class GenericOps a where

  -- | Crawl over the AST and rename the module that defIds live in.
  -- We need this because we are loading our own variant of the standard
  -- library, but all of the definitions there will have the wrong name.
  relocate :: a -> a
  default relocate :: (Generic a, GenericOps' (Rep a)) => a -> a
  relocate x = to (relocate' (from x))

  -- | Find all C-style Adts in the AST and convert them to Custom (CEnum _)
  markCStyle :: (Map DefId Adt,Collection) -> a -> a 
  default markCStyle :: (Generic a, GenericOps' (Rep a)) => (Map DefId Adt,Collection) -> a -> a
  markCStyle s x = to (markCStyle' s (from x))

  -- | Type variable substitution. Type variables are represented via indices.
  tySubst :: HasCallStack => Substs -> a -> a 
  default tySubst :: (Generic a, GenericOps' (Rep a), HasCallStack) => Substs -> a -> a
  tySubst s x = to (tySubst' s (from x))

  -- | Renaming for term variables
  replaceVar :: Var -> Var -> a -> a
  default replaceVar :: (Generic a, GenericOps' (Rep a)) => Var -> Var -> a -> a
  replaceVar o n x = to (replaceVar' o n (from x))

  -- | ???
  replaceLvalue :: Lvalue -> Lvalue -> a -> a
  default replaceLvalue :: (Generic a, GenericOps' (Rep a)) => Lvalue -> Lvalue -> a -> a
  replaceLvalue o n x = to (replaceLvalue' o n (from x))

  -- | count number of type params that appear (i.e. returns index of largest TyParam + 1)
  numTyParams :: a -> Integer
  default numTyParams ::  (Generic a, GenericOps' (Rep a)) => a -> Integer
  numTyParams x = numTyParams' (from x)

  -- | replace "TyProjection"s with their associated types
  -- and add additional arguments to type substitutions
  abstractATs :: (HasCallStack, MonadError String m) =>  ATInfo -> a -> m a 
  default abstractATs :: (Generic a, GenericOps' (Rep a), HasCallStack, MonadError String m) => ATInfo -> a -> m a
  abstractATs s x = to <$> (abstractATs' s (from x))

  -- | Update the list of predicates in an AST node
  modifyPreds :: RUPInfo -> a -> a
  default modifyPreds :: (Generic a, GenericOps' (Rep a)) => RUPInfo -> a -> a
  modifyPreds s x = to (modifyPreds' s (from x))


---------------------------------------------------------------------------------------------
-- "Unification"
-- Actually this is just "matching" as we only produce a substitution in one direction

combineMaps :: (MonadError String m) => Map Integer Ty -> Map Integer Ty -> m (Map Integer Ty)
combineMaps m1 m2 = Map.foldrWithKey go (return m2) m1 where
  -- go :: Integer -> Ty -> m (Map Integer Ty) -> m (Map Integer Ty)
  go k ty mres = do
    res <- mres
    case Map.lookup k res of
      Just ty' -> if ty == ty' then return res else throwError $ "Type mismatch: " ++ fmt ty ++ " and " ++ fmt ty'
      Nothing -> return (Map.insert k ty res)

-- | Try to match an implementation type against a trait type
-- TODO: do we also need to match the params/ats?
-- TODO: allow re-ordering of preds??
-- TODO: prune vars bound by the sig from the returned unifier
matchSig :: (MonadError String m) => FnSig -> FnSig -> m (Map Integer Ty)
matchSig (FnSig instArgs instRet [] [] _instATs)
         (FnSig genArgs  genRet  [] []  _genATs) = do
  m1 <- matchTys instArgs genArgs
  m2 <- matchTy  instRet  genRet
  combineMaps m1 m2
matchSig s1@(FnSig _instArgs _instRet _instParams _instPreds _instATs)
         s2@(FnSig _genArgs  _genRet  _genParams  _genPreds  _genATs) =
  error $ "TODO: extend matchSig to include params and/or preds"
        ++ "\n\t" ++ fmt s1
        ++ "\n\t" ++ fmt s2

matchPred :: (MonadError String m) => Predicate -> Predicate -> m (Map Integer Ty)
matchPred (TraitPredicate d1 ss1) (TraitPredicate d2 ss2)
  | d1 == d2
  = matchSubsts ss1 ss2
matchPred (TraitProjection lhs1 ty1) (TraitProjection lhs2 ty2)
  = do m1 <- matchTy lhs1 lhs2
       m2 <- matchTy ty1 ty2
       combineMaps m1 m2
matchPred p1 p2 = throwError $ "Cannot match predicates " ++ fmt p1 ++ " and " ++ fmt p2
       
-- | Try to match an implementation type (first argument) against a trait type (second argument)
-- If they succeed, produce a substitution -- a mapping from type params to types
-- Neither type should include TyProjections. They should have already been abstracted out
-- using [abstractAssociatedTypes]
matchTy :: (MonadError String m) => Ty -> Ty -> m (Map Integer Ty)
matchTy ty (TyParam i) 
  = return (Map.insert i ty Map.empty)
matchTy (TyTuple instTys) (TyTuple genTys) =
  matchTys instTys genTys
matchTy (TySlice t1) (TySlice t2) = matchTy t1 t2
matchTy (TyArray t1 i1) (TyArray t2 i2) | i1 == i2 = matchTy t1 t2
matchTy (TyRef t1 m1) (TyRef t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyAdt d1 s1) (TyAdt d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyFnDef d1 s1) (TyFnDef d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyClosure d1 s1) (TyClosure d2 s2) | d1 == d2 =  matchSubsts s1 s2
matchTy (TyFnPtr sig1) (TyFnPtr sig2) = matchSig sig1 sig2
matchTy (TyRawPtr t1 m1)(TyRawPtr t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyDowncast t1 i1) (TyDowncast t2 i2) | i1 == i2 = matchTy t1 t2
matchTy inst arg
  | inst == arg
  = return Map.empty
matchTy ty1 ty2@(TyProjection _d2 _s2) = throwError $
  "BUG: found " ++ fmt ty2 ++ " when trying to match " ++ fmt ty1
matchTy ty1 ty2 = throwError $ "Cannot match " ++ fmt ty1 ++ " with " ++ fmt ty2

matchSubsts :: (MonadError String m) => Substs -> Substs -> m (Map Integer Ty)
matchSubsts (Substs tys1) (Substs tys2) = matchTys tys1 tys2

matchTys :: (MonadError String m) => [Ty] -> [Ty] -> m (Map Integer Ty)
matchTys = matchList matchTy

matchList :: (MonadError String m) => (a -> a -> m (Map Integer Ty)) -> [a] -> [a] -> m (Map Integer Ty)
matchList _f [] [] = return Map.empty
matchList f (t1:instTys) (t2:genTys) = do
  m1 <- f t1 t2
  m2 <- matchList f instTys genTys
  combineMaps m1 m2
matchList _f _ _ = throwError $ "matchList: lengths of lists differ"  


mkSubsts :: Map Integer Ty -> Substs
mkSubsts m = Substs (map g [0 ..]) where
  g i = case Map.lookup i m of
          Just ty -> ty
          Nothing -> TyParam i


--------------------------------------------------------------------------------------
-- ** abstractATs

{-
   We need this operation to turn associated types into additional type arguments
   in *trait definitions* and in polymorphic methods.

   For example, consider this Rust trait:

   pub trait Index<Idx> where
    Idx: ?Sized, 
   {
    type Output: ?Sized;
    fn index(&self, index: Idx) -> &Self::Output;
   }

   In MIR it will look like this, where Self is "TyParam 0"
   and other parameters follow.

   Trait "Index"
         [TraitType "Output",
          TraitMethod "index" (&0,&1) -> &Output<0,1>]

   This operation converts the Output<0,1> type so that it
   is an additional type parameter to the trait method.

   Trait "Index"
         [TraitType "Output",
          TraitMethod "index" (&0,&1) -> &2]

   Implementations of this trait will then unify this
   parameter just as the others.

   NOTE: associated types must go between the trait parameters and
   the method parameters. So we need to rename any method parameters
   starting at a particular index (start) and shift them over by the
   number of ATs that we add.

-}





lookupATDict :: HasCallStack => ATDict -> AssocTy -> Maybe Ty
lookupATDict dict (d, ss) 
    | Just f <- atd_dict dict Map.!? d
    = f ss
    | otherwise
    = Nothing

instance Semigroup ATDict where
  (<>) = unionATDict
instance Monoid ATDict where
  mempty = emptyATDict
  mappend = ((<>))

emptyATDict :: ATDict
emptyATDict = ATDict { atd_dict = Map.empty , atd_doc = [] }

insertATDict :: HasCallStack => AssocTy -> Ty -> ATDict -> ATDict
insertATDict at ty d = d <> (concSingletonATDict at ty)

concSingletonATDict :: HasCallStack => AssocTy -> Ty -> ATDict
concSingletonATDict (did,ss) ty =
  ATDict { atd_dict = Map.singleton did (\ss' -> case matchSubsts ss' ss of
                                            Right m -> Just $ tySubst (mkSubsts m) ty
                                            Left _e -> Nothing)
         , atd_doc  = [pretty did <+> pretty ss <+> text "=" <+> pretty ty]
         }

singletonATDict :: HasCallStack => DefId -> (Substs -> Maybe Ty) -> ATDict
singletonATDict did f =
  ATDict { atd_dict = Map.singleton did f
         , atd_doc  = [pretty did <+> "<abstract>"]
         }

extendATDict :: HasCallStack => DefId -> (Substs -> Maybe Ty) -> ATDict -> ATDict
extendATDict d f dict =
   dict <> (singletonATDict d f)

unionATDict :: HasCallStack => ATDict -> ATDict -> ATDict
unionATDict d1 d2 = ATDict
  { atd_dict = 
      Map.unionWith (\f1 f2 ss ->
                        case f1 ss of Just ty -> Just ty
                                      Nothing -> f2 ss)
    (atd_dict d1) (atd_dict d2)
    ,  atd_doc = (atd_doc d1 <> atd_doc d2)
  }
  
ppATDict :: ATDict -> Doc
ppATDict d = vcat (atd_doc d)




-- | Special case for Ty
abstractATs_Ty :: (HasCallStack, MonadError String m) => ATInfo -> Ty -> m Ty
abstractATs_Ty ati (TyParam i)
    | i < (ati^.atStart) = return $ TyParam i          -- trait param,  leave alone
    | otherwise = return $ TyParam (i + (ati^.atNum))  -- method param, shift over
    
abstractATs_Ty ati ty@(TyProjection d substs)
    -- hacky case for FnOnce::Output
    | d == (textId "::ops[0]::function[0]::FnOnce[0]::Output[0]")    
    = TyProjection d <$> abstractATs ati substs
    
    -- associated type, replace with new param    
    | Just nty <- lookupATDict (ati^.atDict) (d,substs)
    = return nty
    
    -- try translating the substs
    | otherwise = do
       substs' <- abstractATs ati substs
       case lookupATDict (ati^.atDict) (d,substs') of
         Just nty -> return nty
         Nothing ->
           -- return ty
           -- throw error for unknown Projections alone
           throwError $ fmt ty ++ " with unknown translation.\n"
                     ++ "Dict is\n" ++ show (ppATDict (ati^.atDict))
abstractATs_Ty s ty = (to <$> (abstractATs' s (from ty)))

-- Add additional args to the substs for traits with atys
abstractATs_Predicate :: (HasCallStack, MonadError String m) => ATInfo -> Predicate -> m Predicate
abstractATs_Predicate ati (TraitPredicate tn ss) 
    | Just tr <- (ati^.atCol.traits) Map.!? tn
    = do let ats  = map (\(n,ss') -> TyProjection n ss') (tr^.traitAssocTys)
         ss1  <- abstractATs ati ss
         let ats' = tySubst ss1 ats
         ss2  <- mapM (abstractATs ati) ats'
         return $ TraitPredicate tn (ss1 <> Substs ss2)
    | otherwise
    = throwError $ "BUG: Found trait " ++ fmt tn ++ " with no info in collection."
abstractATs_Predicate ati (TraitProjection ty1 ty2)
    = TraitProjection <$> (abstractATs ati ty1) <*> (abstractATs ati ty2)
--    = pure $ TraitProjection ty1 ty2
abstractATs_Predicate _ati UnknownPredicate = throwError "BUG: found UnknownPredicate"

-- Add extra arguments for associated types to a const function call
-- NOTE: is this complete?
abstractATs_ConstVal :: (HasCallStack, MonadError String m) => ATInfo -> ConstVal -> m ConstVal
abstractATs_ConstVal ati (ConstFunction defid funsubst)
  | Just (fs,mt) <- fnType ati defid
  = do
       -- remove any ats from the current substs
       funsubst1 <- abstractATs ati funsubst

       -- add ATs from trait (if any) to the appropriate place
       -- in the middle of the funsubst
       funsubst2 <- case mt of
                     Nothing -> pure funsubst1
                     Just tr -> do
                       let tats  = tySubst funsubst1 (tr^.traitAssocTys)
                       let j     = length $ tr^.traitParams
                       tats' <- lookupATs ati tats
                       return $
                         insertAtSubsts tats' j funsubst1
                         
       -- find any ats for the method and instantiate them 
       let ats       = tySubst funsubst1 (fs^.fsassoc_tys)
       
       -- replace ats with their definition
       ats'      <- lookupATs ati ats

       -- add method ats to the end of the function subst
       let hsubst    = funsubst2 <> ats'
       
       return $ ConstFunction defid hsubst
         
abstractATs_ConstVal ati val = to <$> (abstractATs' ati (from val))

abstractATs_FnSig :: (HasCallStack, MonadError String m) => ATInfo -> FnSig -> m FnSig
abstractATs_FnSig ati (FnSig args ret gens preds atys) = do
  let ati' = ati & atDict %~ mappend (mkAssocTyMap (toInteger (length gens)) atys)
  preds' <- abstractATs ati' preds
  args'  <- abstractATs ati' args
  ret'   <- abstractATs ati' ret
  return $ FnSig args'
        ret' 
        (gens ++ map toParam atys)
        preds' 
        atys
      


-- | Convert an associated type into a Mir type parameter
toParam :: AssocTy -> Param
toParam (did,_substs) = Param (idText did)  -- do we need to include substs?

-- | Create a mapping for associated types to type parameters, starting at index k
-- For traits, k should be == length traitParams
mkAssocTyMap :: Integer -> [AssocTy] -> ATDict
mkAssocTyMap k assocs =
  foldl (\m ((a,ss),ty) ->
           let ati = ATInfo 0 0 m (error "no col") (error "only types")
               ss' = case abstractATs ati ss of
                       Left err -> trace ("WARNING " ++ err) ss
                       Right ss2 -> ss2
           in
             insertATDict (a,ss') ty m) mempty zips where
    zips = zip assocs (map TyParam [k ..])

lookupATs :: (MonadError String m) => ATInfo -> [AssocTy] -> m Substs
lookupATs ati ats =
  Substs <$> abstractATs ati (map (\(a,b) -> TyProjection a b) ats)

-- | Find the type of a function
-- so that we know what new type arguments to add
fnType :: ATInfo -> MethName -> Maybe (FnSig, Maybe Trait)
fnType ati mn 

  -- normal function 
  | Just fn <- (ati^.atCol.functions) Map.!? mn
  = Just (fn^.fsig, Nothing)

  -- trait method
  | Just (s, tr) <- (ati^.atMeths) Map.!? mn
  = Just (s, Just tr)
  
  | otherwise
  = Nothing




--------------------------------------------------------------------------------------

-- ** markCStyle

-- A CStyle ADT is one that is an enumeration of numeric valued options
-- containing no data
isCStyle :: Adt -> Bool
isCStyle (Adt _ variants) = all isConst variants where
    isConst (Variant _ _ [] ConstKind) = True
    isConst _ = False


-- | For ADTs that are represented as CEnums, we need to find the actual numbers that we
-- use to represent each of the constructors.
adtIndices :: Adt -> Collection -> [Integer]
adtIndices (Adt _aname vars) col = map go vars where
 go (Variant _vname (Explicit did) _fields _knd) =
    case Map.lookup did (_functions col) of
      Just fn ->
        case fn^.fbody.mblocks of
          [ BasicBlock _info (BasicBlockData [Assign _lhs (Use (OpConstant (Constant _ty (Value (ConstInt i))))) _loc] _term) ] ->
            fromIntegerLit i
            
          _ -> error "CEnum should only have one basic block"
          
      Nothing -> error "cannot find CEnum value"
 go (Variant _vname (Relative i) _fields _kind) = toInteger i    --- TODO: check this

markCStyleTy :: (Map DefId Adt,Collection) -> Ty -> Ty
markCStyleTy (ads,s) (TyAdt n ps)  | Just adt <- Map.lookup n ads =
   if ps == Substs [] then
      TyCustom (CEnum n (adtIndices adt s))
   else
      error "Cannot have params to C-style enum!"
markCStyleTy s ty = to (markCStyle' s (from ty))

--------------------------------------------------------------------------------------
-- ** modifyPreds 

--- Annoyingly, we don't use the newtype for the list of predicates
-- So we have to implement this operation in all of the containing types

-- filter function for predicates
type RUPInfo = TraitName -> Bool

filterPreds :: RUPInfo -> [Predicate] -> [Predicate]
filterPreds f =
  filter knownPred where
     knownPred :: Predicate -> Bool
     knownPred (TraitPredicate did _) = f did
     knownPred (TraitProjection {})   = True
     knownPred UnknownPredicate       = False


modifyPreds_FnSig :: RUPInfo -> FnSig -> FnSig
modifyPreds_FnSig f fs = fs & fspredicates %~ filterPreds f
                            & fsarg_tys    %~ modifyPreds f
                            & fsreturn_ty  %~ modifyPreds f
                            
modifyPreds_Trait :: RUPInfo -> Trait -> Trait
modifyPreds_Trait f fs = fs & traitPredicates %~ filterPreds f
                            & traitItems      %~ modifyPreds f
                            & traitSupers     %~ filter f

modifyPreds_TraitImpl :: RUPInfo -> TraitImpl -> TraitImpl
modifyPreds_TraitImpl f fs = fs & tiPredicates %~ filterPreds f
                                & tiItems      %~ modifyPreds f
                                & tiTraitRef   %~ modifyPreds f 

modifyPreds_TraitImplItem :: RUPInfo -> TraitImplItem -> TraitImplItem
modifyPreds_TraitImplItem f fs@(TraitImplMethod {}) = fs & tiiPredicates %~ filterPreds f
                                                         & tiiSignature  %~ modifyPreds f
modifyPreds_TraitImplItem f fs@(TraitImplType {}) = fs & tiiPredicates %~ filterPreds f
                                                       & tiiType       %~ modifyPreds f
                                                       

--------------------------------------------------------------------------------------

-- ** Overridden instances for Mir AST types

instance GenericOps ConstVal where
  abstractATs = abstractATs_ConstVal
instance GenericOps Predicate where
  abstractATs = abstractATs_Predicate
                                                       
-- special case for DefIds
instance GenericOps DefId where
  relocate          = id
  markCStyle _      = id
  tySubst    _      = id
  replaceVar _ _    = id
  replaceLvalue _ _ = id
  numTyParams _     = 0
  abstractATs _     = pure
  modifyPreds _     = id



-- | increment all free variables in the range of the substitution by n
lift :: Int -> Substs -> Substs
lift 0 ss = ss
lift n ss = takeSubsts n (incN 0) <> tySubst (incN n) ss  where


-- | An infinite substitution that increments all type vars by n
incN :: Int -> Substs
incN n = Substs (TyParam . toInteger <$> [n ..])

-- special case for Ty
instance GenericOps Ty where

  -- see above
  markCStyle = markCStyleTy
  abstractATs = abstractATs_Ty
  
  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | Just x <- safeNth (fromInteger i) substs  = x
     | otherwise    = error $
           "BUG in substitution: Indexing at " ++ show i ++ "  from subst " ++ fmt (Substs substs)
  tySubst substs ty = to (tySubst' substs (from ty))

  -- Count ty params
  numTyParams (TyParam x) = x + 1
  numTyParams ty = numTyParams' (from ty)



-- special case for Vars
instance GenericOps Var where
  replaceVar old new v = if _varname v == _varname old then new else v

  replaceLvalue (Local old) (Local new) v = replaceVar old new v
  replaceLvalue _ _ v = v

-- special case for LValue
instance GenericOps Lvalue where
    replaceLvalue old new v = fromMaybe v (repl_lv v)
      where
        repl_lv :: Lvalue -> Maybe Lvalue -- some light unification
        repl_lv v0 =
          case v0 of
            LProjection (LvalueProjection lb k)
              | Just ans <- repl_lv lb -> Just $ LProjection (LvalueProjection ans k)
            _ | v == old -> Just new
            _ -> Nothing

-- ** derived instances for MIR AST types
-- If new types are added to the AST, then new derived instances need to be added here

instance GenericOps BaseSize
instance GenericOps FloatKind
instance GenericOps FnSig where
  modifyPreds = modifyPreds_FnSig
  abstractATs = abstractATs_FnSig
  
  tySubst substs (FnSig args ret params preds atys) =
      (FnSig (tySubst ss args) (tySubst ss ret) params (tySubst ss preds) (tySubst ss atys)) where
         ss = lift (length params) substs

  
instance GenericOps Adt
instance GenericOps VariantDiscr
instance GenericOps CtorKind
instance GenericOps Variant
instance GenericOps Field
instance GenericOps CustomTy
instance GenericOps Mutability
instance GenericOps Collection
instance GenericOps Param
instance GenericOps Fn
instance GenericOps MirBody
instance GenericOps BasicBlock
instance GenericOps BasicBlockData
instance GenericOps Statement
instance GenericOps Rvalue
instance GenericOps AdtAg
instance GenericOps Terminator
instance GenericOps Operand
instance GenericOps Constant
instance GenericOps LvalueProjection
instance GenericOps Lvpelem
instance GenericOps NullOp
instance GenericOps BorrowKind
instance GenericOps UnOp
instance GenericOps BinOp
instance GenericOps CastKind
instance GenericOps Literal
instance GenericOps IntLit
instance GenericOps FloatLit
instance GenericOps AggregateKind
instance GenericOps CustomAggregate
instance GenericOps Trait where
  modifyPreds = modifyPreds_Trait
instance GenericOps TraitItem
instance GenericOps TraitRef
instance GenericOps TraitImpl where
  modifyPreds = modifyPreds_TraitImpl
instance GenericOps TraitImplItem where
  modifyPreds = modifyPreds_TraitImplItem
instance GenericOps Promoted
instance GenericOps Static

-- instances for newtypes
-- we need the deriving strategy 'anyclass' to disambiguate 
-- from generalized newtype deriving
-- either version would work, but GHC doesn't know that and gives a warning
instance GenericOps Substs
instance GenericOps Params
instance GenericOps Predicates

-- *** Instances for Prelude types                 

instance GenericOps Int     where
   relocate   = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const pure
   modifyPreds = const id
instance GenericOps Integer where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0 
   abstractATs = const pure  
   modifyPreds = const id   
instance GenericOps Char    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const pure
   modifyPreds = const id   
instance GenericOps Bool    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const pure
   modifyPreds = const id
   
instance GenericOps Text    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const pure
   modifyPreds = const id
   
instance GenericOps B.ByteString where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id   
   numTyParams _ = 0
   abstractATs = const pure
   modifyPreds = const id
   
instance GenericOps b => GenericOps (Map.Map a b) where
   relocate          = Map.map relocate 
   markCStyle s      = Map.map (markCStyle s)
   tySubst s         = Map.map (tySubst s)
   replaceVar o n    = Map.map (replaceVar o n)
   replaceLvalue o n = Map.map (replaceLvalue o n)   
   numTyParams m     = Map.foldr (max . numTyParams) 0 m
   abstractATs i     = mapM (abstractATs i)
   modifyPreds i     = Map.map (modifyPreds i)
   
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)
instance GenericOps a => GenericOps (Vector a) where
   relocate          = V.map relocate 
   markCStyle s      = V.map (markCStyle s)
   tySubst s         = V.map (tySubst s)
   replaceVar o n    = V.map (replaceVar o n)
   replaceLvalue o n = V.map (replaceLvalue o n)   
   numTyParams m     = V.foldr (max . numTyParams) 0 m
   abstractATs i     = mapM (abstractATs i)
   modifyPreds i     = V.map (modifyPreds i)
  
   
replaceList :: GenericOps a => [(Lvalue, Lvalue)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replaceLvalue old new a




--------------------------------------------------------------------------------------
-- ** Generic programming plumbing

class GenericOps' f where
  relocate'      :: f p -> f p
  markCStyle'    :: (Map.Map DefId Adt,Collection) -> f p -> f p
  tySubst'       :: Substs -> f p -> f p 
  replaceVar'    :: Var -> Var -> f p -> f p
  replaceLvalue' :: Lvalue -> Lvalue -> f p -> f p
  numTyParams'   :: f p -> Integer
  abstractATs'   :: (MonadError String m) => ATInfo -> f p -> m (f p)
  modifyPreds'   :: RUPInfo -> f p -> f p
  
instance GenericOps' V1 where
  relocate' _x      = error "impossible: this is a void type"
  markCStyle' _ _x  = error "impossible: this is a void type"
  tySubst' _ _      = error "impossible: this is a void type"
  replaceVar' _ _ _ = error "impossible: this is a void type"
  replaceLvalue' _ _ _ = error "impossible: this is a void type"
  numTyParams' _    = error "impossible: this is a void type"
  abstractATs' _  = error "impossible: this is a void type"
  modifyPreds' _  = error "impossible: this is a void type"

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :+: g) where
  relocate'     (L1 x) = L1 (relocate' x)
  relocate'     (R1 x) = R1 (relocate' x)
  markCStyle' s (L1 x) = L1 (markCStyle' s x)
  markCStyle' s (R1 x) = R1 (markCStyle' s x)
  tySubst'    s (L1 x) = L1 (tySubst' s x)
  tySubst'    s (R1 x) = R1 (tySubst' s x)
  replaceVar' o n (L1 x) = L1 (replaceVar' o n x)
  replaceVar' o n (R1 x) = R1 (replaceVar' o n x)
  replaceLvalue' o n (L1 x) = L1 (replaceLvalue' o n x)
  replaceLvalue' o n (R1 x) = R1 (replaceLvalue' o n x)
  numTyParams' (L1 x) = numTyParams' x
  numTyParams' (R1 x) = numTyParams' x
  abstractATs' s (L1 x) = L1 <$> (abstractATs' s x)
  abstractATs' s (R1 x) = R1 <$> (abstractATs' s x)
  modifyPreds' s (L1 x) = L1 (modifyPreds' s x)
  modifyPreds' s (R1 x) = R1 (modifyPreds' s x)

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  relocate'       (x :*: y) = relocate'   x     :*: relocate' y
  markCStyle' s   (x :*: y) = markCStyle'   s x :*: markCStyle' s y
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  replaceVar' o n (x :*: y) = replaceVar' o n x :*: replaceVar' o n y
  replaceLvalue' o n (x :*: y) = replaceLvalue' o n x :*: replaceLvalue' o n y
  numTyParams' (x :*: y)    = max (numTyParams' x) (numTyParams' y)
  abstractATs' s (x :*: y) = (:*:) <$> abstractATs' s x <*>  abstractATs' s y
  modifyPreds' s (x :*: y) = modifyPreds' s x :*: modifyPreds' s y  

instance (GenericOps c) => GenericOps' (K1 i c) where
  relocate'     (K1 x) = K1 (relocate x)
  markCStyle' s (K1 x) = K1 (markCStyle s x)
  tySubst'    s (K1 x) = K1 (tySubst s x)
  replaceVar' o n (K1 x) = K1 (replaceVar o n x)
  replaceLvalue' o n (K1 x) = K1 (replaceLvalue o n x)  
  numTyParams' (K1 x)  = numTyParams x
  abstractATs'    s (K1 x) = K1 <$> (abstractATs s x)
  modifyPreds'    s (K1 x) = K1 (modifyPreds s x)
  
instance (GenericOps' f) => GenericOps' (M1 i t f) where
  relocate'     (M1 x) = M1 (relocate' x)
  markCStyle' s (M1 x) = M1 (markCStyle' s x)
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  replaceVar' o n (M1 x) = M1 (replaceVar' o n x)
  replaceLvalue' o n (M1 x) = M1 (replaceLvalue' o n x)
  numTyParams' (M1 x)  = numTyParams' x
  abstractATs' s (M1 x) = M1 <$> (abstractATs' s x)
  modifyPreds' s (M1 x) = M1 (modifyPreds' s x)  
  
instance (GenericOps' U1) where
  relocate'      U1 = U1
  markCStyle' _s U1 = U1
  tySubst'    _s U1 = U1
  replaceVar' _ _ U1 = U1
  replaceLvalue' _ _ U1 = U1
  numTyParams' U1 = 0
  abstractATs' _s U1 = pure U1
  modifyPreds' _s U1 = U1  
