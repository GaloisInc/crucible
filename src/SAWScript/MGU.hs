{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.MGU where

import           SAWScript.Unify.Fix(Mu(..),(:+:)(..))
import qualified SAWScript.AST as A
import SAWScript.AST (Bind)

import           Data.Graph.SCC(stronglyConnComp)
import           Data.Graph (SCC(..))
import Control.Applicative

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Data.Function (on)
import Data.List (sortBy,intercalate)
import Data.Maybe (mapMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.PrettyPrint.HughesPJ as PP

-- Types {{{

-- Type Level

type Name = String

data Type
  = TyCon TyCon [Type]
  | TyRecord (M.Map Name Type)
  | TyVar TyVar
 deriving (Eq,Show) 

data TyVar
  = FreeVar Integer
  | BoundVar Name
 deriving (Eq,Ord,Show) 

data TyCon
 = TupleCon Integer
 | ArrayCon
 | FunCon
 | StringCon
 | BoolCon
 | ZCon
 | NumCon Integer
 | BlockCon
 | ContextCon A.Context
 | AbstractCon String
 deriving (Eq,Show) 

data Schema = Forall [Name] Type deriving (Show)


-- }}}

-- Pretty Printer {{{

pShow :: PrettyPrint a => a -> String
pShow = show . pretty True

class PrettyPrint p where
  -- Bool indicates whether term should be parenthesized, eg. if rendering is space separated.
  pretty :: Bool -> p -> PP.Doc

instance PrettyPrint Schema where
  pretty _ (Forall ns t) = case ns of
    [] -> pretty False t
    _  -> PP.braces (commaSepAll $ map PP.text ns) PP.<+> pretty False t

instance PrettyPrint Type where
  pretty par t@(TyCon tc ts) = case (tc,ts) of
    (_,[])                 -> pretty par tc
    (TupleCon n,_)         -> PP.parens $ commaSepAll $ map (pretty False) ts
    (ArrayCon,[len,TyCon BoolCon []]) -> PP.brackets (pretty False len)
    (ArrayCon,[len,typ])   -> PP.brackets (pretty False len) PP.<> (pretty True typ)
    (FunCon,[f,v])         -> (if par then PP.parens else id) $
                                pretty False f PP.<+> PP.text "->" PP.<+> pretty False v
    (BlockCon,[cxt,typ])   -> (if par then PP.parens else id) $
                                pretty True cxt PP.<+> pretty True typ
    _ -> error $ "malformed TyCon: " ++ pShow t
  pretty par (TyRecord fs) =
      PP.braces
    $ commaSepAll
    $ map (\(n,t) -> PP.text n `prettyTypeSig` pretty False t)
    $ M.toList fs
  pretty par (TyVar tv) = case tv of
    FreeVar n  -> PP.text "fv." PP.<> PP.integer n
    BoundVar n -> PP.text n

instance PrettyPrint TyCon where
  pretty par tc = case tc of
    TupleCon n     -> PP.parens $ replicateDoc (n - 1) $ PP.char ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.empty
    FunCon         -> PP.parens $ PP.text "->"
    StringCon      -> PP.text "String"
    BoolCon        -> PP.text "Bit"
    ZCon           -> PP.text "Int"
    NumCon n       -> PP.integer n
    BlockCon       -> PP.text "<Block>"
    ContextCon cxt -> pretty par cxt
    AbstractCon n  -> PP.text n

instance PrettyPrint A.Context where
  pretty _ c = case c of
    A.CryptolSetup -> PP.text "CryptolSetup"
    A.JavaSetup    -> PP.text "JavaSetup"
    A.LLVMSetup    -> PP.text "LLVMSetup"
    A.ProofScript  -> PP.text "ProofScript"
    A.TopLevel     -> PP.text "TopLevel"

replicateDoc :: Integer -> PP.Doc -> PP.Doc
replicateDoc n d 
  | n < 1 = PP.empty
  | True  = d PP.<> replicateDoc (n-1) d

prettyTypeSig :: PP.Doc -> PP.Doc -> PP.Doc
prettyTypeSig n t = n PP.<+> PP.char ':' PP.<+> t

commaSep :: PP.Doc -> PP.Doc -> PP.Doc
commaSep = ((PP.<+>) . (PP.<> PP.comma))

commaSepAll :: [PP.Doc] -> PP.Doc
commaSepAll ds = case ds of
  [] -> PP.empty
  _  -> foldl1 commaSep ds

-- Expr Level

data Expr
  -- Constants
  = Bit Bool
  | String String
  | Z Integer
  -- Structures
  | Array  [Expr]
  | Block  [BlockStmt]
  | Tuple  [Expr]
  | Record (M.Map Name Expr)
  -- Accessors
  | Index  Expr Expr
  | Lookup Expr Name
  -- LC
  | Var A.ResolvedName
  | Function    Name (Maybe Type) Expr
  | Application Expr Expr
  -- Sugar
  | Let [Bind Expr] Expr
  | TSig Expr Schema
  deriving (Show)

data BlockStmt
  = Bind          (Maybe Name) (Maybe Type) Expr
  -- | BlockTypeDecl Name             typeT  
  | BlockLet      [Bind Expr]
  deriving (Show)

-- }}}

-- Type Constructors {{{

tMono :: Type -> Schema
tMono = Forall []

tForall :: [Name] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t

tTuple :: [Type] -> Type
tTuple ts = TyCon (TupleCon $ fromIntegral $ length ts) ts

tArray :: Type -> Type -> Type
tArray l t = TyCon ArrayCon [l,t]

tFun :: Type -> Type -> Type
tFun f v = TyCon FunCon [f,v]

tString :: Type
tString = TyCon StringCon []

tBool :: Type
tBool = TyCon BoolCon []

tZ :: Type
tZ = TyCon ZCon []

tNum :: Integral a => a -> Type
tNum n = TyCon (NumCon $ toInteger n) []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: A.Context -> Type
tContext c = TyCon (ContextCon c) []

tAbstract :: Name -> Type
tAbstract n = TyCon (AbstractCon n) []

-- }}}

-- Subst {{{

newtype Subst = Subst { unSubst :: M.Map TyVar Type }

(@@) :: Subst -> Subst -> Subst
s2@(Subst m2) @@ (Subst m1) = Subst $ m1' `M.union` m2
  where
  m1' = fmap (appSubst s2) m1

emptySubst :: Subst
emptySubst = Subst M.empty

singletonSubst :: TyVar -> Type -> Subst
singletonSubst tv t = Subst $ M.singleton tv t

listSubst :: [(TyVar,Type)] -> Subst
listSubst = Subst . M.fromList

-- }}}

-- mgu {{{

failMGU :: String -> Either String a
failMGU = Left

assert :: Bool -> String -> Either String ()
assert b msg = unless b $ failMGU msg

mgu :: Type -> Type -> Either String Subst
mgu (TyVar tv) t2 = bindVar tv t2
mgu t1 (TyVar tv) = bindVar tv t1
mgu r1@(TyRecord ts1) r2@(TyRecord ts2) = do
  assert (M.keys ts1 == M.keys ts2) $ "mismatched record fields: " ++ pShow r1 ++ " and " ++ pShow r2
  mgus (M.elems ts1) (M.elems ts2)
mgu t1@(TyCon tc1 ts1) t2@(TyCon tc2 ts2) = do
  assert (tc1 == tc2) $ "mismatched type constructors: " ++ pShow tc1 ++ " and " ++ pShow tc2
  mgus ts1 ts2
mgu t1 t2 = failMGU $ "type mismatch: " ++ pShow t1 ++ " and " ++ pShow t2

mgus :: [Type] -> [Type] -> Either String Subst
mgus [] [] = return emptySubst
mgus (t1:ts1) (t2:ts2) = do
  s <- mgu t1 t2
  s' <- mgus (map (appSubst s) ts1) (map (appSubst s) ts2)
  return (s' @@ s)
mgus ts1 ts2 = failMGU $ "type mismatch in constructor arity"

bindVar :: TyVar -> Type -> Either String Subst
bindVar (FreeVar i) (TyVar (FreeVar j))
  | i == j    = return emptySubst
bindVar tv@(FreeVar _) t
  | tv `S.member` freeVars t = failMGU "occurs check failMGUs"
  | otherwise                = return $ singletonSubst tv t

bindVar (BoundVar n) (TyVar (BoundVar m))
  | n == m  = return emptySubst

bindVar _ _ = failMGU "generality mismatch"

-- }}}

-- FreeVars {{{

class FreeVars t where
  freeVars :: t -> S.Set TyVar

instance (Ord k, FreeVars a) => FreeVars (M.Map k a) where
  freeVars = freeVars . M.elems

instance (FreeVars a) => FreeVars [a] where
  freeVars = S.unions . map freeVars

instance FreeVars Type where
  freeVars t = case t of
    TyCon tc ts -> freeVars ts
    TyRecord fs -> freeVars fs
    TyVar tv    -> S.singleton tv

instance FreeVars Schema where
  freeVars (Forall ns t) = freeVars t S.\\ (S.fromList $ map BoundVar ns)

-- }}}

-- TI Monad {{{

newtype TI a = TI { unTI :: ReaderT RO (StateT RW Identity) a }
                        deriving (Functor,Applicative,Monad)

data RO = RO
  { typeEnv :: M.Map A.ResolvedName Schema
  , curMod  :: A.ModuleName
  }

emptyRO :: A.ModuleName -> RO
emptyRO m = RO { typeEnv = M.empty, curMod = m }

data RW = RW
  { nameGen :: Integer
  , subst :: Subst
  , errors :: [String]
  }

emptyRW :: RW
emptyRW = RW 0 emptySubst []

newType :: TI Type
newType = do
  rw <- TI get
  TI $ put $ rw { nameGen = nameGen rw + 1 }
  return $ TyVar $ FreeVar $ nameGen rw

appSubstM :: AppSubst t => t -> TI t
appSubstM t = do
  s <- TI $ gets subst
  return $ appSubst s t

recordError :: String -> TI ()
recordError err = TI $ modify $ \rw ->
  rw { errors = err : errors rw }

unify :: Type -> Type -> TI ()
unify t1 t2 = do
  t1' <- appSubstM t1
  t2' <- appSubstM t2
  case mgu t1' t2' of
    Right s -> TI $ modify $ \rw -> rw { subst = s @@ subst rw }
    Left e -> recordError $ unlines
                [ "type mismatch: " ++ pShow t1 ++ " and " ++ pShow t2
                , e
                ]

bindSchema :: A.ResolvedName -> Schema -> TI a -> TI a
bindSchema n s m = TI $ local (\ro -> ro { typeEnv = M.insert n s $ typeEnv ro })
  $ unTI m

bindSchemas :: [(A.ResolvedName, Schema)] -> TI a -> TI a
bindSchemas bs m = foldr (uncurry bindSchema) m bs

bindTopSchemas :: [Bind Schema] -> TI a -> TI a
bindTopSchemas ds k =
  do m <- curModName
     bindSchemas [ (A.TopLevelName m x, s) | (x,s) <- ds ] k

bindLocalSchemas :: [Bind Schema] -> TI a -> TI a
bindLocalSchemas ds k =
  bindSchemas [ (A.LocalName x,s) | (x,s) <- ds ] k

curModName :: TI A.ModuleName
curModName = TI $ asks curMod

lookupVar :: A.ResolvedName -> TI Type
lookupVar n = do
  env <- TI $ asks typeEnv
  case M.lookup n env of
    Nothing -> do recordError $ "unbound variable: " ++ show n
                  newType
    Just (Forall as t) -> do ats <- forM as $ \a ->
                               do t <- newType
                                  return (BoundVar a,t)
                             let s = listSubst ats
                             return $ appSubst s t

freeVarsInEnv :: TI (S.Set TyVar)
freeVarsInEnv = do
  env <- TI $ asks typeEnv
  let ss = M.elems env
  ss' <- mapM appSubstM ss
  return $ freeVars ss'

-- }}}

-- AppSubst {{{

class AppSubst t where
  appSubst :: Subst -> t -> t

instance (AppSubst t) => AppSubst [t] where
  appSubst s = map $ appSubst s

instance (AppSubst t) => AppSubst (Maybe t) where
  appSubst s = fmap $ appSubst s

instance AppSubst Type where
  appSubst s t = case t of
    TyCon tc ts -> TyCon tc $ appSubst s ts
    TyRecord fs -> TyRecord $ appSubst s fs
    TyVar tv    -> case M.lookup tv $ unSubst s of
                     Just t' -> t'
                     Nothing -> t

instance AppSubst Schema where
  appSubst s (Forall ns t) = Forall ns $ appSubst s t

instance AppSubst Expr where
  appSubst s expr = case expr of
    TSig e t           -> TSig (appSubst s e) (appSubst s t)

    Bit b              -> Bit b
    String str         -> String str
    Z i                -> Z i
    Array es           -> Array $ appSubst s es
    Block bs           -> Block $ appSubst s bs
    Tuple es           -> Tuple $ appSubst s es
    Record fs          -> Record $ appSubst s fs
    Index ar ix        -> Index (appSubst s ar) (appSubst s ix)
    Lookup rec fld     -> Lookup (appSubst s rec) fld
    Var x              -> Var x
    Function x xt body -> Function x (appSubst s xt) (appSubst s body)
    Application f v    -> Application (appSubst s f) (appSubst s v)
    Let nes e          -> Let (appSubstBinds s nes) (appSubst s e)

instance AppSubst ty => AppSubst (A.Expr names ty) where
  appSubst s expr = case expr of
    A.Bit b t            -> A.Bit b (appSubst s t)
    A.Quote str t        -> A.Quote str (appSubst s t)
    A.Z i t              -> A.Z i (appSubst s t)

    A.Array es t         -> A.Array  (appSubst s es) (appSubst s t)
    A.Block bs t         -> A.Block  (appSubst s bs) (appSubst s t)
    A.Tuple es t         -> A.Tuple  (appSubst s es) (appSubst s t)
    A.Record nes t       -> A.Record (appSubstBinds s nes) (appSubst s t)

    A.Index ar ix t -> A.Index (appSubst s ar) (appSubst s ix) (appSubst s t)
    A.Lookup rec fld t   -> A.Lookup (appSubst s rec) fld (appSubst s t)
    A.Var x t            -> A.Var x (appSubst s t)
    A.Function x xt body t-> A.Function x (appSubst s xt) (appSubst s body) (appSubst s t)
    A.Application f v t  -> A.Application (appSubst s f) (appSubst s v) (appSubst s t)

    A.LetBlock nes e     -> A.LetBlock (appSubstBinds s nes) (appSubst s e)

instance AppSubst ty => AppSubst (A.BlockStmt names ty) where
  appSubst s bst = case bst of
    A.Bind mn ctx e     -> A.Bind mn (appSubst s ctx) (appSubst s e)
    A.BlockLet bs       -> A.BlockLet (appSubstBinds s bs)
    A.BlockTypeDecl x t -> A.BlockTypeDecl x (appSubst s t)

instance (Ord k, AppSubst a) => AppSubst (M.Map k a) where
  appSubst s = fmap (appSubst s)

instance AppSubst BlockStmt where
  appSubst s bst = case bst of
    Bind mn ctx e -> Bind mn ctx e
    BlockLet bs   -> BlockLet $ appSubstBinds s bs

appSubstBinds :: (AppSubst a) => Subst -> [Bind a] -> [Bind a]
appSubstBinds s bs = [ (n,appSubst s a) | (n,a) <- bs ]

-- }}}

-- Expr translation {{{

translateExpr :: A.Expr A.ResolvedName A.ResolvedT -> Expr
translateExpr expr = case expr of
  A.Bit b t              -> sig t $ Bit b
  A.Quote s t            -> sig t $ String s
  A.Z i t                -> sig t $ Z i
  A.Array es t           -> sig t $ Array $ map translateExpr es
  A.Block bs t           -> sig t $ Block $ map translateBStmt bs
  A.Tuple es t           -> sig t $ Tuple $ map translateExpr es
  A.Record fs t          -> sig t $ Record $ M.fromList [ (n,translateExpr t) | (n,t) <- fs ]
  A.Index ar ix t        -> sig t $ Index (translateExpr ar) (translateExpr ix)
  A.Lookup rec fld t     -> sig t $ Lookup (translateExpr rec) fld
  A.Var x t              -> sig t $ Var x
  A.Function x xt body t -> sig t $ Function x (translateType `fmap` xt) $
                                      translateExpr body
  A.Application f v t    -> sig t $ Application (translateExpr f) (translateExpr v)
  A.LetBlock nes e       ->         Let (map translateField nes) (translateExpr e)
  where
  sig :: A.ResolvedT -> Expr -> Expr
  sig Nothing e = e
  sig (Just t) e = TSig e $ translateTypeS t

translateBStmt :: A.BlockStmt A.ResolvedName A.ResolvedT -> BlockStmt
translateBStmt bst = case bst of
  A.Bind mn ctx e -> Bind mn (translateType `fmap` ctx) (translateExpr e)
  A.BlockLet bs   -> BlockLet (map translateField bs)
  --BlockTypeDecl Name             typeT  

translateField :: (a,A.Expr A.ResolvedName A.ResolvedT) -> (a,Expr)
translateField (n,e) = (n,translateExpr e)

translateTypeS :: A.FullT -> Schema
translateTypeS (In (Inl (A.I n)))   = tMono $ tNum n
translateTypeS (In (Inr (Inl ctx))) = tMono $
  case ctx of
    A.CryptolSetupContext -> tContext $ A.CryptolSetup
    A.JavaSetupContext    -> tContext $ A.JavaSetup
    A.LLVMSetupContext    -> tContext $ A.LLVMSetup
    A.ProofScriptContext  -> tContext $ A.ProofScript
    A.TopLevelContext     -> tContext $ A.TopLevel

translateTypeS (In (Inr (Inr ty))) =
  case ty of
    A.BitF            -> tMono tBool
    A.ZF              -> tMono tZ
    A.QuoteF          -> tMono tString

    A.ArrayF tE tL    -> tMono $ tArray (translateType tL) (translateType tE)
    A.BlockF tC tE    -> tMono $ tBlock (translateType tC) (translateType tE)
    A.TupleF ts       -> tMono $ tTuple $ map translateType ts
    A.RecordF fs      -> tMono $ TyRecord $ M.fromList [ (n,translateType t) | (n,t) <- fs ]

    A.FunctionF t1 t2 -> tMono $ tFun (translateType t1) (translateType t2)
    A.AbstractF n     -> tMono $ tAbstract n

    A.PVar x          -> tMono $ TyVar (BoundVar x)
    A.PAbs xs t       -> case translateTypeS t of
                           Forall ys t1 -> Forall (xs ++ ys) t1

translateType :: A.FullT -> Type
translateType typ = case translateTypeS typ of
  Forall [] t -> t
  _ -> error "my brain exploded: translateType"

exportType :: Type -> A.Type
exportType ty =
  case ty of
    TyVar var ->
      case var of
        BoundVar name -> A.TypVar name
        FreeVar _name ->
          error "Free type variable: bug/default to something."

    TyRecord fs ->
      A.RecordT [ (x, exportType t) | (x, t) <- M.toList fs ]

    TyCon tc ts ->
      case (tc, map exportType ts) of
        (TupleCon _, ts') -> A.TupleT ts'
        (ArrayCon, [i,e]) -> A.ArrayT e i -- argument order changes
        (FunCon,   [a,b]) -> A.FunctionT a b
        (StringCon, [])   -> A.QuoteT
        (BoolCon, [])     -> A.BitT
        (ZCon, [])        -> A.ZT
        (ContextCon c, _) -> A.ContextT c
        (NumCon n, _)     -> A.IntegerT n
        (BlockCon, [a,b]) -> A.BlockT a b
        (AbstractCon s, _) -> A.Abstract s
        _                 -> error "exportType: malformed TyCon"

exportSchema :: Schema -> A.Type
exportSchema (Forall xs t) =
  case xs of
    [] -> exportType t
    _  -> A.TypAbs xs $ exportType t

exportExpr :: OutExpr -> TI (A.Expr A.ResolvedName A.Type)
exportExpr e0 =
  do e1 <- appSubstM e0
     go e1
  where
  go expr =
    case expr of
      A.Bit b t          -> A.Bit b     <$> exportSchema' t
      A.Quote str t      -> A.Quote str <$> exportSchema' t
      A.Z i t            -> A.Z i       <$> exportSchema' t

      A.Array es t       -> A.Array <$> mapM go es  <*> exportSchema' t
      A.Block bs t       -> A.Block <$> mapM goB bs <*> exportSchema' t
      A.Tuple es t       -> A.Tuple <$> mapM go es  <*> exportSchema' t
      A.Record nes t     -> A.Record <$> mapM go2 nes <*> exportSchema' t

      A.Index ar ix t    -> A.Index <$> go ar <*> go ix <*> exportSchema' t
      A.Lookup rec fld t -> A.Lookup <$> go rec <*> pure fld <*> exportSchema' t
      A.Var x t          -> A.Var x <$> exportSchema' t

      A.Function x xt body t-> A.Function x <$> exportSchema' xt
                                            <*> go body <*> exportSchema' t

      A.Application f v t -> A.Application <$> go f <*> go v <*> exportSchema' t
      A.LetBlock nes e   -> A.LetBlock <$> mapM go2 nes <*> go e

  go2 (x,e) = do e1 <- go e
                 return (x,e1)

  goB stm =
    case stm of
      A.Bind mn ctx e     -> A.Bind mn <$> exportSchema' ctx <*> go e
      A.BlockLet bs       -> A.BlockLet <$> mapM go2 bs
      A.BlockTypeDecl x t -> A.BlockTypeDecl x <$> exportSchema' t
  exportSchema' = pure . exportSchema





-- }}}

-- Type Inference {{{

type OutExpr      = A.Expr      A.ResolvedName Schema
type OutBlockStmt = A.BlockStmt A.ResolvedName Schema


ret :: Monad m => (Schema -> a) -> Type -> m (a, Type)
ret thing ty = return (thing (tMono ty), ty)

inferE :: Expr -> TI (OutExpr,Type)
inferE expr = case expr of
  Bit b    -> ret (A.Bit b)   tBool
  String s -> ret (A.Quote s) tString
  Z i      -> ret (A.Z i)     tZ

  Array  [] -> do a <- newType
                  ret (A.Array []) $ tArray (tNum (0 :: Int)) a

  Array (e:es) -> do (e',t) <- inferE e
                     es' <- mapM (`checkE` t) es
                     ret (A.Array (e':es')) $ tArray (tNum $ length es + 1) t

  Block bs -> do ctx <- newType
                 (bs',t') <- inferStmts ctx bs
                 ret (A.Block bs') $ tBlock ctx t'

  Tuple  es -> do (es',ts) <- unzip `fmap` mapM inferE es
                  ret (A.Tuple es') $ tTuple ts

  Record fs -> do (nes',nts) <- unzip `fmap` mapM inferField (M.toList fs)
                  ret (A.Record nes') $ TyRecord $ M.fromList nts

  Index ar ix -> do (ar',at) <- inferE ar
                    ix'      <- checkE ix tZ
                    l        <- newType
                    t        <- newType
                    unify (tArray l t) at
                    ret (A.Index ar' ix') t

  TSig e (Forall [] t) -> do t' <- checkKind t
                             e' <- checkE e t'
                             return (e', t')

  TSig e (Forall _ _) -> do recordError "TODO: TSig with Schema"
                            inferE e


  Function x Nothing body -> do a <- newType
                                (body',t) <- bindLocalSchemas [(x,tMono a)] $
                                               inferE body
                                ret (A.Function x (tMono a) body') $ tFun a t
  Function _ (Just _) _ -> error "inferE (Function _ (Just _) _)"


  Application f v -> do (v',fv) <- inferE v
                        t <- newType
                        let ft = tFun fv t
                        f' <- checkE f ft
                        ret (A.Application f' v')  t

  Var x -> do t <- lookupVar x
              ret (A.Var x) t


  Let bs body -> inferDecls bs $ \bs' -> do
                   (body',t) <- inferE body
                   return (A.LetBlock bs' body', t)

  Lookup e n ->
    do (e1,t) <- inferE e
       t1 <- appSubstM t
       elTy <- case t1 of
                 TyRecord fs
                    | Just t <- M.lookup n fs -> return t
                    | otherwise ->
                          do recordError $ unlines
                                [ "Selecting a missing field."
                                , "Field name: " ++ n
                                ]
                             newType
                 _ -> do recordError $ unlines
                            [ "We only support simple record lookup for now."
                            , "Please add type signature on argument."
                            ]
                         newType
       ret (A.Lookup e1 n) elTy



checkE :: Expr -> Type -> TI OutExpr
checkE e t = do
  (e',t') <- inferE e
  unify t t'
  return e'

inferField :: Bind Expr -> TI (Bind OutExpr,Bind Type)
inferField (n,e) = do
  (e',t) <- inferE e
  return ((n,e'),(n,t))

inferDecls :: [Bind Expr] -> ([Bind OutExpr] -> TI a) -> TI a
inferDecls bs nextF = do
  (bs',ss) <- unzip `fmap` mapM inferDecl bs
  bindLocalSchemas ss (nextF bs')

inferStmts :: Type -> [BlockStmt] -> TI ([OutBlockStmt],Type)

inferStmts ctx [] = do
  recordError "do block must include at least one expression"
  t <- newType
  return ([], t)

inferStmts ctx [Bind Nothing mc e] = do
  t  <- newType
  e' <- checkE e (tBlock ctx t)
  mc' <- case mc of
    Nothing -> return (tMono ctx)
    Just t  -> do t' <- checkKind t
                  unify t ctx
                  return (tMono t')
  return ([A.Bind Nothing mc' e'],t)

inferStmts _ [_] = do
  recordError "do block must end with expression"
  t <- newType
  return ([],t)

inferStmts ctx (Bind mn mc e : more) = do
  t <- newType
  e' <- checkE e (tBlock ctx t)
  mc' <- case mc of
    Nothing -> return (tMono ctx)
    Just t  -> do t' <- checkKind t
                  unify t ctx
                  return (tMono t')
  let f = case mn of
        Nothing -> id
        Just n  -> bindSchema (A.LocalName n) (tMono t)
  (more',t) <- f $ inferStmts ctx more

  return (A.Bind mn mc' e' : more', t)

inferStmts ctx (BlockLet bs : more) = inferDecls bs $ \bs' -> do
  (more',t) <- inferStmts ctx more
  return (A.BlockLet bs' : more', t)

inferDecl :: Bind Expr -> TI (Bind OutExpr,Bind Schema)
inferDecl (n,e) = do
  (e',t) <- inferE e
  [(e1,s)] <- generalize [e'] [t]
  return ( (n,e1), (n,s) )


-- XXX: For now, no schema type signatures.
inferRecDecls :: [Bind Expr] -> TI ([Bind OutExpr], [Bind Schema])
inferRecDecls ds =
  do let names = map fst ds
     guessedTypes <- mapM (\_ -> newType) ds
     (es,ts) <- unzip `fmap`
                bindTopSchemas (zip names (map tMono guessedTypes))
                               (mapM (inferE . snd) ds)
     _ <- zipWithM unify ts guessedTypes
     (es1,ss) <- unzip `fmap` generalize es ts
     return (zip names es1, zip names ss)


generalize :: [OutExpr] -> [Type] -> TI [(OutExpr,Schema)]
generalize es0 ts0 =
  do ts <- appSubstM ts0
     es <- appSubstM es0

     let cs = freeVars ts
     withAsmps <- freeVarsInEnv
     let (ns,gvs) = unzip $ mapMaybe toBound $ S.toList $ cs S.\\ withAsmps
     let s = listSubst gvs
         mk e t = (quant ns (appSubst s e), Forall ns (appSubst s t))

     return $ zipWith mk es ts

  where
  toBound :: TyVar -> Maybe (Name,(TyVar,Type))
  toBound v@(FreeVar i) = let nm = "a." ++ show i in
                                Just (nm,(v,TyVar (BoundVar nm)))
  toBound _ = Nothing

  quant :: [Name] -> OutExpr -> OutExpr
  quant xs expr =
    case expr of
      A.Bit b t             -> A.Bit b (tForall xs t)
      A.Quote str t         -> A.Quote str (tForall xs t)
      A.Z i t               -> A.Z i (tForall xs t)

      A.Array es t          -> A.Array es (tForall xs t)
      A.Block bs t          -> A.Block bs (tForall xs t)
      A.Tuple es t          -> A.Tuple es (tForall xs t)
      A.Record nes t        -> A.Record nes (tForall xs t)

      A.Index ar ix t       -> A.Index ar ix (tForall xs t)
      A.Lookup rec fld t    -> A.Lookup rec fld (tForall xs t)
      A.Var x t             -> A.Var x (tForall xs t)
      A.Function x xt body t-> A.Function x xt body (tForall xs t)
      A.Application f v t   -> A.Application f v (tForall xs t)

      A.LetBlock nes e      -> A.LetBlock nes (quant xs e)


-- Check a list of recursive groups, sorted by dependency.
inferTopDecls :: [ [Bind Expr] ] -> TI [ [Bind OutExpr] ]
inferTopDecls [] = return []
inferTopDecls (ds : dss) =
  do (ds1, ss) <- inferRecDecls ds
     rest <- bindTopSchemas ss (inferTopDecls dss)
     return (ds1 : rest)


-- Compute groups of recursive components
computeSCCGroups :: A.ModuleName -> [ Bind Expr ] -> [ [Bind Expr] ]
computeSCCGroups m bs = map forget $ mkScc $ map (defsDepsBind m) bs
  where forget (CyclicSCC xs) = xs
        forget (AcyclicSCC x) = [x]

{- | Given a list of declarations, annoted with (i) the names that they
 - define, and (ii) the names that they use, we compute a list of strongly
 - connected components of the declarations.  The SCCs are in dependency order. -}
mkScc :: [(a,[A.ResolvedName],[A.ResolvedName])] -> [SCC a]
mkScc ents = stronglyConnComp $ zipWith mkGr keys ents
  where
  keys                    = [ 0 :: Integer .. ]

  mkGr i (x,_,uses)       = (x,i,mapMaybe (`M.lookup` nodeMap) uses)

  -- Maps names to node ids.
  nodeMap                 = M.fromList $ concat $ zipWith mkNode keys ents
  mkNode i (_,defs,_)     = [ (d,i) | d <- defs ]

defsDepsBind :: A.ModuleName -> Bind Expr
                        -> (Bind Expr, [A.ResolvedName], [A.ResolvedName])
defsDepsBind m it@(x,e0) = (it, [ A.TopLevelName m x ], S.toList (uses e0))
  where
  -- we are only interested in top-level names
  uses expr =
    case expr of
      Bit _               -> S.empty
      String _            -> S.empty
      Z _                 -> S.empty
      Array es            -> S.unions (map uses es)
      Block bs            -> S.unions (map usesB bs)
      Tuple es            -> S.unions (map uses es)
      Record fs           -> S.unions (map uses $ M.elems fs)
      Index  e1 e2        -> S.union (uses e1) (uses e2)
      Lookup e _          -> uses e
      Var (A.LocalName _) -> S.empty
      Var x               -> S.singleton x  -- This is what we look for
      Function  _ _ e     -> uses e
      Application e1 e2   -> S.union (uses e1) (uses e2)
      Let bs e            -> S.unions (uses e : map (uses . snd) bs)
      TSig e _            -> uses e

  usesB bl =
    case bl of
      Bind _ _ e  -> uses e
      BlockLet bs -> S.unions (map (uses . snd) bs)

-- XXX: TODO
checkKind :: Type -> TI Type
checkKind = return



-- }}}

-- Main interface {{{
checkModule :: [(A.ResolvedName, Schema)] -> -- Temporarily made a parameter for prelude
                          A.Module A.ResolvedName A.ResolvedT A.ResolvedT ->
         Either [String] (A.Module A.ResolvedName A.Type      A.ResolvedT)
checkModule initTs m =
  case errs of
    [] -> Right m { A.moduleExprEnv = M.fromList res }
    _  -> Left errs
  where
  --initTs = []   -- XXX: Compute these from the other modules

  exportBinds dss = sequence [ do e1 <- exportExpr e
                                  return (x,e1)
                             | ds <- dss, (x,e) <- ds ]

  (res,_,errs)  = runTI (A.moduleName m)
                        $ bindSchemas initTs
                        $ exportBinds =<<
                            ( inferTopDecls
                            $ computeSCCGroups (A.moduleName m)
                            $ M.toList
                            $ fmap translateExpr
                            $ A.moduleExprEnv m
                            )




runTI :: A.ModuleName -> TI a -> (a,Subst,[String])
runTI mn m = (a,subst rw, errors rw)
  where
  m' = runReaderT (unTI m) (emptyRO mn)
  (a,rw) = runState m' emptyRW

-- }}}

