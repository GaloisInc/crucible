{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.AST where

import SAWScript.Unify

import Data.List
import qualified Data.Map as M

import Data.Foldable hiding (concat, elem)
import qualified Data.Traversable as T

-- Intermediate Types {{{

type RawT      = Maybe RawSigT
type RawSigT   = Mu (Syn :+: Poly :+: BaseT)
type ResolvedT = Maybe FinalT
type FinalT    = Mu (Poly :+: BaseT)
type TCheckT   = Mu (Logic :+: Poly :+: BaseT)

type BaseT = I :+: ContextF :+: TypeF

-- }}}

-- Names {{{

type Name = String
data ModuleName = ModuleName Name [Name] deriving (Eq,Ord,Show)

data QName = QName
  { qualModule :: ModuleName
  , qualName   :: Name
  }

type Bind a = (Name,a)
onBind :: (a -> b) -> Bind a -> Bind b
onBind f (n,a) = (n,f a)
onBinds :: (a -> b) -> [Bind a] -> [Bind b]
onBinds = map . onBind

type Env a = M.Map Name a

-- }}}

-- Module Level {{{

data Module refT exprT typeT = Module
  { moduleName         :: ModuleName
  , moduleExprEnv      :: Env (Expr refT typeT)
  , moduleTypeEnv      :: Env typeT
  , moduleDependencies :: Env ValidModule
  }

type ValidModule = Module QName FinalT FinalT

-- }}}

-- Expr Level {{{

type TopStmtSimple = TopStmt Name
type ExprSimple = Expr Name
type BlockStmtSimple = BlockStmt Name

data TopStmt refT typeT
  = Import      ModuleName (Maybe [Name])    (Maybe Name)
  | TypeDef     Name       FinalT
  | TopTypeDecl Name       FinalT
  | TopBind     Name       (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,T.Traversable)

data Expr refT typeT
  -- Constants
  = Unit         typeT
  | Bit Bool     typeT
  | Quote String typeT
  | Z Integer    typeT
  -- Structures
  | Array  [Expr refT typeT]         typeT
  | Block  [BlockStmt refT typeT]    typeT
  | Tuple  [Expr refT typeT]         typeT
  | Record [Bind (Expr refT typeT)] typeT
  -- Accessors
  | Index  (Expr refT typeT) (Expr refT typeT) typeT
  | Lookup (Expr refT typeT) Name              typeT
  -- LC
  | Var         refT       typeT
  | Function    Name       typeT  (Expr refT typeT) typeT
  | Application (Expr refT typeT) (Expr refT typeT) typeT
  -- Sugar
  | LetBlock [Bind (Expr refT typeT)] (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,T.Traversable)

data BlockStmt refT typeT
  = Bind          (Maybe Name)     typeT   (Expr refT typeT)
  | BlockTypeDecl Name             FinalT
  | BlockLet      [(Name,Expr refT typeT)]
  deriving (Eq,Show,Functor,Foldable,T.Traversable)

-- }}}

-- Type Level {{{

data TypeF typeT
  -- Constants
  = UnitF
  | BitF
  | ZF
  | QuoteF
  -- Structures
  | ArrayF       typeT typeT
  | BlockF       typeT typeT
  | TupleF       [typeT]
  | RecordF      [Bind typeT]
  -- LC
  | FunctionF    typeT typeT
  deriving (Show,Functor,Foldable,T.Traversable)

data ContextF typeT
  = CryptolSetupContext
  | JavaSetupContext
  | LLVMSetupContext
  | ProofScriptContext
  | TopLevelContext
  deriving (Eq,Show,Functor,Foldable,T.Traversable)

data Type 
  = UnitT
  | BitT
  | ZT
  | QuoteT
  | ArrayT Type Integer
  | BlockT Context Type
  | TupleT [Type]
  | RecordT [Bind Type]
  | FunctionT Type Type
  deriving (Eq,Show)

data Syn typeF = Syn Name
  deriving (Show,Functor,Foldable,T.Traversable)

type Context = ContextF ()

data Poly typeT
  = PAbs [Name] typeT
  | PVar Name
  deriving (Show,Functor,Foldable,T.Traversable)

data I a = I Integer deriving (Show,Functor,Foldable,T.Traversable)

-- }}}

-- Equal Instances {{{

instance Equal TypeF where
  equal t1 t2 = case (t1,t2) of
    (UnitF,UnitF)                         -> True
    (BitF,BitF)                           -> True
    (ZF,ZF)                               -> True
    (QuoteF,QuoteF)                       -> True
    (ArrayF at1 l1,ArrayF at2 l2)         -> l1 == l2 && at1 == at2
    (BlockF c1 bt1,BlockF c2 bt2)         -> c1 == c2 && bt1 == bt2
    (TupleF ts1,TupleF ts2)               -> ts1 == ts2
    (RecordF fts1,RecordF fts2)           -> fts1 == fts2
    (FunctionF at1 bt1,FunctionF at2 bt2) -> at1 == at2 && bt1 == bt2
    _                                     -> False

instance Equal I where
  equal (I x) (I y) = x == y

instance Equal Poly where
  equal (PVar n1) (PVar n2) = n1 == n2
  equal (PAbs ns1 t1) (PAbs ns2 t2) = ns1 == ns2 && t1 == t2
  equal _ _ = False

instance Equal ContextF where
  equal CryptolSetupContext CryptolSetupContext = True
  equal JavaSetupContext    JavaSetupContext    = True
  equal LLVMSetupContext    LLVMSetupContext    = True
  equal ProofScriptContext  ProofScriptContext  = True
  equal TopLevelContext     TopLevelContext     = True
  equal _ _ = False

instance Equal Syn where
  equal (Syn n1) (Syn n2) = n1 == n2

-- }}}

-- Render Instances {{{

instance Render TypeF where
  render t = case t of
    UnitF           -> "UnitF"
    BitF            -> "BitF"
    ZF              -> "ZF"
    QuoteF          -> "QuoteF"
    ArrayF at l     -> "(ArrayF " ++ show at ++ " " ++ show l ++ ")"
    BlockF c bt     -> "(BlockF " ++ show c ++ " " ++ show bt ++ ")"
    TupleF ts       -> "(TupleF [" ++ (intercalate ", " $ map show ts) ++ "])"
    RecordF fts     -> "(RecordF [" ++ (intercalate ", " $ map (\(n,bt)-> n ++ " :: " ++ show bt) fts) ++ "])"
    FunctionF at bt -> "(FunctionF " ++ show at ++ " " ++ show bt ++ ")"

instance Render I where
  render (I x) = "(I " ++ show x ++ ")"

instance Render ContextF where
  render CryptolSetupContext = "CryptolSetupContext"
  render JavaSetupContext    = "JavaSetupContext"
  render LLVMSetupContext    = "LLVMSetupContext"
  render ProofScriptContext  = "ProofScriptContext"
  render TopLevelContext     = "TopLevelContext"

instance Render Syn where
  render (Syn n) = "(Syn " ++ show n ++ ")"

instance Render Poly where
  render p = case p of
    PVar n    -> "(PVar " ++ show n ++ ")"
    PAbs ns t -> "(PAbs " ++ show ns ++ " " ++ show t ++ ")"

-- }}}

-- Uni Instances {{{

instance Uni TypeF where
  uni t1 t2 = case (t1,t2) of
    (ArrayF at1 l1,ArrayF at2 l2)             -> unify l1 l2 >> unify at1 at2
    (BlockF c1 bt1,BlockF c2 bt2)             -> assert (c1 == c2) ("Could not match contexts " ++ show c1 ++ " and " ++ show c2) >> unify bt1 bt2
    (TupleF ts1,TupleF ts2)                   -> zipWithMP_ unify ts1 ts2
    (RecordF fts1,RecordF fts2)               -> do conj [ disj [ unify x y | (nx,x) <- fts1, nx == ny ] | (ny,y) <- fts2 ]
                                                    conj [ disj [ unify y x | (ny,y) <- fts2, nx == ny ] | (nx,x) <- fts1 ]
    (FunctionF at1 bt1,FunctionF at2 bt2)     -> unify at1 at2 >> unify bt1 bt2
    _                                         -> fail ("Type Mismatch: " ++ render t1 ++ " could not be unified with " ++ render t2)

instance Uni I where
  uni (I x) (I y) = fail ("I: " ++ show x ++ " =/= " ++ show y)

instance Uni Poly where
  uni p1 p2 = case (p1,p2) of
    (PVar n1,PVar n2)          -> fail ("Poly: " ++ show n1 ++ " =/= " ++ show n2)
    -- TODO: Alpha renaming? no, variable substitution.
    (PAbs ns1 t1, PAbs ns2 t2) -> undefined
    _ -> fail ("Type Mismatch: " ++ render p1 ++ " could not be unified with " ++ render p2)

-- }}}

-- Injection Operators {{{

unit :: (TypeF :<: f) => Mu f
unit = inject UnitF

bit :: (TypeF :<: f) => Mu f
bit = inject BitF

quote :: (TypeF :<: f) => Mu f
quote = inject QuoteF

z :: (TypeF :<: f) => Mu f
z = inject ZF

array :: (I :<: f, TypeF :<: f) => Mu f -> Mu f -> Mu f
array t l = inject $ ArrayF t l

block :: (ContextF :<: f, TypeF :<: f) => Mu f -> Mu f -> Mu f
block c t = inject $ BlockF c t

tuple :: (TypeF :<: f) => [Mu f] -> Mu f
tuple ts = inject $ TupleF ts

record :: (TypeF :<: f) => [(Name,Mu f)] -> Mu f
record fts = inject $ RecordF fts

function :: (TypeF :<: f) => Mu f -> Mu f -> Mu f
function at bt = inject $ FunctionF at bt

cryptolSetupContext :: (ContextF :<: f) => Mu f
cryptolSetupContext = inject CryptolSetupContext

javaSetupContext    :: (ContextF :<: f) => Mu f
javaSetupContext = inject JavaSetupContext

llvmSetupContext    :: (ContextF :<: f) => Mu f
llvmSetupContext = inject LLVMSetupContext

proofScriptContext  :: (ContextF :<: f) => Mu f
proofScriptContext = inject ProofScriptContext

topLevelContext     :: (ContextF :<: f) => Mu f
topLevelContext = inject TopLevelContext

syn :: (Syn :<: f) => String -> Mu f
syn n = inject $ Syn n

i :: (I :<: f) => Integer -> Mu f
i x = inject $ I x

pVar :: (Poly :<: f) => Name -> Mu f
pVar n = inject $ PVar n

pAbs :: (Poly :<: f) => [Name] -> Mu f -> Mu f
pAbs ns t = inject $ PAbs ns t

-- }}}

-- Expr Accessors/Modifiers {{{

typeOf :: Expr refT typeT -> typeT
typeOf e = case e of
  Unit t            -> t
  Bit _ t           -> t
  Quote _ t         -> t
  Z _ t             -> t
  Array _ t         -> t
  Block _ t         -> t
  Tuple _ t         -> t
  Record _ t        -> t
  Index _ _ t       -> t
  Lookup _ _ t      -> t
  Var _ t           -> t
  Function _ _ _ t  -> t
  Application _ _ t -> t
  LetBlock _ e'     -> typeOf e'

context :: BlockStmt refT typeT -> Maybe typeT
context s = case s of
  Bind _ c _ -> Just c
  _          -> Nothing

updateAnnotation :: typeT -> Expr refT typeT -> Expr refT typeT
updateAnnotation t e = case e of
  Unit _            -> Unit t
  Bit x _           -> Bit x t
  Quote x _         -> Quote x t
  Z x _             -> Z x t
  Array x _         -> Array x t
  Block x _         -> Block x t
  Tuple x _         -> Tuple x t
  Record x _        -> Record x t
  Index x y _       -> Index x y t
  Lookup x y _      -> Lookup x y t
  Var x _           -> Var x t
  Function a at b _ -> Function a at b t
  Application f v _ -> Application f v t
  LetBlock bs e'    -> LetBlock bs (updateAnnotation t e')

-- }}}

-- capturePVars {{{

capturePVars :: [Name] -> RawSigT -> RawSigT
capturePVars = foldMu . capturePVarsF

class (Functor f) => CapturePVars f where
  capturePVarsF :: [Name] -> f RawSigT -> RawSigT

instance (CapturePVars f, CapturePVars g) => CapturePVars (f :+: g) where
  capturePVarsF ns t = case t of
    Inl e -> capturePVarsF ns e 
    Inr e -> capturePVarsF ns e

instance CapturePVars TypeF where
  capturePVarsF ns t = case t of
    ArrayF ty1 ty2    -> array (capturePVars ns ty1) (capturePVars ns ty2)
    BlockF ctx ty1    -> block ctx (capturePVars ns ty1)
    TupleF tys        -> tuple $ map (capturePVars ns) tys
    RecordF flds      -> record $ onBinds (capturePVars ns) flds
    FunctionF ty1 ty2 -> function (capturePVars ns ty1) (capturePVars ns ty2)
    _ -> inject t

instance CapturePVars Syn where
  capturePVarsF ns (Syn n) = if n `elem` ns
    then pVar n
    else syn n

instance CapturePVars Poly where
  capturePVarsF ns p = case p of
    PVar n    -> pVar n
    PAbs ns' t -> pAbs ns' $ capturePVars ns t

instance CapturePVars I where
  capturePVarsF _ = inject

instance CapturePVars ContextF where
  capturePVarsF _ = inject

-- }}}

