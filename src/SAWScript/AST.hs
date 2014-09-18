{-# LANGUAGE DeriveFunctor,DeriveFoldable,DeriveTraversable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.AST where

import SAWScript.Unify hiding (pretty)
import SAWScript.Token
import SAWScript.Utils

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Arrow

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import System.FilePath (joinPath,splitPath,dropExtension)
import qualified Text.PrettyPrint.Leijen as PP

-- Intermediate Types {{{

type RawT      = Maybe RawSigT
type RawSigT   = Mu (Syn :+: BaseT)
type ResolvedT = Maybe FullT
type FullT     = Mu BaseT
type TCheckT   = Mu (Logic :+: BaseT)

type BaseT = I :+: ContextF :+: TypeF

-- }}}

-- Names {{{

type Name = String
-- dot separated names designating module heirarchy,
--  and single name designating module name.
data ModuleName = ModuleName [Name] Name deriving (Eq,Ord,Show)

-- some name, qualified with some dot separated names.
--  compiler doesn't know what those names are yet.
newtype UnresolvedName = UnresolvedName Name
  deriving (Eq,Ord,Show)

-- a name that has been resolved to a particular module.
data ResolvedName
  -- locally bound in the environment, ie. in a lambda.
  = LocalName Name
  -- a name bound at the top level of some module.
  | TopLevelName ModuleName Name
  deriving (Eq,Ord,Show)

moduleNameFromString :: String -> ModuleName
moduleNameFromString nm = case ns of
  [] -> error "ModuleName cannot be made from empty string"
  _  -> ModuleName (init ns) (last ns)
  where
  ns = breakAll (== '.') nm

moduleNameFromPath :: FilePath -> ModuleName
moduleNameFromPath fp = case ns of
  [] -> error "ModuleName cannot be made from empty string"
  -- _  -> ModuleName (init ns) (last ns)
  _  -> ModuleName [] (last ns)
  where
  ns = splitPath $ dropExtension fp

breakAll :: (Char -> Bool) -> String -> [String]
breakAll _ [] = []
breakAll pr s  = let (ss,rest) = break pr s in
  ss : breakAll pr (drop 1 rest)

renderDotSepName :: [Name] -> String
renderDotSepName = intercalate "."

renderSlashSepName :: [Name] -> String
renderSlashSepName = joinPath

renderModuleName :: ModuleName -> String
renderModuleName (ModuleName ns n) = renderDotSepName $ ns ++ [n]

moduleNameFilePath :: ModuleName -> String
moduleNameFilePath (ModuleName ns n) = renderSlashSepName $ ns ++ [n]

renderUnresolvedName :: UnresolvedName -> String
renderUnresolvedName (UnresolvedName n) = n

renderResolvedName :: ResolvedName -> String
renderResolvedName rn = case rn of
  TopLevelName (ModuleName ns mn) n -> renderDotSepName $ (ns ++ [mn,n])
  LocalName n                       -> show n

type Bind a = (Name,a)
type LBind a = (LName, a)
onBind :: (a -> b) -> Bind a -> Bind b
onBind f (n,a) = (n,f a)
onBinds :: (a -> b) -> [Bind a] -> [Bind b]
onBinds = map . onBind

type Env a       = Map Name a
type LEnv a      = Map LName a
type ModuleEnv a = Map ModuleName a

singletonEnv :: Name -> a -> Env a
singletonEnv = Map.singleton

lookupEnv :: Name -> Env a -> Maybe a
lookupEnv = Map.lookup

lookupLEnv :: LName -> LEnv a -> Maybe a
lookupLEnv = Map.lookup

memberEnv :: Name -> Env a -> Bool
memberEnv = Map.member

unionEnv :: Env a -> Env a -> Env a
unionEnv = Map.union

emptyEnv :: Env a
emptyEnv = Map.empty

insertEnv :: Name -> a -> Env a -> Env a
insertEnv = Map.insert

unionsLEnv :: [LEnv a] -> LEnv a
unionsLEnv = Map.unions

-- }}}

-- Module Level {{{

data Module refT exprT typeT = Module
  { moduleName         :: ModuleName
  , moduleExprEnv      :: [(LName, Expr refT exprT)]
  , modulePrimEnv      :: LEnv exprT
  , moduleDependencies :: ModuleEnv ValidModule
  , moduleCryDeps      :: [FilePath]
  } deriving (Eq,Show)

-- A fully type checked module.
--  Exprs have resolved names, concrete types
--  Types have ResolvedT (Nothing for abstract types, Just FullT for type synonyms)
type ValidModule = Module ResolvedName Schema ResolvedT

-- }}}

-- Expr Level {{{

data Located a = Located { getVal :: a, getOrig :: Name, getPos :: Pos } deriving (Functor, Foldable, Traversable)
instance Show (Located a) where
  show (Located _ v p) = show v ++ " (" ++ show p ++ ")"

type LName = Located Name

instance Eq a => Eq (Located a) where
  a == b = getVal a == getVal b

instance Ord a => Ord (Located a) where
  compare a b = compare (getVal a) (getVal b)

toLName :: Token Pos -> LName
toLName p = Located (tokStr p) (tokStr p) (tokPos p)

toNameDec :: (LName, a) -> (Name, a)
toNameDec = first getVal

type TopStmtSimple   = TopStmt   UnresolvedName
type ExprSimple      = Expr      UnresolvedName
type BlockStmtSimple = BlockStmt UnresolvedName

data TopStmt refT typeT
  = Import      ModuleName (Maybe [Name])    (Maybe Name)   -- ^ import <module> [(<names>)] [as <name>]
  | TopTypeDecl LName       RawSigT                         -- ^ <name> : <type>
  | TopBind     LName       (Expr refT typeT)               -- ^ <name> = <expr>
  | Prim        LName       RawT                            -- ^ prim <name> : <type>
  | ImportCry   FilePath                                    -- ^ import "filepath.cry"
  deriving (Eq,Show,Functor,Foldable,Traversable)

{-
data Exprs refT typeT
  = PrimExpr typeT
  | Defined (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,Traversable)
-}

data Expr refT typeT
  -- Constants
  = Bit Bool     typeT
  | Quote String typeT
  | Z Integer    typeT
  | Undefined    typeT
  | Code (Located String) typeT
  -- Structures
  | Array  [Expr refT typeT]         typeT
  | Block  [BlockStmt refT typeT]    typeT
  | Tuple  [Expr refT typeT]         typeT
  | Record [Bind (Expr refT typeT)]  typeT
  -- Accessors
  | Index  (Expr refT typeT) (Expr refT typeT) typeT
  | Lookup (Expr refT typeT) Name              typeT
  | TLookup (Expr refT typeT) Integer          typeT
  -- LC
  | Var         (Located refT)  typeT
  | Function    LName  typeT       (Expr refT typeT) typeT
  | Application (Expr refT typeT) (Expr refT typeT) typeT
  -- Sugar
  | LetBlock [LBind (Expr refT typeT)] (Expr refT typeT)
  deriving (Eq,Show,Functor,Foldable,Traversable)

data BlockStmt refT typeT
 -- Bind          bind var         context   expr
  = Bind          (Maybe (LBind typeT))     typeT     (Expr refT typeT)
  | BlockLet      [(LName,Expr refT typeT)]
  | BlockCode     (Located String)
  deriving (Eq,Show,Functor,Foldable,Traversable)

-- }}}

-- Type Level {{{

data TypeF typeT
  -- Constants
  = BitF
  | ZF
  | QuoteF
  | TermF
  -- Structures
  | ArrayF      typeT
  | BlockF      typeT typeT
  | TupleF      [typeT]
  | RecordF     [Bind typeT]
  -- LC
  | FunctionF   typeT typeT
  -- Abstract type
  | AbstractF Name
  -- Poly
  | PVar Name
  | PAbs [Name] typeT
  deriving (Show,Functor,Foldable,Traversable)

data ContextF typeT
  = CryptolSetupContext
  | JavaSetupContext
  | LLVMSetupContext
  | ProofScriptContext
  | TopLevelContext
  deriving (Eq,Show,Functor,Foldable,Traversable)

data Syn typeF = Syn LName
  deriving (Show,Functor,Foldable,Traversable)

data Context
  = CryptolSetup
  | JavaSetup
  | LLVMSetup
  | ProofScript
  | TopLevel
  deriving (Eq,Show)

data I a = I Integer deriving (Show,Functor,Foldable,Traversable)

data Type
  = TyCon TyCon [Type]
  | TyRecord (Map Name Type)
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
 | TermCon
 | BoolCon
 | ZCon
 | NumCon Integer
 | BlockCon
 | ContextCon Context
 | AbstractCon String
 deriving (Eq,Show)

data Schema = Forall [Name] Type deriving (Eq, Show)

-- }}}

-- Pretty Printing {{{

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
    (TupleCon _,_)         -> PP.parens $ commaSepAll $ map (pretty False) ts
    (ArrayCon,[len,TyCon BoolCon []]) -> PP.brackets (pretty False len)
    (ArrayCon,[len,typ])   -> PP.brackets (pretty False len) PP.<> (pretty True typ)
    (FunCon,[f,v])         -> (if par then PP.parens else id) $
                                pretty False f PP.<+> PP.text "->" PP.<+> pretty False v
    (BlockCon,[cxt,typ])   -> (if par then PP.parens else id) $
                                pretty True cxt PP.<+> pretty True typ
    _ -> error $ "malformed TyCon: " ++ pShow t
  pretty _par (TyRecord fs) =
      PP.braces
    $ commaSepAll
    $ map (\(n,t) -> PP.text n `prettyTypeSig` pretty False t)
    $ Map.toList fs
  pretty par (TyVar tv) = pretty par tv

instance PrettyPrint TyVar where
  pretty _par tv = case tv of
    FreeVar n  -> PP.text "fv." PP.<> PP.integer n
    BoundVar n -> PP.text n

instance PrettyPrint TyCon where
  pretty par tc = case tc of
    TupleCon n     -> PP.parens $ replicateDoc (n - 1) $ PP.char ','
    ArrayCon       -> PP.parens $ PP.brackets $ PP.empty
    FunCon         -> PP.parens $ PP.text "->"
    StringCon      -> PP.text "String"
    TermCon        -> PP.text "Term"
    BoolCon        -> PP.text "Bit"
    ZCon           -> PP.text "Int"
    NumCon n       -> PP.integer n
    BlockCon       -> PP.text "<Block>"
    ContextCon cxt -> pretty par cxt
    AbstractCon n  -> PP.text n

instance PrettyPrint Context where
  pretty _ c = case c of
    CryptolSetup -> PP.text "CryptolSetup"
    JavaSetup    -> PP.text "JavaSetup"
    LLVMSetup    -> PP.text "LLVMSetup"
    ProofScript  -> PP.text "ProofScript"
    TopLevel     -> PP.text "TopLevel"

instance PrettyPrint ModuleName where
  pretty _ mn = PP.text (renderModuleName mn)

instance PrettyPrint (Module refT exprT typeT) where
  pretty par m = pretty par (moduleName m)

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

-- }}}

-- Type Constructors {{{

tMono :: Type -> Schema
tMono = Forall []

tForall :: [Name] -> Schema -> Schema
tForall xs (Forall ys t) = Forall (xs ++ ys) t

tTuple :: [Type] -> Type
tTuple ts = TyCon (TupleCon $ fromIntegral $ length ts) ts

tArray :: Type -> Type
tArray t = TyCon ArrayCon [t]

tFun :: Type -> Type -> Type
tFun f v = TyCon FunCon [f,v]

tString :: Type
tString = TyCon StringCon []

tTerm :: Type
tTerm = TyCon TermCon []

tBool :: Type
tBool = TyCon BoolCon []

tZ :: Type
tZ = TyCon ZCon []

tNum :: Integral a => a -> Type
tNum n = TyCon (NumCon $ toInteger n) []

tBlock :: Type -> Type -> Type
tBlock c t = TyCon BlockCon [c,t]

tContext :: Context -> Type
tContext c = TyCon (ContextCon c) []

tAbstract :: Name -> Type
tAbstract n = TyCon (AbstractCon n) []

boundVar :: Name -> Type
boundVar n = TyVar (BoundVar n)

-- }}}

-- Equal Instances {{{

instance Equal TypeF where
  equal ty1 ty2 = case (ty1,ty2) of
    (BitF,BitF)                           -> True
    (ZF,ZF)                               -> True
    (QuoteF,QuoteF)                       -> True
    (TermF,TermF)                         -> True
    (ArrayF at1,ArrayF at2)               -> at1 == at2
    (BlockF c1 bt1,BlockF c2 bt2)         -> c1 == c2 && bt1 == bt2
    (TupleF ts1,TupleF ts2)               -> ts1 == ts2
    (RecordF fts1,RecordF fts2)           -> fts1 == fts2
    (FunctionF at1 bt1,FunctionF at2 bt2) -> at1 == at2 && bt1 == bt2
    (PVar n1,PVar n2)                     -> n1 == n2
    (PAbs ns1 t1,PAbs ns2 t2)             -> ns1 == ns2 && t1 == t2
    _                                     -> False

instance Equal I where
  equal (I x) (I y) = x == y

instance Equal ContextF where
  equal c1 c2 = case (c1,c2) of
    (CryptolSetupContext , CryptolSetupContext) -> True
    (JavaSetupContext    , JavaSetupContext   ) -> True
    (LLVMSetupContext    , LLVMSetupContext   ) -> True
    (ProofScriptContext  , ProofScriptContext ) -> True
    (TopLevelContext     , TopLevelContext    ) -> True
    _ -> False

instance Equal Syn where
  equal (Syn n1) (Syn n2) = n1 == n2

-- }}}

-- Render Instances {{{

instance Render TypeF where
  render ty = case ty of
    BitF            -> "BitF"
    ZF              -> "ZF"
    QuoteF          -> "QuoteF"
    TermF           -> "TermF"
    ArrayF at       -> "(ArrayF " ++ show at ++ ")"
    BlockF c bt     -> "(BlockF " ++ show c ++ " " ++ show bt ++ ")"
    TupleF ts       -> "(TupleF [" ++ (intercalate ", " $ map show ts) ++ "])"
    RecordF fts     -> "(RecordF [" ++ (intercalate ", " $ map (\(n,bt)-> n ++ " :: " ++ show bt) fts) ++ "])"
    FunctionF at bt -> "(FunctionF " ++ show at ++ " " ++ show bt ++ ")"
    AbstractF n     -> "(AbstractF " ++ show n ++ ")"
    PVar n          -> "(PVar " ++ show n ++ ")"
    PAbs ns t       -> "(PAbs " ++ show ns ++ " " ++ show t ++ ")"

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

-- }}}

-- Uni Instances {{{

instance Uni TypeF where
  uni t1 t2 = case (t1,t2) of
    (ArrayF at1,ArrayF at2)                   -> unify at1 at2
    (BlockF c1 bt1,BlockF c2 bt2)             -> unify c1 c2 >> unify bt1 bt2
    (TupleF ts1,TupleF ts2)                   -> zipWithMP_ unify ts1 ts2
    (RecordF fts1,RecordF fts2)               -> do conj [ disj [ unify x y | (nx,x) <- fts1, nx == ny ] | (ny,y) <- fts2 ]
                                                    conj [ disj [ unify y x | (ny,y) <- fts2, nx == ny ] | (nx,x) <- fts1 ]
    (FunctionF at1 bt1,FunctionF at2 bt2)     -> unify at1 at2 >> unify bt1 bt2
    (PVar n1, PVar n2)                        -> fail ("Poly: " ++ show n1 ++ " =/= " ++ show n2)
    -- TODO: Alpha renaming? no, variable substitution.
    -- (PAbs ns1 ty1, PAbs ns2 ty2)              -> undefined ns1 ty1 ns2 ty2
    _                                         -> fail ("Type Mismatch: " ++ render t1 ++ " could not be unified with " ++ render t2)

instance Uni I where
  uni (I x) (I y) = fail $ "I: " ++ show x ++ " =/= " ++ show y

instance Uni ContextF where
  uni c1 c2 = fail $ "Context: " ++ render c1 ++ " =/= " ++ render c2

-- }}}

-- Injection Operators {{{

bit :: (TypeF :<: f) => Mu f
bit = inject BitF

quote :: (TypeF :<: f) => Mu f
quote = inject QuoteF

term :: (TypeF :<: f) => Mu f
term = inject TermF

z :: (TypeF :<: f) => Mu f
z = inject ZF

array :: (I :<: f, TypeF :<: f) => Mu f -> Mu f
array t = inject $ ArrayF t

block :: (ContextF :<: f, TypeF :<: f) => Mu f -> Mu f -> Mu f
block c t = inject $ BlockF c t

tuple :: (TypeF :<: f) => [Mu f] -> Mu f
tuple ts = inject $ TupleF ts

record :: (TypeF :<: f) => [Bind (Mu f)] -> Mu f
record fts = inject $ RecordF fts

function :: (TypeF :<: f) => Mu f -> Mu f -> Mu f
function at bt = inject $ FunctionF at bt

abstract :: (TypeF :<: f) => Name -> Mu f
abstract n = inject $ AbstractF n

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

syn :: (Syn :<: f) => LName -> Mu f
syn n = inject $ Syn n

i :: (I :<: f) => Integer -> Mu f
i x = inject $ I x

pVar :: (TypeF :<: f) => Name -> Mu f
pVar n = inject $ PVar n

pAbs :: (TypeF :<: f) => [Name] -> Mu f -> Mu f
pAbs ns t = inject $ PAbs ns t

-- }}}

-- Expr Accessors/Modifiers {{{

typeOf :: Expr refT typeT -> typeT
typeOf expr = case expr of
  Bit _ t           -> t
  Quote _ t         -> t
  Z _ t             -> t
  Undefined t       -> t
  Code _ t          -> t
  Array _ t         -> t
  Block _ t         -> t
  Tuple _ t         -> t
  Record _ t        -> t
  Index _ _ t       -> t
  Lookup _ _ t      -> t
  TLookup _ _ t     -> t
  Var _ t           -> t
  Function _ _ _ t  -> t
  Application _ _ t -> t
  LetBlock _ e'     -> typeOf e'

context :: BlockStmt refT typeT -> Maybe typeT
context s = case s of
  Bind _ c _ -> Just c
  _          -> Nothing

updateAnnotation :: typeT -> Expr refT typeT -> Expr refT typeT
updateAnnotation t expr = case expr of
  Bit x _           -> Bit x t
  Quote x _         -> Quote x t
  Z x _             -> Z x t
  Undefined _       -> Undefined t
  Code x _          -> Code x t
  Array x _         -> Array x t
  Block x _         -> Block x t
  Tuple x _         -> Tuple x t
  Record x _        -> Record x t
  Index x y _       -> Index x y t
  Lookup x y _      -> Lookup x y t
  TLookup x y _     -> TLookup x y t
  Var x _           -> Var x t
  Function a at b _ -> Function a at b t
  Application f v _ -> Application f v t
  LetBlock bs e'    -> LetBlock bs (updateAnnotation t e')

-- }}}

-- Type conversion {{{

{- 'SAWScript.MGU' handles the fairly complex process of inference and
unification that converts 'ResolvedT' to 'Schema'.  Since 'Schema' is really a
subtype of 'ResolvedT', going in the other direction is trivial.
'rewindSchema' performs this trivial (but necessary) conversion, effectively
rewinding a SAWScript type through one stage of the compiler pipeline.  Since
it's intended to work on 'SAWScript.MGU' output, it makes a lot of assumptions
about the precise format of the 'Schema'; failure to adhere to these
assumptions yields an 'error' (hooray). -}

rewindSchema :: Schema -> ResolvedT
rewindSchema (Forall vars t) = Just $ if null vars
                                      then rewindType t
                                      else pAbs vars $ rewindType t

{- I wish we could use 'Data.Data' and 'Data.Typeable' to make these assertions
a bit nicer.  Too bad 'Data.Typeable' doesn't play nicely with 'Mu'.... -}
rewindType :: Type -> FullT
rewindType (TyCon BoolCon parameters) = rewindNullary "BoolCon" bit parameters
rewindType (TyCon ZCon parameters) = rewindNullary "ZCon" z parameters
rewindType (TyCon StringCon parameters)= rewindNullary "StringCon" quote parameters
rewindType (TyCon TermCon parameters)= rewindNullary "TermCon" quote parameters
rewindType (TyCon (NumCon n) parameters) = rewindNullary "NumCon" (i n) parameters
rewindType (TyCon (AbstractCon n) parameters) = rewindNullary "AbstractCon" (abstract n) parameters
rewindType (TyCon (ContextCon ctx) parameters) = rewindNullary "context" (rewindContext ctx) parameters
rewindType (TyCon ArrayCon parameters) = rewindUnary "ArrayCon" array parameters
rewindType (TyCon BlockCon parameters) = rewindBinary "BlockCon" block parameters
rewindType (TyCon FunCon parameters) = rewindBinary "FunCon" function parameters
rewindType (TyCon (TupleCon _len) types) = tuple $ map rewindType types
rewindType (TyRecord bindings) = record $ Map.assocs $ Map.map rewindType bindings
rewindType (TyVar var) = case var of
  BoundVar name -> pVar name
  FreeVar name -> error $ "rewindType: FreeVar in Schema: " ++ show name

rewindContext :: Context -> FullT
rewindContext CryptolSetup = cryptolSetupContext
rewindContext JavaSetup = javaSetupContext
rewindContext LLVMSetup = llvmSetupContext
rewindContext ProofScript = proofScriptContext
rewindContext TopLevel = topLevelContext

rewindNullary :: String -> FullT -> [a] -> FullT
rewindNullary _name  con [] = con
rewindNullary  name _con _  = error $ "rewindType: applied " ++ name

rewindUnary :: String -> (FullT -> FullT) -> [Type] -> FullT
rewindUnary _name  con [a] = con (rewindType a)
rewindUnary  name _con parameters =
  error $ "rewindType: "
          ++ name
          ++ " should have arity 1 but was applied to "
          ++ show (length parameters)
          ++ " arguments"

rewindBinary :: String -> (FullT -> FullT -> FullT) -> [Type] -> FullT
rewindBinary _name  con [a, b] = con (rewindType a) (rewindType b)
rewindBinary  name _con parameters =
  error $ "rewindType: "
          ++ name
          ++ " should have arity 2 but was applied to "
          ++ show (length parameters)
          ++ " arguments"

-- }}}

-- capturePVars {{{

capturePVars :: [Name] -> RawSigT -> RawSigT
capturePVars ns = foldMu (capturePVarsF ns)

class (Functor f) => CapturePVars f where
  capturePVarsF :: [Name] -> f RawSigT -> RawSigT

instance (CapturePVars f, CapturePVars g) => CapturePVars (f :+: g) where
  capturePVarsF ns t = case t of
    Inl e -> capturePVarsF ns e
    Inr e -> capturePVarsF ns e

instance CapturePVars TypeF where
  capturePVarsF ns t = case t of
    ArrayF ty1        -> array (capturePVars ns ty1)
    BlockF ctx ty1    -> block ctx (capturePVars ns ty1)
    TupleF tys        -> tuple $ map (capturePVars ns) tys
    RecordF flds      -> record $ onBinds (capturePVars ns) flds
    FunctionF ty1 ty2 -> function (capturePVars ns ty1) (capturePVars ns ty2)
    PAbs ns' ty       -> pAbs ns' $ capturePVars ns ty
    _ -> inject t

instance CapturePVars Syn where
  capturePVarsF ns (Syn n) = if getVal n `elem` ns
    then pVar (getVal n)
    else syn n

instance CapturePVars I where
  capturePVarsF _ = inject

instance CapturePVars ContextF where
  capturePVarsF _ = inject

-- }}}
