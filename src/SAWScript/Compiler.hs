{-# LANGUAGE CPP #-}
module SAWScript.Compiler where

import SAWScript.Unify (foldMuM)
import SAWScript.AST

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.State
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Monoid
import Data.Traversable
#if __GLASGOW_HASKELL__ < 706
import Prelude hiding (catch)
#endif

-- Compiler {{{

type Compiler a b = a -> Err b

type Err = E (IO ())

newtype E r a = E { runE :: (String -> r) -> (a -> r) -> r }

instance Functor (E r) where
  fmap f m = E $ \ fl sc -> runE m fl (sc . f)

instance Monad (E r) where
  return a = E $ \ _  sc -> sc a
  m >>= k  = E $ \ fl sc ->
    runE m fl $ \ a ->
      runE (k a) fl sc
  fail str = E $ \ fl _  -> fl str

instance MonadPlus (E r) where
  mzero = fail "mzero"
  m1 `mplus` m2 = E $ \ fl sc ->
    runE m1 (\err -> runE m2 (\err' -> fl (err ++ "\n" ++ err')) sc) sc

instance Applicative (E r) where
  pure = return
  (<*>) = ap

instance Alternative (E r) where
  empty = mzero
  (<|>) = mplus

onFailure :: Compiler a b -> ((String -> IO ()) -> String -> IO ()) -> Compiler a b
(pass `onFailure` handler) input = E $ \fl sc -> runE (pass input) (handler fl) sc

onSuccess :: Compiler a b -> ((b -> IO ()) -> b -> IO ()) -> Compiler a b
(pass `onSuccess` handler) input = E $ \fl sc -> runE (pass input) fl (handler sc)

onFailureRes :: E r a -> ((String -> r) -> String -> r) -> E r a
m `onFailureRes` handler = E $ \fl sc -> runE m (handler fl) sc

compiler :: Show a => String -> Compiler a b -> Compiler a b
compiler name comp input = onFailureRes (comp input) $ \fl err ->
  fl $ intercalate "\n" [name ++ ": " ++ err, "in:",show input]

-- }}}

-- Interpret {{

data Env a = Env
  { typeEnv :: TypeEnv a
  , exprEnv :: ExprEnv a
  } deriving (Eq,Show)
data TypeEnv a = TypeEnv
  { teTypes :: [(Name,PType)]
  , teEnv   :: Maybe (Env a)
  } deriving (Eq,Show)
data ExprEnv a = ExprEnv
  { eeExprs :: [(Name,Expr a)]
  , eeEnv   :: Maybe (Env a)
  } deriving (Eq,Show)

modifyTypeEnv :: (TypeEnv a -> TypeEnv a) -> Env a -> Env a
modifyTypeEnv f e = e { typeEnv = f $ typeEnv e }
modifyExprEnv :: (ExprEnv a -> ExprEnv a) -> Env a -> Env a
modifyExprEnv f e = e { exprEnv = f $ exprEnv e }

modifyTypes :: ([(Name,PType)] -> [(Name,PType)]) -> TypeEnv a -> TypeEnv a
modifyTypes f te = te { teTypes = f $ teTypes te }
modifyTEEnv :: (Maybe (Env a) -> Maybe (Env a)) -> TypeEnv a -> TypeEnv a
modifyTEEnv f te = te { teEnv = f $ teEnv te }

modifyExprs :: ([(Name,Expr a)] -> [(Name,Expr a)]) -> ExprEnv a -> ExprEnv a
modifyExprs f ee = ee { eeExprs = f $ eeExprs ee }
modifyEEEnv :: (Maybe (Env a) -> Maybe (Env a)) -> ExprEnv a -> ExprEnv a
modifyEEEnv f ee = ee { eeEnv = f $ eeEnv ee }

instance Monoid (TypeEnv a) where
  mempty = TypeEnv mempty mempty
  (TypeEnv t1 e1) `mappend`(TypeEnv t2 e2) =
    TypeEnv (t1 <> t2) (e1 <> e2)

instance Monoid (ExprEnv a) where
  mempty = ExprEnv mempty mempty
  (ExprEnv t1 e1) `mappend`(ExprEnv t2 e2) =
    ExprEnv (t1 <> t2) (e1 <> e2)

instance Monoid (Env a) where
  mempty = Env mempty mempty
  (Env t1 e1) `mappend`(Env t2 e2) =
    Env (t1 <> t2) (e1 <> e2)

typePair :: Name -> PType -> Env a
typePair n pt = Env (TypeEnv [(n,pt)] Nothing) mempty
exprPair :: Name -> Expr a -> Env a
exprPair n e = Env mempty (ExprEnv [(n,e)] Nothing)

lookupType :: Name -> Env a -> Maybe PType
lookupType n = lookup n . teTypes . typeEnv

lookupExpr :: Name -> Env a -> Maybe (Expr a)
lookupExpr n = lookup n . eeExprs . exprEnv

{-
data Env = Env
  { sBinds :: M.Map Name (Expr PType)
  , sTypes :: M.Map Name PType
  }
-}

--type Interpret s d t = BlockStmt t -> ReaderT s (StateT d Err) ()

{-
data Mod ds mn =
  { modDecls :: M.Map Name (TopStmt ds)
  , modMain  :: [BlockStmt mn]
  } 
-}

