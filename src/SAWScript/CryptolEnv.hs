module SAWScript.CryptolEnv
  ( CryptolEnv
  , initCryptolEnv
  , importModule
  , bindTypedTerm
  , parseTypedTerm
  , parseDecls
  )
  where

--import qualified Control.Exception as X
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Traversable

import Verifier.SAW.SharedTerm (SharedContext, SharedTerm, incVars)

import qualified Verifier.SAW.Cryptol as C

import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
--import qualified Cryptol.TypeCheck.InferTypes as T
import qualified Cryptol.TypeCheck.Monad as TM

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Renamer as MR

import Cryptol.Utils.PP

--import SAWScript.REPL.Monad (REPLException(..))
import SAWScript.Value
import SAWScript.Utils (Pos(..))
import SAWScript.AST (Located(getVal, getPos))

--------------------------------------------------------------------------------

data CryptolEnv s = CryptolEnv
  { eTargetMods :: [(P.ModName, FilePath)]    -- ^ Which modules to use for naming environment
  , eModuleEnv  :: ME.ModuleEnv               -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv               -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.QName T.Schema       -- ^ Cryptol types for extra names in scope
  , eTermEnv    :: Map T.QName (SharedTerm s) -- ^ SAWCore terms for *all* names in scope
  }

-- Initialize ------------------------------------------------------------------

initCryptolEnv :: SharedContext s -> IO (CryptolEnv s)
initCryptolEnv sc = do
  modEnv0 <- M.initialModuleEnv

  -- Load Cryptol prelude
  (preludePath, modEnv) <-
    liftModuleM modEnv0 $ do
      path <- MB.findModule MB.preludeName
      MB.loadModuleByPath path
      return path

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv

  return CryptolEnv
    { eTargetMods = [(MB.preludeName, preludePath)]
    , eModuleEnv  = modEnv
    , eExtraNames = mempty
    , eExtraTypes = Map.empty
    , eTermEnv    = termEnv
    }

-- Parse -----------------------------------------------------------------------

ioParseExpr :: Located String -> IO P.Expr
ioParseExpr = ioParseGeneric P.parseExprWith

ioParseDecls :: Located String -> IO [P.Decl]
ioParseDecls = ioParseGeneric P.parseDeclsWith

ioParseGeneric :: (P.Config -> String -> Either P.ParseError a) -> Located String -> IO a
ioParseGeneric parse lstr = ioParseResult (parse cfg str)
  where
    (file, line, col) =
      case getPos lstr of
        Pos f l c     -> (f, l, c)
        PosInternal s -> (s, 1, 1)
        PosREPL       -> ("<interactive>", 1, 1)
    cfg = P.defaultConfig { P.cfgSource = file }
    str = concat [ replicate (line - 1) '\n'
                 , replicate (col - 1 + 2) ' ' -- ^ add 2 to compensate for dropped "{{"
                 , getVal lstr ]

ioParseResult :: Either P.ParseError a -> IO a
ioParseResult res = case res of
  Right a -> return a
  Left e  -> fail $ "Cryptol parse error:\n" ++ show (P.ppError e) -- X.throwIO (ParseError e)

-- Rename ----------------------------------------------------------------------

getNamingEnv :: CryptolEnv s -> IO MR.NamingEnv
getNamingEnv env = do
  let modEnv = eModuleEnv env
  let names = eExtraNames env
  let mods = eTargetMods env
  (envs, _) <- liftModuleM modEnv $ traverse (getModuleNamingEnv . fst) mods
  return (names `MR.shadowing` mconcat envs)

getModuleNamingEnv :: P.ModName -> MM.ModuleM MR.NamingEnv
getModuleNamingEnv mn = do
  -- FIXME HACK; should replace/rewrite getFocusedEnv instead, and get rid of meFocusedModule
  MM.setFocusedModule mn
  MR.namingEnv `fmap` MM.getFocusedEnv

getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me = mconcat (map (both . ME.lmInterface) (ME.getLoadedModules (ME.meLoadedModules me)))
  where both ifc = M.ifPublic ifc `mappend` M.ifPrivate ifc

-- Typecheck -------------------------------------------------------------------

runInferOutput :: TM.InferOutput a -> MM.ModuleM a
runInferOutput out =
  case out of

    TM.InferOK warns seeds o ->
      do MM.setNameSeeds seeds
         MM.typeCheckWarnings warns
         return o

    TM.InferFailed warns errs ->
      do MM.typeCheckWarnings warns
         MM.typeCheckingFailed errs

-- Translate -------------------------------------------------------------------

translateExpr :: SharedContext s -> CryptolEnv s -> T.Expr -> IO (SharedTerm s)
translateExpr sc env expr = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv
  (types, _) <- liftModuleM modEnv $
                TM.inpVars `fmap` MB.genInferInput P.emptyRange ifaceDecls
  let types' = Map.union (eExtraTypes env) types
  let terms = eTermEnv env
  let cryEnv = C.Env
        { C.envT = Map.empty
        , C.envE = fmap (\t -> (t, 0)) terms
        , C.envP = Map.empty
        , C.envC = types'
        }
  C.importExpr sc cryEnv expr

translateDeclGroups :: SharedContext s -> CryptolEnv s -> [T.DeclGroup] -> IO (CryptolEnv s)
translateDeclGroups sc env dgs = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv
  (types, _) <- liftModuleM modEnv $
                TM.inpVars `fmap` MB.genInferInput P.emptyRange ifaceDecls
  let types' = Map.union (eExtraTypes env) types
  let terms = eTermEnv env
  let cryEnv = C.Env
        { C.envT = Map.empty
        , C.envE = fmap (\t -> (t, 0)) terms
        , C.envP = Map.empty
        , C.envC = types'
        }
  cryEnv' <- C.importDeclGroups sc cryEnv dgs
  termEnv' <- traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv')

  let decls = concatMap T.groupDecls dgs
  let qnames = map T.dName decls
  let newTypes = Map.fromList [ (T.dName d, T.dSignature d) | d <- decls ]
  let addName qn = MR.shadowing (MN.singletonE qn (MN.EFromBind (P.Located P.emptyRange qn)))
  return env
        { eExtraNames = foldr addName (eExtraNames env) qnames
        , eExtraTypes = Map.union (eExtraTypes env) newTypes
        , eTermEnv = termEnv'
        }

-- | Translate all declarations in all loaded modules to SAWCore terms
genTermEnv :: SharedContext s -> ME.ModuleEnv -> IO (Map T.QName (SharedTerm s))
genTermEnv sc modEnv = do
  let declGroups = concatMap T.mDecls (ME.loadedModules modEnv)
  cryEnv <- C.importDeclGroups sc C.emptyEnv declGroups
  traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv)

--------------------------------------------------------------------------------

importModule :: SharedContext s -> CryptolEnv s -> FilePath -> IO (CryptolEnv s)
importModule sc env path = do
  let modEnv = eModuleEnv env
  (m, modEnv') <- liftModuleM modEnv (MB.loadModuleByPath path)

  -- | Regenerate SharedTerm environment. TODO: preserve old
  -- values, only translate decls from new module.
  let oldTermEnv = eTermEnv env
  newTermEnv <- genTermEnv sc modEnv'

  return env { eTargetMods = (T.mName m, path) : eTargetMods env
             , eModuleEnv = modEnv'
             , eTermEnv = Map.union newTermEnv oldTermEnv }

bindTypedTerm :: (T.QName, TypedTerm s) -> CryptolEnv s -> CryptolEnv s
bindTypedTerm (qname, TypedTerm schema trm) env =
  env { eExtraNames = MR.shadowing (MN.singletonE qname ename) (eExtraNames env)
      , eExtraTypes = Map.insert qname schema (eExtraTypes env)
      , eTermEnv    = Map.insert qname trm (eTermEnv env)
      }
  where
    ename = MN.EFromBind (P.Located P.emptyRange qname)

--------------------------------------------------------------------------------

parseTypedTerm :: SharedContext s -> CryptolEnv s -> Located String -> IO (TypedTerm s)
parseTypedTerm sc env input = do
  let modEnv = eModuleEnv env

  -- | Parse
  pexpr <- ioParseExpr input

  -- | Eliminate patterns
  (npe, _) <- liftModuleM modEnv (MM.interactive (MB.noPat pexpr))

  -- | Resolve names
  nameEnv <- getNamingEnv env
  (re, _) <- liftModuleM modEnv (MM.interactive (MB.rename nameEnv npe))

  -- | Infer types
  let ifDecls = getAllIfaceDecls modEnv
  let range = fromMaybe P.emptyRange (P.getLoc re)
  (tcEnv, _) <- liftModuleM modEnv $ MB.genInferInput range ifDecls
  let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv) }

  out <- T.tcExpr re tcEnv'
  ((expr, schema), modEnv') <- liftModuleM modEnv (MM.interactive (runInferOutput out))
  let env' = env { eModuleEnv = modEnv' }

  -- | Translate
  trm <- translateExpr sc env' expr
  return (TypedTerm schema trm)

parseDecls :: SharedContext s -> CryptolEnv s -> Located String -> IO (CryptolEnv s)
parseDecls sc env input = do
  let modEnv = eModuleEnv env

  -- | Parse
  decls <- ioParseDecls input

  -- | Eliminate patterns
  (npdecls, _) <- liftModuleM modEnv (MM.interactive (MB.noPat decls))

  -- | Resolve names
  nameEnv <- MR.shadowing (MR.namingEnv npdecls) `fmap` getNamingEnv env
  (rdecls, _) <- liftModuleM modEnv (MM.interactive (MB.rename nameEnv npdecls))

  -- | Infer types
  let ifDecls = getAllIfaceDecls modEnv
  let range = fromMaybe P.emptyRange (P.getLoc rdecls)
  (tcEnv, _) <- liftModuleM modEnv $ MB.genInferInput range ifDecls
  let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv) }

  out <- T.tcDecls rdecls tcEnv'
  (dgs, modEnv') <- liftModuleM modEnv (runInferOutput out)
  let env' = env { eModuleEnv = modEnv' }

  -- | Translate
  translateDeclGroups sc env' dgs

------------------------------------------------------------

liftModuleM :: ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m = MM.runModuleM env m >>= moduleCmdResult

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (print . pp) ws
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> fail $ "Cryptol error:\n" ++ show (pp err) -- X.throwIO (ModuleSystemError err)
