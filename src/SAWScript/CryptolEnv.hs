module SAWScript.CryptolEnv
  ( CryptolEnv(..)
  , initCryptolEnv
  , loadCryptolModule
  , bindCryptolModule
  , lookupCryptolModule
  , importModule
  , bindTypedTerm
  , bindInteger
  , parseTypedTerm
  , parseDecls
  , parseSchema
  )
  where

--import qualified Control.Exception as X
import Control.Monad (unless)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Text.Lazy (Text, pack)
import Data.Traversable

import System.Environment.Executable(splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath)

import Verifier.SAW.SharedTerm (SharedContext, SharedTerm, incVars)

import qualified Verifier.SAW.Cryptol as C

import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
--import qualified Cryptol.TypeCheck.InferTypes as T
import qualified Cryptol.TypeCheck.Kind as TK
import qualified Cryptol.TypeCheck.Monad as TM

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Renamer as MR

import Cryptol.Utils.PP

--import SAWScript.REPL.Monad (REPLException(..))
import SAWScript.TypedTerm
import SAWScript.Utils (Pos(..))
import SAWScript.AST (Located(getVal, getPos), Import(..))

--------------------------------------------------------------------------------

data CryptolEnv s = CryptolEnv
  { eImports    :: [P.Import]                 -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv               -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv               -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.QName T.Schema       -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.QName T.TySyn        -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.QName (SharedTerm s) -- ^ SAWCore terms for *all* names in scope
  }

-- Initialize ------------------------------------------------------------------

initCryptolEnv :: SharedContext s -> IO (CryptolEnv s)
initCryptolEnv sc = do
  modEnv0 <- M.initialModuleEnv

  -- Set the Cryptol include path (TODO: we may want to do this differently)
  (binDir, _) <- splitExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  let modEnv1 = modEnv0 { ME.meSearchPath =
                           (instDir </> "lib") : ME.meSearchPath modEnv0 }

  -- Load Cryptol prelude
  (_, modEnv) <-
    liftModuleM modEnv1 $ do
      path <- MB.findModule MB.preludeName
      MB.loadModuleByPath path

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv

  return CryptolEnv
    { eImports    = [P.Import MB.preludeName Nothing Nothing]
    , eModuleEnv  = modEnv
    , eExtraNames = mempty
    , eExtraTypes = Map.empty
    , eExtraTSyns = Map.empty
    , eTermEnv    = termEnv
    }

-- Parse -----------------------------------------------------------------------

ioParseExpr :: Located String -> IO P.Expr
ioParseExpr = ioParseGeneric P.parseExprWith

ioParseDecls :: Located String -> IO [P.Decl]
ioParseDecls = ioParseGeneric P.parseDeclsWith

ioParseSchema :: Located String -> IO P.Schema
ioParseSchema = ioParseGeneric P.parseSchemaWith

ioParseGeneric :: (P.Config -> Text -> Either P.ParseError a) -> Located String -> IO a
ioParseGeneric parse lstr = ioParseResult (parse cfg (pack str))
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

getNamingEnv :: CryptolEnv s -> MR.NamingEnv
getNamingEnv env = eExtraNames env `MR.shadowing` MR.namingEnv iface
  where
    iface = mconcat $ fromMaybe [] $ traverse loadImport (eImports env)
    loadImport i = do
      lm <- ME.lookupModule (T.iModule i) (eModuleEnv env)
      let iface' = fst (MI.interpImport i (ME.lmInterface lm))
      return (MI.ifPublic iface')

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
  cryEnv' <- C.importTopLevelDeclGroups sc cryEnv dgs
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
  cryEnv <- C.importTopLevelDeclGroups sc C.emptyEnv declGroups
  traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv)

--------------------------------------------------------------------------------

loadCryptolModule :: SharedContext s -> FilePath -> IO (CryptolModule s)
loadCryptolModule sc path = do
  (result, warnings) <- M.loadModuleByPath path =<< M.initialModuleEnv
  mapM_ (print . pp) warnings
  (m, modEnv) <-
    case result of
      Left err -> fail (show (pp err))
      Right x -> return x
  let ifaceDecls = getAllIfaceDecls modEnv
  (types, _) <- liftModuleM modEnv $
                TM.inpVars `fmap` MB.genInferInput P.emptyRange ifaceDecls
  terms <- genTermEnv sc modEnv
  let qnames = P.eBinds (T.mExports m) -- :: Set T.QName
  let tm' = Map.mapKeysMonotonic P.unqual $
            Map.filterWithKey (\k _ -> Set.member k qnames) $
            Map.intersectionWith TypedTerm types terms
  return (CryptolModule tm')

bindCryptolModule :: (T.ModName, CryptolModule s) -> CryptolEnv s -> CryptolEnv s
bindCryptolModule (modName, CryptolModule tm) env =
  env { eExtraNames = foldr addName (eExtraNames env) (Map.keys tm)
      , eExtraTypes = Map.union (fmap (\(TypedTerm s _) -> s) tm') (eExtraTypes env)
      , eTermEnv    = Map.union (fmap (\(TypedTerm _ t) -> t) tm') (eTermEnv env)
      }
  where
    tm' = Map.mapKeysMonotonic (P.mkQual modName) tm
    addName name = MN.shadowing (MN.singletonE qname ename)
      where
        qname = P.QName (Just modName) name
        ename = MN.EFromBind (P.Located P.emptyRange qname)

lookupCryptolModule :: CryptolModule s -> String -> IO (TypedTerm s)
lookupCryptolModule (CryptolModule tm) name =
  case Map.lookup (P.Name name) tm of
    Nothing -> fail $ "Binding not found: " ++ name
    Just t -> return t

--------------------------------------------------------------------------------

importModule :: SharedContext s -> CryptolEnv s -> Import -> IO (CryptolEnv s)
importModule sc env imp = do
  let modEnv = eModuleEnv env
  path <- case iModule imp of
            Left path -> return path
            Right mn -> fst `fmap` liftModuleM modEnv (MB.findModule mn)
  (m, modEnv') <- liftModuleM modEnv (MB.loadModuleByPath path)

  -- | Regenerate SharedTerm environment. TODO: preserve old
  -- values, only translate decls from new module.
  let oldTermEnv = eTermEnv env
  newTermEnv <- genTermEnv sc modEnv'

  return env { eImports = P.Import (T.mName m) (iAs imp) (iSpec imp) : eImports env
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

bindInteger :: (T.QName, Integer) -> CryptolEnv s -> CryptolEnv s
bindInteger (qname, n) env =
  env { eExtraNames = MR.shadowing (MN.singletonT qname tname) (eExtraNames env)
      , eExtraTSyns = Map.insert qname tysyn (eExtraTSyns env)
      }
  where
    tname = MN.TFromSyn (P.Located P.emptyRange qname)
    tysyn = T.TySyn qname [] [] (T.tNum n)

--------------------------------------------------------------------------------

parseTypedTerm :: SharedContext s -> CryptolEnv s -> Located String -> IO (TypedTerm s)
parseTypedTerm sc env input = do
  let modEnv = eModuleEnv env

  -- | Parse
  pexpr <- ioParseExpr input

  -- | Eliminate patterns
  (npe, _) <- liftModuleM modEnv (MM.interactive (MB.noPat pexpr))

  -- | Resolve names
  let nameEnv = getNamingEnv env
  (re, _) <- liftModuleM modEnv (MM.interactive (MB.rename nameEnv npe))

  -- | Infer types
  let ifDecls = getAllIfaceDecls modEnv
  let range = fromMaybe P.emptyRange (P.getLoc re)
  (tcEnv, _) <- liftModuleM modEnv $ MB.genInferInput range ifDecls
  let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                     , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                     }

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
  let nameEnv = MR.namingEnv npdecls `MR.shadowing` getNamingEnv env
  (rdecls, _) <- liftModuleM modEnv (MM.interactive (MB.rename nameEnv npdecls))

  -- | Infer types
  let ifDecls = getAllIfaceDecls modEnv
  let range = fromMaybe P.emptyRange (P.getLoc rdecls)
  (tcEnv, _) <- liftModuleM modEnv $ MB.genInferInput range ifDecls
  let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv) }

  -- Convert from 'Decl' to 'TopDecl' so that types will be generalized
  let topdecls = [ P.Decl (P.TopLevel P.Public d) | d <- rdecls ]
  out <- T.tcDecls topdecls tcEnv'
  (dgs, modEnv') <- liftModuleM modEnv (MM.interactive (runInferOutput out))
  let env' = env { eModuleEnv = modEnv' }

  -- | Translate
  translateDeclGroups sc env' dgs

parseSchema :: CryptolEnv s -> Located String -> IO T.Schema
parseSchema env input = do
  --putStrLn $ "parseSchema: " ++ show input
  let modEnv = eModuleEnv env
  pschema <- ioParseSchema input
  --putStrLn $ "ioParseSchema: " ++ show pschema
  let ifDecls = getAllIfaceDecls modEnv
  let range = fromMaybe P.emptyRange (P.getLoc pschema)
  (tcEnv, _) <- liftModuleM modEnv $ MB.genInferInput range ifDecls
  out <- TM.runInferM tcEnv (TK.checkSchema pschema)
  ((schema, goals), _) <- liftModuleM modEnv (MM.interactive (runInferOutput out))
  unless (null goals) (print goals)
  return schema

------------------------------------------------------------

liftModuleM :: ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m = MM.runModuleM env m >>= moduleCmdResult

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (print . pp) ws
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> fail $ "Cryptol error:\n" ++ show (pp err) -- X.throwIO (ModuleSystemError err)
