{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.CryptolEnv
  ( CryptolEnv(..)
  , initCryptolEnv
  , loadCryptolModule
  , bindCryptolModule
  , lookupCryptolModule
  , importModule
  , bindTypedTerm
  , bindType
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
import Data.Text.Lazy (Text, pack)

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
import Data.Traversable
#endif

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
import qualified Cryptol.ModuleSystem.Name as MN
import qualified Cryptol.ModuleSystem.Renamer as MR

import Cryptol.Utils.PP
import Cryptol.Utils.Ident (Ident, preludeName, packIdent, interactiveName)

--import SAWScript.REPL.Monad (REPLException(..))
import SAWScript.TypedTerm
import SAWScript.Utils (Pos(..))
import SAWScript.AST (Located(getVal, getPos), Import(..))

--------------------------------------------------------------------------------

data CryptolEnv s = CryptolEnv
  { eImports    :: [P.Import]                -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv              -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv              -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.Name T.Schema       -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn        -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name (SharedTerm s) -- ^ SAWCore terms for *all* names in scope
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
      path <- MB.findModule preludeName
      MB.loadModuleByPath path

  -- Generate SAWCore translations for all values in scope
  termEnv <- genTermEnv sc modEnv

  return CryptolEnv
    { eImports    = [P.Import preludeName Nothing Nothing]
    , eModuleEnv  = modEnv
    , eExtraNames = mempty
    , eExtraTypes = Map.empty
    , eExtraTSyns = Map.empty
    , eTermEnv    = termEnv
    }

-- Parse -----------------------------------------------------------------------

ioParseExpr :: Located String -> IO (P.Expr P.PName)
ioParseExpr = ioParseGeneric P.parseExprWith

ioParseDecls :: Located String -> IO [P.Decl P.PName]
ioParseDecls = ioParseGeneric P.parseDeclsWith

ioParseSchema :: Located String -> IO (P.Schema P.PName)
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
                 , replicate (col - 1 + 2) ' ' -- add 2 to compensate for dropped "{{"
                 , getVal lstr ]

ioParseResult :: Either P.ParseError a -> IO a
ioParseResult res = case res of
  Right a -> return a
  Left e  -> fail $ "Cryptol parse error:\n" ++ show (P.ppError e) -- X.throwIO (ParseError e)

-- Rename ----------------------------------------------------------------------

getNamingEnv :: CryptolEnv s -> MR.NamingEnv
getNamingEnv env = eExtraNames env `MR.shadowing` nameEnv
  where
    nameEnv = mconcat $ fromMaybe [] $ traverse loadImport (eImports env)
    loadImport i = do
      lm <- ME.lookupModule (T.iModule i) (eModuleEnv env)
      return $ MN.interpImport i (MI.ifPublic (ME.lmInterface lm))

getAllIfaceDecls :: ME.ModuleEnv -> M.IfaceDecls
getAllIfaceDecls me = mconcat (map (both . ME.lmInterface) (ME.getLoadedModules (ME.meLoadedModules me)))
  where both ifc = M.ifPublic ifc `mappend` M.ifPrivate ifc

-- Typecheck -------------------------------------------------------------------

runInferOutput :: TM.InferOutput a -> MM.ModuleM a
runInferOutput out =
  case out of

    TM.InferOK warns seeds supply o ->
      do MM.setNameSeeds seeds
         MM.setSupply supply
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
  (prims, _) <- liftModuleM modEnv MB.getPrimMap
  (types, _) <- liftModuleM modEnv $
                TM.inpVars `fmap` MB.genInferInput P.emptyRange prims ifaceDecls
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
  (types, _) <- liftModuleM modEnv $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims ifaceDecls
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
  let names = map T.dName decls
  let newTypes = Map.fromList [ (T.dName d, T.dSignature d) | d <- decls ]
  let addName name = MR.shadowing (MN.singletonE (P.mkUnqual (MN.nameIdent name)) name)
  return env
        { eExtraNames = foldr addName (eExtraNames env) names
        , eExtraTypes = Map.union (eExtraTypes env) newTypes
        , eTermEnv = termEnv'
        }

-- | Translate all declarations in all loaded modules to SAWCore terms
genTermEnv :: SharedContext s -> ME.ModuleEnv -> IO (Map T.Name (SharedTerm s))
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
  (types, _) <- liftModuleM modEnv $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims ifaceDecls
  terms <- genTermEnv sc modEnv
  let names = P.eBinds (T.mExports m) -- :: Set T.Name
  let tm' = Map.filterWithKey (\k _ -> Set.member k names) $
            Map.intersectionWith TypedTerm types terms
  return (CryptolModule tm')

bindCryptolModule :: forall s. (P.ModName, CryptolModule s) -> CryptolEnv s -> CryptolEnv s
bindCryptolModule (modName, CryptolModule tm) env =
  env { eExtraNames = foldr addName (eExtraNames env) (Map.keys tm)
      , eExtraTypes = Map.union (fmap (\(TypedTerm s _) -> s) tm) (eExtraTypes env)
      , eTermEnv    = Map.union (fmap (\(TypedTerm _ t) -> t) tm) (eTermEnv env)
      }
  where
    addName name = MN.shadowing (MN.singletonE (P.mkQual modName (MN.nameIdent name)) name)

lookupCryptolModule :: CryptolModule s -> String -> IO (TypedTerm s)
lookupCryptolModule (CryptolModule tm) name =
  case Map.lookup (packIdent name) (Map.mapKeys MN.nameIdent tm) of
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

  -- Regenerate SharedTerm environment. TODO: preserve old
  -- values, only translate decls from new module.
  let oldTermEnv = eTermEnv env
  newTermEnv <- genTermEnv sc modEnv'

  return env { eImports = P.Import (T.mName m) (iAs imp) (iSpec imp) : eImports env
             , eModuleEnv = modEnv'
             , eTermEnv = Map.union newTermEnv oldTermEnv }

bindIdent :: Ident -> CryptolEnv s -> (T.Name, CryptolEnv s)
bindIdent ident env = (name, env')
  where
    modEnv = eModuleEnv env
    supply = ME.meSupply modEnv
    (name, supply') = MN.mkDeclared interactiveName ident P.emptyRange supply
    modEnv' = modEnv { ME.meSupply = supply' }
    env' = env { eModuleEnv = modEnv' }

bindTypedTerm :: (Ident, TypedTerm s) -> CryptolEnv s -> CryptolEnv s
bindTypedTerm (ident, TypedTerm schema trm) env =
  env' { eExtraNames = MR.shadowing (MN.singletonE pname name) (eExtraNames env)
       , eExtraTypes = Map.insert name schema (eExtraTypes env)
       , eTermEnv    = Map.insert name trm (eTermEnv env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env

bindType :: (Ident, T.Schema) -> CryptolEnv s -> CryptolEnv s
bindType (ident, T.Forall [] [] ty) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] ty
bindType _ env = env -- only monomorphic types may be bound

bindInteger :: (Ident, Integer) -> CryptolEnv s -> CryptolEnv s
bindInteger (ident, n) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] (T.tNum n)

--------------------------------------------------------------------------------

parseTypedTerm :: SharedContext s -> CryptolEnv s -> Located String -> IO (TypedTerm s)
parseTypedTerm sc env input = do
  let modEnv = eModuleEnv env

  -- Parse
  pexpr <- ioParseExpr input

  ((expr, schema), modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    npe <- MM.interactive (MB.noPat pexpr)

    -- Resolve names
    let nameEnv = getNamingEnv env
    re <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename npe))

    -- Infer types
    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc re)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }

  -- Translate
  trm <- translateExpr sc env' expr
  return (TypedTerm schema trm)

parseDecls :: SharedContext s -> CryptolEnv s -> Located String -> IO (CryptolEnv s)
parseDecls sc env input = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv

  -- Parse
  (decls :: [P.Decl P.PName]) <- ioParseDecls input

  (dgs, modEnv') <- liftModuleM modEnv $ do

    -- Eliminate patterns
    (npdecls :: [P.Decl P.PName]) <- MM.interactive (MB.noPat decls)

    -- Convert from 'Decl' to 'TopDecl' so that types will be generalized
    let topdecls = [ P.Decl (P.TopLevel P.Public Nothing d) | d <- npdecls ]

    -- Label each TopDecl with the "interactive" module for unique name generation
    let (mdecls :: [MN.InModule (P.TopDecl P.PName)]) = map (MN.InModule interactiveName) topdecls
    nameEnv1 <- MN.liftSupply (MN.namingEnv' mdecls)

    -- Resolve names
    let nameEnv = nameEnv1 `MR.shadowing` getNamingEnv env
    (rdecls :: [P.TopDecl T.Name]) <- MM.interactive (MB.rename interactiveName nameEnv (traverse MR.rename topdecls))

    -- Infer types
    let range = fromMaybe P.emptyRange (P.getLoc rdecls)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims ifaceDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcDecls rdecls tcEnv') -- FIXME: instead of using tcDecls,
                                           -- use something like inferModule,
                                           -- which also returns TSyns.
    dgs <- MM.interactive (runInferOutput out)
    return dgs

  let env' = env { eModuleEnv = modEnv' }

  -- Translate
  translateDeclGroups sc env' dgs

parseSchema :: CryptolEnv s -> Located String -> IO T.Schema
parseSchema env input = do
  --putStrLn $ "parseSchema: " ++ show input
  let modEnv = eModuleEnv env

  -- Parse
  pschema <- ioParseSchema input
  --putStrLn $ "ioParseSchema: " ++ show pschema

  fmap fst $ liftModuleM modEnv $ do

    nameEnv1 <- MN.liftSupply (MN.namingEnv' pschema)
    -- Resolve names
    let nameEnv = nameEnv1 `MR.shadowing` getNamingEnv env
    rschema <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename pschema))

    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc rschema)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims ifDecls
    let tcEnv' = tcEnv { TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv) }
    let infer =
          case rschema of
            P.Forall [] [] t _ -> do
              t' <- TK.checkType t Nothing -- allow either kind KNum or KType
              return (T.Forall [] [] t', [])
            _ -> TK.checkSchema rschema
    out <- MM.io (TM.runInferM tcEnv' infer)
    (schema, goals) <- MM.interactive (runInferOutput out)
    unless (null goals) (MM.io (print goals))
    return (schemaNoUser schema)

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec [ (n, typeNoUser ty) | (n, ty) <- fields ]

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)

------------------------------------------------------------

liftModuleM :: ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m = MM.runModuleM env m >>= moduleCmdResult

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  mapM_ (print . pp) ws
  case res of
    Right (a, me) -> return (a, me)
    Left err      -> fail $ "Cryptol error:\n" ++ show (pp err) -- X.throwIO (ModuleSystemError err)
