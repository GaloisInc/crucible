{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module      : $Header$
Description : Context for interpreting Cryptol within the cryptol server
License     : BSD3
Maintainer  : rdockins
Stability   : provisional

NOTE! This module is ripped from the corresponding functionality in SAWScript, and is
basically a copy-paste of module "SAWScript.CryptolEnv".  It would probably be better
to abstract this functionality into a single place, either within Crytpol proper,
or in a separate package
-}
module Lang.Crucible.Server.CryptolEnv
  ( CryptolEnv(..)
  , Import(..)
  , initCryptolEnv
  , loadCryptolModule
  , bindCryptolModule
  , lookupCryptolModule
  , importModule
  , bindTypedTerm
  , bindType
  , bindInteger
  , parseTypedTerm
  , inferTerm
  , checkTerm
  , renameTerm
  , translateExpr
  , parseDecls
  , parseSchema
  , declareName
  , declareIdent
  , typeNoUser
  , schemaNoUser
  , getNamingEnv
  , defaultEvalOpts
  )
  where

--import qualified Control.Exception as X
import qualified Data.ByteString as BS
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe (fromMaybe)
import Data.Text (Text, pack)

import System.Environment (lookupEnv)
import System.Environment.Executable (splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, splitSearchPath)

import Verifier.SAW.SharedTerm (SharedContext, Term, incVars)

import qualified Verifier.SAW.Cryptol as C

import qualified Cryptol.Eval as E
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Position as P
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Infer as TI
import qualified Cryptol.TypeCheck.Kind as TK
import qualified Cryptol.TypeCheck.Monad as TM
import qualified Cryptol.TypeCheck.Solve as TS

--import qualified Cryptol.TypeCheck.PP as TP

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as MB
import qualified Cryptol.ModuleSystem.Env as ME
import qualified Cryptol.ModuleSystem.Exports as MEx
import qualified Cryptol.ModuleSystem.Interface as MI
import qualified Cryptol.ModuleSystem.Monad as MM
import qualified Cryptol.ModuleSystem.NamingEnv as MN
import qualified Cryptol.ModuleSystem.Name as MN
import qualified Cryptol.ModuleSystem.Renamer as MR

import Cryptol.Utils.PP
import Cryptol.Utils.Ident (Ident, preludeName, packIdent, interactiveName)
import Cryptol.Utils.Logger (quietLogger)

import Lang.Crucible.Server.TypedTerm


--------------------------------------------------------------------------------
data Import = Import
  { iModule    :: Either FilePath P.ModName
  , iAs        :: Maybe P.ModName
  , iSpec      :: Maybe P.ImportSpec
  } deriving (Eq, Show)

data CryptolEnv = CryptolEnv
  { eImports    :: [P.Import]           -- ^ Declarations of imported Cryptol modules
  , eModuleEnv  :: ME.ModuleEnv         -- ^ Imported modules, and state for the ModuleM monad
  , eExtraNames :: MR.NamingEnv         -- ^ Context for the Cryptol renamer
  , eExtraTypes :: Map T.Name T.Schema  -- ^ Cryptol types for extra names in scope
  , eExtraTSyns :: Map T.Name T.TySyn   -- ^ Extra Cryptol type synonyms in scope
  , eTermEnv    :: Map T.Name Term      -- ^ SAWCore terms for *all* names in scope
  }

-- Initialize ------------------------------------------------------------------

initCryptolEnv :: SharedContext -> IO CryptolEnv
initCryptolEnv sc = do
  modEnv0 <- M.initialModuleEnv

  -- Set the Cryptol include path (TODO: we may want to do this differently)
  (binDir, _) <- splitExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  mCryptolPath <- lookupEnv "CRYPTOLPATH"
  let cryptolPaths =
        case mCryptolPath of
          Nothing -> []
          Just path ->
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
            -- Windows paths search from end to beginning
            reverse (splitSearchPath path)
#else
            splitSearchPath path
#endif
  let modEnv1 = modEnv0 { ME.meSearchPath = cryptolPaths ++
                           (instDir </> "lib") : ME.meSearchPath modEnv0 }

  -- Load Cryptol prelude
  (_, modEnv) <-
    liftModuleM modEnv1 $
      MB.loadModuleFrom False (MM.FromModule preludeName)

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

ioParseExpr :: String -> IO (P.Expr P.PName)
ioParseExpr = ioParseGeneric P.parseExprWith

ioParseDecls :: String -> IO [P.Decl P.PName]
ioParseDecls = ioParseGeneric P.parseDeclsWith

ioParseSchema :: String -> IO (P.Schema P.PName)
ioParseSchema = ioParseGeneric P.parseSchemaWith

ioParseGeneric :: (P.Config -> Text -> Either P.ParseError a) -> String -> IO a
ioParseGeneric parse str = ioParseResult (parse cfg (pack str))
  where
    cfg = P.defaultConfig

ioParseResult :: Either P.ParseError a -> IO a
ioParseResult res = case res of
  Right a -> return a
  Left e  -> fail $ "Cryptol parse error:\n" ++ show (P.ppError e) -- X.throwIO (ParseError e)

-- Rename ----------------------------------------------------------------------

getNamingEnv :: CryptolEnv -> MR.NamingEnv
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

translateExpr :: SharedContext -> CryptolEnv -> T.Expr -> IO Term
translateExpr sc env expr = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv
  (types, _) <- liftModuleM modEnv $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims MI.noIfaceParams ifaceDecls
  let types' = Map.union (eExtraTypes env) types
  let terms = eTermEnv env
  let cryEnv = C.emptyEnv
        { C.envE = fmap (\t -> (t, 0)) terms
        , C.envC = types'
        }
  C.importExpr sc cryEnv expr

translateDeclGroups :: SharedContext -> CryptolEnv -> [T.DeclGroup] -> IO CryptolEnv
translateDeclGroups sc env dgs = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv
  (types, _) <- liftModuleM modEnv $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims MI.noIfaceParams ifaceDecls
  let types' = Map.union (eExtraTypes env) types
  let terms = eTermEnv env
  let cryEnv = C.emptyEnv
        { C.envE = fmap (\t -> (t, 0)) terms
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
genTermEnv :: SharedContext -> ME.ModuleEnv -> IO (Map T.Name Term)
genTermEnv sc modEnv = do
  let declGroups = concatMap T.mDecls (ME.loadedModules modEnv)
  cryEnv <- C.importTopLevelDeclGroups sc C.emptyEnv declGroups
  traverse (\(t, j) -> incVars sc 0 j t) (C.envE cryEnv)

--------------------------------------------------------------------------------

loadCryptolModule :: SharedContext -> CryptolEnv -> FilePath
                     -> IO (CryptolModule, CryptolEnv)
loadCryptolModule sc env path = do
  let modEnv = eModuleEnv env
  (m, modEnv') <- liftModuleM modEnv (MB.loadModuleByPath path)

  let ifaceDecls = getAllIfaceDecls modEnv'
  (types, modEnv'') <- liftModuleM modEnv' $ do
    prims <- MB.getPrimMap
    TM.inpVars `fmap` MB.genInferInput P.emptyRange prims MI.noIfaceParams ifaceDecls

  -- Regenerate SharedTerm environment.
  let oldTermEnv = eTermEnv env
  newTermEnv <- genTermEnv sc modEnv''
  let names = MEx.eBinds (T.mExports m) -- :: Set T.Name
  let tm' = Map.filterWithKey (\k _ -> Set.member k names) $
            Map.intersectionWith TypedTerm types newTermEnv
  let env' = env { eModuleEnv = modEnv''
                 , eTermEnv = Map.union newTermEnv oldTermEnv
                 }
  let sm' = Map.filterWithKey (\k _ -> Set.member k (T.eTypes (T.mExports m))) (T.mTySyns m)
  return (CryptolModule sm' tm', env')

bindCryptolModule :: (P.ModName, CryptolModule) -> CryptolEnv -> CryptolEnv
bindCryptolModule (modName, CryptolModule sm tm) env =
  env { eExtraNames = flip (foldr addName) (Map.keys tm) $
                      flip (foldr addTSyn) (Map.keys sm) $ eExtraNames env
      , eExtraTSyns = Map.union sm (eExtraTSyns env)
      , eExtraTypes = Map.union (fmap (\(TypedTerm s _) -> s) tm) (eExtraTypes env)
      , eTermEnv    = Map.union (fmap (\(TypedTerm _ t) -> t) tm) (eTermEnv env)
      }
  where
    addName name = MN.shadowing (MN.singletonE (P.mkQual modName (MN.nameIdent name)) name)
    addTSyn name = MN.shadowing (MN.singletonT (P.mkQual modName (MN.nameIdent name)) name)

lookupCryptolModule :: CryptolModule -> String -> IO TypedTerm
lookupCryptolModule (CryptolModule _ tm) name =
  case Map.lookup (packIdent name) (Map.mapKeys MN.nameIdent tm) of
    Nothing -> fail $ "Binding not found: " ++ name
    Just t -> return t

--------------------------------------------------------------------------------

importModule :: SharedContext -> CryptolEnv -> Import -> IO CryptolEnv
importModule sc env imp = do
  let modEnv = eModuleEnv env

  (m, modEnv') <-
    liftModuleM modEnv $
    case iModule imp of
      Left path -> MB.loadModuleByPath path
      Right mn -> snd <$> MB.loadModuleFrom True (MM.FromModule mn)

  -- Regenerate SharedTerm environment. TODO: preserve old
  -- values, only translate decls from new module.
  let oldTermEnv = eTermEnv env
  newTermEnv <- genTermEnv sc modEnv'

  return env { eImports = P.Import (T.mName m) (iAs imp) (iSpec imp) : eImports env
             , eModuleEnv = modEnv'
             , eTermEnv = Map.union newTermEnv oldTermEnv }

bindIdent :: Ident -> CryptolEnv -> (T.Name, CryptolEnv)
bindIdent ident env = (name, env')
  where
    modEnv = eModuleEnv env
    supply = ME.meSupply modEnv
    fixity = Nothing
    (name, supply') = MN.mkDeclared interactiveName MN.UserName ident fixity P.emptyRange supply
    modEnv' = modEnv { ME.meSupply = supply' }
    env' = env { eModuleEnv = modEnv' }

-- | Produce a unique term-level @Name@ for the given @Ident@ and record its type,
--   without giving it a definition.
declareIdent :: Ident -> T.Schema -> CryptolEnv -> (T.Name, CryptolEnv)
declareIdent ident schema env =
   ( name
   , env' { eExtraNames = MR.shadowing (MN.singletonE pname name) (eExtraNames env')
          , eExtraTypes = Map.insert name schema (eExtraTypes env')
          }
   )
  where
   pname = P.mkUnqual ident
   (name, env') = bindIdent ident env


bindTypedTerm :: (Ident, TypedTerm) -> CryptolEnv -> CryptolEnv
bindTypedTerm (ident, TypedTerm schema trm) env =
  env' { eExtraNames = MR.shadowing (MN.singletonE pname name) (eExtraNames env)
       , eExtraTypes = Map.insert name schema (eExtraTypes env)
       , eTermEnv    = Map.insert name trm (eTermEnv env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env

bindType :: (Ident, T.Schema) -> CryptolEnv -> CryptolEnv
bindType (ident, T.Forall [] [] ty) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] ty Nothing
bindType _ env = env -- only monomorphic types may be bound

bindInteger :: (Ident, Integer) -> CryptolEnv -> CryptolEnv
bindInteger (ident, n) env =
  env' { eExtraNames = MR.shadowing (MN.singletonT pname name) (eExtraNames env)
       , eExtraTSyns = Map.insert name tysyn (eExtraTSyns env)
       }
  where
    pname = P.mkUnqual ident
    (name, env') = bindIdent ident env
    tysyn = T.TySyn name [] [] (T.tNum n) Nothing

--------------------------------------------------------------------------------

parseTypedTerm :: SharedContext -> CryptolEnv -> String -> IO TypedTerm
parseTypedTerm sc env input = do
  pexpr <- ioParseExpr input
  (env', schema, expr) <- inferTerm env pexpr

  -- Translate
  trm <- translateExpr sc env' expr
  return (TypedTerm schema trm)


renameTerm :: CryptolEnv -> P.Expr P.PName -> IO (CryptolEnv, P.Expr MN.Name)
renameTerm env pexpr = do
  let modEnv = eModuleEnv env

  (expr, modEnv') <- liftModuleM modEnv $ do
    -- Eliminate patterns
    npe <- MM.interactive (MB.noPat pexpr)

    -- Resolve names
    let nameEnv = getNamingEnv env
    MM.interactive (MB.rename interactiveName nameEnv (MR.rename npe))

  let env' = env{ eModuleEnv = modEnv' }
  return (env', expr)


checkTerm :: CryptolEnv -> P.Expr MN.Name -> T.Type -> IO (CryptolEnv, T.Expr)
checkTerm env re expectedType = do
  let modEnv = eModuleEnv env

  (expr, modEnv') <- liftModuleM modEnv $ do

    -- Infer types
    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc re)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    --out <- MM.io (T.tcExpr re tcEnv')
    out <- MM.io $ TM.runInferM tcEnv'
                (do e <- TI.checkE re (T.WithSource expectedType T.TypeWildCard) -- type source is kinda bogus...
                    TS.simplifyAllConstraints
                    return e)
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }
  return (env', expr)


inferTerm :: CryptolEnv -> P.Expr P.PName -> IO (CryptolEnv, T.Schema, T.Expr)
inferTerm env pexpr = do
  let modEnv = eModuleEnv env

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
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (T.tcExpr re tcEnv')
    MM.interactive (runInferOutput out)

  let env' = env { eModuleEnv = modEnv' }

  return (env', schema, expr)


parseDecls :: SharedContext -> CryptolEnv -> String -> IO CryptolEnv
parseDecls sc env input = do
  let modEnv = eModuleEnv env
  let ifaceDecls = getAllIfaceDecls modEnv

  -- Parse
  (decls :: [P.Decl P.PName]) <- ioParseDecls input

  (tmodule, modEnv') <- liftModuleM modEnv $ do

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

    -- Create a Module to contain the declarations
    let rmodule = P.Module (P.Located P.emptyRange interactiveName) Nothing [] rdecls

    -- Infer types
    let range = fromMaybe P.emptyRange (P.getLoc rdecls)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifaceDecls
    let tcEnv' = tcEnv { TM.inpVars = Map.union (eExtraTypes env) (TM.inpVars tcEnv)
                       , TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv)
                       }

    out <- MM.io (TM.runInferM tcEnv' (TI.inferModule rmodule))
    tmodule <- MM.interactive (runInferOutput out)
    return tmodule

  -- Add new type synonyms and their name bindings to the environment
  let syns' = Map.union (eExtraTSyns env) (T.mTySyns tmodule)
  let addName name = MR.shadowing (MN.singletonT (P.mkUnqual (MN.nameIdent name)) name)
  let names' = foldr addName (eExtraNames env) (Map.keys (T.mTySyns tmodule))
  let env' = env { eModuleEnv = modEnv', eExtraNames = names', eExtraTSyns = syns' }

  -- Translate
  let dgs = T.mDecls tmodule
  translateDeclGroups sc env' dgs

parseSchema :: CryptolEnv -> String -> IO T.Schema
parseSchema env input = do
  --putStrLn $ "parseSchema: " ++ show input
  let modEnv = eModuleEnv env

  -- Parse
  pschema <- ioParseSchema input
  --putStrLn $ "ioParseSchema: " ++ show pschema

  fmap fst $ liftModuleM modEnv $ do

    -- Resolve names
    let nameEnv = getNamingEnv env
    rschema <- MM.interactive (MB.rename interactiveName nameEnv (MR.rename pschema))

    let ifDecls = getAllIfaceDecls modEnv
    let range = fromMaybe P.emptyRange (P.getLoc rschema)
    prims <- MB.getPrimMap
    tcEnv <- MB.genInferInput range prims MI.noIfaceParams ifDecls
    let tcEnv' = tcEnv { TM.inpTSyns = Map.union (eExtraTSyns env) (TM.inpTSyns tcEnv) }
    let infer =
          case rschema of
            P.Forall [] [] t _ -> do
              let k = Nothing -- allow either kind KNum or KType
              (t', goals) <- TM.collectGoals $ TK.checkType t k
              return (T.Forall [] [] t', goals)
            _ -> TK.checkSchema TM.AllowWildCards rschema
    out <- MM.io (TM.runInferM tcEnv' infer)
    (schema, _goals) <- MM.interactive (runInferOutput out)
    --mapM_ (MM.io . print . TP.ppWithNames TP.emptyNameMap) goals
    return (schemaNoUser schema)

declareName :: CryptolEnv -> P.ModName -> String -> IO (T.Name, CryptolEnv)
declareName env mname input = do
  let pname = P.mkUnqual (packIdent input)
  let modEnv = eModuleEnv env
  (cname, modEnv') <-
    liftModuleM modEnv $ MM.interactive $
    MN.liftSupply (MN.mkDeclared mname MN.UserName (P.getIdent pname) Nothing P.emptyRange)
  let env' = env { eModuleEnv = modEnv' }
  return (cname, env')

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec $ typeNoUser <$> fields

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)

------------------------------------------------------------

liftModuleM :: ME.ModuleEnv -> MM.ModuleM a -> IO (a, ME.ModuleEnv)
liftModuleM env m = MM.runModuleM (defaultEvalOpts, BS.readFile, env) m >>= moduleCmdResult

defaultEvalOpts :: E.EvalOpts
defaultEvalOpts = E.EvalOpts quietLogger E.defaultPPOpts

moduleCmdResult :: M.ModuleRes a -> IO (a, ME.ModuleEnv)
moduleCmdResult (res, ws) = do
  --mapM_ (print . pp) ws
  case res of
    Right (a, me) -> return (a, me)
    Left err      ->
      fail $ unlines (["Cryptol error:\n" ++ show (pp err)] ++ map (show . pp) ws)

-- X.throwIO (ModuleSystemError err)
