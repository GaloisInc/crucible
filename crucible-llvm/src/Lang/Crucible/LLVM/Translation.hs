-- |
-- Module           : Lang.Crucible.LLVM.Translation
-- Description      : Translation of LLVM AST into Crucible control-flow graph
-- Copyright        : (c) Galois, Inc 2014-2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module translates an LLVM 'Module' into a collection of Crucible
-- control-flow graphs, one per function.  The tricky parts of this translation
-- are 1) mapping LLVM types onto Crucible types in a sensible way and 2)
-- translating the phi-instructions of LLVM's SSA form.
--
-- To handle the translation of phi-functions, we first perform a
-- pre-pass over all the LLVM basic blocks looking for phi-functions
-- and build a datastructure that tells us what assignments to make
-- when jumping from block l to block l'.  We then emit instructions
-- to make these assignments in a separate Crucible basic block (see
-- 'definePhiBlock').  Thus, the translated CFG will generally have
-- more basic blocks than the original LLVM.
--
-- Points of note:
--
--  * Immediate (i.e., not in memory) structs and packed structs are translated the same.
--  * Undefined values generate special Crucible expressions (e.g., BVUndef) to
--     represent arbitrary bitpatterns.
--  * The floating-point domain is interpreted by IsSymInterface as either
--    the IEEE754 floating-point domain, the real domain, or a domain with
--    bitvector values and uninterpreted operations.
--
-- Some notes on undefined/poison values: (outcome of discussions between JHx and RWD)
--
-- * Continue to add Crucible expressions for undefined values as
-- required (e.g. for floating-point values).  Crucible itself is
-- currently treating undefined values as fresh symbolic inputs; it
-- should instead invent a new category of "arbitrary" values that get
-- passed down into the solvers in a way that is dependent on the task
-- at hand.  For example, in verification tasks, it is appropriate to
-- treat the arbitrary values the same as symbolic inputs.  However,
-- for preimage-finding tasks, the arbitrary values must be treated as
-- universally-quantified, unlike the symbolic inputs which are
-- existentially-quantified.
--
-- * For poison values, our implementation strategy is to assert
-- side conditions onto values that may create poison.  As opposed
-- to assertions (which must be satisfied because you passed through
-- a control-flow point) side conditions are intended to mean that
-- a condition must hold when a value is used (i.e., side conditions
-- follow data-flow).  So if a poison value is created but not examined
-- (e.g., because we later do a test to determine if the value is safe),
-- that should be allowed.
--
-- A (probably) partial list of things we intend to support, but do not yet:
--
--  * Various vector instructions. This includes a variety of instructions
--      that LLVM allows to take vector arguments, but are currently only
--      defined on scalar (nonvector) arguments. (Progress has been made on
--      this, but may not yet be complete).
--
-- A list of things that are unsupported and may never be:
--
--  * Computed jumps and blockaddress expressions
--  * Multithreading primitives
--  * Alternate calling conventions
------------------------------------------------------------------------

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Translation
  ( ModuleTranslation
  , getTranslatedCFG
  , getTranslatedFnHandle
  , transContext
  , globalInitMap
  , modTransDefs
  , modTransModule
  , modTransHalloc
  , LLVMContext(..)
  , llvmTypeCtx
  , translateModule
  , LLVMTranslationWarning(..)

  , module Lang.Crucible.LLVM.Translation.Constant
  , module Lang.Crucible.LLVM.Translation.Options
  , module Lang.Crucible.LLVM.Translation.Types
  ) where

import           Control.Lens hiding (op, (:>) )
import           Control.Monad (foldM)
import           Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Maybe
import           Data.String
import qualified Data.Text   as Text
import           Prettyprinter (pretty)

import qualified Text.LLVM.AST as L

import           Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.Nonce

import           What4.FunctionName
import           What4.ProgramLoc

import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion( toSSA )

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Globals
import qualified Lang.Crucible.LLVM.Mem as Mem
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.PrettyPrint as LPP
import           Lang.Crucible.LLVM.Translation.Aliases
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Translation.Expr
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Options
import           Lang.Crucible.LLVM.Translation.Instruction
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.Types


------------------------------------------------------------------------
-- Translation results

type ModuleCFGMap mem = Map L.Symbol (CFGMapEntry mem)

data CFGMapEntry mem
  = TranslatedCFG L.Declare (C.AnyCFG (LLVM mem))
  | UntranslatedCFG L.Define SomeHandle

-- | The result of translating an LLVM module into Crucible CFGs.
data ModuleTranslation mem arch
   = ModuleTranslation
      { _cfgMap        :: IORef (ModuleCFGMap mem)
      , _transContext :: LLVMContext mem arch
      , _globalInitMap :: GlobalInitializerMap
        -- ^ A map from global names to their (constant) values
        -- Note: Willy-nilly global initialization may be unsound in the
        -- presence of compositional verification.
      , _modTransNonce :: !(Nonce GlobalNonceGenerator arch)
        -- ^ For a reasonably quick 'testEquality' instance
      , _modTransDefs :: ![(L.Declare, SomeHandle)]
        -- ^ A collection of declarations for all the functions
        --   defined in this module.
      , _modTransHalloc :: HandleAllocator
      , _modTransModule :: L.Module
      , _modTransOpts   :: TranslationOptions
      }

instance TestEquality (ModuleTranslation mem) where
  testEquality mt1 mt2 =
    testEquality (_modTransNonce mt1) (_modTransNonce mt2)

transContext :: Getter (ModuleTranslation mem arch) (LLVMContext mem arch)
transContext = to _transContext

globalInitMap :: Getter (ModuleTranslation mem arch) GlobalInitializerMap
globalInitMap = to _globalInitMap

modTransDefs :: Getter (ModuleTranslation mem arch) [(L.Declare,SomeHandle)]
modTransDefs = to _modTransDefs

modTransModule :: Getter (ModuleTranslation mem arch) L.Module
modTransModule = to _modTransModule

modTransHalloc :: Getter (ModuleTranslation mem arch) HandleAllocator
modTransHalloc = to _modTransHalloc

typeToRegExpr :: MemType -> LLVMGenerator s mem arch ret (Some (Reg s))
typeToRegExpr tp = do
  llvmTypeAsRepr tp $ \tpr ->
    Some <$> newUnassignedReg tpr

-- | This function pre-computes the types of all the crucible registers by scanning
--   through each basic block and finding the place where that register is assigned.
--   Because LLVM programs are in SSA form, this will occur in exactly one place.
--   The type of the register is inferred from the instruction that assigns to it
--   and is recorded in the ident map.
buildRegMap :: IdentMap s -> L.Define -> LLVMGenerator s mem arch reg (IdentMap s)
buildRegMap m d = foldM (\m0 bb -> buildRegTypeMap m0 bb) m $ L.defBody d

buildRegTypeMap :: IdentMap s
                -> L.BasicBlock
                -> LLVMGenerator s mem arch ret (IdentMap s)
buildRegTypeMap m0 bb = foldM stmt m0 (L.bbStmts bb)
 where
    err instr msg =
       malformedLLVMModule "Invalid type in instruction result"
          [ fromString (showInstr instr)
          , fromString msg
          ]

    stmt m (L.Effect _ _) = return m
    stmt m (L.Result ident instr _) = do
         ty <- either (err instr) return $ instrResultType instr
         ex <- typeToRegExpr ty
         case Map.lookup ident m of
           Just _ ->
             malformedLLVMModule "Register not used in SSA fashion"
              [ fromString (show ident)
              , fromString (showInstr instr)
              ]
           Nothing -> return $ Map.insert ident (Left ex) m


-- | Generate crucible code for each LLVM statement in turn.
generateStmts :: (?transOpts :: TranslationOptions, Mem.Mem mem)
  => TypeRepr ret
        -> L.BlockLabel
        -> Set L.Ident {- ^ Set of usable identifiers -}
        -> [L.Stmt]
        -> LLVMGenerator s mem arch ret a
generateStmts retType lab defSet0 stmts = go defSet0 (processDbgDeclare stmts)
 where go _ [] = fail "LLVM basic block ended without a terminating instruction"
       go defSet (x:xs) =
         case x of
           -- a result statement assigns the result of the instruction into a register
           L.Result ident instr md ->
              do setLocation md
                 generateInstr retType lab defSet instr
                   (assignLLVMReg ident)
                   (go (Set.insert ident defSet) xs)

           -- an effect statement simply executes the instruction for its effects and discards the result
           L.Effect instr md ->
              do setLocation md
                 generateInstr retType lab defSet instr
                   (\_ -> return ())
                   (go defSet xs)

-- | Search for calls to intrinsic 'llvm.dbg.declare' and copy the
-- metadata onto the corresponding 'alloca' statement.  Also copy
-- metadata backwards from 'bitcast' statements toward 'alloca'.
processDbgDeclare :: [L.Stmt] -> [L.Stmt]
processDbgDeclare = snd . go
  where
    go :: [L.Stmt] -> (Map L.Ident [(String, L.ValMd)] , [L.Stmt])
    go [] = (Map.empty, [])
    go (stmt : stmts) =
      let (m, stmts') = go stmts in
      case stmt of
        L.Result x instr@L.Alloca{} md ->
          case Map.lookup x m of
            Just md' -> (m, L.Result x instr (md' ++ md) : stmts')
            Nothing -> (m, stmt : stmts')
              --error $ "Identifier not found: " ++ show x ++ "\nPossible identifiers: " ++ show (Map.keys m)

        L.Result x (L.Conv L.BitCast (L.Typed _ (L.ValIdent y)) _) md ->
          let md' = md ++ fromMaybe [] (Map.lookup x m)
              m'  = Map.alter (Just . maybe md' (md'++)) y m
           in (m', stmt:stmts)

        L.Effect (L.Call _ _ (L.ValSymbol "llvm.dbg.declare") (L.Typed _ (L.ValMd (L.ValMdValue (L.Typed _ (L.ValIdent x)))) : _)) md ->
          (Map.insert x md m, stmt : stmts')

        -- This is needlessly fragile. Let's just ignore debug declarations we don't understand.
        -- L.Effect (L.Call _ _ (L.ValSymbol "llvm.dbg.declare") args) md ->
        --  error $ "Ill-formed arguments to llvm.dbg.declare: " ++ show (args, md)

        _ -> (m, stmt : stmts')

setLocation
  :: [(String,L.ValMd)]
  -> LLVMGenerator s mem arch ret ()
setLocation [] = return ()
setLocation (x:xs) =
  case x of
    ("dbg",L.ValMdLoc dl) ->
      let ln   = fromIntegral $ L.dlLine dl
          col  = fromIntegral $ L.dlCol dl
          file = getFile $ L.dlScope dl
       in setPosition (SourcePos file ln col)
    ("dbg",L.ValMdDebugInfo (L.DebugInfoSubprogram subp))
      | Just file' <- L.dispFile subp
      -> let ln = fromIntegral $ L.dispLine subp
             file = getFile file'
          in setPosition (SourcePos file ln 0)
    _ -> setLocation xs

 where
 getFile = Text.pack . maybe "" filenm . findFile

 -- The typical values available here will be something like:
 --
 -- > L.difDirectory = "/home/joeuser/work"
 -- > L.difFilename  = "src/lib/foo.c"
 --
 -- At the present time, only the 'difFilename' is used for the
 -- relative path because combining these to form an absolute path
 -- would cause superfluous result differences (e.g. golden test
 -- failures) and potentially leak information.
 --
 -- The downside is that relative paths may make it harder for various
 -- tools (e.g. emacs) to locate the offending source file.  The
 -- suggested method for handling this is to have the emacs compile
 -- function emit an initial rooted directory location in the proper
 -- syntax, but if this is problematic, a future direction would be to
 -- add a config option to control whether an absolute or a relative
 -- path is desired (defaulting to the latter).
 --
 -- [The previous implementation always generated absolute paths, but
 -- was careful to check if `difFilename` was already absolute.]
 filenm = L.difFilename

findFile :: (?lc :: TypeContext) => L.ValMd -> Maybe L.DIFile
findFile (L.ValMdRef x) = findFile =<< lookupMetadata x

findFile (L.ValMdNode (_:Just (L.ValMdRef y):_)) =
  case lookupMetadata y of
    Just (L.ValMdNode [Just (L.ValMdString fname), Just (L.ValMdString fpath)]) ->
        Just (L.DIFile fname fpath)
    _ -> Nothing

findFile (L.ValMdDebugInfo di) =
  case di of
    L.DebugInfoFile dif -> Just dif
    L.DebugInfoLexicalBlock dilex
      | Just md <- L.dilbFile dilex -> findFile md
      | Just md <- L.dilbScope dilex -> findFile md
    L.DebugInfoLexicalBlockFile dilexFile
      | Just md <- L.dilbfFile dilexFile -> findFile md
      | otherwise -> findFile (L.dilbfScope dilexFile)
    L.DebugInfoSubprogram disub
      | Just md <- L.dispFile disub -> findFile md
      | Just md <- L.dispScope disub -> findFile md
    _ -> Nothing

findFile _ = Nothing

-- | Lookup the block info for the given LLVM block and then define a new crucible block
--   by translating the given LLVM statements.
defineLLVMBlock
        :: (?transOpts :: TranslationOptions, Mem.Mem mem)
        => TypeRepr ret
        -> LLVMBlockInfoMap s
        -> L.BasicBlock
        -> LLVMGenerator s mem arch ret ()
defineLLVMBlock retType lm L.BasicBlock{ L.bbLabel = Just lab, L.bbStmts = stmts } = do
  case Map.lookup lab lm of
    Just bi -> defineBlock (block_label bi) (generateStmts retType lab (block_use_set bi) stmts)
    Nothing -> fail $ unwords ["LLVM basic block not found in block info map", show lab]

defineLLVMBlock _ _ _ = fail "LLVM basic block has no label!"

-- | Do some initial preprocessing to find all the phi nodes in the program
--   and to preallocate all the crucible registers we will need based on the LLVM
--   types of all the LLVM registers.  Then translate each LLVM basic block in turn.
--
--   This step introduces a new dummy entry point that simply jumps to the LLVM entry
--   point.  It is inconvenient to avoid doing this when using the Generator interface.
genDefn :: (?transOpts :: TranslationOptions, Mem.Mem mem)
        => L.Define
        -> TypeRepr ret
        -> LLVMGenerator s mem arch ret (Expr ext s ret)
genDefn defn retType =
  case L.defBody defn of
    [] -> fail "LLVM define with no blocks!"
    ( L.BasicBlock{ L.bbLabel = Nothing } : _ ) -> fail $ unwords ["entry block has no label"]
    ( L.BasicBlock{ L.bbLabel = Just entry_lab } : _ ) -> do
      let (L.Symbol nm) = L.defName defn
      callPushFrame $ Text.pack nm
      setLocation $ Map.toList (L.defMetadata defn)

      bim <- buildBlockInfoMap defn
      blockInfoMap .= bim

      im <- use identMap
      im' <- buildRegMap im defn
      identMap .= im'

      case Map.lookup entry_lab bim of
        Nothing -> fail $ unwords ["entry label not found in label map:", show entry_lab]
        Just entry_bi -> do
          checkEntryPointUseSet nm entry_bi (L.defArgs defn)
          mapM_ (\bb -> defineLLVMBlock retType bim bb) (L.defBody defn)
          jump (block_label entry_bi)


-- | Check that the input LLVM CFG satisfies the def/use invariant,
--   and raise an error if some virtual register has a use site that
--   is not dominated by its definition site.
checkEntryPointUseSet ::
  String ->
  LLVMBlockInfo s ->
  [L.Typed L.Ident] ->
  LLVMGenerator s mem arch ret ()
checkEntryPointUseSet nm bi args
  | Set.null unsatisfiedUses = return ()
  | otherwise =
      malformedLLVMModule ("Invalid SSA form for function: " <> pretty nm)
        ([ "The following LLVM virtual registers have at least one use site that"
         , "is not dominated by the corresponding definition:" ] ++
         [ "   " <> pretty (show (LPP.ppIdent i)) | i <- Set.toList unsatisfiedUses ])
  where
    argSet = Set.fromList (map L.typedValue args)
    useSet = block_use_set bi
    unsatisfiedUses = Set.difference useSet argSet

------------------------------------------------------------------------
-- transDefine
--
-- | Translate a single LLVM function definition into a crucible CFG.
--
transDefine :: forall mem arch wptr args ret.
  (HasPtrWidth wptr, wptr ~ ArchWidth arch, ?transOpts :: TranslationOptions, Mem.Mem mem) =>
  FnHandle args ret ->
  LLVMContext mem arch ->
  IORef [LLVMTranslationWarning] ->
  L.Define ->
  IO (L.Declare, C.AnyCFG (LLVM mem))
transDefine h ctx warnRef d = do
  let ?lc = ctx^.llvmTypeCtx
  let decl = declareFromDefine d
  let L.Symbol fstr = L.defName d

  llvmDeclToFunHandleRepr' decl $ \argTys retTy ->
    case (testEquality argTys (handleArgTypes h),
          testEquality retTy (handleReturnType h)) of
       (Nothing, _) -> fail $ unlines
                         [ "Argument type mismatch when defining function: " ++ fstr
                         , show argTys
                         , show h ]
       (_, Nothing) -> fail $ unlines $
                         [ "Return type mismatch when bootstrapping function: " ++ fstr
                         , show retTy, show h
                         ]
       (Just Refl, Just Refl) ->
         do let def :: FunctionDef (LLVM mem) (LLVMState mem arch) args ret IO
                def inputs = (s, f)
                    where s = initialState d ctx argTys inputs warnRef
                          f = genDefn d retTy
            sng <- newIONonceGenerator
            (SomeCFG g, []) <- defineFunctionOpt InternalPos sng h def $ \ng cfg ->
              if optLoopMerge ?transOpts then earlyMergeLoops ng cfg else return cfg
            case toSSA g of
              C.SomeCFG g_ssa -> g_ssa `seq` return (decl, C.AnyCFG g_ssa)


------------------------------------------------------------------------
-- translateModule

-- | Translate a module into Crucible control-flow graphs.
-- Return the translated module and a list of warning messages
-- generated during translation.
-- Note: We may want to add a map from symbols to existing function handles
-- if we want to support dynamic loading.
translateModule :: (?transOpts :: TranslationOptions)
                => HandleAllocator -- ^ Generator for nonces.
                -> GlobalVar mem   -- ^ Memory model to associate with this context
                -> L.Module        -- ^ Module to translate
                -> IO (Some (ModuleTranslation mem))
translateModule halloc mvar m = do
  Some ctx <- mkLLVMContext mvar m
  let nonceGen = haCounter halloc
  llvmPtrWidth ctx $ \wptr -> withPtrWidth wptr $
    do let ?lc  = ctx^.llvmTypeCtx -- implicitly passed to makeGlobalMap
       let ctx' = ctx{ llvmGlobalAliases = globalAliases m
                     , llvmFunctionAliases = functionAliases m
                     }
       nonce <- freshNonce nonceGen
       prep <- mapM (prepareCFGMapEntry halloc) (L.modDefines m)
       cfgRef <- newIORef $! Map.fromList [ (L.defName def, UntranslatedCFG def h) | (def,_,h) <- prep ]
       return (Some (ModuleTranslation { _cfgMap = cfgRef
                                       , _globalInitMap = makeGlobalMap ctx' m
                                       , _transContext = ctx'
                                       , _modTransNonce = nonce
                                       , _modTransDefs = [ (decl,h) | (_,decl,h) <- prep ]
                                       , _modTransHalloc = halloc
                                       , _modTransModule = m
                                       , _modTransOpts = ?transOpts
                                       }))

prepareCFGMapEntry ::
  (HasPtrWidth wptr, ?lc :: TypeContext) =>
  HandleAllocator ->
  L.Define ->
  IO (L.Define, L.Declare, SomeHandle)
prepareCFGMapEntry halloc def =
  let decl = declareFromDefine def in
  let L.Symbol fstr = L.defName def in
  let fn_name = functionNameFromText $ Text.pack fstr in
  llvmDeclToFunHandleRepr' decl $ \argTys retTy ->
    do h <- mkHandle' halloc fn_name argTys retTy
       return (def, decl, SomeHandle h)


-- | Given a 'ModuleTranslationmem ' and a function symbol corresponding to a function
--   defined in the module, attempt to look up the symbol name and retrieve the corresponding
--   Crucible CFG. This will load and translate the CFG if this is the first time
--   the given symbol is requested.
--
--   Will return 'Nothing' if the symbol does not refer to a function defined in this
--   module.
getTranslatedCFG ::
  Mem.Mem mem =>
  ModuleTranslation mem arch ->
  L.Symbol ->
  IO (Maybe (L.Declare, C.AnyCFG (LLVM mem), [LLVMTranslationWarning]))
getTranslatedCFG mt s =
  do m <- readIORef (_cfgMap mt)
     case Map.lookup s m of
       Nothing -> return Nothing
       Just (TranslatedCFG decl cfg) -> return (Just (decl, cfg, []))
       Just (UntranslatedCFG def (SomeHandle h)) ->
         let ?transOpts = _modTransOpts mt in
         let ctx = _transContext mt in
         llvmPtrWidth ctx $ \wptr -> withPtrWidth wptr $
         do warnRef <- newIORef []
            (decl, cfg) <- transDefine h ctx warnRef def
            warns <- reverse <$> readIORef warnRef
            modifyIORef (_cfgMap mt) (Map.insert s (TranslatedCFG decl cfg))
            return (Just (decl, cfg, warns))

-- | Look up the signature and function handle for a function defined in this
--   module translation.  This does not trigger translation of the named function
--   into Crucible if it has not already been requested.
--
--   Will return 'Nothing' if the symbol does not refer to a function defined in this
--   module.
getTranslatedFnHandle ::
  ModuleTranslation mem arch ->
  L.Symbol ->
  IO (Maybe (L.Declare, SomeHandle))
getTranslatedFnHandle mt s =
  do m <- readIORef (_cfgMap mt)
     case Map.lookup s m of
       Nothing -> return Nothing
       Just (TranslatedCFG decl (C.AnyCFG cfg)) -> return (Just (decl, SomeHandle (C.cfgHandle cfg)))
       Just (UntranslatedCFG def h) -> return (Just (declareFromDefine def, h))
