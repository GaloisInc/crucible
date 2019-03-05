{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ExplicitForAll   #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

-- Crucible
import           Lang.Crucible.Backend.Simple (newSimpleBackend, SimpleBackend)
import           Lang.Crucible.FunctionHandle (newHandleAllocator, withHandleAllocator, HandleAllocator)
import           Lang.Crucible.LLVM.Globals (initializeMemory)
import           Lang.Crucible.LLVM.MemType (i32)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Intrinsics (mkLLVMContext)
import           Lang.Crucible.LLVM.Extension (ArchRepr(..), ArchWidth, X86(..))

import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr (knownNat, LeqProof(..), NatRepr, testLeq)
import           Data.Parameterized.Nonce (withIONonceGenerator, NonceGenerator)
import           What4.Expr.Builder (ExprBuilder, Flags, FloatReal, newExprBuilder)
import           Lang.Crucible.Backend (IsSymInterface)

-- LLVM
import qualified Text.LLVM.AST as L
import           Text.LLVM.AST (Module)
import           Data.LLVM.BitCode (parseBitCodeFromFile)
import           Lang.Crucible.LLVM.TypeContext (TypeContext)


-- Tasty
import           Test.Tasty (defaultMain, TestTree, testGroup)
import           Test.Tasty.HUnit (testCase, (@=?))
import           Test.Tasty.QuickCheck (testProperty)

-- General
import           Control.Monad.ST
import           Data.Foldable (toList)
import           Data.Sequence (Seq)
import           Control.Monad (when, forM_)
import           Control.Monad.Except
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified System.Directory as Dir
import           System.Exit (exitFailure, ExitCode(..))
import qualified System.Process as Proc

-- Modules being tested
import           Lang.Crucible.LLVM.Translation
import           Lang.Crucible.LLVM.MemModel (reverseAliases)

import           Debug.Trace

doProc :: String -> [String] -> IO (Int, String, String)
doProc !exe !args = do
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode exe args ""
  pure $ (exitCodeToInt exitCode, stdout, stderr)
  where exitCodeToInt ExitSuccess     = 0
        exitCodeToInt (ExitFailure i) = i


-- | Compile a C file with clang, returning the exit code
compile :: FilePath -> IO (Int, String, String)
compile !file = doProc "clang" ["-emit-llvm", "-g", "-O0", "-c", file]

-- | Assemble a ll file with llvm-as, returning the exit code
assemble :: FilePath -> FilePath -> IO (Int, String, String)
assemble !inputFile !outputFile =
  doProc "llvm-as" ["-o", outputFile, inputFile]

-- | Parse an LLVM bit-code file.
-- Mostly copied from crucible-c.
parseLLVM :: FilePath -> IO (Either String Module)
parseLLVM !file =
  parseBitCodeFromFile file >>=
    \case
      Left err -> pure $ Left $ "Couldn't parse LLVM bitcode from file"
                                ++ file ++ "\n" ++ show err
      Right m  -> pure $ Right m

main :: IO ()
main = do
  wd <- Dir.getCurrentDirectory
  putStrLn $ "Looking for tests in " ++ wd

  let prepend pr = map (\s -> pr ++ s)
  let cfiles     = prepend "global" [ "-int", "-struct", "-uninitialized", "-extern" ]
  let llfiles    = ["lifetime"]
  let append ext = map (\s -> s ++ ext)
  let assertSuccess msg file (exitCode, stdout, stderr) = do
        when (exitCode /= 0) $ do
          putStrLn $ msg ++ " " ++ file
          putStrLn stdout
          putStrLn stderr
          exitFailure

  putStrLn "Compiling C code to LLVM bitcode with clang"
  forM_ (prepend "test/c/" $ append ".c" cfiles) $ \file -> do
    assertSuccess "compile" file =<< compile file

  putStrLn "Assembling LLVM assembly with llvm-as"
  forM_ (zip (prepend "test/ll/" $ append ".ll" llfiles)
             (append ".bc" llfiles)) $ \(inputFile, outputFile) -> do
    assertSuccess "assemble" inputFile =<< assemble inputFile outputFile

  putStrLn "Parsing LLVM bitcode"
  -- parsed :: [Module]
  parsed <-
    forM (append ".bc" (cfiles ++ llfiles)) $ \file -> do
    parsed <- parseLLVM file
    case parsed of
      Left err -> do
        putStrLn $ "Failed to parse " ++ file
        putStrLn err
        exitFailure
      Right m  -> pure m

  putStrLn "Translating LLVM modules"
  halloc     <- newHandleAllocator
  -- translated :: [ModuleTranslation]
  translated <- stToIO $ traverse (translateModule halloc) parsed

  -- Run tests on the results
  case translated of
    [Some g1, Some g2, Some g3, Some g4, Some l1] ->
      defaultMain (tests g1 g2 g3 g4 l1)

tests :: ModuleTranslation arch1
      -> ModuleTranslation arch2
      -> ModuleTranslation arch3
      -> ModuleTranslation arch4
      -> ModuleTranslation arch5
      -> TestTree
tests int struct uninitialized _ lifetime = do
  testGroup "Tests" $ concat
    [ [ testCase "int" $
          Map.singleton (L.Symbol "x") (Right $ (i32, Just $ IntConst (knownNat @32) 42)) @=?
             Map.map snd (globalInitMap int)
      , testCase "struct" $
          IntConst (knownNat @32) 17 @=?
             case snd <$> Map.lookup (L.Symbol "z") (globalInitMap struct) of
               Just (Right (_, Just (StructConst _ (x : _)))) -> x
               _ -> IntConst (knownNat @1) 0
      , testCase "unitialized" $
          Map.singleton (L.Symbol "x") (Right $ (i32, Just $ ZeroConst i32)) @=?
             Map.map snd (globalInitMap uninitialized)
      -- The actual value for this one contains the error message, so it's a pain
      -- to type out. Uncomment this test to take a look.
      -- , testCase "extern" $
      --     Map.singleton (L.Symbol "x") (Left $ "") @=?
      --        (globalMap extern)

      -- We're really just checking that the translation succeeds without
      -- exceptions.
      , testCase "lifetime" $
          False @=? Map.null (cfgMap lifetime)
      ]

    , ------------- Tests for reverseAliases

      let evenAlias xs x =
            let s = Set.fromList (toList xs)
            in if even x && Set.member x s
               then Just (x `div` 2)
               else Nothing
          addTargets xs = xs <> fmap (`div` 2) (Seq.filter even xs)
      in
        [ testCase "reverseAliases: empty" $
            Map.empty @=?
              reverseAliases id (const Nothing) (Seq.empty :: Seq Int)
        , testProperty "reverseAliases: singleton" $ \x ->
            Map.singleton (x :: Int) Set.empty ==
              reverseAliases id (const Nothing) (Seq.singleton x)
        , -- The result should not depend on ordering
          testProperty "reverseAliases: reverse" $ \xs ->
            let -- no self-aliasing allowed
                xs' = addTargets (Seq.filter (/= 0) xs)
            in reverseAliases id (evenAlias xs) (xs' :: Seq Int) ==
                 reverseAliases id (evenAlias xs) (Seq.reverse xs')
        , -- Every item should appear exactly once
          testProperty "reverseAliases: xor" $ \xs ->
            let xs'    = addTargets (Seq.filter (/= 0) xs)
                result = reverseAliases id (evenAlias xs) (xs' :: Seq Int)
                keys   = Map.keysSet result
                values = Set.unions (Map.elems result)
                --
                xor True a = not a
                xor False a = a
                --
            in all (\x -> Set.member x keys `xor` Set.member x values) xs'
        ]

    , ------------- Handling of global aliases

      -- It would be nice to have access to the Arbitrary instances for L.AST from
      -- llvm-pretty-bc-parser here.
      let mkGlobal name = L.Global (L.Symbol name) L.emptyGlobalAttrs L.Opaque Nothing Nothing Map.empty
          mkAlias  name global = L.GlobalAlias (L.Symbol name) L.Opaque (L.ValSymbol (L.Symbol global))
          mkModule as   gs     = L.emptyModule { L.modGlobals = gs
                                               , L.modAliases = as
                                               }
      in
         [ testCase "globalAliases: empty module" $
             withInitializedMemory (mkModule [] []) $ \_ ->
             Map.empty @=? globalAliases L.emptyModule
         , testCase "globalAliases: singletons, aliased" $
             let g = mkGlobal "g"
                 a = mkAlias  "a" "g"
             in withInitializedMemory (mkModule [] []) $ \_ ->
                Map.singleton g (Set.singleton a) @=? globalAliases (mkModule [a] [g])
         , testCase "globalAliases: two aliases" $
             let g  = mkGlobal "g"
                 a1 = mkAlias  "a1" "g"
                 a2 = mkAlias  "a2" "g"
             in withInitializedMemory (mkModule [] []) $ \_ ->
                Map.singleton g (Set.fromList [a1, a2]) @=? globalAliases (mkModule [a1, a2] [g])
         ]

    , -- The following test ensures that SAW treats global aliases properly in that
      -- they are present in the @Map@ of globals after initializing the memory.

      let t = L.PrimType (L.Integer 2)
          mkGlobal name = L.Global (L.Symbol name) L.emptyGlobalAttrs t Nothing Nothing Map.empty
          mkAlias  name global = L.GlobalAlias (L.Symbol name) t (L.ValSymbol (L.Symbol global))
          mkModule as   gs     = L.emptyModule { L.modGlobals = gs
                                               , L.modAliases = as
                                               }
      in [ testCase "initializeMemory" $
           let mod     = mkModule [mkAlias  "a" "g"] [mkGlobal "g"]
               inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
           in withInitializedMemory mod $ \result ->
                inMap (L.Symbol "a") (memImplGlobalMap result)
         ]

    , -- The following ensures that Crucible treats aliases to functions properly

      let alias = L.GlobalAlias
            { L.aliasName = L.Symbol "aliasName"
            , L.aliasType =
                L.FunTy
                  (L.PrimType L.Void)
                  [ L.PtrTo (L.Alias (L.Ident "class.std::cls")) ]
                  False
            , L.aliasTarget =
                L.ValSymbol (L.Symbol "defName")
            }

          def = L.Define
            { L.defLinkage = Just L.WeakODR
            , L.defRetType = L.PrimType L.Void
            , L.defName = L.Symbol "defName"
            , L.defArgs =
                [ L.Typed
                    { L.typedType = L.PtrTo (L.Alias (L.Ident "class.std::cls"))
                    , L.typedValue = L.Ident "0"
                    }
                ]
            , L.defVarArgs = False
            , L.defAttrs = []
            , L.defSection = Nothing
            , L.defGC = Nothing
            , L.defBody =
                [ L.BasicBlock
                  { L.bbLabel = Just (L.Anon 1)
                  , L.bbStmts =
                      [ L.Result
                          (L.Ident "2")
                          (L.Alloca
                             (L.PtrTo
                              (L.Alias (L.Ident "class.std::cls"))) Nothing (Just 8))
                          []
                      , L.Effect L.RetVoid []
                      ]
                  }
              ]
            , L.defMetadata = mempty
            , L.defComdat = Nothing
            }
      in [ testCase "initializeMemory (functions)" $
           let mod     = L.emptyModule { L.modDefines = [def]
                                       , L.modAliases = [alias]
                                       }
               inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
           in withInitializedMemory mod $ \memImpl ->
              inMap
                (L.Symbol "aliasName")
                (memImplGlobalMap memImpl)
        ]
    ]


-- | Create an LLVM context from a module and make some assertions about it.
withLLVMCtx :: forall a. L.Module
            -> (forall arch sym. ( ?lc :: TypeContext
                                 , HasPtrWidth (ArchWidth arch)
                                 , IsSymInterface sym
                                 )
                => LLVMContext arch
                -> sym
                -> IO a)
            -> IO a
withLLVMCtx mod action =
  let -- This is a separate function because we need to use the scoped type variable
      -- @s@ in the binding of @sym@, which is difficult to do inline.
      with :: forall s. NonceGenerator IO s -> HandleAllocator RealWorld -> IO a
      with nonceGen halloc = do
        sym <- newSimpleBackend nonceGen :: IO (SimpleBackend s (Flags FloatReal))
        Some (ModuleTranslation _ ctx _) <- stToIO $ translateModule halloc mod
        case llvmArch ctx                   of { X86Repr width ->
        case assertLeq (knownNat @1)  width of { LeqProof      ->
        case assertLeq (knownNat @16) width of { LeqProof      -> do
          let ?ptrWidth = width
          let ?lc = _llvmTypeCtx ctx
          action ctx sym
        }}}
  in withIONonceGenerator $ \nonceGen ->
     withHandleAllocator  $ \halloc   -> with nonceGen halloc

-- | Call 'initializeMemory' and get the result
withInitializedMemory :: forall a. L.Module
                      -> (forall wptr sym. ( ?lc :: TypeContext
                                           , HasPtrWidth wptr
                                           , IsSymInterface sym
                                           )
                          => MemImpl sym
                          -> IO a)
                      -> IO a
withInitializedMemory mod action =
  withLLVMCtx mod $ \(ctx :: LLVMContext arch) sym ->
    action @(ArchWidth arch) =<< initializeMemory sym ctx mod

-- Copied from what4/test/ExprBuilderSMTLib2
data State t = State

assertLeq :: forall m n . NatRepr m -> NatRepr n -> LeqProof m n
assertLeq m n =
  case testLeq m n of
    Just LeqProof -> LeqProof
    Nothing       -> error $ "No LeqProof for " ++ show m ++ " and " ++ show n
