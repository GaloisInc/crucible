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
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.Simple as Crucible
import qualified Lang.Crucible.Backend.Online as Crucible
import           Lang.Crucible.FunctionHandle (newHandleAllocator, withHandleAllocator, HandleAllocator)
import qualified Lang.Crucible.Types as Crucible

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import qualified What4.Expr.Builder as What4
import qualified What4.Interface as What4
import qualified What4.Protocol.Online as What4
import qualified What4.SatResult as What4

-- LLVM
import qualified Text.LLVM.AST as L
import           Text.LLVM.AST (Module)
import           Data.LLVM.BitCode

-- Tasty
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

-- General
import           Data.Foldable
import           Data.Sequence (Seq)
import           Control.Monad
import           Data.IORef
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified System.Directory as Dir
import           System.Exit (exitFailure, ExitCode(..))
import qualified System.Process as Proc

-- Modules being tested
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Globals
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation
import           Lang.Crucible.LLVM.Translation.Aliases
import           Lang.Crucible.LLVM.TypeContext

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
  let ?laxArith = False
  translated <- traverse (translateModule halloc) parsed

  -- Run tests on the results
  case translated of
    [Some g1, Some g2, Some g3, Some g4, Some l1] ->
      defaultMain (tests g1 g2 g3 g4 l1)
    _ -> error "translation failure!"

tests :: ModuleTranslation arch1
      -> ModuleTranslation arch2
      -> ModuleTranslation arch3
      -> ModuleTranslation arch4
      -> ModuleTranslation arch5
      -> TestTree
tests int struct uninitialized _ lifetime = do
  testGroup "Tests" $ concat
    [ [ testCase "int" $
          Map.singleton (L.Symbol "x") (Right $ (i32, Just $ IntConst (knownNat @32) (BV.mkBV knownNat 42))) @=?
             Map.map snd (globalInitMap int)
      , testCase "struct" $
          IntConst (knownNat @32) (BV.mkBV knownNat 17) @=?
             case snd <$> Map.lookup (L.Symbol "z") (globalInitMap struct) of
               Just (Right (_, Just (StructConst _ (x : _)))) -> x
               _ -> IntConst (knownNat @1) (BV.zero knownNat)
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
                Map.singleton (L.globalSym g) (Set.singleton a) @=? globalAliases (mkModule [a] [g])
         , testCase "globalAliases: two aliases" $
             let g  = mkGlobal "g"
                 a1 = mkAlias  "a1" "g"
                 a2 = mkAlias  "a2" "g"
             in withInitializedMemory (mkModule [] []) $ \_ ->
                Map.singleton (L.globalSym g) (Set.fromList [a1, a2]) @=? globalAliases (mkModule [a1, a2] [g])
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
           let mod'    = mkModule [mkAlias  "a" "g"] [mkGlobal "g"]
               inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
           in withInitializedMemory mod' $ \result ->
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
           let mod'    = L.emptyModule { L.modDefines = [def]
                                       , L.modAliases = [alias]
                                       }
               inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
           in withInitializedMemory mod' $ \memImpl ->
              inMap
                (L.Symbol "aliasName")
                (memImplGlobalMap memImpl)
        ]

    , [ testArrayStride
      , testMemArray
      ]
    ]


-- | Create an LLVM context from a module and make some assertions about it.
withLLVMCtx :: forall a. L.Module
            -> (forall arch sym. ( ?lc :: TypeContext
                                 , HasPtrWidth (ArchWidth arch)
                                 , Crucible.IsSymInterface sym
                                 )
                => LLVMContext arch
                -> sym
                -> IO a)
            -> IO a
withLLVMCtx mod' action =
  let -- This is a separate function because we need to use the scoped type variable
      -- @s@ in the binding of @sym@, which is difficult to do inline.
      with :: forall s. NonceGenerator IO s -> HandleAllocator -> IO a
      with nonceGen halloc = do
        sym <- Crucible.newSimpleBackend What4.FloatRealRepr nonceGen
        let ?laxArith = False
        Some (ModuleTranslation _ ctx _ _) <- translateModule halloc mod'
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
                                           , Crucible.IsSymInterface sym
                                           )
                          => MemImpl sym
                          -> IO a)
                      -> IO a
withInitializedMemory mod' action =
  withLLVMCtx mod' $ \(ctx :: LLVMContext arch) sym ->
    action @(ArchWidth arch) =<< initializeAllMemory sym ctx mod'

assertLeq :: forall m n . NatRepr m -> NatRepr n -> LeqProof m n
assertLeq m n =
  case testLeq m n of
    Just LeqProof -> LeqProof
    Nothing       -> error $ "No LeqProof for " ++ show m ++ " and " ++ show n

userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

withMem ::
  EndianForm ->
  (forall sym scope solver fs wptr .
    ( sym ~ Crucible.OnlineBackend scope solver fs
    , Crucible.IsSymInterface sym
    , HasLLVMAnn sym
    , What4.OnlineSolver scope solver
    , HasPtrWidth wptr ) =>
    sym -> MemImpl sym -> IO a) ->
  IO a
withMem endianess action = withIONonceGenerator $ \nonce_gen ->
  Crucible.withZ3OnlineBackend What4.FloatIEEERepr nonce_gen Crucible.NoUnsatFeatures $ \sym -> do
    let ?ptrWidth = knownNat @64
    mem <- emptyMem endianess
    bbMapRef <- newIORef mempty
    let ?badBehaviorMap = bbMapRef
    action sym mem

assume :: Crucible.IsSymInterface sym => sym -> What4.Pred sym -> IO ()
assume sym p = do
  loc <- What4.getCurrentProgramLoc sym
  Crucible.addAssumption sym $
    Crucible.LabeledPred p $ Crucible.AssumptionReason loc ""

checkSat ::
  What4.OnlineSolver scope solver =>
  Crucible.OnlineBackend scope solver fs ->
  What4.BoolExpr scope ->
  IO (What4.SatResult () ())
checkSat sym p = do
  Crucible.withSolverProcess sym $ \proc ->
     What4.checkSatisfiable proc "" p

testArrayStride :: TestTree
testArrayStride = testCase "array stride" $ withMem BigEndian $ \sym mem0 -> do
  sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (1024 * 1024)
  (base_ptr, mem1) <- mallocRaw sym mem0 sz noAlignment

  let byte_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @8
  let byte_storage_type = bitvectorType 1
  let ptr_byte_repr = LLVMPointerRepr $ knownNat @8

  init_array_val <- LLVMValArray byte_storage_type <$>
    V.generateM (1024 * 1024)
      (\i -> packMemValue sym byte_storage_type byte_type_repr
        =<< What4.bvLit sym (knownNat @8) (BV.mkBV knownNat (fromIntegral (mod i (512 * 1024)))))
  mem2 <- storeRaw
    sym
    mem1
    base_ptr
    (arrayType (1024 * 1024) byte_storage_type)
    noAlignment
    init_array_val

  stride <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (512 * 1024)

  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  ptr_i <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvMul sym stride i
  ptr_i' <- ptrAdd sym ?ptrWidth ptr_i =<< What4.bvLit sym ?ptrWidth (BV.one ?ptrWidth)

  zero_bv <- What4.bvLit sym (knownNat @8) (BV.zero knownNat)
  mem3 <-
    doStore sym mem2 ptr_i byte_type_repr byte_storage_type noAlignment zero_bv
  one_bv <- What4.bvLit sym (knownNat @8) (BV.one knownNat)
  mem4 <-
    doStore sym mem3 ptr_i' byte_type_repr byte_storage_type noAlignment one_bv

  at_0_val <- projectLLVM_bv sym
    =<< doLoad sym mem4 base_ptr byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.zero knownNat)) @=? What4.asBV at_0_val

  j <- What4.freshConstant sym (userSymbol' "j") $ What4.BaseBVRepr ?ptrWidth
  ptr_j <- ptrAdd sym ?ptrWidth base_ptr =<< What4.bvMul sym stride j
  ptr_j' <- ptrAdd sym ?ptrWidth ptr_j =<< What4.bvLit sym ?ptrWidth (BV.one ?ptrWidth)

  at_j_val <- projectLLVM_bv sym
    =<< doLoad sym mem4 ptr_j byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.zero knownNat)) @=? What4.asBV at_j_val

  at_j'_val <- projectLLVM_bv  sym
    =<< doLoad sym mem4 ptr_j' byte_storage_type ptr_byte_repr noAlignment
  (Just (BV.one knownNat)) @=? What4.asBV at_j'_val

testMemArray :: TestTree
testMemArray = testCase "smt array memory model" $ withMem BigEndian $ \sym mem0 -> do
  sz <- What4.bvLit sym ?ptrWidth $ BV.mkBV ?ptrWidth (1024 * 1024)
  (base_ptr, mem1) <- mallocRaw sym mem0 sz noAlignment

  arr <- What4.freshConstant
    sym
    (userSymbol' "a")
    (What4.BaseArrayRepr
      (Ctx.singleton $ What4.BaseBVRepr ?ptrWidth)
      (What4.BaseBVRepr (knownNat @8)))
  mem2 <- doArrayStore sym mem1 base_ptr noAlignment arr sz

  let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
  let long_storage_type = bitvectorType 8
  let ptr_long_repr = LLVMPointerRepr $ knownNat @64

  i <- What4.freshConstant sym (userSymbol' "i") $ What4.BaseBVRepr ?ptrWidth
  ptr_i <- ptrAdd sym ?ptrWidth base_ptr i
  assume sym =<< What4.bvUlt sym i =<< What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 1024)
  some_val <- What4.bvLit sym (knownNat @64) (BV.mkBV knownNat 0x88888888f0f0f0f0)
  mem3 <-
    doStore sym mem2 ptr_i long_type_repr long_storage_type noAlignment some_val
  at_i_val <- projectLLVM_bv sym
    =<< doLoad sym mem3 ptr_i long_storage_type ptr_long_repr noAlignment
  res_i <- checkSat sym =<< What4.bvNe sym some_val at_i_val
  True @=? What4.isUnsat res_i

  j <- What4.freshConstant sym (userSymbol' "j") $ What4.BaseBVRepr ?ptrWidth
  ptr_j <- ptrAdd sym ?ptrWidth base_ptr j
  assume sym =<< What4.bvEq sym i j
  at_j_val <- projectLLVM_bv sym
    =<< doLoad sym mem3 ptr_j long_storage_type ptr_long_repr noAlignment
  res_j <- checkSat sym =<< What4.bvNe sym some_val at_j_val
  True @=? What4.isUnsat res_j

testMemWritesIndexed :: TestTree
testMemWritesIndexed = testCase "indexed memory writes" $ withMem BigEndian $ \sym mem0 -> do
  let count = 100 * 1000

  sz <- What4.bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth 8)
  (base_ptr1, mem1) <- mallocRaw sym mem0 sz noAlignment
  (base_ptr2, mem2) <- mallocRaw sym mem1 sz noAlignment

  let long_type_repr = Crucible.baseToType $ What4.BaseBVRepr $ knownNat @64
  let long_storage_type = bitvectorType 8
  let ptr_long_repr = LLVMPointerRepr $ knownNat @64

  zero_val <- What4.bvLit sym (knownNat @64) (BV.zero knownNat)
  mem3 <- doStore
    sym
    mem2
    base_ptr1
    long_type_repr
    long_storage_type
    noAlignment
    zero_val

  mem4 <- foldlM
    (\mem' i ->
      doStore sym mem' base_ptr2 long_type_repr long_storage_type noAlignment
        =<< What4.bvLit sym (knownNat @64) i)
    mem3
    (BV.enumFromToUnsigned (BV.zero (knownNat @64)) (BV.mkBV knownNat count))

  forM_ [0 .. count] $ \_ -> do
    val1 <- projectLLVM_bv sym
      =<< doLoad sym mem4 base_ptr1 long_storage_type ptr_long_repr noAlignment
    (Just (BV.zero knownNat)) @=? What4.asBV val1

  val2 <- projectLLVM_bv sym
    =<< doLoad sym mem4 base_ptr2 long_storage_type ptr_long_repr noAlignment
  (Just (BV.mkBV knownNat count)) @=? What4.asBV val2
