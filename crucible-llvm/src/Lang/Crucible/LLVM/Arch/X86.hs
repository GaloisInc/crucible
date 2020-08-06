{-# Language GADTs #-}
{-# Language DataKinds #-}
{-# Language KindSignatures #-}
{-# Language TypeOperators #-}
{-# Language ExplicitNamespaces #-}
{-# Language TemplateHaskell #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language PatternGuards #-}
{-# Language MultiWayIf #-}
module Lang.Crucible.LLVM.Arch.X86 where

import qualified Data.BitVector.Sized as BV
import Data.Word(Word8)
import Data.Bits
import Data.Kind
import GHC.TypeNats (type (<=))

import Data.Parameterized.NatRepr(knownNat)
import Data.Parameterized.Classes(testEquality,compareF)
import Data.Parameterized.TraversableFC
import Data.Parameterized.TH.GADT as U

import           What4.Interface (SymBV)
import qualified What4.Interface as I

import Lang.Crucible.CFG.Extension
import Lang.Crucible.Types(CrucibleType,BVType,NatRepr,TypeRepr(..))
import Lang.Crucible.Simulator.RegValue(RegValue)
import Lang.Crucible.Panic(panic)

import Lang.Crucible.LLVM.Arch.Util((|->))

data AVXOp1 = VShiftL Word8     -- ^ Shift left by this many bytes
                                -- New bytes are 0.
            | VShufD Word8      -- ^ Shuffle 32-bit words of vector
                                -- according to pattern in the word8
              deriving (Eq,Ord)


data ExtX86 :: (CrucibleType -> Type) -> CrucibleType -> Type where

  {- | Unary operation on a vector.  Should have no side effects. -}
  VOp1 :: (1 <= n) =>
     !(NatRepr n)        -> {- width of input/result -}
     !AVXOp1             -> {- do this operation -}
     !(f (BVType n))     -> {- on this thing -}
     ExtX86 f (BVType n)



eval :: forall sym f tp.
        I.IsSymExprBuilder sym =>
        sym ->
        (forall subT. f subT -> IO (RegValue sym subT)) ->
        ExtX86 f tp ->
        IO (RegValue sym tp)
eval sym ev ext =
  case ext of
    VOp1 w op e ->
      case op of
        VShiftL amt -> vShiftL sym w amt =<< ev e
        VShufD ixes -> vShufD sym w ixes =<< ev e


-- | See @vpslldq@
vShiftL :: (I.IsSymExprBuilder sym, 1 <= w) =>
           sym -> NatRepr w -> Word8 -> SymBV sym w -> IO (SymBV sym w)
vShiftL sym w amt v =
  do i <- I.bvLit sym w (BV.mkBV w (8 * fromIntegral amt))
     I.bvShl sym v i


-- | See @vpshufd@
vShufD :: forall sym w.
          I.IsSymExprBuilder sym =>
          sym -> NatRepr w -> Word8 -> SymBV sym w -> IO (SymBV sym w)
vShufD sym w ixes v
  | Just I.Refl <- testEquality w n128 = mk128 v
  | Just I.Refl <- testEquality w n256 =
    do lower128 <- mk128 =<< I.bvSelect sym n0   n128 v
       upper128 <- mk128 =<< I.bvSelect sym n128 n128 v
       I.bvConcat sym upper128 lower128
  | otherwise = panic "Arch.X86.vShufD"
                        [ "*** Unexpected width: " ++ show (I.natValue w) ]

  where
  mk128 :: SymBV sym 128 -> IO (SymBV sym 128)
  mk128 src = do f0 <- getV src 0
                 f1 <- getV src 1
                 f2 <- getV src 2
                 f3 <- getV src 3
                 lower64 <- I.bvConcat sym f1 f0
                 upper64 <- I.bvConcat sym f3 f2
                 I.bvConcat sym upper64 lower64

  getV :: SymBV sym 128 -> Int -> IO (SymBV sym 32)
  getV src n = case getIx n of
                 0 -> I.bvSelect sym n0 n32 src
                 1 -> I.bvSelect sym n1 n32 src
                 2 -> I.bvSelect sym n2 n32 src
                 _ -> I.bvSelect sym n3 n32 src

  getIx :: Int -> Word8
  getIx n = (ixes `shiftR` (2 * n)) .&. 0x03 -- get 2 bit field




--------------------------------------------------------------------------------
n0 :: NatRepr 0
n0 = knownNat

n1 :: NatRepr 1
n1 = knownNat

n2 :: NatRepr 2
n2 = knownNat

n3 :: NatRepr 3
n3 = knownNat

n32 :: NatRepr 32
n32 = knownNat

n128 :: NatRepr 128
n128 = knownNat

n256 :: NatRepr 256
n256 = knownNat


--------------------------------------------------------------------------------

$([d| {- New TH Scope -} |])


-- This is going to go away
instance ShowFC ExtX86 where
  showFC _ _ = error "[ShowFC ExtX86] Not implmented."

instance TestEqualityFC ExtX86 where
  testEqualityFC testSubterm =
    $(U.structuralTypeEquality [t| ExtX86 |]
        [ U.ConType [t|NatRepr |] `U.TypeApp` U.AnyType |-> [|testEquality|]
        , U.DataArg 0             `U.TypeApp` U.AnyType |-> [|testSubterm|]
        ])

instance OrdFC ExtX86 where
  compareFC testSubterm =
    $(U.structuralTypeOrd [t| ExtX86 |]
        [ U.ConType [t|NatRepr |] `U.TypeApp` U.AnyType |-> [|compareF|]
        , U.DataArg 0             `U.TypeApp` U.AnyType |-> [|testSubterm|]
        ])

-- This is going away
instance HashableFC ExtX86 where
  hashWithSaltFC _hash _s _x = error "[HashableFC ExtX86] Not implmented."

instance FunctorFC ExtX86 where
  fmapFC = fmapFCDefault

instance FoldableFC ExtX86 where
  foldMapFC = foldMapFCDefault

instance TraversableFC ExtX86 where
  traverseFC = $(U.structuralTraversal [t|ExtX86|] [])

instance PrettyApp ExtX86 where
  ppApp _pp _x = error "[PrettyApp ExtX86] XXX"

instance TypeApp ExtX86 where
  appType x =
    case x of
      VOp1 w _ _ -> BVRepr w

