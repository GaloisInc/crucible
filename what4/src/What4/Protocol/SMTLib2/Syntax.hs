{-|
This module defines types and operations for generating SMTLIB2 files.

It does not depend on the rest of What4 so that it can be used
directly by clients interested in generating SMTLIB without depending
on the What4 formula interface.  All the type constructors are exposed
so that clients can generate new values that are not exposed through
this interface.
-}

{-# LANGUAGE OverloadedStrings #-}
module What4.Protocol.SMTLib2.Syntax
  ( -- * Commands
    Command(..)
  , setLogic
  , setOption
  , setProduceModels
  , exit
     -- * Declarations
  , declareSort
  , defineSort
  , declareConst
  , declareFun
  , defineFun
  , Symbol
    -- * Assertions and checking
  , checkSat
  , checkSatAssuming
  , checkSatWithAssumptions
  , getModel
  , getValue
  , push
  , pop
  , resetAssertions
  , assert
  , assertNamed
  , getUnsatAssumptions
  , getUnsatCore
    -- * Logic
  , Logic(..)
  , qf_bv
  , allSupported
    -- * Sort
  , Sort(..)
  , boolSort
  , bvSort
  , intSort
  , realSort
  , varSort
    -- * Term
  , Term(..)
  , un_app
  , bin_app
  , term_app
  , pairwise_app
  , namedTerm
    -- * Core theory
  , true
  , false
  , not
  , implies
  , and
  , or
  , xor
  , eq
  , distinct
  , ite
  , forall
  , exists
  , letBinder
    -- * @Ints@, @Reals@, @Reals_Ints@ theories
  , negate
  , numeral
  , decimal
  , sub
  , add
  , mul
  , div
  , (./)
  , mod
  , abs
  , le
  , lt
  , ge
  , gt
  , toReal
  , toInt
  , isInt
    -- * Bitvector theory and extensions
  , concat
  , extract
  , bvnot
  , bvand
  , bvor
  , bvxor
  , bvneg
  , bvadd
  , bvsub
  , bvmul
  , bvudiv
  , bvurem
  , bvshl
  , bvlshr
  , bvult
    -- ** Extensions provided by QF_BV
  , bit0
  , bit1
  , bvbinary
  , bvdecimal
  , bvhexadecimal
  , bvashr
  , bvslt
  , bvsle
  , bvule
  , bvsgt
  , bvsge
  , bvugt
  , bvuge
  , bvsdiv
  , bvsrem
  , bvsignExtend
  , bvzeroExtend
    -- * Array theory
  , arraySort
  , arrayConst
  , select
  , store
  ) where

import           Data.Bits hiding (xor)
import           Data.Char (intToDigit)
import           Data.Monoid ((<>))
import           Data.String
import           Data.Text (Text)
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.Builder.Int as Builder

import qualified Prelude
import           Prelude hiding (and, or, concat, negate, div, mod, abs, not)

app_list :: Builder -> [Builder] -> Builder
app_list o args = "(" <> o <> go args
  where go [] = ")"
        go (f:r) = " " <> f <> go r

app :: Builder -> [Builder] -> Builder
app o [] = o
app o args = app_list o args

builder_list :: [Builder] -> Builder
builder_list [] = "()"
builder_list (h:l) = app_list h l

------------------------------------------------------------------------
-- Logic

-- | Identifies the set of predefined sorts and operators available.
newtype Logic = Logic Builder

-- | Use the QF_BV logic
qf_bv :: Logic
qf_bv = Logic "QF_BV"

-- | Set the logic to all supported logics.
allSupported :: Logic
allSupported = Logic "ALL_SUPPORTED"

------------------------------------------------------------------------
-- Symbol

type Symbol = Text

------------------------------------------------------------------------
-- Sort

-- | Sort for SMTLIB expressions
newtype Sort = Sort { unSort :: Builder }

-- | Create a sort from a symbol name
varSort :: Symbol -> Sort
varSort = Sort . Builder.fromText

-- | Booleans
boolSort :: Sort
boolSort = Sort "Bool"

-- | Bitvectors with the given number of bits.
bvSort :: Integer -> Sort
bvSort w | w >= 1 = Sort $ "(_ BitVec " <> fromString (show w) <> ")"
         | otherwise = error "bvSort expects a positive number."

-- | Integers
intSort :: Sort
intSort = Sort "Int"

-- | Real numbers
realSort :: Sort
realSort = Sort "Real"

-- | @arraySort a b@ denotes the set of functions from @a@ to be @b@.
arraySort :: Sort -> Sort -> Sort
arraySort (Sort i) (Sort v) = Sort $ "(Array " <> i <> " " <> v <> ")"

------------------------------------------------------------------------
-- Term

-- | Denotes an expression in the SMT solver
newtype Term = T { renderTerm :: Builder }

-- | Construct an expression with the given operator and list of arguments.
term_app :: Builder -> [Term] -> Term
term_app o args = T (app o (renderTerm <$> args))

-- | Construct an expression with the given operator and single argument.
un_app :: Builder -> Term -> Term
un_app o (T x) = T $ mconcat ["(", o, " ", x, ")"]

-- | Construct an expression with the given operator and two arguments.
bin_app :: Builder -> Term -> Term -> Term
bin_app o (T x) (T y) = T $ mconcat ["(", o, " ", x, " ", y, ")"]

-- | Construct a chainable term with the given relation
--
-- @chain_app p [x1, x2, ..., xn]@ is equivalent to
-- @p x1 x2 /\ p x2 x3 /\ ... /\ p x(n-1) xn@.
chain_app :: Builder -> [Term] -> Term
chain_app f l@(_:_:_) = term_app f l
chain_app f _ = error $ show f ++ " expects two or more arguments."

-- | Build a term for a left-associative operator.
assoc_app :: Builder -> Term -> [Term] -> Term
assoc_app _ t [] = t
assoc_app f t l = term_app f (t:l)

-- | Append a "name" to a term so that it will be printed when
-- @(get-assignment)@ is called.
namedTerm :: Term -> Text -> Term
namedTerm (T x) nm = T $ "(! " <> x <> " :named " <> Builder.fromText nm <> ")"

------------------------------------------------------------------------
-- Core theory

-- | @true@ Boolean term
true :: Term
true = T "true"

-- | @false@ Boolean term
false :: Term
false = T "false"

-- | Complement a Boolean
not :: Term -> Term
not = un_app "not"

-- | @implies c r@ is equivalent to @c1 => c2 => .. cn => r@.
implies :: [Term] -> Term -> Term
implies [] t = t
implies l t = term_app "=>" (l ++ [t])

-- | Conjunction of all terms
and :: [Term] -> Term
and [] = true
and [x] = x
and l = term_app "and" l

-- | Disjunction of all terms
or :: [Term] -> Term
or [] = true
or [x] = x
or l = term_app "or" l

-- | Disjunction of all terms
xor :: [Term] -> Term
xor l@(_:_:_) = term_app "xor" l
xor _ = error "xor expects two or more arguments."

-- | Return true if all terms are equal.
eq :: [Term] -> Term
eq = chain_app "="

-- | Construct a chainable term with the givne relation
--
-- @pairwise_app p [x1, x2, ..., xn]@ is equivalent to
-- \forall_{i,j} p x_i x_j@.
pairwise_app :: Builder -> [Term] -> Term
pairwise_app _ [] = true
pairwise_app _ [_] = true
pairwise_app f l@(_:_:_) = term_app f l

-- | Asserts that each term in the list is unique.
distinct :: [Term] -> Term
distinct = pairwise_app "distinct"

-- | Create an if-then-else expression.
ite :: Term -> Term -> Term -> Term
ite c x y = term_app "ite" [c, x, y]

varBinding :: (Text,Sort) -> Builder
varBinding (nm, tp) = "(" <> Builder.fromText nm <> " " <> unSort tp <> ")"

-- | @forall vars t@ denotes a predicate that holds if @t@ for every valuation of the
-- variables in @vars@.
forall :: [(Text, Sort)] -> Term -> Term
forall [] r = r
forall vars r =
  T $ app "forall" [builder_list (varBinding <$> vars), renderTerm r]

-- | @exists vars t@ denotes a predicate that holds if @t@ for some valuation of the
-- variables in @vars@.
exists :: [(Text, Sort)] -> Term -> Term
exists [] r = r
exists vars r =
  T $ app "exists" [builder_list (varBinding <$> vars), renderTerm r]

letBinding :: (Text, Term) -> Builder
letBinding (nm, t) = app_list (Builder.fromText nm) [renderTerm t]

-- | Create a let binding
letBinder :: [(Text, Term)] -> Term -> Term
letBinder [] r = r
letBinder vars r =
  T (app "let" [builder_list (letBinding <$> vars), renderTerm r])

------------------------------------------------------------------------
-- Reals/Int/Real_Ints theories

-- | Negate an integer or real number.
negate :: Term -> Term
negate = un_app "-"

-- | Create a numeral literal from the given integer.
numeral :: Integer -> Term
numeral i | i >= 0 = T $ Builder.decimal i
          | otherwise = negate (T (Builder.decimal (Prelude.negate i)))

-- | Create a literal as a real from the given integer.
decimal :: Integer -> Term
decimal i | i >= 0 = T $ Builder.decimal i <> ".0"
          | otherwise = negate $ T $ Builder.decimal (Prelude.negate i) <> ".0"

-- | @sub x1 [x2, ..., xn]@ with n >= 1 returns
-- @x1@ minus @x2 + ... + xn@.
--
-- The terms are expected to have type @Int@ or @Real@.
sub :: Term -> [Term] -> Term
sub x [] = x
sub x l = term_app "-" (x:l)

-- | @add [x1, x2, ..., xn]@ with n >= 2 returns
-- @x1@ minus @x2 + ... + xn@.
--
-- The terms are expected to have type @Int@ or @Real@.
add :: [Term] -> Term
add [] = T "0"
add [x] = x
add l = term_app "+" l

-- | @add [x1, x2, ..., xn]@ with n >= 2 returns
-- @x1@ minus @x2 + ... + xn@.
--
-- The terms are expected to have type @Int@ or @Real@.
mul :: [Term] -> Term
mul [] = T "1"
mul [x] = x
mul l = term_app "*" l

-- | @div x1 [x2, ..., xn]@ with n >= 1 returns
-- @x1@ div @x2 * ... * xn@.
--
-- The terms are expected to have type @Int@.
div :: Term -> [Term] -> Term
div x [] = x
div x l = term_app "div" (x:l)

-- | @x1 ./ [x2, ..., xn]@ with n >= 1 returns
-- @x1@ / @x2 * ... * xn@.
(./) :: Term -> [Term] -> Term
x ./ [] = x
x ./ l = term_app "/" (x:l)

-- | @mod x1 x2@ returns x1 - x2 * (x1 `div` [x2])@.
--
-- The terms are expected to have type @Int@.
mod :: Term -> Term -> Term
mod = bin_app "mod"

-- | @abs x1@ returns the absolute value of @x1@.
--
-- The term is expected to have type @Int@.
abs :: Term -> Term
abs = un_app "abs"

-- | Less than or equal over a chained list of terms.
--
-- @le [x1, x2, ..., xn]@ is equivalent to
-- @x1 <= x2 /\ x2 <= x3 /\ ... /\ x(n-1) <= xn@.
--
-- This is defined in the Reals, Ints, and Reals_Ints theories,
-- and the number of elements must be at least 2.
--
-- With a strict interpretation of the SMTLIB standard, the terms should
-- be all of the same type (i.e. "Int" or Real"), but existing solvers appear
-- to implicitly all mixed terms.
le :: [Term] -> Term
le = chain_app "<="

-- | Less than over a chained list of terms.
--
-- @lt [x1, x2, ..., xn]@ is equivalent to
-- @x1 < x2 /\ x2 < x3 /\ ... /\ x(n-1) < xn@.
--
-- With a strict interpretation of the SMTLIB standard, the terms should
-- be all of the same type (i.e. "Int" or Real"), but existing solvers appear
-- to implicitly all mixed terms.
lt :: [Term] -> Term
lt = chain_app "<"

-- | Greater than or equal over a chained list of terms.
--
-- @ge [x1, x2, ..., xn]@ is equivalent to
-- @x1 >= x2 /\ x2 >= x3 /\ ... /\ x(n-1) >= xn@.
--
-- With a strict interpretation of the SMTLIB standard, the terms should
-- be all of the same type (i.e. "Int" or Real"), but existing solvers appear
-- to implicitly all mixed terms.
ge :: [Term] -> Term
ge = chain_app ">="

-- | Greater than over a chained list of terms.
--
-- @gt [x1, x2, ..., xn]@ is equivalent to
-- @x1 > x2 /\ x2 > x3 /\ ... /\ x(n-1) > xn@.
--
-- With a strict interpretation of the SMTLIB standard, the terms should
-- be all of the same type (i.e. "Int" or Real"), but existing solvers appear
-- to implicitly all mixed terms.
gt :: [Term] -> Term
gt = chain_app ">"

-- | Maps a term with type @Int@ to @Real@.
toReal :: Term -> Term
toReal = un_app "to_real"

-- | Returns the largest integer not larger than the given real term.
toInt :: Term -> Term
toInt = un_app "to_int"

-- | Returns true if this is an integer.
isInt :: Term -> Term
isInt = un_app "is_int"

------------------------------------------------------------------------
-- Array theory

-- | @arrayConst t1 t2 c@ generates an array with index type `t1` and
-- value type `t2` that always returns `c`.
--
-- This uses the non-standard SMTLIB2 syntax
-- @((as const (Array t1 t2)) c)@ which is supported by CVC4 and Z3
-- (and perhaps others).
arrayConst :: Sort -> Sort -> Term -> Term
arrayConst itp rtp c =
  let tp = arraySort itp rtp
      cast_app = builder_list [ "as" , "const" , unSort tp ]
   in term_app cast_app [ c ]

-- | @select a i@ denotes the value of @a@ at @i@.
select :: Term -> Term -> Term
select = bin_app "select"

-- | @store a i v@ denotes the array whose valuation is @v@ at index @i@ and
-- @select a j@ at every other index @j@.
store :: Term -> Term -> Term -> Term
store a i v = term_app "store" [a,i,v]

------------------------------------------------------------------------
-- Bitvector theory

-- | A 1-bit bitvector representing @0@.
bit0 :: Term
bit0 = T "#b0"

-- | A 1-bit bitvector representing @1@.
bit1 :: Term
bit1 = T "#b1"

-- | @bvbinary x w@ constructs a bitvector term with width @w@ equal to @x `mod` 2^w@.
--
-- The width @w@ must be positive.
--
-- The literal uses a binary notation.
bvbinary :: Integer -> Integer -> Term
bvbinary u w0
    | w0 <= 0 = error $ "bvbinary width must be positive."
    | w0 > toInteger (maxBound :: Int) = error $ "Integer width is too large."
    | otherwise = T $ "#b" <> go (fromIntegral w0)
  where go :: Int -> Builder
        go 0 = mempty
        go w =
          let i = w - 1
              b :: Builder
              b = if  u `testBit` i then "1" else "0"
           in b <> go i

-- | @bvdecimal x w@ constructs a bitvector term with width @w@ equal to @x `mod` 2^w@.
--
-- The width @w@ must be positive.
--
-- The literal uses a decimal notation.
bvdecimal :: Integer -> Integer -> Term
bvdecimal u w
    | w <= 0 = error "bvdecimal width must be positive."
    | otherwise = T $ mconcat [ "(_ bv", Builder.decimal d, " ", Builder.decimal w, ")"]
  where d = u .&. (2^w - 1)

-- | @bvhexadecimal x w@ constructs a bitvector term with width @w@ equal to @x `mod` 2^w@.
--
-- The width @w@ must be a positive multiple of 4.
--
-- The literal uses hex notation.
bvhexadecimal :: Integer -> Integer -> Term
bvhexadecimal u w0
    | w0 <= 0 = error $ "bvhexadecimal width must be positive."
    | w0 > toInteger (maxBound :: Int) = error $ "Integer width is too large."
    | otherwise = T $ "#x" <> go (fromIntegral w0)
  where go :: Int -> Builder
        go 0 = mempty
        go w | w < 4 = error "bvhexadecimal width must be a multiple of 4."
        go w =
          let i = w - 4
              c :: Char
              c = intToDigit $ fromInteger $ (u `shiftR` i) .&. 0xf
           in Builder.singleton c <> go i

-- | @concat x y@ returns the bitvector with the bits of @x@ followed by the bits of @y@.
concat :: Term -> Term -> Term
concat = bin_app "concat"

-- | @extract i j x@ returns the bitvector containing the bits @[j..i]@.
extract :: Integer -> Integer -> Term -> Term
extract i j x
  | j < 0 = error "Initial bit is negative"
  | i < j = error $ "End of extract (" ++ show i ++ ") less than beginning (" ++ show j ++ ")."
  | otherwise = -- We cannot check that j is small enough.
    let e = "(_ extract " <> Builder.decimal i <> " " <> Builder.decimal j <> ")"
     in un_app e x

-- | Bitwise negation of term.
bvnot :: Term -> Term
bvnot = un_app "bvnot"

-- | Bitwise and of all arguments.
bvand :: Term -> [Term] -> Term
bvand = assoc_app "bvand"

-- | Bitwise include or of all arguments.
bvor :: Term -> [Term] -> Term
bvor = assoc_app "bvor"

-- | Bitvector exclusive or of all arguments.
bvxor :: Term -> [Term] -> Term
bvxor = assoc_app "bvxor"

-- | Negate the bitvector
bvneg :: Term -> Term
bvneg = un_app "bvneg"

-- | Bitvector addition
bvadd :: Term -> [Term] -> Term
bvadd = assoc_app "bvadd"

-- | Bitvector subtraction
bvsub :: Term -> Term -> Term
bvsub = bin_app "bvsub"

-- | Bitvector multiplication
bvmul :: Term -> [Term] -> Term
bvmul = assoc_app "bvmul"

-- | @bvudiv x y@ returns @floor (to_nat x / to_nat y)@ when @y != 0@.
--
-- When @y = 0@, this returns @not (from_nat 0)@.
bvudiv :: Term -> Term -> Term
bvudiv = bin_app "bvudiv"

-- | @bvurem x y@ returns @x - y * bvudiv x y@ when @y != 0@.
--
-- When @y = 0@, this returns @from_nat 0@.
bvurem :: Term -> Term -> Term
bvurem = bin_app "bvurem"

-- | @bvshl x y@ shifts the bits in @x@ to the left by @to_nat u@ bits.
--
-- The new bits are zeros (false)
bvshl :: Term -> Term -> Term
bvshl = bin_app "bvshl"

-- | @bvlshr x y@ shifts the bits in @x@ to the right by @to_nat u@ bits.
--
-- The new bits are zeros (false)
bvlshr :: Term -> Term -> Term
bvlshr = bin_app "bvlshr"

-- | @bvult x y@ returns a Boolean term that is true if @to_nat x < to_nat y@.
bvult :: Term -> Term -> Term
bvult = bin_app "bvult"

-- | @bvule x y@ returns a Boolean term that is true if @to_nat x <= to_nat y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvule :: Term -> Term -> Term
bvule = bin_app "bvule"

-- | @bvsle x y@ returns a Boolean term that is true if @to_int x <= to_int y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsle :: Term -> Term -> Term
bvsle = bin_app "bvsle"

-- | @bvslt x y@ returns a Boolean term that is true if @to_int x < to_int y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvslt :: Term -> Term -> Term
bvslt = bin_app "bvslt"

-- | @bvuge x y@ returns a Boolean term that is true if @to_nat x <= to_nat y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvuge :: Term -> Term -> Term
bvuge = bin_app "bvuge"

-- | @bvugt x y@ returns a Boolean term that is true if @to_nat x < to_nat y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvugt :: Term -> Term -> Term
bvugt = bin_app "bvugt"

-- | @bvsge x y@ returns a Boolean term that is true if @to_int x <= to_int y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsge :: Term -> Term -> Term
bvsge = bin_app "bvsge"

-- | @bvsgt x y@ returns a Boolean term that is true if @to_int x < to_int y@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsgt :: Term -> Term -> Term
bvsgt = bin_app "bvsgt"

-- | @bvashr x y@ shifts the bits in @x@ to the right by @to_nat u@ bits.
--
-- The new bits are the same as the most-significant bit of @x@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvashr :: Term -> Term -> Term
bvashr = bin_app "bvashr"

-- | @bvsdiv x y@ returns @round_to_zero (to_int x / to_int y)@ when @y != 0@.
--
-- When @y = 0@, this returns @not (from_nat 0)@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsdiv :: Term -> Term -> Term
bvsdiv = bin_app "bvudiv"

-- | @bvsrem x y@ returns @x - y * bvsdiv x y@ when @y != 0@.
--
-- When @y = 0@, this returns @from_nat 0@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsrem :: Term -> Term -> Term
bvsrem = bin_app "bvsrem"

-- | @bvsignExtend w x@ adds an additional @w@ bits to the most
-- significant bits of @x@ by sign extending @x@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvsignExtend :: Integer -> Term -> Term
bvsignExtend w x =
  let e = "(_ sign_extend " <> Builder.decimal w <> ")"
   in un_app e x

-- | @bvzeroExtend w x@ adds an additional @w@ zero bits to the most
-- significant bits of @x@.
--
-- Note. This is in @QF_BV@, but not the bitvector theory.
bvzeroExtend :: Integer -> Term -> Term
bvzeroExtend w x =
  let e = "(_ zero_extend " <> Builder.decimal w <> ")"
   in un_app e x

------------------------------------------------------------------------
-- Command

-- | This represents a command to be sent to the SMT solver.
newtype Command = Cmd Builder

-- | Set the logic of the SMT solver
setLogic :: Logic -> Command
setLogic (Logic nm) = Cmd $ "(set-logic " <> nm <> ")"

-- | Set an option in the SMT solver
--
-- The name should not need to be prefixed with a colon."
setOption :: Text -> Text -> Command
setOption nm val = Cmd $ app_list "set-option" [":" <> Builder.fromText nm, Builder.fromText val]

ppBool :: Bool -> Text
ppBool b = if b then "true" else "false"

-- | Set option to produce models
--
-- This is a widely used option so, we we have a custom command to
-- make it.
setProduceModels :: Bool -> Command
setProduceModels b = setOption "produce-models" (ppBool b)

-- | Request the SMT solver to exit
exit :: Command
exit = Cmd "(exit)"

-- | Declare an uninterpreted sort with the given number of sort parameters.
declareSort :: Symbol -> Integer -> Command
declareSort v n = Cmd $ app "declare-sort" [Builder.fromText v, fromString (show n)]

-- | Define a sort in terms of other sorts
--
defineSort :: Symbol -- ^ Name of new sort
           -> [Symbol] -- ^ Parameters for polymorphic sorts
           -> Sort -- ^ Definition
           -> Command
defineSort v params d =
  Cmd $ app "define-sort" [ Builder.fromText v
                          , builder_list (Builder.fromText <$> params)
                          , unSort d
                          ]

-- | Declare a constant with the given name and return types.
declareConst :: Text -> Sort -> Command
declareConst v tp = Cmd $ app "declare-const" [Builder.fromText v, unSort tp]

-- | Declare a function with the given name, argument types, and
-- return type.
declareFun :: Text -> [Sort] -> Sort -> Command
declareFun v argSorts retSort = Cmd $
  app "declare-fun" [ Builder.fromText v
                    , builder_list $ unSort <$> argSorts
                    , unSort retSort
                    ]

-- | Declare a function with the given name, argument types, and
-- return type.
defineFun :: Text -> [(Text,Sort)] -> Sort -> Term -> Command
defineFun f args return_type e =
  let resolveArg (var, tp) = app (Builder.fromText var) [unSort tp]
   in Cmd $ app "define-fun" [ Builder.fromText f
                             , builder_list (resolveArg <$> args)
                             , unSort return_type
                             , renderTerm e
                             ]

-- | Assert the predicate holds in the current context.
assert :: Term -> Command
assert p = Cmd $ app "assert" [renderTerm p]

-- | Assert the predicate holds in the current context, and assign
--   it a name so it can appear in unsatisfiable core results.
assertNamed :: Term -> Text -> Command
assertNamed p nm =
  Cmd $ app "assert"
    [builder_list [Builder.fromText "!", renderTerm p, Builder.fromText ":named", Builder.fromText nm]]

-- | Check the satisfiability of the current assertions
checkSat :: Command
checkSat = Cmd "(check-sat)"

-- | Check the satisfiability of the current assertions and the additional ones in the list.
checkSatAssuming :: [Term] -> Command
checkSatAssuming l = Cmd $ "(check-sat-assuming " <> builder_list (renderTerm <$> l) <> ")"

-- | Check satisfiability of the given atomic assumptions in the current context.
--
--   NOTE! The names of variables passed to this function MUST be generated using
--   a `declare-fun` statement, and NOT a `define-fun` statement.  Thus, if you
--   want to bind an arbitrary term, you must declare a new term and assert that
--   it is equal to it's definition. Yes, this is quite irritating.
checkSatWithAssumptions :: [Text] -> Command
checkSatWithAssumptions nms = Cmd $ app "check-sat-assuming" [builder_list (map Builder.fromText nms)]

-- | Get the model associated with the last call to @check-sat@.
getModel :: Command
getModel = Cmd "(get-model)"

getUnsatAssumptions :: Command
getUnsatAssumptions = Cmd "(get-unsat-assumptions)"

getUnsatCore :: Command
getUnsatCore = Cmd "(get-unsat-core)"

-- | Get the values associated with the terms from the last call to @check-sat@.
getValue :: [Term] -> Command
getValue values = Cmd $ app "get-value" [builder_list (renderTerm <$> values)]

-- | Empties the assertion stack and remove all global assertions and declarations.
resetAssertions :: Command
resetAssertions = Cmd "(reset-assertions)"

-- | Push the given number of scope frames to the SMT solver.
push :: Integer -> Command
push n =  Cmd $ "(push " <> Builder.decimal n <> ")"

-- | Pop the given number of scope frames to the SMT solver.
pop :: Integer -> Command
pop n =  Cmd $ "(pop " <> Builder.decimal n <> ")"
