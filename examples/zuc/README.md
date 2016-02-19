This directory contains an example of using SAW to reason about both
equivalence and cryptographic properties of a stream cipher. This
document is derived from a blog post about using Cryptol to describe the
ZUC cipher, and extended with examples of using SAW to compare Cryptol
and C versions of the algorithm. If you're primarily interested in using
SAW for the analysis of C code, you can skip to the "Security of ZUC"
section toward the end.

ZUC is a stream cipher that is proposed for inclusion in the "4G" mobile
standard named LTE (Long Term Evolution), the future of secure GSM. The
proposal is actually comprised several different algorithms:

* A stream cipher named ZUC,
* the LTEencryption algorithm (128-EEA3), based on ZUC, and
* the LTEintegrity algorithm (128-EIA3), which is a hash function using
ZUC as its core.

We will walk through a Cryptol implementation of ZUC, providing
executable reference code. In addition, we will discuss some of the
security concerns raised for version 1.4 of the algorithm: we will use
Cryptol to automatically identify an initialization vector (IV)
collision vulnerability, which was independently discovered and is
addressed in version 1.5 of the algorithm. We will also prove that the
proposed fix is indeed valid, again using Cryptol’s formal verification
tools. Finally, we will prove that the Cryptol code is equivalent to the
C reference implementation provided with the specification document.

While we do assume some familiarity with ZUC and Cryptol, we hope to
also shed some light into how Cryptol can be used in the cryptographic
design and evaluation processes even if you skip all the ZUC-specific
details.

Our implementation follows the
[specification](http://www.gsma.com/aboutus/wp-content/uploads/2014/12/eea3eia3zucv16.pdf)
of ZUC.

# Addition in GF(2^31 - 1)

One of the core operations in ZUC is addition of two 31-bit numbers, say
a and b. The specification states that this operation can be done as
follows:

* Compute v = a+b
* If the carry bit is 1, set v=v+1

We transliterate this algorithm to Cryptol straightforwardly:

~~~~ {.cryptol}
plus : ([31], [31]) -> [31]
plus (a, b) =
    if sab @ 0 then sab' + 1 else sab'
    where
      sab : [32]
      sab = ((zero : [1]) # a) + ((zero : [1]) # b)
      sab' : [31]
      sab' = drop sab
~~~~

Note how we detect overflow by doing the 32-bit addition and checking
the final bit. We can generalize `plus` to `add`, which will add any
sequence of numbers in GF(2^31-1) using plus repetitively:

~~~~ {.cryptol}
add : {a} (fin a) => [a][31] -> [31]
add xs =
    sums ! 0
    where
      sums =
          [0] #
          [plus (s, x) | s <- sums
                       | x <- xs]
~~~~

We simply generate the partial sums, and return the final sum by
selecting the last element.

# A digression on plus

As an interesting aside, the ZUC specification calls the plus operation
we have defined above addition modulo 23^1-1, which does not seem to be
the traditional modular addition. In particular, you can prove that will
never evaluate to 0 unless its arguments are both 0, which is not quite
how modular addition typically behaves. We can prove this claim using
SAW’s satisfiability checker:

~~~~
# saw
sawscript> import "zuc.cry"
sawscript> sat abc {{ \(a,b) -> (a != 0) && (b != 0) && (plus(a, b) == 0) }}
Unsat
~~~~

# The LFSR

At the core of ZUC lies an LFSR (Linear Feedback Shift Register), which
comprises 16 cells, each of which is precisely 31 bits wide. Cryptol’s
type-system has been designed to accurately capture such specifications:

~~~~ {.cryptol}
type LFSR = [16][31]
~~~~

Note that we do not have to resort to using 32-bit machine integers or
some other machine mandated bit-size, freeing us to give a fully
faithful implementation of the specification.

ZUC uses the LFSR in two different modes. In the initialization mode, it
takes a 31-bit input `u`, and transforms the LFSR by computing a
polynomial modulo 2^31 - 1 and adding the resulting value to the input
`u`. ZUC then "tweaks" the sum to avoid a `0` result. The Cryptol code
below implements the specification quite closely:

~~~~ {.cryptol}
LFSRWithInitializationMode : ([31], LFSR) -> LFSR
LFSRWithInitializationMode (u, ss) =
    ss @@ [1 .. 15] # [s16]
    where
      v = add [s <<< c | s <- ss @@ [15, 13, 10, 4, 0, 0]
                       | c <- [15, 17, 21, 20, 8, 0]]
      vu = if version1_5 then add [v, u] else v ^ u
      s16 = if vu == 0 then `0x7FFFFFFF else vu
~~~~

Note how we pick elements of the LFSR and the coefficients by a simple
sequence comprehension.

Compare this with the reference implementation in C:

~~~~ {.c}
void LFSRWithInitialisationMode(u32 u)
{
    u32 f, v;
    f = LFSR_S0;
    v = MulByPow2(LFSR_S0, 8);
    f = AddM(f, v);
    v = MulByPow2(LFSR_S4, 20);
    f = AddM(f, v);
    v = MulByPow2(LFSR_S10, 21);
    f = AddM(f, v);
    v = MulByPow2(LFSR_S13, 17);
    f = AddM(f, v);
    v = MulByPow2(LFSR_S15, 15);
    f = AddM(f, v);
    LFSR_S0 = LFSR_S1;
    LFSR_S1 = LFSR_S2;
    LFSR_S2 = LFSR_S3;
    LFSR_S3 = LFSR_S4;
    LFSR_S4 = LFSR_S5;
    LFSR_S5 = LFSR_S6;
    LFSR_S6 = LFSR_S7;
    LFSR_S7 = LFSR_S8;
    LFSR_S8 = LFSR_S9;
    LFSR_S9 = LFSR_S10;
    LFSR_S10 = LFSR_S11;
    LFSR_S11 = LFSR_S12;
    LFSR_S12 = LFSR_S13;
    LFSR_S13 = LFSR_S14;
    LFSR_S14 = LFSR_S15;
#ifdef VERSION_1_4
    LFSR_S15 = f ^ u;
#else
    LFSR_S15 = AddM(f, u);
#endif
    if (LFSR_S15 == 0)
    {
        LFSR_S15 = 0x7FFFFFFF;
    }
}
~~~~

In the work mode, there is no initializer value `u`, but otherwise the
operation is very similar (as is the C code, so we omit it):

~~~~ {.cryptol}
LFSRWithWorkMode : LFSR -> LFSR
LFSRWithWorkMode ss =
    ss @@ [1 .. 15] # [s16]
    where
      v = add [s <<< c | s <- ss @@ [15, 13, 10, 4, 0, 0]
                       | c <- [15, 17, 21, 20, 8, 0]]
      s16 = if v == 0 then `0x7FFFFFFF else v
~~~~

We could have defined `LFSRWithWorkMode` in terms of
`LFSRWithInitializationMode` by passing `0` for `u`, but the above
definition follows the specification much more closely, a desirable
thing to do for a reference implementation. (Also, this version of is a
bit faster for obvious reasons, saving us some cycles during execution.)

# Bit reorganization

The middle layer of ZUC takes the LFSR and shuffles its contents as follows:

~~~~ {.cryptol}
BitReorganization : LFSR -> [4][32]
BitReorganization ss =
    [ hi s15 # lo s14
    , lo s11 # hi s9
    , lo s7  # hi s5
    , lo s2  # hi s0]
    where
      lo : [31] -> [16]
      hi : [31] -> [16]
      lo x = x @@ [15 .. 30]
      hi x = x @@ [0  .. 15]
      [s0, s2, s5, s7, s9, s11, s14, s15] = ss @@ [0, 2, 5, 7, 9, 11, 14, 15]
~~~~

There isn't much to say about bit-reorganization, except to note that
selecting high and low bytes of a 31-bit word comes out quite clean in
Cryptol, thanks to bit-level addressability and compact selection
operation `@@`. Note how ZUC defines the higher 16 bits of a 31 bit
number by picking bits 15 through 30; which is just as natural in
Cryptol to express as any other slice of a given word.

# The nonlinear function F

Cryptol implementation of ZUC's F function follows the specification
almost literally:

~~~~ {.cryptol}
F : ([3][32], [2][32]) -> ([32], [2][32])
F ([X0, X1, X2], [R1, R2]) =
    (W, [R1', R2'])
    where
      W = (X0 ^ R1) + R2
      W1 = R1 + X1
      W2 = R2 ^ X2
      [W1H, W1L] = split W1
      [W2H, W2L] = split W2
      R1' = S (L1 (W1L # W2H))
      R2' = S (L2 (W2L # W1H))
~~~~

Note that we keep track of the parameters R1 and R2 explicitly. Being a
purely functional language, Cryptol does not have any notion of state,
and hence does not support in-place updates. However, this does not mean
inefficient execution: the purely functional approach makes sure the
specifications remain easy to develop and reason about, while backend
tools (compilers, synthesizers, etc.) can transform the code to run
efficiently on various targets appropriately, such as on FPGAs or in
software.

The C reference implementation is similarly long, but less clear, partly
due to the lack of a 31-bit integer type in C:

~~~~ {.c}
u32 F()
{
    u32 W, W1, W2, u, v;
    W = (BRC_X0 ^ F_R1) + F_R2;
    W1 = F_R1 + BRC_X1;
    W2 = F_R2 ^ BRC_X2;
    u = L1((W1 << 16) | (W2 >> 16));
    v = L2((W2 << 16) | (W1 >> 16));
    F_R1 = MAKEU32(S0[u >> 24],         S1[(u >> 16) & 0xFF],
                   S0[(u >> 8) & 0xFF], S1[u & 0xFF]);
    F_R2 = MAKEU32(S0[v >> 24],         S1[(v >> 16) & 0xFF],
                   S0[(v >> 8) & 0xFF], S1[v & 0xFF]);
    return W;
}
~~~~

We will skip the details of ZUC’s S-boxes and the functions `L1` and
`L2`, but you can see their implementation [here](zuc.cry).

# Loading the key

ZUC receives a 128 bit key and a 128-bit IV (initialization vector), to
construct the initial starting configuration of the LFSR. The following
definition follows the specification (Section 3.5) literally:

~~~~ {.cryptol}
LoadKey : ([128], [128]) -> LFSR
LoadKey (key, iv) =
    [k # d # i | k <- ks
               | i <- is
               | d <- ds]
    where
      ks : [16][8]
      ks = split key
      is : [16][8]
      is = split iv
      ds : [16][15]
      ds =
          [ 0b100010011010111, 0b010011010111100
          , 0b110001001101011, 0b001001101011110
          , 0b101011110001001, 0b011010111100010
          , 0b111000100110101, 0b000100110101111
          , 0b100110101111000, 0b010111100010011
          , 0b110101111000100, 0b001101011110001
          , 0b101111000100110, 0b011110001001101
          , 0b111100010011010, 0b100011110101100
          ]
~~~~

# Initializing ZUC

During the initialization stage, ZUC loads the key and the IV, and then
repeatedly performs bit-reorganization, a run of `F`, and a run of LFSR
in initialization mode. This process is repeated 32 times. For purposes
that will become clear later, we represent this operation as a Cryptol
stream function that returns an infinite sequence of ZUC configurations:

~~~~ {.cryptol}
type ZUC = (LFSR, [32], [32])
InitializeZUC : ([128], [128]) -> [inf]ZUC
InitializeZUC (key, iv) =
    outs
    where
      initLFSR = LoadKey (key, iv)
      outs = [(initLFSR, 0, 0)] # [step out | out <- outs]
      step (lfsr, R1, R2) =
          (LFSRWithInitializationMode (drop (w >> 1), lfsr), R1', R2')
          where
            [X0, X1, X2, X3] = BitReorganization lfsr
            (w', [R1', R2']) = F ([X0, X1, X2], [R1, R2])
            w = if version1_5 then w' else w' ^ X3
~~~~

# Executing ZUC

We need two more pieces of functionality. In the so called working
stage, ZUC runs bit-reorganization, `F`, and LFSR in work mode,
discarding the result of the call to `F`:

~~~~ {.cryptol}
WorkingStage : ZUC -> ZUC
WorkingStage (lfsr, R1, R2) =
    (lfsr', R1', R2')
    where
      [X0, X1, X2, _] = BitReorganization lfsr
      (_, [R1', R2']) = F ([X0, X1, X2], [R1, R2])
      lfsr' = LFSRWithWorkMode lfsr
~~~~

Cryptol's pattern-matching based definitions come out quite nicely in
picking (and ignoring) results of operations.

In the `production stage`, ZUC transforms works just like in the working
stage, except the result of the call to `F` is returned as the next
32-bit key, after XORing with the last word of what bit-reorganization
returns. Again, the Cryptol code is straightforward:

~~~~ {.cryptol}
ProductionStage : ZUC -> ([32], ZUC)
ProductionStage (lfsr, R1, R2) =
    (w ^ X3, (lfsr', R1', R2'))
    where
      [X0, X1, X2, X3] = BitReorganization lfsr
      (w, [R1', R2']) = F ([X0, X1, X2], [R1, R2])
      lfsr' = LFSRWithWorkMode lfsr
~~~~

# The ZUC API

We can finally give the ZUC API. Given a key and an IV, ZUC initializes
itself, and then keeps calling `ProductionStage` to generate successive
sequences of 32-bit words as key expansion. The result is most naturally
captured in Cryptol as an infinite sequence of 32-bit words:

~~~~ {.cryptol}
ZUC : [128] -> [128] -> [inf][32]
ZUC key iv =
    tail [w | (w, _) <- zucs]
    where
      initZuc = WorkingStage (InitializeZUC (key, iv) @ 32)
      zucs = [(zero, initZuc)] # [ProductionStage zuc | (_, zuc) <- zucs]
~~~~

Encryption can now be done by taking the plaintext and XOR’ing with the
successive words that come out of the above function: Clearly,
decryption is the same as encryption, and the fact that they are
inverses follows trivially from the fact that it’s a mere XOR operation.

And this completes our development of ZUC in Cryptol. You can see the
entire code here.

# Testing

One thing about developing cryptographic algorithms is that it is hard
to convince oneself that the algorithm is coded correctly. ZUC is no
exception. Hopefully, Cryptol makes that task easier by abstracting away
from many of the machine-specific details, providing a language that
allows one to express idioms that appear in cryptography quite
concisely, thus removing a whole class of bugs that has nothing to do
with the algorithm itself but rather with how it has to be implemented.

The other aspect of Cryptol is that the specification, as high level as
it is, remains executable. So, we can use our implementation and test it
against the published test-vectors for ZUC. Here’s the first example
from the test document (Section 3.3):

~~~~
# cryptol zuc.cry
Main> take (ZUC 0 0) : [2][32]
[0x27bede74, 0x018082da]
~~~~

(The full [implementation](zuc.cry) has further test vectors from the
specification, see the theorem `ZUC_TestVectors`.) Note that since our
implementation of ZUC returns an infinite sequence, we have used the
`take` function to just look at the first two outputs. Naturally, we can
pull out as many outputs as we would like from that infinite stream.

# Security of ZUC

One essential activity in crypto-algorithm design is to provide rigorous
security arguments. While the current state-of-the-art in developing
such arguments relies largely on human intelligence, we can use tools to
attest our findings. In this section we will see how to use Cryptol to
mechanically demonstrate an IV collision vulnerability found in version
1.4 of the ZUC specification, and how the modifications in version 1.5
addressed the problem.

An IV collision occurs if two different IVs cause the algorithm to
initialize itself to precisely the same state, thus losing entropy.
Cryptographers seriously worry about such losses of entropy as they can
lead to efficient attacks by cutting down the search space
significantly. In a recent conference, Wu et al.,
[demonstrated](http://www.iacr.org/archive/asiacrypt2012/76580257/76580257.pdf)
one such vulnerability in ZUC 1.4. In that version of the specification,
ZUC had a slightly different initialization sequence. First, instead of
addition in GF(2^31-1), it performed a simple XOR when LFSR is used in
the initialization mode. Second, version 1.4 XORed the last byte from
the bit-reorganization during initialization with the result of the call
to the nonlinear function F. (You can see the precise differences
between versions 1.4 and 1.5 in the attached Cryptol code, search for
the occurrences of the variable version1_5, which distinguishes between
the two.)

As demonstrated by Wu et al., the 1.4 version of the algorithm suffers
from IV collision: That is, two different IV’s can result in the precise
same ZUC state, causing loss of entropy. It is easy to express this
property as a Cryptol theorem:

~~~~ {.cryptol}
property ZUC_isResistantToCollisionAttack (k, iv1, iv2) =
    if iv1 != iv2
    then InitializeZUC (k, iv1) @ 1 != InitializeZUC (k, iv2) @ 1
    else True
~~~~

Let’s spend a moment on what the above theorem is stating. It says that
for all values of `k`, `iv1`, and `iv2`, the initial state of ZUC will
be different so long as `iv1` and `iv2` are not the same. If this
theorem holds of our algorithm, it would mean that there is no entropy
loss due to IV collision. (We also now see why we chose `InitializeZUC`
to return an infinite stream: This way we can simply look at the result
of the first step, which will create a simpler verification problem for
the backend SAT/SMT solver used by Cryptol.)

Here is SAW's response when we tell it to prove the above theorem,
using version 1.4 of the specification:

~~~~
sawscript> set_base 16
sawscript> time (prove z3 {{ ZUC_isResistantToCollisionAttack }})
Time: 1.439527s
Invalid: (0x1a00000001ec00000095d9000029006b,
 0x8a008f00f30000000000f008004c0800,
 0x0a008f00f30000000000f008004c0800)
~~~~

The first command tells SAW to print values in base 16, which will make
the counter-examples easier to read. In the second command, we asked SAW
to prove that the theorem holds of our implementation, using the Z3
theorem prover. Not only has SAW told us that the theorem we have stated
is false, it also provided a concrete counterexample! (Note that those
two IV values are different, check the first digit!) Let’s verify that
the vulnerability indeed does exist with the IV values Cryptol gave us:

~~~~
sawscript> print {{ ZUC 0x1a00000001ec00000095d9000029006b 0x8a008f00f30000000000f008004c0800 }}
[0xbc152974, 0xc8745eae, 0x44db1a3c, 0xbc23ee0a, 0xcc6337aa, ...]
sawscript> print {{ ZUC 0x1a00000001ec00000095d9000029006b 0x0a008f00f30000000000f008004c0800 }}
[0xbc152974, 0xc8745eae, 0x44db1a3c, 0xbc23ee0a, 0xcc6337aa, ...]
~~~~

Voila! We have two different IVs, yet we get precisely the same
key-sequence. Cryptol can attest to what Wu et al. showed, providing a
concrete counterexample to wit.

In response to this vulnerability, the ZUC algorithm was slightly
tweaked to remove the possibility of collision. (Again, you can look at
the attached Cryptol code to see what those changes were, search for the
word `version1_5`.) Is the vulnerability really removed? While
mathematicians will have their own tools to claim as such, we can use
Cryptol to verify that the fix indeed does work (and is correctly
implemented) in our version as well. With version 1.5 of the spec, we
have:

~~~~
sawscript> time (prove z3 {{ ZUC_isResistantToCollisionAttack }})
Time: 0.836055s
Valid
~~~~

It is important to note that the above theorem does **not** prove that
there are no IV collisions in ZUC 1.5. This is because we’ve only proved
the theorem after the first run of the `InitializeZUC` routine. Recall
that the actual implementation actually runs that operation 32 times.
While we can express the full theorem in Cryptol as well, it generates
quite a large verification problem, and the SAT solver running on my
laptop is not quite powerful enough to tackle it. (The proof might
indeed be feasible on a more decent machine with enough RAM. One can
also construct an argument that the initialization step is injective for
all possible LFSR configurations that LoadKey will produce, thus
completing the proof in two steps. We leave that as an exercise for the
interested reader!) In any case, our proof above shows that ZUC version
1.5 is at least free of "easy to find" IV collision attacks.

# Analyzing the C code

So far, although we've presented some C code alongside our Cryptol
implementation of ZUC, all of the analysis we've done has been on the
Cryptol code. However, SAW is capable of proving all of the same facts
about the C implementation, as well as proving that the C and Cryptol
implementations always produce exactly the same results.

The complete proof script showing the equivalence between the Cryptol
and C code, as well as proving the presence of the IV collision in
version 1.4 and its absence in version 1.5, is [here](zuc.saw).

In this document, we step through some, but not all of the proofs in
that document.

To start analyzing the C code, we first tell SAW to load the LLVM
bitcode file generated by compiling the C code with Clang (one for each
of version 1.4 and 1.5), as well as the Cryptol version (in this latter
case, we demonstrate an alternative way of loading Cryptol code into
SAW).

~~~~ {.sawscript}
zucbc <- llvm_load_module "zuc.bc";
zuc14bc <- llvm_load_module "zuc14.bc";
zuccry <- cryptol_load "zuc.cry";
~~~~

Given an LLVM module, there are several ways to analyze its contents
using SAW. The first we'll describe combines the notions of
specification and proof into one process. Consider the C implementation
of the `add` function described earlier (which is called `AddM` in the C
code). To prove that it is equivalent to the Cryptol version, we can
start by writing the following specification:

~~~~ {.sawscript}
let AddM_spec cry_add = do {
    a <- llvm_var "a" (llvm_int 32);
    b <- llvm_var "b" (llvm_int 32);
    llvm_assert {{ a == (a && 0x7FFFFFFF) }};
    llvm_assert {{ b == (b && 0x7FFFFFFF) }};
    let {{ t (x : [32]) = drop`{1} x : [31] }};
    llvm_return {{ (0 # (cry_add [t a, t b])) : [32] }};
    llvm_verify_tactic abc;
};
~~~~

This is a function that takes the Cryptol version of the `add` function
as a parameter. It then declares that the C function has two parameters,
`a` and `b`, which are both 32-bit LLVM integers. It then declares that
this proof is only considering the case where the most significant bit
of each parameter is not set (which we'll later see is true whenever it
is called). It finally declares that the expected return value is the
the same as the result of the Cryptol `add` function, with one caveat.
The Cryptol function operates on 31-bit values, so it's necessary to
drop the most significant bit of the inputs to the C version (using the
`t` function defined inline), and then pad the result of the Cryptol
function with an extra zero. The final line tells SAW to prove that the
C code matches this specification using the ABC theorem prover.

The above code just declares a specification, however. The `llvm_verify`
command will actually run the proof.

~~~~ {.sawscript}
AddM_ov <- llvm_verify zucbc "AddM" [] (AddM_spec {{ zuccry::add }});
~~~~

This command uses the `zucbc` LLVM module loaded above, and looks up the
`add` function in the `zuccry` Cryptol module loaded above.

The SAWScript file [here](zuc.saw) includes proofs of equivalence
between more Cryptol and C functions, though most of those follow the
same basic outline as the `add` function.

In addition to showing equivalence, we can also prove security
properties directly on the C code. This isn't necessarily relevant if
we've already proved equivalence with the Cryptol code, but it can be
very useful in the process of analyzing C code for which a Cryptol
specification does not exist.

To show the IV weakness in ZUC 1.4, we'll use an alternative interface
to LLVM analysis. This interface, instead of immediately attempting to
prove theorems, constructs a logical representation of the semantics of
the underlying code, and then allows you to use that representation in a
variety of ways: you can do almost all of the same things with it that
you could with a Cryptol function.

The translation to a logical representation makes use of "symbolic"
variables to represent arbitrary inputs. Since we know the IV problem
consists of one key and two IVs that lead to the same key stream, let's
create variables for each.

~~~~ {.sawscript}
k   <- fresh_symbolic "k"   {| [16][8] |};
iv1 <- fresh_symbolic "iv1" {| [16][8] |};
iv2 <- fresh_symbolic "iv2" {| [16][8] |};
~~~~

Each of these is 16 bytes, for compatibility with the types in the C
code, rather than the flat 128-bit values used in the Cryptol code.

Now we can tell SAW to execute the initialization code using these
symbolic variables as input, rather than concrete values. Before
executing the code, however, we need one additional step: describing
where the inputs and results of the initialization function are stored.

~~~~ {.sawscript}
let allocs = [ ("k", 16), ("iv", 16) ];
let results =
  [ ("LFSR_S0", 1)
  , ("LFSR_S1", 1)
  , ("LFSR_S2", 1)
  , ("LFSR_S3", 1)
  , ("LFSR_S4", 1)
  , ("LFSR_S5", 1)
  , ("LFSR_S6", 1)
  , ("LFSR_S7", 1)
  , ("LFSR_S8", 1)
  , ("LFSR_S9", 1)
  , ("LFSR_S10", 1)
  , ("LFSR_S11", 1)
  , ("LFSR_S12", 1)
  , ("LFSR_S13", 1)
  , ("LFSR_S14", 1)
  , ("LFSR_S15", 1)
  , ("F_R1", 1)
  , ("F_R2", 1)
  ];
~~~~

These declarations provide a list of allocation and result expressions
to be passed in the symbolic execution function. The first says that the
C variables `k` and `iv` should be allocated to store 16 elements (which
are uninitialized for now). The second says that the result of the
function will be spread across that long list of global variables.

Now, to show that version 1.4 of the C implementation of ZUC has the IV
bug, we can do the following:

~~~~ {.sawscript}
init1_14 <- llvm_symexec zuc14bc "InitializationOne"
  allocs
  [ ("*k", k, 16)
  , ("*iv", iv1, 16)
  , ("F_R1", {{ 0 }}, 1)
  , ("F_R2", {{ 0 }}, 1)
  ]
  results
  false;
init2_14 <- llvm_symexec zuc14bc "InitializationOne"
  allocs
  [ ("*k", k, 16)
  , ("*iv", iv2, 16)
  , ("F_R1", {{ 0 }}, 1)
  , ("F_R2", {{ 0 }}, 1)
  ]
  results
  false;
~~~~

Both of these calls to the symbolic execution function allocate the same
variables and store their results in the same place. However, they run
on different inputs. The first run stores the symbolic variable `k` in
the location pointed to by the C variable `k`, the symbolic variable
`iv1` in the location pointed to by the C variable `iv`, and sets the
globals `F_R1` and `F_R2` to zero. The second does the same thing except
that it initializes `iv` to the symbolic variable `iv2`.

Now, we can try to prove that different IVs will yield different results
from the `InitializationOne` function.

~~~~ {.sawscript}
r14 <- time (prove abc {{ iv1 == iv2 || init1_14 != init2_14 }});
~~~~

The proof fails with the following result:

~~~~
Time: 6.466523s
k =
[0x3d, 0xff, 0xff, 0xff, 0x35, 0x09, 0xff, 0xff, 0xff, 0x89, 0x01,
 0xff, 0xff, 0x50, 0xff, 0x94]
iv1 =
[0x7b, 0x00, 0x70, 0x00, 0xc6, 0x00, 0x00, 0x10, 0x00, 0x00, 0x70,
 0xe9, 0x00, 0xde, 0x2e, 0x86]
iv2 =
[0xd3, 0x00, 0x70, 0x00, 0xc6, 0x00, 0x00, 0x10, 0x00, 0x00, 0x70,
 0xe9, 0x00, 0xde, 0x2e, 0x86]
init1 =
(0x7fa6bc00, 0x7fe26b70, 0x7f935e00,
 0x1ad789c6, 0x04b5e200, 0x7ff13500,
 0x7f89af10, 0x7fcd7800, 0x44af1300,
 0x00ebc470, 0x7f9af1e9, 0x7fde2600,
 0x283c4dde, 0x7ff89a2e, 0x4a47ac86,
 0x7fffffff, 0xd7d285bd, 0xa3b0ee0b)
init2 =
(0x7fa6bc00, 0x7fe26b70, 0x7f935e00,
 0x1ad789c6, 0x04b5e200, 0x7ff13500,
 0x7f89af10, 0x7fcd7800, 0x44af1300,
 0x00ebc470, 0x7f9af1e9, 0x7fde2600,
 0x283c4dde, 0x7ff89a2e, 0x4a47ac86,
 0x7fffffff, 0xd7d285bd, 0xa3b0ee0b)
~~~~

If you look carefully, you'll see that `iv1` and `iv2` are different (in
the first byte) and `init1` is equal to `init2`.

The same process on `zucbc` instead of `zuc14bc` yields:

~~~~
Time: 8.71032s
Q.E.D.
~~~~

# Summary

Designing cryptographic algorithms requires a deep understanding of the
underlying science of cryptography, and a fair amount of the mathematics
thus involved. Implementing such algorithms need not! We believe that
the Cryptol and SAW tools provide the right idioms and features to
simplify cryptographic algorithm implementations and evaluations,
abstracting away from machine specific details and platform specific
concerns. Specifications remain pure, and hence easier to reason about
and communicate. The executable nature of Cryptol also makes it easy to
just play around with your implementations, without worrying about
implementation specific concerns. At the same time, all of the
high-level specification done in Cryptol can be compared to more
efficient implementations used in practice, bridging the theoretical and
applied realms of cryptography.
