This directory includes a proof of equivalence between a Cryptol
specification of AES and the implementation included in OpenSSL. Unlike
many of the other examples in the repository, this script uses the
standalone `lss` executable to generate a model of the OpenSSL AES
function, since this is currently the most efficient route. Since
proving the equivalence of AES implemented in different styles is very
computationally expensive, using the most efficient approach is crucial.

The `Makefile` in this directory automatically downloads and compiles
OpenSSL, and then extracts the relevant LLVM bitcode file.

Because the OpenSSL implementation uses a separate function to expand
the key and then perform encryption, while the Cryptol specification
uses a single function from the plaintext and key to a ciphertext, we
include a wrapper to do key expansion followed by encryption:

~~~~{.c}
int aes_encrypt(const unsigned char *in,
                unsigned char *out,
                const unsigned char *key) {
  AES_KEY rkey;
  int r = private_AES_set_encrypt_key(key, 128, &rkey);
  AES_encrypt(in, out, &rkey);
  return r;
}
~~~~

We also include a wrapper that creates fresh symbolic variables, calls
the above function, and writes the result to an And-Inverter Graph:

~~~~{.c}
int main() {
    unsigned char *in = lss_fresh_array_uint8(16, 0, NULL);
    unsigned char *key = lss_fresh_array_uint8(16, 0, NULL);
    unsigned char *out = malloc(16 * sizeof(unsigned char));
    aes_encrypt(in, out, key);
    lss_write_aiger_array_uint8(out, 16, "aes_imp.aig");
}
~~~~

The `Makefile` runs `lss` on the bitcode file consisting of this wrapper
plus the OpenSSL AES implementation, resulting in the `aes_imp.aig` file
representing the implementation's semantics. SAW can then load this model:

~~~~
aes_imp <- time (load_aig "aes_imp.aig");
~~~~

Loading the Cryptol model is similarly straightforward:

~~~~
import "../../deps/cryptol/docs/ProgrammingCryptol/aes/AES.cry";

let {{
  aesExtract x = aesEncrypt (pt,key)
    where [pt,key] = split x
}};

aes_ref <- time (bitblast {{ aesExtract }});
~~~~

Other than loading the appropriate Cryptol file, the rest of the code
exists simply to lower the more structured type of the Cryptol
implementation so that it is simply a function from 256 bits to 128
bits, compatible with the low-level structure of the AIG file.

Comparing the two implementations uses ABC's combinational equivalence checker:

~~~~
res <- time (cec aes_imp aes_ref);
~~~~

Finally, the script writes out an AIG representation of the Cryptol
specification, which may be compared with the implementation AIG using
any AIG-based equivalence checker.

~~~~
time (write_aig "aes_ref.aig" {{ aesExtract }});
~~~~
