#include <aes.h>
#include <sym-api.h>

int aes_encrypt(const unsigned char *in, unsigned char *out, const unsigned char *key) {
  AES_KEY rkey;
  int r = private_AES_set_encrypt_key(key, 128, &rkey);
  AES_encrypt(in, out, &rkey);
  return r;
}

int main() {
    unsigned char *in = lss_fresh_array_uint8(16, 0, NULL);
    unsigned char *key = lss_fresh_array_uint8(16, 0, NULL);
    unsigned char *out = malloc(16 * sizeof(unsigned char));
    aes_encrypt(in, out, key);
    lss_write_aiger_array_uint8(out, 16, "aes_imp.aig");
}
