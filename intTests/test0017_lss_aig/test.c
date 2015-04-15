#include <inttypes.h>
#include <stdint.h>
#include <sym-api.h>

// Very secure!
void encrypt(uint32_t *pt, uint32_t *key, uint32_t *ct) {
  for (int i = 0; i < 4; ++i) {
    ct[i]     = (((1 + i) * 17) << 24) ^ pt[i];
    ct[4 + i] = (((5 + i) * 17) << 24) ^ key[i];
  }
}

int main_helper(char *out_file)
{
  uint32_t *pt  = lss_fresh_array_uint32(4, 0x8899aabbUL, NULL);
  uint32_t *key = lss_fresh_array_uint32(4, 0x08090a0bUL, NULL);
  uint32_t ct[8];
  encrypt(pt, key, ct);
  lss_write_aiger_array_uint32(ct, 8, out_file);
  return 0;
}
