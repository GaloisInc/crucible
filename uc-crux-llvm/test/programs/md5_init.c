#include <stdint.h>

struct md5_ctx {
  uint32_t buf[4];
  uint32_t bits[2];
  unsigned char in[64];
};

void md5_init(struct md5_ctx *ctx)
{
  ctx->buf[0] = 0x67452301;
  ctx->buf[1] = 0xefcdab89;
  ctx->buf[2] = 0x98badcfe;
  ctx->buf[3] = 0x10325476;
  ctx->bits[0] = 0;
  ctx->bits[1] = 0;
}
