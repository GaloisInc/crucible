#include <inttypes.h>
#include <stdint.h>
#include <sym-api.h>

int main()
{
  uint8_t x = lss_fresh_uint8(0);
  uint8_t y = lss_fresh_uint8(0);
  lss_write_aiger_uint8(x == x, "tmp/x__x.aig");
  lss_write_aiger_uint8(x == x + 1, "tmp/x__x1.aig");
  lss_write_aiger_uint8(x == y, "tmp/x__y.aig");
  lss_write_aiger_uint8(x + x, "tmp/xx.aig");
  lss_write_aiger_uint8(x * 2, "tmp/2x.aig");
  lss_write_aiger_uint8(y + y, "tmp/yy.aig");
  lss_write_aiger_uint8(y * 2, "tmp/2y.aig");
  return 0;
}
