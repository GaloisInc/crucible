#include <inttypes.h>
#include <stdint.h>
#include <sym-api.h>
#include <stdio.h>

int main()
{
  uint8_t x = lss_fresh_uint8(0);
  uint8_t y = lss_fresh_uint8(0);
  lss_write_cnf(x == x, "tmp/x__x.cnf");
  lss_write_cnf(x == x + 1, "tmp/x__x1.cnf");
  lss_write_cnf(x == y, "tmp/x__y.cnf");
  lss_write_cnf(x != y, "tmp/x_not_y.cnf");
  lss_write_cnf(x + x != x * 2, "tmp/xx_not_2x.cnf");
  return 0;
}
