#include <crucible-model.h>
#include <stdio.h>
#include <inttypes.h>

int main () {
  size_t i;
  for (i = 0; i < crux_value_num(int8_t); ++i)
    printf("%s = %"PRId8", %"PRIu8", 0x%"PRIx8"\n", crux_names(int8_t)[i], crux_values(int8_t)[i], crux_values(int8_t)[i], crux_values(int8_t)[i]);

  for (i = 0; i < crux_value_num(int16_t); ++i)
    printf("%s = %"PRId16", %"PRIu16", 0x%"PRIx16"\n", crux_names(int16_t)[i], crux_values(int16_t)[i], crux_values(int16_t)[i], crux_values(int16_t)[i]);

  for (i = 0; i < crux_value_num(int32_t); ++i)
    printf("%s = %"PRId32", %"PRIu32", 0x%"PRIx32"\n", crux_names(int32_t)[i], crux_values(int32_t)[i], crux_values(int32_t)[i], crux_values(int32_t)[i]);

  for (i = 0; i < crux_value_num(int64_t); ++i)
    printf("%s = %"PRId64", %"PRIu64", 0x%"PRIx64"\n", crux_names(int64_t)[i], crux_values(int64_t)[i], crux_values(int64_t)[i], crux_values(int64_t)[i]);

  for (i = 0; i < crux_value_num(float); ++i)
    printf("%s = %f, %a\n", crux_names(float)[i], crux_values(float)[i], crux_values(float)[i]);

  for (i = 0; i < crux_value_num(double); ++i)
    printf("%s = %f, %a\n", crux_names(double)[i], crux_values(double)[i], crux_values(double)[i]);

  return 0;
}
