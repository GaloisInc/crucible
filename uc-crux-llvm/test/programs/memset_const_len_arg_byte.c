#include <string.h>
void memset_const_len_arg_byte(void *dest, char byte) {
  memset(dest, byte, 8);
}
