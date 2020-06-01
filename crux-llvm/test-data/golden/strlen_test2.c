#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <crucible.h>

// This test exists to ensure that the for loop in `test`
// terminates well before hitting the static upper bound of 200.
//
// Right now, it terminates because `strlen` is able to know that
// the length of the string is at most 14.  This follows because
// only the first 15 bytes are written by the `havoc`.
// As a result `length - i - 1` is only a legal memory access
// until `i = 13`.  At `i = 14`, the loop aborts on a failed memory access.
// We are later able to prove the iterations leading up to that failed access
// are infeasible.
//
// If path sat checking is on, this loop will terminate even
// earlier because of the `assuming( str[i] == 0 )` line.  This
// makes the loop test infeasible when `i = 9`.

void crucible_havoc_memory (void*, size_t);

void test(const char *string, uint32_t length) {
  uint32_t i;
  for(i = 0; i < length && i < 200; i++) {
    printf("i = %u\n", i);
    printf("string[(length - i) - 1] = %u\n", string[(length - i) - 1]);
  }

  return;
}

int main () {
  char str[100];
  crucible_havoc_memory( str, 15 );
  uint32_t i = crucible_int32_t( "i" );

  assuming( i < 10 );
  assuming( str[i] == 0 );

  uint32_t length = strlen( str );
  test( str, length );

  check( length < 10 );

  return 0;
}
