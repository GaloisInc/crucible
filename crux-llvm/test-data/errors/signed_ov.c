#include <stdio.h>
#include "crucible.h"

int main () {
  int i = crucible_uint32_t( "i" );
  int j = crucible_uint32_t( "j" );
  int x = i + j;
  printf( "%d\n", x );
}
