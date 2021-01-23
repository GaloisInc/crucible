#include <stdlib.h>
#include <string.h>

#include "crucible.h"

#define MAX 10

char* mkstr() {
  char* x = malloc(MAX);
  for( int i=0; i<MAX; i++ ) {
    x[i] = crucible_int8_t( "x" );
  }

  assuming( x[MAX-1] == 0 );

  return x;
}

int main() {
  char *str = mkstr();
  size_t sz = strlen(str);
  check( sz < MAX );
}
