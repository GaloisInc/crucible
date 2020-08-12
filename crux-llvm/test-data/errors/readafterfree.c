#include <stdlib.h>
#include <stdio.h>
#include <crucible.h>

int* f () {
  int* x = malloc( sizeof(int) );
  *x = 42;
  return x;
}

int main () {
  int* x = f();
  free(x);

  printf( "%d\n", *x );
}
