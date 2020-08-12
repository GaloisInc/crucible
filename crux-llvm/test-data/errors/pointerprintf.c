#include <stdio.h>
#include <crucible.h>

int main () {
  int x = 42;
  printf( "%d\n", (long) &x );
}
