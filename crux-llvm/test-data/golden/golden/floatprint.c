#include <stdio.h>

int main() {
  float  x = 1.123;
  double y = 100e5;

  printf("%f %g %.10e\n", (double)x, y, x+y );
}
