#include <crucible.h>
#include <math.h>

int main(void) {
  double x = 5.0;
  double y = 3.0;
  check(fmod(x, y) == 2.0);
  return 0;
}
