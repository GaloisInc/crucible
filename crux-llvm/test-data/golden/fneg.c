#include <crucible.h>

double negate(double x) {
  return -x;
}

int main() {
  double x = crucible_double("x");
  return (negate(x) > 0);
}
