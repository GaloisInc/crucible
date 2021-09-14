#include <crucible.h>
#include <float.h>
#include <math.h>
#include <stdbool.h>

// A reasonable specification for copysign, assuming that x isn't NAN or
// INFINITY.
float copysign_spec(float x, float y) {
  float magnitude = fabs(x);
  if (signbit(y)) {
    return -magnitude;
  } else {
    return magnitude;
  }
}

int main() {
  // The general cases
  float x = crucible_float("x");
  float y = crucible_float("y");
  assuming(!isnan(x));
  check(copysign(x, y) == copysign_spec(x, y));

  // NAN edge cases
  //
  // We don't have a way to distinguish the sign bits of NAN values in
  // Crucible, so the best we can do is check using isnan().
  float z = crucible_float("z");
  assuming(isnan(z));
  check(isnan(copysign(z, y)));

  return 0;
}
