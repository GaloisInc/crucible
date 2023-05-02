#include <string.h>
char str[] = "str";
// We mark this function as noinline to ensure that LLVM 14+ does not
// over-optimize the call site in read_global_neg_offset_strlen and produce a
// getelementptr expression with an out-of-bounds index. This would cause
// crucible-llvm to abort before it has a chance to report the undefined
// behavior in subtracting 1 from a global pointer, which is the ultimate goal
// of this test case.
char *minus_1(char *ptr) __attribute__((noinline)) { return ptr - 1; }
int read_global_neg_offset_strlen() {
  return strlen(minus_1(str));
}
