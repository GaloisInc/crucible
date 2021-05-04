int mul_by_max_int(int x) __attribute__((noinline)) {
  return x * 2147483647; // 2^32 - 1
}
int signed_mul_wrap_concrete(int x) {
  if (x) {
    return mul_by_max_int(4);
  }
  return 0;
}
