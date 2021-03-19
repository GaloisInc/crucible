int add_max_int_minus_one(int x) __attribute__((noinline)) {
  return x + 2147483646; // 2^32 - 2
}
int signed_add_wrap_concrete(int x) {
  if (x) {
    return add_max_int_minus_one(4);
  }
  return 0;
}
