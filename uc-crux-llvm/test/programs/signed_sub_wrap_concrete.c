int sub_from_min_int_plus_one(int x) __attribute__((noinline)) {
  return (-2147483647) - x;
}
int signed_sub_wrap_concrete(int x) {
  if (x) {
    return sub_from_min_int_plus_one(4);
  }
  return 0;
}
