// Adapted from the Clang test suite:
// (https://github.com/llvm/llvm-project/blob/32103608fc073700f04238872d8b22655ddec3fb/clang/test/CodeGen/asm-goto.c#L5-L20),
// which is licensed under the Apache License v2.0


int main(void) {
  int cond = 0;
  asm volatile goto("testl %0, %0; jne %l1;"
                    : /* No outputs */
                    : "r"(cond)
                    : /* No clobbers */
                    : label_true, loop);
  return 0;
loop:
  return 0;
label_true:
  return 1;
}
