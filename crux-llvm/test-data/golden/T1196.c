void foo(int* restrict p0, int* restrict p1) {
	*p0 = *p1;
}

__attribute__((noinline)) void test_inline_foo(int* p0, int* p1) {
	foo(p0, p1);
}

int main(void) {
    int p0 = 0;
    int p1 = 1;
    test_inline_foo(&p0, &p1);
    return 0;
}
