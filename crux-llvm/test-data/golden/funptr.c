#include <crucible.h>

int f(void) {
    return 42;
}

int g(void) {
    return 99;
}

unsigned long int sel(int a) {
    if (a < 10)
        return (unsigned long int)(&f);
    return (unsigned long int)(&g);
}

int main() {
    int arg = 3;
    int (*fptr)(void) = sel(arg);
    check (fptr() == 42);
    return 0;
}
