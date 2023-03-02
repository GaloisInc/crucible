#include <stdio.h>
int loop(int n) {
    int value = n * n;
    printf("%d ^2 = %d\n", n, value);
    return loop(n + 1);
}

int main() {
    loop(0);
    return 0;
}
