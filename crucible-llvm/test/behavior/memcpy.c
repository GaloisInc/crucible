#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    char src[20] = "hello";
    char dst[20];

    memset(dst, 'X', one * 20);
    memcpy(dst, src, zero);
    printf("memcpy zero-length: %c\n", dst[zero]);
    /// memcpy zero-length: X

    memset(dst, zero, one * 20);
    memcpy(dst, src, one * 1);
    printf("memcpy single byte: %c\n", dst[zero]);
    /// memcpy single byte: h

    memset(dst, zero, one * 20);
    memcpy(dst, src, one * 6);
    printf("memcpy full string: %s\n", dst);
    /// memcpy full string: hello

    memcpy(dst + one * 6, src, one * 6);
    printf("memcpy append: %s\n", dst);
    /// memcpy append: hello

    return zero;
}
