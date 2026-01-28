#include <string.h>
#include <stdio.h>

int main(int argc, char** argv) {
    char src[20] = "hello";
    char dst[20];

    memset(dst, 'X', 20);
    memcpy(dst, src, 0);
    printf("memcpy zero-length: %c\n", dst[0]);
    /// memcpy zero-length: X

    memset(dst, 0, 20);
    memcpy(dst, src, 1);
    printf("memcpy single byte: %c\n", dst[0]);
    /// memcpy single byte: h

    memset(dst, 0, 20);
    memcpy(dst, src, 6);
    printf("memcpy full string: %s\n", dst);
    /// memcpy full string: hello

    memcpy(dst + 6, src, 6);
    printf("memcpy append: %s\n", dst);
    /// memcpy append: hello

    return 0;
}
