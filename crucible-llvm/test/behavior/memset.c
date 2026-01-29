#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    char buf[20];

    memset(buf, 'X', one * 10);
    memset(buf, 'Y', zero);
    buf[one * 1] = '\0';
    printf("memset zero-length: %c\n", buf[zero]);
    /// memset zero-length: X

    memset(buf, 'A', one * 1);
    buf[one * 1] = '\0';
    printf("memset single byte: %s\n", buf);
    /// memset single byte: A

    memset(buf, 'B', one * 5);
    buf[one * 5] = '\0';
    printf("memset five bytes: %s\n", buf);
    /// memset five bytes: BBBBB

    memset(buf, zero, one * 10);
    printf("memset zero all: %d\n", buf[zero] == zero && buf[one * 9] == zero);
    /// memset zero all: 1

    memset(buf, one * 42, one * 3);
    printf("memset value 42: %d %d %d\n", buf[zero], buf[one * 1], buf[one * 2]);
    /// memset value 42: 42 42 42

    return zero;
}
