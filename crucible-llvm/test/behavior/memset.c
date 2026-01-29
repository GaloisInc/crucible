#include <string.h>
#include <stdio.h>

int main(int argc, char** argv) {
    char buf[20];

    memset(buf, 'X', 10);
    memset(buf, 'Y', 0);
    buf[1] = '\0';
    printf("memset zero-length: %c\n", buf[0]);
    /// memset zero-length: X

    memset(buf, 'A', 1);
    buf[1] = '\0';
    printf("memset single byte: %s\n", buf);
    /// memset single byte: A

    memset(buf, 'B', 5);
    buf[5] = '\0';
    printf("memset five bytes: %s\n", buf);
    /// memset five bytes: BBBBB

    memset(buf, 0, 10);
    printf("memset zero all: %d\n", buf[0] == 0 && buf[9] == 0);
    /// memset zero all: 1

    memset(buf, 42, 3);
    printf("memset value 42: %d %d %d\n", buf[0], buf[1], buf[2]);
    /// memset value 42: 42 42 42

    return 0;
}
