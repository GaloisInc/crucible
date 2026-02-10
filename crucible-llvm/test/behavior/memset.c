#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    char buf[20];

    memset(buf, 'X', one * 10);
    //- check "call ptr @__memset"
    memset(buf, 'Y', zero);
    //- check "call ptr @__memset"
    buf[one * 1] = '\0';
    printf("memset zero-length: %c\n", buf[zero]);
    /// checkln "memset zero-length: X"

    memset(buf, 'A', one * 1);
    //- check "call ptr @__memset"
    buf[one * 1] = '\0';
    printf("memset single byte: %s\n", buf);
    /// checkln "memset single byte: A"

    memset(buf, 'B', one * 5);
    //- check "call ptr @__memset"
    buf[one * 5] = '\0';
    printf("memset five bytes: %s\n", buf);
    /// checkln "memset five bytes: BBBBB"

    memset(buf, zero, one * 10);
    //- check "call ptr @__memset"
    printf("memset zero all: %d\n", buf[zero] == zero && buf[one * 9] == zero);
    /// checkln "memset zero all: 1"

    memset(buf, one * 42, one * 3);
    //- check "call ptr @__memset"
    printf("memset value 42: %d %d %d\n", buf[zero], buf[one * 1], buf[one * 2]);
    /// checkln "memset value 42: 42 42 42"

    return zero;
}
