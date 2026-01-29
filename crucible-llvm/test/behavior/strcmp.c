#include <string.h>
#include <stdio.h>

int main() {
    char hello1[6] = "Hello";
    char hello2[6] = "Hello";
    char abc[4] = "abc";
    char xyz[4] = "xyz";
    char empty1[1] = "";
    char empty2[1] = "";
    char ab[3] = "ab";

    // strcmp of equal strings
    int r1 = strcmp(hello1, hello2);
    printf("strcmp('Hello', 'Hello') == 0: %d\n", r1 == 0);
    /// strcmp('Hello', 'Hello') == 0: 1

    // strcmp of different strings - first is less
    int r2 = strcmp(abc, xyz);
    printf("strcmp('abc', 'xyz') < 0: %d\n", r2 < 0);
    /// strcmp('abc', 'xyz') < 0: 1

    // strcmp of different strings - first is greater
    int r3 = strcmp(xyz, abc);
    printf("strcmp('xyz', 'abc') > 0: %d\n", r3 > 0);
    /// strcmp('xyz', 'abc') > 0: 1

    // strcmp with aliased strings (same pointer)
    int r5 = strcmp(hello1, hello1);
    printf("strcmp(s, s) == 0: %d\n", r5 == 0);
    /// strcmp(s, s) == 0: 1

    // strcmp with empty strings
    int r6 = strcmp(empty1, empty2);
    printf("strcmp('', '') == 0: %d\n", r6 == 0);
    /// strcmp('', '') == 0: 1

    // strcmp where first string is a prefix
    int r7 = strcmp(ab, abc);
    printf("strcmp('ab', 'abc') < 0: %d\n", r7 < 0);
    /// strcmp('ab', 'abc') < 0: 1

    // strcmp where second string is a prefix
    int r8 = strcmp(abc, ab);
    printf("strcmp('abc', 'ab') > 0: %d\n", r8 > 0);
    /// strcmp('abc', 'ab') > 0: 1

    return 0;
}
