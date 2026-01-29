#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    char hello1[6] = "Hello";
    char hello2[6] = "Hello";
    char abc[4] = "abc";
    char xyz[4] = "xyz";
    char empty1[1] = "";
    char empty2[1] = "";
    char ab[3] = "ab";

    // strcmp of equal strings
    int r1 = strcmp(&hello1[zero], &hello2[zero]);
    printf("strcmp('Hello', 'Hello') == 0: %d\n", r1 == zero);
    /// strcmp('Hello', 'Hello') == 0: 1

    // strcmp of different strings - first is less
    int r2 = strcmp(&abc[zero], &xyz[zero]);
    printf("strcmp('abc', 'xyz') < 0: %d\n", (r2 < zero) * one);
    /// strcmp('abc', 'xyz') < 0: 1

    // strcmp of different strings - first is greater
    int r3 = strcmp(&xyz[zero], &abc[zero]);
    printf("strcmp('xyz', 'abc') > 0: %d\n", (r3 > zero) * one);
    /// strcmp('xyz', 'abc') > 0: 1

    // strcmp with aliased strings (same pointer)
    int r5 = strcmp(&hello1[zero], &hello1[zero]);
    printf("strcmp(s, s) == 0: %d\n", r5 == zero);
    /// strcmp(s, s) == 0: 1

    // strcmp with empty strings
    int r6 = strcmp(&empty1[zero], &empty2[zero]);
    printf("strcmp('', '') == 0: %d\n", r6 == zero);
    /// strcmp('', '') == 0: 1

    // strcmp where first string is a prefix
    int r7 = strcmp(&ab[zero], &abc[zero]);
    printf("strcmp('ab', 'abc') < 0: %d\n", (r7 < zero) * one);
    /// strcmp('ab', 'abc') < 0: 1

    // strcmp where second string is a prefix
    int r8 = strcmp(&abc[zero], &ab[zero]);
    printf("strcmp('abc', 'ab') > 0: %d\n", (r8 > zero) * one);
    /// strcmp('abc', 'ab') > 0: 1

    return zero;
}
