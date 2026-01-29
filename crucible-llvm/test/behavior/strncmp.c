#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    char hello1[6] = "Hello";
    char hello2[6] = "Hello";
    char abc[4] = "abc";
    char xyz[4] = "xyz";
    char abcdef[7] = "abcdef";
    char abcxyz[7] = "abcxyz";
    char empty[1] = "";

    // strncmp of equal strings
    int r1 = strncmp(&hello1[zero], &hello2[zero], one * 5);
    printf("strncmp('Hello', 'Hello', 5) == 0: %d\n", r1 == zero);
    /// strncmp('Hello', 'Hello', 5) == 0: 1

    // strncmp with length 0 should always return 0
    int r2 = strncmp(&abc[zero], &xyz[zero], zero);
    printf("strncmp with length 0 returns 0: %d\n", r2 == zero);
    /// strncmp with length 0 returns 0: 1

    // strncmp with partial comparison - equal prefix
    int r3 = strncmp(&abcdef[zero], &abcxyz[zero], one * 3);
    printf("strncmp('abcdef', 'abcxyz', 3) == 0: %d\n", r3 == zero);
    /// strncmp('abcdef', 'abcxyz', 3) == 0: 1

    // strncmp with partial comparison - different within range
    int r4 = strncmp(&abcdef[zero], &abcxyz[zero], one * 5);
    printf("strncmp('abcdef', 'abcxyz', 5) < 0: %d\n", (r4 < zero) * one);
    /// strncmp('abcdef', 'abcxyz', 5) < 0: 1

    // strncmp stops at null terminator even if length is larger
    int r5 = strncmp(&abc[zero], &abc[zero], one * 100);
    printf("strncmp('abc', 'abc', 100) == 0: %d\n", r5 == zero);
    /// strncmp('abc', 'abc', 100) == 0: 1

    // strncmp with aliased strings
    int r6 = strncmp(&hello1[zero], &hello1[zero], one * 5);
    printf("strncmp(ptr, ptr, n) == 0: %d\n", r6 == zero);
    /// strncmp(ptr, ptr, n) == 0: 1

    // strncmp with empty strings
    char empty2[1] = "";
    int r7 = strncmp(&empty[zero], &empty2[zero], one * 10);
    printf("strncmp('', '', 10) == 0: %d\n", r7 == zero);
    /// strncmp('', '', 10) == 0: 1

    // strncmp stops at null in first string
    int r8 = strncmp(&abc[zero], &abcdef[zero], one * 10);
    printf("strncmp('abc', 'abcdef', 10) < 0: %d\n", (r8 < zero) * one);
    /// strncmp('abc', 'abcdef', 10) < 0: 1

    // strncmp stops at null in second string
    int r9 = strncmp(&abcdef[zero], &abc[zero], one * 10);
    printf("strncmp('abcdef', 'abc', 10) > 0: %d\n", (r9 > zero) * one);
    /// strncmp('abcdef', 'abc', 10) > 0: 1

    // strncmp compares exactly n characters when no null
    char hel[4] = "Hel";
    int r10 = strncmp(&hello1[zero], &hel[zero], one * 3);
    printf("strncmp('Hello', 'Hel', 3) == 0: %d\n", r10 == zero);
    /// strncmp('Hello', 'Hel', 3) == 0: 1

    return zero;
}
