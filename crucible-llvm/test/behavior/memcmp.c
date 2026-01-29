#include <string.h>
#include <stdio.h>

int main() {
    // memcmp of equal strings
    char hello1[6] = "Hello";
    char hello2[6] = "Hello";
    int r1 = memcmp(hello1, hello2, 5);
    printf("memcmp('Hello', 'Hello', 5) == 0: %d\n", r1 == 0);
    /// memcmp('Hello', 'Hello', 5) == 0: 1

    // memcmp with length 0 should always return 0
    char abc[4] = "abc";
    char xyz[4] = "xyz";
    int r2 = memcmp(abc, xyz, 0);
    printf("memcmp with length 0 returns 0: %d\n", r2 == 0);
    /// memcmp with length 0 returns 0: 1

    // memcmp with partial comparison - equal prefix
    char hello[7] = "Hello!";
    char help[7] = "Help!!";
    int r3 = memcmp(hello, help, 3);
    printf("memcmp('Hello!', 'Help!!', 3) == 0: %d\n", r3 == 0);
    /// memcmp('Hello!', 'Help!!', 3) == 0: 1

    // memcmp with single byte - equal
    char a1[1] = "a";
    char a2[1] = "a";
    int r4 = memcmp(a1, a2, 1);
    printf("memcmp('a', 'a', 1) == 0: %d\n", r4 == 0);
    /// memcmp('a', 'a', 1) == 0: 1

    // memcmp with aliased strings (same pointer)
    char aliased[6] = "Hello";
    int r6 = memcmp(aliased, aliased, 5);
    printf("memcmp(ptr, ptr, n) == 0: %d\n", r6 == 0);
    /// memcmp(ptr, ptr, n) == 0: 1

    // memcmp('a', 'b') returns negative value
    char a4[1] = "a";
    char b2[1] = "b";
    int r7 = memcmp(a4, b2, 1);
    printf("memcmp('a', 'b', 1) < 0: %d\n", r7 < 0);
    /// memcmp('a', 'b', 1) < 0: 1

    // memcmp('b', 'a') returns positive value
    char b3[1] = "b";
    char a5[1] = "a";
    int r8 = memcmp(b3, a5, 1);
    printf("memcmp('b', 'a', 1) > 0: %d\n", r8 > 0);
    /// memcmp('b', 'a', 1) > 0: 1

    // memcmp with null bytes in the middle - equal
    char buf1[3] = {'a', '\0', 'b'};
    char buf2[3] = {'a', '\0', 'b'};
    int r9 = memcmp(buf1, buf2, 3);
    printf("memcmp('a\\0b', 'a\\0b', 3) == 0: %d\n", r9 == 0);
    /// memcmp('a\0b', 'a\0b', 3) == 0: 1

    // memcmp with null bytes in the middle - different
    char buf3[3] = {'a', '\0', 'c'};
    int r10 = memcmp(buf1, buf3, 3);
    printf("memcmp('a\\0b', 'a\\0c', 3) < 0: %d\n", r10 < 0);
    /// memcmp('a\0b', 'a\0c', 3) < 0: 1

    return 0;
}
