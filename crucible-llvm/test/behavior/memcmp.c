#include <string.h>
#include <stdio.h>

int main(int one, char** argv) {
    int zero = one - 1;

    // memcmp of equal strings
    char hello1[6] = "Hello";
    char hello2[6] = "Hello";
    int r1 = memcmp(hello1, hello2, one * 5);
    //- check "call i32 @memcmp"
    printf("memcmp('Hello', 'Hello', 5) == 0: %d\n", r1 == zero);
    /// checkln "memcmp('Hello', 'Hello', 5) == 0: 1"

    // memcmp with length 0 should always return 0
    char abc[4] = "abc";
    char xyz[4] = "xyz";
    int r2 = memcmp(abc, xyz, zero);
    //- check "call i32 @memcmp"
    printf("memcmp with length 0 returns 0: %d\n", r2 == zero);
    /// checkln "memcmp with length 0 returns 0: 1"

    // memcmp with partial comparison - equal prefix
    char hello[7] = "Hello!";
    char help[7] = "Help!!";
    int r3 = memcmp(hello, help, one * 3);
    //- check "call i32 @memcmp"
    printf("memcmp('Hello!', 'Help!!', 3) == 0: %d\n", r3 == zero);
    /// checkln "memcmp('Hello!', 'Help!!', 3) == 0: 1"

    // memcmp with single byte - equal
    char a1[1] = "a";
    char a2[1] = "a";
    int r4 = memcmp(a1, a2, one * 1);
    //- check "call i32 @memcmp"
    printf("memcmp('a', 'a', 1) == 0: %d\n", r4 == zero);
    /// checkln "memcmp('a', 'a', 1) == 0: 1"

    // memcmp with aliased strings (same pointer)
    char aliased[6] = "Hello";
    int r6 = memcmp(aliased, aliased, one * 5);
    //- check "call i32 @memcmp"
    printf("memcmp(ptr, ptr, n) == 0: %d\n", r6 == zero);
    /// checkln "memcmp(ptr, ptr, n) == 0: 1"

    // memcmp('a', 'b') returns negative value
    char a4[1] = "a";
    char b2[1] = "b";
    int r7 = memcmp(a4, b2, one * 1);
    //- check "call i32 @memcmp"
    printf("memcmp('a', 'b', 1) < 0: %d\n", (r7 < zero) * one);
    /// checkln "memcmp('a', 'b', 1) < 0: 1"

    // memcmp('b', 'a') returns positive value
    char b3[1] = "b";
    char a5[1] = "a";
    int r8 = memcmp(b3, a5, one * 1);
    //- check "call i32 @memcmp"
    printf("memcmp('b', 'a', 1) > 0: %d\n", (r8 > zero) * one);
    /// checkln "memcmp('b', 'a', 1) > 0: 1"

    // memcmp with null bytes in the middle - equal
    char buf1[3] = {'a', '\0', 'b'};
    char buf2[3] = {'a', '\0', 'b'};
    int r9 = memcmp(buf1, buf2, one * 3);
    //- check "call i32 @memcmp"
    printf("memcmp('a\\0b', 'a\\0b', 3) == 0: %d\n", r9 == zero);
    /// checkln "memcmp('a\\0b', 'a\\0b', 3) == 0: 1"

    // memcmp with null bytes in the middle - different
    char buf3[3] = {'a', '\0', 'c'};
    int r10 = memcmp(buf1, buf3, one * 3);
    //- check "call i32 @memcmp"
    printf("memcmp('a\\0b', 'a\\0c', 3) < 0: %d\n", (r10 < zero) * one);
    /// checkln "memcmp('a\\0b', 'a\\0c', 3) < 0: 1"

    return zero;
}
