#include <stdio.h>

char buf1[] = "adsf";
char buf2[] = {0, 1, 2, 3, 4};
int arr[] = {13, 37, 1234};
struct Point {
    int x;
    int y;
};

struct Point p = {41, 42};

#define SKIP_FAIL_O0
// #define SKIP_FAIL_O1
// #define SKIP_FAIL_O2
// #define SKIP_FAIL_O3
// #define SKIP_FAIL_Os

int main () {
    struct Point p1;
    struct Point p2 = {0, 0};
    struct Point p3 = {1,2};
    int int1;
    int int2 = 69;
    int int3 = 0;
    char* str1;
    char* str2 = "adsf";
    char* str3 = 0;

    char buf1[10];
    char buf2[10] = "xxxx";
    char buf3[10] = "\0\0\0\0\0\0\0\0\0";

    int arr1[3];
    int arr2[3] = {1,2,3};
    int arr3[3] = {0,0,0};

    #if !defined(SKIP_FAIL_O0)
    printf("p1: %d %d\n", p1.x, p1.y);
    #endif
    printf("p2: %d %d\n", p2.x, p2.y);
    printf("p3: %d %d\n", p3.x, p3.y);

    #if !defined(SKIP_FAIL_O0)
    printf("int1: %d\n", int1);
    #endif
    printf("int2: %d\n", int2);
    printf("int3: %d\n", int3);

    #if !defined(SKIP_FAIL_O0) && !defined(SKIP_FAIL_O1) && !defined(SKIP_FAIL_O2) && !defined(SKIP_FAIL_O3)
    printf("str1: %s\n", str1);
    #endif
    printf("str2: %s\n", str2);
    #if !defined(SKIP_FAIL_O0) && !defined(SKIP_FAIL_O1) && !defined(SKIP_FAIL_O2) && !defined(SKIP_FAIL_O3)
    printf("str3: %s\n", str3);
    #endif

    #if !defined(SKIP_FAIL_O0) && !defined(SKIP_FAIL_O1) && !defined(SKIP_FAIL_O2) && !defined(SKIP_FAIL_O3)
    printf("buf1: %s\n", buf1);
    #endif
    printf("buf2: %s\n", buf2);
    printf("buf3: %s\n", buf3);

    #if !defined(SKIP_FAIL_O0)
    printf("arr1: [%d, %d, %d]\n", arr1[0], arr1[1], arr1[2]);
    #endif
    printf("arr2: [%d, %d, %d]\n", arr2[0], arr2[1], arr2[2]);
    printf("arr3: [%d, %d, %d]\n", arr3[0], arr3[1], arr3[2]);
    return 0;
}
