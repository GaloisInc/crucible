#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

#include <crucible.h>

int main() {
    char buf[100];
    for (int i = 0; i < 100; i++) {
        buf[i] = crucible_uint8_t("x");
    }
    char buf2[100];
    memcpy(buf2, buf, sizeof(buf2));
    volatile int* p = malloc(0x100);
    if (crucible_uint8_t("var") == 0)
    {
        puts("a");
        if (crucible_uint8_t("b") == 0)
        {
            if (crucible_uint8_t("c") == 0)
            {
                puts("hi there, c!\n");
            }
            puts("b");
        }
        else
        {
            puts("~b");
        }
    }
    else {
	    puts("~a");
    }
    free(p);
}
