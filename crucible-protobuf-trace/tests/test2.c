#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>

#include <crucible.h>

int main() {
    if (crucible_uint8_t("var") == 0) {
        puts("a");
    }
    else {
	puts("~a");
    }
}
