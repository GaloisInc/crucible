#include <string.h>
#include <stdio.h>

void do_strlen(char *s) {
    printf("strlen(%s) = %zu\n", s, strlen(s));
}

int main(int argc, char** argv) {
    do_strlen("");
    do_strlen("a");
    do_strlen("test");
    /// strlen() = 0
    /// strlen(a) = 1
    /// strlen(test) = 4
    return 0;
}
