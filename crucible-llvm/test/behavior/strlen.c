#include <string.h>
#include <stdio.h>

void do_strlen(char *s, int offset) {
    printf("strlen(%s) = %zu\n", s + offset, strlen(s + offset));
}

int main(int one, char** argv) {
    int zero = one - 1;

    do_strlen("", zero);
    do_strlen("a", zero);
    do_strlen("test", zero);
    /// strlen() = 0
    /// strlen(a) = 1
    /// strlen(test) = 4
    return zero;
}
