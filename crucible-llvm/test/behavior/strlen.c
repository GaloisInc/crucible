#include <string.h>
#include <stdio.h>

void do_strlen(char *s, int offset) {
    printf("strlen(%s) = %zu\n", s + offset, strlen(s + offset));
}

int main(int one, char** argv) {
    int zero = one - 1;

    do_strlen("", zero);
    //- check "call i64 @strlen"
    do_strlen("a", zero);
    //- check "call i64 @strlen"
    do_strlen("test", zero);
    //- check "call i64 @strlen"
    /// checkln "strlen() = 0"
    /// checkln "strlen(a) = 1"
    /// checkln "strlen(test) = 4"
    return zero;
}
