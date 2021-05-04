#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

// #define PRINTF(...) printf(__VA_ARGS__)
#define PRINTF(...) do {} while(0)

int __attribute__((noinline)) value(void) {
  return 5;
}

int do_fork() {
  pid_t pid = fork();
  if (pid == -1) {
    return -1; // could not fork
  }
  if (pid == 0) {
    PRINTF("In child process\n");
    return value();
  }
  PRINTF("In parent process\n");
  return value();
}
