#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

// The values here aren't important.
#define PORT 1100

int do_recv() {
  struct sockaddr_in sa;
  int socket_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (socket_fd == -1) {
    return EXIT_FAILURE;
  }

  memset(&sa, 0, sizeof sa);

  sa.sin_family = AF_INET;
  sa.sin_port = htons(PORT);
  sa.sin_addr.s_addr = htonl(INADDR_ANY);

  if (bind(socket_fd, (struct sockaddr *)&sa, sizeof sa) == -1) {
    close(socket_fd);
    return EXIT_FAILURE;
  }

  if (listen(socket_fd, 10) == -1) {
    close(socket_fd);
    return EXIT_FAILURE;
  }

  int connection_fd = accept(socket_fd, NULL, NULL);

  if (0 > connection_fd) {
    close(socket_fd);
    return EXIT_FAILURE;
  }

  char buf[6];
  memset(buf, 0, 6);
  recv(connection_fd, buf, 5, 0);
  buf[5] = 0;
  if (strcmp(buf, "magic") == 0) {
    printf("Magic!!\n");
  }

  if (shutdown(connection_fd, SHUT_RDWR) == -1) {
    close(connection_fd);
    close(socket_fd);
    return EXIT_FAILURE;
  }
  close(connection_fd);
  close(socket_fd);
  return EXIT_SUCCESS;
}
