typedef struct empty {
} empty;

typedef struct empties {
  empty empties[8];
} empties;

const empties glob = {};

int main(void) { return 0; }
