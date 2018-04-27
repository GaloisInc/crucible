#ifndef CRUCIBLE_H
#define CRUCIBLE_H

#include <stdbool.h>
#include <stdint.h>

void crucible_assume(uint8_t x, const char *file, int line);
void crucible_assert(uint8_t x, const char *file, int line);

int8_t  crucible_int8_t  (const char *name);
int16_t crucible_int16_t (const char *name);
int32_t crucible_int32_t (const char *name);
int64_t crucible_int64_t (const char *name);

#define forall(ty,nm) ty nm = crucible_##ty(#nm)
#define assuming(e) crucible_assume(e, __FILE__, __LINE__)
#define check(e) crucible_assert(e, __FILE__, __LINE__)

#endif

