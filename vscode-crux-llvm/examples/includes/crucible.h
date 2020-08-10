#ifndef CRUCIBLE_H
#define CRUCIBLE_H

#ifdef __cplusplus
extern "C" {
#endif //__cplusplus

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

void crucible_assume(uint8_t x, const char *file, int line);
void crucible_assert(uint8_t x, const char *file, int line);

int8_t   crucible_int8_t   (const char *name);
int16_t  crucible_int16_t  (const char *name);
int32_t  crucible_int32_t  (const char *name);
int64_t  crucible_int64_t  (const char *name);
float    crucible_float    (const char *name);
double   crucible_double   (const char *name);

size_t   crucible_size_t   (const char *name);

// Allocate a string of fixed length with symbolic contents
//
// The string has @max_len@ symbolic bytes plus a fixed NUL terminator.  Each
// character is unconstrained and may also be NUL, allowing for verification of
// algorithms over strings up to a certain length.
//
// The string contents are read-only.
const char* crucible_string(const char *name, size_t max_len);

// Fill a region of memory with fresh symbolic bytes
void crucible_havoc_memory( void* p, size_t len );

// Print a symbolic value to stdout
void crucible_print_uint32( uint32_t val );

// Print the current state of the symbolic memory to stdout
void crucible_dump_memory(void);


#define crucible_uint8_t(n)  ((uint8_t)crucible_int8_t(n))
#define crucible_uint16_t(n)  ((uint16_t)crucible_int16_t(n))
#define crucible_uint32_t(n)  ((uint32_t)crucible_int32_t(n))
#define crucible_uint64_t(n)  ((uint64_t)crucible_int64_t(n))

#define assuming(e) crucible_assume(e, __FILE__, __LINE__)
#define check(e) crucible_assert(e, __FILE__, __LINE__)

#ifdef __cplusplus
}
#endif //__cplusplus

#endif
