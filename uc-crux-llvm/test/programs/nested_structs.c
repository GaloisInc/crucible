#include "stdint.h"
#include "stdio.h"

struct nestedtypes {
  uint64_t field_1;
  uint64_t field_2;
  struct nested_1_type {
    uint8_t field_3;
    double *field_4;
  } nested_1;
  struct /* anonymous */ {
    char field_5[10];
    float field_6;
  } nested_2;
};

void nested_structs(int i, struct nestedtypes *foo) {
  if (i) {
    foo->nested_1.field_3 = i ? 1 : 0;
    foo->nested_2.field_6 = 100.0 + (i * i + 1);
  } else {
    foo->nested_1.field_3 = 0xBB;
    foo->nested_2.field_6 = (i + 1) * 3.14;
  }

  printf("field_3:%x field_6:%f\n", foo->nested_1.field_3, foo->nested_2.field_6);
}
