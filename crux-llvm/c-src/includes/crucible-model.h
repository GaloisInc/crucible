#ifndef CRUCIBLE_MODEL_H
#define CRUCIBLE_MODEL_H

#ifdef __cplusplus__
extern "C" {
#endif //__cplusplus__

#include <stdint.h>
#include <stddef.h>

#define crux_names(ty)     crucible_names_##ty
#define crux_values(ty)    crucible_values_##ty
#define crux_value_num(ty) crucible_values_number_##ty

#define mk_model_ty(ty) \
  extern const size_t  crux_value_num(ty); \
  extern const char*   crux_names(ty)[]; \
  extern const ty      crux_values(ty) [];

mk_model_ty(int8_t)
mk_model_ty(int16_t)
mk_model_ty(int32_t)
mk_model_ty(int64_t)
mk_model_ty(float)
mk_model_ty(double)

#ifdef __cplusplus__
}
#endif //__cplusplus__

#endif

