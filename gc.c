#include <inttypes.h>
#include "types.h"
#include "values.h"
#include "runtime.h"

val_t* collect_garbage(val_t* rsp, val_t *rbp, val_t* rbx) {
  return rbx;
}
