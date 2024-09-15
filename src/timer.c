#include "idris_rts.h"
#include <time.h>

double doubleTime() {
    return ((double)clock())/CLOCKS_PER_SEC;
}
