#ifndef SET_REDUCTIONS_H
#define SET_REDUCTIONS_H

#include "xlts.h"

extern void set_reduce_strong(lts_t lts);

extern void set2_reduce_strong(lts_t lts);



extern int tau_cycle_elim;

extern int tau_indir_elim;

extern void set_reduce_branching(lts_t lts);

extern void set_reduce_weak(lts_t lts);

extern void set_reduce_branching2(lts_t lts);

extern void set_reduce_branching3(lts_t lts);

extern void set_reduce_tau_star_a(lts_t lts);

extern void set_mkdet(lts_t lts);

#endif
