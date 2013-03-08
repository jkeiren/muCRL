#ifndef XLTS_H
#define XLTS_H

#include <sys/types.h>
#include "config.h"

#ifdef SVC
#define USE_SVC 1
#endif

#ifdef USE_SVC
extern void* lts_stack_bottom;
extern int lts_aterm_init_done;
#endif



typedef enum {LTS_LIST,LTS_BLOCK,LTS_BLOCK_INV} LTS_TYPE;

typedef unsigned long cell_t;

typedef struct lts {
	LTS_TYPE type;
	cell_t root, root2;
	cell_t transitions;
	uint32_t states;
        uint32_t s_ofs, t_ofs;
	cell_t *begin;
	cell_t *src;
	uint32_t *label;
	cell_t *dest;
	int tau, divergence, deadlock;
	char **label_string;
	uint32_t label_count;
} *lts_t;


extern lts_t lts_create();

extern void lts_free(lts_t lts);

extern void lts_set_type(lts_t lts,LTS_TYPE type);

extern void lts_set_size(lts_t lts, uint32_t states, cell_t transitions);

extern void lts_uniq(lts_t lts);

extern void lts_sort(lts_t lts);

extern void lts_sort_alt(lts_t lts);

extern void lts_sort_dest(lts_t lts);

extern void lts_bfs_reorder(lts_t lts);

extern void lts_randomize(lts_t lts);

extern void lts_tau_cycle_elim(lts_t lts);

extern void lts_divergence_marking(lts_t lts);

extern void lts_remove_divergence_marking(lts_t lts);

extern void lts_tau_indir_elim(lts_t lts);

extern int lts_diameter(lts_t lts);

#define LTS_AUTO 0
#define LTS_AUT 1
#ifdef USE_BCG
#define LTS_BCG 2
#endif
#define LTS_DIR 3
#ifdef USE_SVC
#define LTS_SVC 4
#endif
#define LTS_FSM 5
#define LTS_FC2 6
#define LTS_DMP 7
#define LTS_GZ 8

extern int lts_write_segments;

extern void lts_read(int format,char *name,lts_t lts);

extern void lts_write(int format,char *name,lts_t lts);

void lts_join(lts_t lts1, lts_t lts2, lts_t lts);

extern int lts_equivalent(lts_t lts);



#endif
