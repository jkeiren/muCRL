/* $Id: discover.h,v 1.5 2006/12/21 09:12:04 bertl Exp $ */

#ifndef DISCOVER_H
#define DISCOVER_H

#include "vector_db.h"
#include "term_db.h"
#include "mgr.h"

typedef void *step_t;

typedef int (*expl_cbt)(elm_t *src, act_t *act, elm_t *dest);
typedef int (*finexpl_cbt)(unexplored_t *src, int count);

step_t  DIScreateMCRL(int segment, int nseg, int k, int local, tdb_t labels, tdb_t leafs, vdb_t *nodes,
     expl_cbt ecb, finexpl_cbt fecb);
int DISsegment(step_t st, elm_t *dest);
int DISexplore(step_t step, unexplored_t *elm);
elm_t *DISfold(step_t step, term_t *data);
void DIShelpMCRL(void);
int DISgetSegment(step_t step);
elm_t *DISexploreInitialState(step_t step);
int DISevaluate(char *e);
char *DISsetArgumentsMCRL(char *args, int *nargs, char ***argv, void *topStack);
int DISmapNodeId(int id, int pos, int n);
#endif
