/* $Id: bitset.h,v 1.1 2004/01/29 13:17:28 bertl Exp $ */
#ifndef BITSET_H
#define BITSET_H

#include <stdio.h>

struct bitset;
typedef struct bitset *bitset_t;

typedef unsigned int element_t;

extern bitset_t bitset_create(int node_class,int base_class);
extern void bitset_destroy(bitset_t set);

extern int bitset_clear_all(bitset_t set);
extern int bitset_set_all(bitset_t set);

extern int bitset_clear(bitset_t set,element_t e);
extern int bitset_set(bitset_t set,element_t e);

extern int bitset_test(bitset_t set,element_t e);

/*
 * future expansion might include:
 *
 * extern int bitset_next_clear(bitset_t set,element_t *e);
 * extern int bitset_prev_clear(bitset_t set,element_t *e);
 */

extern int bitset_next_set(bitset_t set,element_t *e);
extern int bitset_prev_set(bitset_t set,element_t *e);

extern void bitset_fprint(FILE*f,bitset_t set);

#endif

