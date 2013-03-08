#ifndef FINSET_H
#define FINSET_H

typedef struct finset *FINSET_t;

void add_elt(FINSET_t A, int x);
/* x must be smaller than size of A 
   x is added to set A */

void rem_elt(FINSET_t A, int x);
/* x must be smaller than size of A 
   x is removed from set A */

FINSET_t emptyset(int size);
/* creates an empty finite set of this size */

void merge(FINSET_t A, const FINSET_t B);
/* A and B should be of the same size.
   A becomes A union B, and B is unchanged
*/

char disjoint(const FINSET_t A, const FINSET_t B);
/* A and B should be of the same size.
   A and B are unchanged.
   returns 1 if A and B are disjoint, 0 otherwise
*/

char test_elt(const FINSET_t A, int x);
/* x must be smaller than size of A.
   test if x is in A */

void destroy_set(FINSET_t A);
/* free all resources occupied by A;
   After this operation A should not be dereferenced */

#endif
