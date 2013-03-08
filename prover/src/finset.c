#include "finset.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

struct finset {
  int size;
  char* set;
};

void add_elt(FINSET_t A, int x) {
  assert(x < A->size);
  A->set[x]=1;
}

void rem_elt(FINSET_t A, int x) {
  assert(x < A->size);
  A->set[x]=0;
}


FINSET_t emptyset(int size) {
  FINSET_t E = (FINSET_t)malloc(sizeof(struct finset));
  E->size = size;
  E->set = (char*)calloc(size,sizeof(char));
  return E;
}

void merge(FINSET_t A, const FINSET_t B) {
  int i,N=A->size;
  assert(N==B->size);
  for (i=0;i<N;i++)
    A->set[i] = A->set[i] || B->set[i];
}

char disjoint(const FINSET_t A, const FINSET_t B) {
  int i,N=A->size;
  assert(N==B->size);
  for (i=0;i<N;i++)
    if ((A->set[i]==1) && (B->set[i]==1))
      return 0;
  return 1;
}

char test_elt(const FINSET_t A, int x) {
  assert(x < A->size);
  return A->set[x];
}

void destroy_set(FINSET_t A) {
  free(A->set);
  free(A);
}
