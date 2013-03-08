#ifndef LPO3_H
#define LPO3_H

/* this is the part of the implementation, shared by usechange.c and lpo.c */

#include "finset.h"
#include "lpo2.h"

struct sum {
  LPO_t lpo;
  int Nvars;
  ATerm* vars;
  ATerm act;
  int Ndata;
  ATerm* data;
  int Nnext;
  ATerm* next;  /* array of size Nnext*/
  ATerm guard;
}; /* *SUM_t */

struct lpo {
  int Npars;
  ATerm *parnames; /* array of size Npars */
  ATerm *parsorts; /* array of size Npars */
  ATerm *inits;    /* array of size Npars */
  int Nsums;
  int Nsumsallocated;
  SUM_t *sums;     /* array of size Nsums */
  
  /* the following fields are only accessible via usechange.h */
  
  FINSET_t* used_in_act;    /* array of size Nsums */
  FINSET_t* used_in_guard;  /* array of size Nsums */
  FINSET_t* used_in_next;   /* array of size Nsums */
  FINSET_t* used;           /* array of size Nsums */
  FINSET_t* changed;        /* array of size Nsums */
  
}; /* *LPO_t */

#endif
