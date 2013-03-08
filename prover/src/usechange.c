#include "lpo3.h"
#include "usechange.h"
#include <stdlib.h>


static ATermIndexedSet pars2indices(LPO_t lpo) {
  ATermIndexedSet S = ATindexedSetCreate(100,50);
  int i,j;
  ATbool b;
  for (j=0;j<lpo->Npars;j++) {
    i=ATindexedSetPut(S,LPOgetParName(lpo,j),&b);
    assert(i==j);
  }
  return S;
}

static void vars2finset(ATerm term, ATermIndexedSet Vars, FINSET_t A) {
/* add all variables in Vars that occur in term into the finset
   tacit assumption: indices in Vars coincide with size of A */

  int i = ATindexedSetGetIndex(Vars,term);
  if (i>=0)
    add_elt(A,i);
  else {
    int i,n = ATgetArity(ATgetSymbol(term));
    for (i=0 ; i<n ; i++)
      vars2finset(ATgetArgument((ATermAppl)term,i),Vars,A);
  }
}

static void vars2finset_list(ATermList terms, ATermIndexedSet Vars, FINSET_t A) {
  for (;!ATisEmpty(terms); terms=ATgetNext(terms))
    vars2finset(ATgetFirst(terms),Vars,A);
}

FINSET_t Used_in_act_set(LPO_t lpo, int i) {return lpo->used_in_act[i];}
FINSET_t Used_in_guard_set(LPO_t lpo, int i) {return lpo->used_in_guard[i];}
FINSET_t Used_in_next_set(LPO_t lpo, int i) {return lpo->used_in_next[i];}
FINSET_t Used_set(LPO_t lpo, int i) {return lpo->used[i];}
FINSET_t Changed_set(LPO_t lpo, int i) {return lpo->changed[i];}

char Used_in_act(LPO_t lpo, int i, int j) { return test_elt(lpo->used_in_act[i],j); }
char Used_in_next(LPO_t lpo, int i, int j) { return test_elt(lpo->used_in_next[i],j); }
char Used_in_guard(LPO_t lpo, int i, int j) { return test_elt(lpo->used_in_guard[i],j); }
char Used(LPO_t lpo, int i, int j) { return test_elt(lpo->used[i],j); }
char Changed(LPO_t lpo, int i, int j) { return test_elt(lpo->changed[i],j); }
char Used_in_act_or_guard(LPO_t lpo, int i, int j) { 
  return Used_in_act(lpo,i,j) || Used_in_guard(lpo,i,j);
}


static void report_independent_sums(LPO_t lpo) {
  // this function is only needed for test purposes
  int i,j;
  fprintf(stderr,"Table of independent summands\n");
  for (i=0;i<lpo->Nsums;i++) {
    fprintf(stderr,"%2d: ",i);
    for (j=0;j<lpo->Nsums;j++) {
      if (i==j) fprintf(stderr," ");
      else {
	if (disjoint(Used_set(lpo,i),Changed_set(lpo,j))
	    && disjoint(Used_set(lpo,j),Changed_set(lpo,i))
            && disjoint(Changed_set(lpo,i),Changed_set(lpo,j)))
	  fprintf(stderr,"+");
	else
	  fprintf(stderr,"-");
      }
    }
    fprintf(stderr,"\n");
  }
}

extern ATerm MCRLprint(ATerm t);

static void report_used_parameters(LPO_t lpo) {
  // this function is only needed for test purposes
  int i,j;
  for (j=0;j<lpo->Npars;j++) {
    ATfprintf(stderr,"%t is directly used by summand ",MCRLprint(LPOgetParName(lpo,j)));
    for (i=0;i<lpo->Nsums;i++)
      if (Used_in_act_or_guard(lpo,i,j))
	ATfprintf(stderr,"%d,",i+1);
    ATfprintf(stderr,"\n");

    ATfprintf(stderr,"%t is used by summand ",MCRLprint(LPOgetParName(lpo,j)));
    for (i=0;i<lpo->Nsums;i++)
      if (Used(lpo,i,j))
	ATfprintf(stderr,"%d,",i+1);
    ATfprintf(stderr,"\n");

    ATfprintf(stderr,"%t is changed by summand ",MCRLprint(LPOgetParName(lpo,j)));
    for (i=0;i<lpo->Nsums;i++)
      if (Changed(lpo,i,j))
	ATfprintf(stderr,"%d,",i+1);
    ATfprintf(stderr,"\n");
  }
}

void UCinitialize(LPO_t lpo) {
  int i,j;
  int Nparams = LPOnPars(lpo);
  int Nsums   = LPOnSums(lpo);
  ATermIndexedSet Pars = pars2indices(lpo);

  lpo->used_in_act = (FINSET_t*)calloc(Nsums,sizeof(FINSET_t));
  lpo->used_in_guard = (FINSET_t*)calloc(Nsums,sizeof(FINSET_t));
  lpo->used_in_next = (FINSET_t*)calloc(Nsums,sizeof(FINSET_t));
  lpo->used = (FINSET_t*)calloc(Nsums,sizeof(FINSET_t));
  lpo->changed = (FINSET_t*)calloc(Nsums,sizeof(FINSET_t));
  
  /* determine used and changed parameters per summand */
  
  for (i=0;i<Nsums;i++) {
    /* determine the parameters used in action */
    lpo->used_in_act[i] = emptyset(Nparams);
    vars2finset_list(LPOgetDataList(lpo,i),Pars,lpo->used_in_act[i]);
    
    /* determine the parameters used in guard */
    lpo->used_in_guard[i] = emptyset(Nparams);
    vars2finset(LPOgetGuard(lpo,i),Pars,lpo->used_in_guard[i]);
    
    /* determine changed parameters and parameters used for updates */
    lpo->used_in_next[i] = emptyset(Nparams);
    lpo->changed[i] = emptyset(Nparams);
    for (j=0;j<Nparams;j++) {
      ATerm next = LPOgetNext(lpo,i,j);
      if (next != LPOgetParName(lpo,j)) {
	add_elt(lpo->changed[i],j);
	vars2finset(next,Pars,lpo->used_in_next[i]);
      }
    }
    
    /* accumulate information on used parameters */
    lpo->used[i]=emptyset(Nparams);
    merge(lpo->used[i],lpo->used_in_act[i]);
    merge(lpo->used[i],lpo->used_in_guard[i]);
    merge(lpo->used[i],lpo->used_in_next[i]);
  }

  ATindexedSetDestroy(Pars);
  if (0) report_used_parameters(lpo); // for testing purposes: change to 1
  if (0) report_independent_sums(lpo);  // for testing purposes: change to 1
}

void UCdestroy(LPO_t lpo) {
  int i;
  int Nsums   = LPOnSums(lpo);

  for (i=0;i<Nsums;i++) {
    destroy_set(lpo->used_in_act[i]);
    destroy_set(lpo->used_in_guard[i]);
    destroy_set(lpo->used_in_next[i]);
    destroy_set(lpo->changed[i]);
    destroy_set(lpo->used[i]);
  }
  free(lpo->used_in_act);
  free(lpo->used_in_guard);
  free(lpo->used_in_next);
  free(lpo->used);
  free(lpo->changed);
  lpo->used_in_act = NULL;
  lpo->used_in_guard = NULL;
  lpo->used_in_next = NULL;
  lpo->changed = NULL;
}
