#ifndef LPO1_H
#define LPO1_H

#include <stdlib.h>
#include <assert.h>
#include "aterm2.h"

typedef struct lpo *LPO_t;

/* Construction and Destruction of LPO */

LPO_t LPOcreate(ATermList pars, ATermList inits); 
               /* pars should be of the form [v(name,sort) ... ]
		* inits should be of the form [term,..], length equal to pars
		*/
int LPOaddSum(LPO_t lpo, ATerm sum);
               /* this creates a summand in lpo, and returns its index
		* sum should be of the form smd(vars,act,data,i(nexts),guard), where
		* - vars should be of the from [v(name,sort), ... ] 
		* - act is a term
		* - data should be of the form [term, ...]
		* - nexts should be of the form [term, ...]  (length equal to lpo->nPars)
		* - guard is a term
		*/
void LPOdestroy(LPO_t lpo);
               /* this destroys the lpo and all its summands, and frees the memory */

/* below, j<nPars, i<nSums, k<nVars[i], l<nData[i] */

/* Basic data access */

int   LPOnPars(LPO_t lpo);               /* returns number of parameters */
ATerm LPOgetParName(LPO_t lpo, int j);   /* returns name of parameter j  */
ATerm LPOgetParSort(LPO_t lpo, int j);   /* returns sort of parameter j  */
ATerm LPOgetInit(LPO_t lpo, int j);      /* returns init of parameter j  */

int   LPOnSums(LPO_t lpo);                     /* returns number of summands      */
int   LPOnVars(LPO_t lpo, int i);              /* returns number of vars of sum i */
ATerm LPOgetVarName(LPO_t lpo, int i, int k);  /* returns name of var k in sum i  */
ATerm LPOgetVarSort(LPO_t lpo, int i, int k);  /* returns sort of var k in sum i  */
ATerm LPOgetAct(LPO_t lpo, int i);             /* returns action of summand i     */
ATerm LPOgetnData(LPO_t lpo);                  /* returns number of data of sum i */
ATerm LPOgetData(LPO_t lpo, int i, int l);     /* returns datum l of sum i        */
ATerm LPOgetGuard(LPO_t lpo, int i);           /* returns guard of summand i      */
ATerm LPOgetNext(LPO_t lpo, int i, int j);     /* returns next of par j in sum i  */

/* Compound data access */

ATermList LPOgetParList(LPO_t lpo);         /* returns [v(name,sort),...]           */
ATermList LPOgetInitList(LPO_t lpo);        /* returns list of init elements        */
ATermList LPOgetSumList(LPO_t lpo);         /* returns list of summands             */
ATermList LPOgetVarList(LPO_t lpo, int i);  /* returns [v(name,sort),...] of sum i  */
ATermList LPOgetDataList(LPO_t lpo, int i); /* returns list of data elts of sum i   */
ATermList LPOgetNextList(LPO_t lpo, int i); /* returns list of next pars of sum i   */
ATerm LPOgetPar(LPO_t lpo, int j);        /* returns parameter j as v(name,sort)    */
ATerm LPOgetVar(LPO_t lpo, int i, int k); /* returns var k of sum i as v(name,sort) */

/* More constructors */

LPO_t LPOfrom2gen(ATerm lpo2gen);
              /* lpo2gen should be of the form initprocspec(pars,inits,sums) */
ATerm LPOto2gen(LPO_t lpo);
              /* returns initprocspec(pars,inits,sums) */
#endif
