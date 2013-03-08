#ifndef LPO2_H
#define LPO2_H

#include "lpo1.h"

/* Functions on SUM */

/* Note: A summand is always part of an lpo. 
   Changes on summands imply changes on the LPO 
*/

typedef struct sum *SUM_t;

/* Basic access to summands */

SUM_t LPOgetSum(LPO_t lpo, int i);         /* get summand i                  */
int   SUMnVars(SUM_t sum);                 /* get number of variables        */
ATerm SUMgetVar(SUM_t sum, int k);         /* get variable k as v(name,sort) */
ATerm SUMgetVarName(SUM_t sum, int k);     /* get name of variable k         */
ATerm SUMgetVarSort(SUM_t sum, int k);     /* get sort of variable k         */
ATerm SUMgetAct(SUM_t sum);                /* get action label               */
int   SUMnData(SUM_t sum);                 /* get number of data elements    */
ATerm SUMgetDatum(SUM_t sum, int l);       /* get data element l             */
int   SUMnNext(SUM_t sum);                 /* get number of next elements    */
ATerm SUMgetNext(SUM_t sum, int j);        /* get next value of parameter j  */
ATerm SUMgetGuard(SUM_t sum);              /* get guard                      */

/* Modifiers of summands */

void SUMrewrite(SUM_t sum);
void LPOrewriteSum(LPO_t lpo, int i);

/* Compound access to summands */

ATermList SUMgetVarList(SUM_t sum);  /* returns [v(name,sort),...] */
ATermList SUMgetDataList(SUM_t sum); /* returns list of data elts  */
ATermList SUMgetNextList(SUM_t sum); /* returns list of next pars  */

/* The result of the functions below is READ-ONLY and NON-PERSISTENT */

ATerm *LPOgetParNames(LPO_t lpo);    /* array of parameter names of length nPars */
ATerm *LPOgetInits(LPO_t lpo);       /* array of init values of length nPars     */
SUM_t *LPOgetSums(LPO_t lpo);        /* array of summands of length nSums        */
ATerm *SUMgetNexts(SUM_t sum);       /* array of next terms of length nNext      */

/* Efficient Construction */

int LPOaddSUM(LPO_t lpo, int Nvars, ATerm* vars, 
	      ATerm act, int Ndata, ATerm* data, 
	      int Nnext, ATerm* nexts, ATerm guard);
          /* This adds a summand to the LPO, by copying all information */

#endif
