#include "lpo3.h"

/* a variable is of the form var(name,sort) */

static ATerm VARgetName(ATerm var) {return ATgetArgument((ATermAppl)var,0); }
static ATerm VARgetSort(ATerm var) {return ATgetArgument((ATermAppl)var,1); }

static int ATlist2array(ATermList termlist, ATerm **terms) {
  int i=0,Nterms=ATgetLength(termlist);
  ATerm term;
  *terms = (ATerm*)calloc(Nterms,sizeof(ATerm));
  if (!*terms) ATerror("No memory for term array");
  ATprotectArray(*terms,Nterms);
  while(ATmatch((ATerm)termlist,"[<term>,<list>]",&term,&termlist))
    (*terms)[i++] = term;
  if (!ATisEmpty(termlist)) ATerror("term list expected");
  return Nterms;
}

static ATermList ATarray2list(int Nterms, ATerm* terms) {
  ATermList termlist=ATempty;
  int i;
  for(i=Nterms-1; i>=0 ; i--)
    termlist=ATinsert(termlist,terms[i]);
  return termlist;
}

static ATerm* ATcopyArray(int Nterms, ATerm* terms) {
  int i;
  ATerm *newterms = (ATerm*)calloc(Nterms,sizeof(ATerm));
  if (!*newterms) ATerror("No memory for term array");
  ATprotectArray(newterms,Nterms);
  for (i=0;i<Nterms;i++)
    newterms[i]=terms[i];
  return newterms;
}

static ATermList ATlistProject(ATermList L,Symbol f,int i) {
  /* projects [f(..xi..),...] to [xi,...] */
  ATermList result=ATempty;
  ATerm term;
  assert(i<ATgetArity(f));
  while (ATmatch((ATerm)L,"[<term>,<list>]",&term,&L)) {
    assert(ATgetType(term)==AT_APPL);
    assert(ATgetSymbol((ATermAppl)term)==f);
    result=ATinsert(result,ATgetArgument((ATermAppl)term,i));
  }
  assert(ATisEmpty(L));
  return ATreverse(result);
}

LPO_t LPOcreate(ATermList pars, ATermList init) {
  int Ninit;
  Symbol v=ATmakeSymbol("v",2,ATfalse);
  LPO_t lpo = (LPO_t)malloc(sizeof(struct lpo));
  if (!lpo) ATerror("No memory for new LPO");
  lpo->Npars = ATlist2array(ATlistProject(pars,v,0),&lpo->parnames);
  ATlist2array(ATlistProject(pars,v,1),&lpo->parsorts);
  Ninit = ATlist2array(init,&lpo->inits);
  assert(lpo->Npars==Ninit);
  lpo->Nsums = 0;
  lpo->Nsumsallocated = 0;
  lpo->sums = NULL;
  lpo->used_in_act = NULL;
  lpo->used_in_guard = NULL;
  lpo->used_in_next = NULL;
  lpo->used = NULL;
  lpo->changed = NULL;
  return lpo;
}

static SUM_t SUMcreate_(LPO_t lpo, int Nvars, ATerm* vars, 
			ATerm act, int Ndata, ATerm* data, 
			int Nnext, ATerm* nexts, ATerm guard) {
  /* creates a summand pointing to these arrays */
  SUM_t sum = (SUM_t)malloc(sizeof(struct sum));
  if (!sum) ATerror("No memory for new summand");
  sum->lpo = lpo;
  sum->Nvars = Nvars;
  sum->vars = vars;
  sum->act = act;
  sum->Ndata = Ndata;
  sum->data = data;
  sum->Nnext = Nnext;
  sum->next = nexts;
  sum->guard = guard;
  ATprotect(&sum->act);
  ATprotect(&sum->guard);
  return sum;
}

static SUM_t SUMcreate(LPO_t lpo, ATermList vars, 
		       ATerm act, ATermList data, 
		       ATermList nexts, ATerm guard) {
  /* allocates arrays from lists and creates summand there a*/
  ATerm *myvars, *mydata, *mynext;
  int Nvars = ATlist2array(vars,&myvars);
  int Ndata = ATlist2array(data,&mydata);
  int Nnext = ATlist2array(nexts,&mynext);
  return SUMcreate_(lpo,Nvars,myvars,act,Ndata,mydata,Nnext,mynext,guard);
}

static SUM_t SUMcreateCopy(LPO_t lpo, int Nvars, ATerm* vars, 
			   ATerm act, int Ndata, ATerm* data, 
			   int Nnext, ATerm* nexts, ATerm guard) {
  /* copies arrays to new arrays and creates summand there a*/
  ATerm* myvars = ATcopyArray(Nvars,vars);
  ATerm* mydata = ATcopyArray(Ndata,data);
  ATerm* mynext = ATcopyArray(Ndata,nexts);
  return SUMcreate_(lpo,Nvars,myvars,act,Ndata,mydata,Nnext,mynext,guard);
}

static int LPOappendSums(LPO_t lpo, int Nsums, SUM_t *sums) {
  int i,
    oldNsums = lpo->Nsums,
    newNsums = oldNsums + Nsums,
    allocated = lpo->Nsumsallocated;
  
  if (allocated < newNsums) {
    allocated = 2*allocated+1;
    lpo->sums = (SUM_t*)realloc(lpo->sums,allocated*sizeof(SUM_t));
    if (!lpo->sums) { /* if doubling is not possible, go for the minimum required */
      allocated = lpo->Nsums + Nsums;
      lpo->sums = realloc(lpo->sums,allocated);
      if (!lpo->sums) 
	ATerror("No memory to add summands");
    }
    assert(lpo->sums); /* ATerror is expected to abort the program */
    lpo->Nsumsallocated=allocated;
  }
  
  for (i=0; i<Nsums; i++)
    lpo->sums[oldNsums+i] = sums[i];
  
  lpo->Nsums = newNsums;
  return oldNsums;
}

static void SUMdestroy(SUM_t sum) {
  ATunprotect(sum->vars);
  free(sum->vars);
  ATunprotect(&sum->act);
  ATunprotect(sum->data);
  free(sum->data);
  ATunprotect(sum->next);
  free(sum->next);
  ATunprotect(&sum->guard);
  free(sum);
}

void LPOdestroy(LPO_t lpo) {
  int i;
  ATunprotect(lpo->parnames);
  free(lpo->parnames);
  ATunprotect(lpo->parsorts);
  free(lpo->parsorts);
  ATunprotect(lpo->inits);
  free(lpo->inits);
  for (i=0;i<lpo->Nsums;i++)
    SUMdestroy(lpo->sums[i]);
  free(lpo->sums);
  free(lpo);
}

int LPOnPars(LPO_t lpo) { 
  return lpo->Npars; 
}
ATerm *LPOgetParNames(LPO_t lpo) { 
  return lpo->parnames; 
}
ATerm *LPOgetParSorts(LPO_t lpo) { 
  return lpo->parsorts; 
}
ATerm *LPOgetInits(LPO_t lpo) { 
  return lpo->inits; 
}
ATermList LPOgetInitList(LPO_t lpo) {
  return ATarray2list(lpo->Npars,lpo->inits);
}
ATerm LPOgetParName(LPO_t lpo, int j) {
  assert(j<LPOnPars(lpo));
  return lpo->parnames[j];
}
ATerm LPOgetParSort(LPO_t lpo, int j) {
  assert(j<LPOnPars(lpo));
  return lpo->parsorts[j];
}
ATerm LPOgetInit(LPO_t lpo, int j) {
  assert(j<LPOnPars(lpo));
  return lpo->inits[j];
}
ATerm LPOgetPar(LPO_t lpo, int j) {
  assert(j<LPOnPars(lpo));
  return ATmake("v(<term>,<term>)", lpo->parnames[j],lpo->parsorts[j]);
}
ATermList LPOgetParList(LPO_t lpo) {
  ATermList result=ATempty;
  int j;
  for (j=lpo->Npars-1;j>=0;j--)
    result=ATinsert(result,LPOgetPar(lpo,j));
  return result;
}

int LPOnSums(LPO_t lpo) { 
  return lpo->Nsums;
}
SUM_t *LPOgetSums(LPO_t lpo) {
  return lpo->sums;
}
ATermList SUMgetDataList(SUM_t sum) { 
  return ATarray2list(sum->Ndata,sum->data); 
}
ATermList SUMgetVarList(SUM_t sum) { 
  return ATarray2list(sum->Nvars,sum->vars); 
}
ATermList SUMgetNextList(SUM_t sum) {
  return ATarray2list(sum->lpo->Npars,sum->next);
}
int SUMnVars(SUM_t sum) { 
  return sum->Nvars; 
}
ATerm SUMgetAct(SUM_t sum) { 
  return sum->act;
}
int SUMnData(SUM_t sum) { 
  return sum->Ndata; 
}
int SUMnNext(SUM_t sum) {
  return sum->lpo->Npars; 
}
ATerm *SUMgetNexts(SUM_t sum) {
  return sum->next;
}
ATerm SUMgetGuard(SUM_t sum) { 
  return sum->guard; 
}

ATerm SUMgetVar(SUM_t sum, int k) {
  assert(k<SUMnVars(sum));
  return ATelementAt(SUMgetVarList(sum),k);
}
ATerm SUMgetVarName(SUM_t sum, int k) {
  return VARgetName(SUMgetVar(sum,k));
}
ATerm SUMgetVarSort(SUM_t sum, int k) {
  return VARgetSort(SUMgetVar(sum,k));
}

ATerm SUMgetDatum(SUM_t sum, int l) { 
  assert(l<SUMnData(sum));
  return ATelementAt(SUMgetDataList(sum),l);
}
ATerm SUMgetNext(SUM_t sum, int j) { 
  assert(j<SUMnNext(sum));
  return SUMgetNexts(sum)[j];
}

/* Modifier on Summands */

void LPOrewriteSum(LPO_t lpo, int i) {
  SUMrewrite(LPOgetSum(lpo,i));
}

void SUMrewriteData(SUM_t sum) {
  int i,n=SUMnData(sum);
  for (i=0;i<n;i++)
    sum->data[i] = RWrewrite(sum->data[i]);
}

void SUMrewriteGuard(SUM_t sum) {
  sum->guard = RWrewrite(sum->guard);
}

void SUMrewriteNext(SUM_t sum, int i) {
  sum->next[i] = RWrewrite(sum->next[i]);
}


void SUMrewrite(SUM_t sum) {
  /* rewrites guard, act and next of summand, 
     taking into account global environment, cf. RWassign */
  int i, n=SUMnNext(sum);
  SUMrewriteData(sum);
  SUMrewriteGuard(sum);
  for (i=0;i<n;i++)
    SUMrewriteNext(sum, i);
}


/* data access to LPO */

SUM_t LPOgetSum(LPO_t lpo, int i) {
  assert(i<LPOnSums(lpo));
  return LPOgetSums(lpo)[i];
}
ATerm LPOgetVar(LPO_t lpo, int i, int k) {
  return SUMgetVar(LPOgetSum(lpo,i),k);
}
ATerm LPOgetVarName(LPO_t lpo, int i, int k) {
  return VARgetName(LPOgetVar(lpo,i,k));
}
ATerm LPOgetVarSort(LPO_t lpo, int i, int k) {
  return VARgetSort(LPOgetVar(lpo,i,k));
}

ATerm LPOgetAct(LPO_t lpo, int i) {
  assert(i<LPOnSums(lpo));
  return SUMgetAct(LPOgetSums(lpo)[i]);
}
ATerm LPOgetData(LPO_t lpo, int i, int l) {
  assert(i<LPOnSums(lpo));
  return SUMgetDatum(LPOgetSums(lpo)[i],l);
}
ATerm LPOgetGuard(LPO_t lpo, int i) {
  assert(i<LPOnSums(lpo));
  return SUMgetGuard(LPOgetSums(lpo)[i]);
}
ATerm LPOgetNext(LPO_t lpo, int i, int j) {
  assert(i<LPOnSums(lpo));
  return SUMgetNext(LPOgetSums(lpo)[i],j);
}

ATermList LPOgetVarList(LPO_t lpo, int i) {
  return SUMgetVarList(LPOgetSum(lpo,i));
}
ATermList LPOgetDataList(LPO_t lpo,int i) {
  return SUMgetDataList(LPOgetSum(lpo,i));
}
ATermList LPOgetNextList(LPO_t lpo, int i) {
  return SUMgetNextList(LPOgetSum(lpo,i));
}

/* 2gen interface */

int LPOaddSum(LPO_t lpo, ATerm sum2gen) {
  ATerm act,guard;
  ATermList vars, data, next;
  SUM_t summand;
  if (!ATmatch(sum2gen,
	       "smd(<term>,<term>,<term>,i(<term>),<term>)",
	       &vars,&act,&data,&next,&guard))
    ATerror("Summand should be in 2gen format");
  summand = SUMcreate(lpo,vars,act,data,next,guard);
  if (summand->Nnext != lpo->Npars)
    ATerror("Summand doesn't match number of parameters");
  return LPOappendSums(lpo,1,&summand);
}

int LPOaddSUM(LPO_t lpo, int Nvars, ATerm* vars, 
			   ATerm act, int Ndata, ATerm* data, 
			   int Nnext, ATerm* nexts, ATerm guard) {
  SUM_t summand = SUMcreateCopy(lpo,Nvars,vars,act,Ndata,data,Nnext,nexts,guard);
  if (summand->Nnext != lpo->Npars)
    ATerror("Summand doesn't match number of parameters");
  return LPOappendSums(lpo,1,&summand);
}



static ATerm SUMget2gen(SUM_t sum) {
  return ATmake("smd(<term>,<term>,<term>,i(<term>),<term>)",
		SUMgetVarList(sum),
		SUMgetAct(sum),
		SUMgetDataList(sum),
		SUMgetNextList(sum),
		SUMgetGuard(sum));
}

void LPOaddSumList(LPO_t lpo, ATermList sums) {
  ATerm sum;
  while (ATmatch((ATerm)sums,"[<term>,<list>]",&sum,&sums))
    LPOaddSum(lpo,sum);
}
  
LPO_t LPOfrom2gen(ATerm lpo2gen) {
  LPO_t result;
  ATermList init, sums, pars;
  if (!ATmatch(lpo2gen,"initprocspec(<term>,<term>,<term>))",
	       &init,&pars,&sums))
    ATerror("LPO should be in 2gen format\n");
  
  result = LPOcreate(pars,init);
  LPOaddSumList(result,sums);
  return result;
}

ATermList LPOgetSumList(LPO_t lpo) {
  ATermList sumlist=ATempty;
  int i, Nsums=LPOnSums(lpo);
  SUM_t* sums = LPOgetSums(lpo);
  for(i=Nsums-1; i>=0 ; i--)
    sumlist=ATinsert(sumlist,SUMget2gen(sums[i]));
  return sumlist;
}

ATerm LPOto2gen(LPO_t lpo) {
  return ATmake("initprocspec(<term>,<term>,<term>))",
		LPOgetParList(lpo),
		LPOgetInitList(lpo),
		LPOgetSumList(lpo));
}

/* static ATermList PARlistFromParInit(ATermList pars, ATermList inits) { */
/*   ATermList result=ATempty; */
/*   ATerm init, name, sort; */
/*   assert(ATgetLength(inits)==ATgetLength(pars)); */
/*   while (ATmatch((ATerm)pars,"[v(<term>,<term>),<list>]",&name,&sort,&pars) */
/* 	 && ATmatch((ATerm)inits,"[<term>,<list>]",&init,&inits)) */
/*     result = ATinsert(result,ATmake("par(<term>,<term>,<term>)",name,sort,init)); */
/*   assert(ATisEmpty(pars) && ATisEmpty(inits)); */
/*   return ATreverse(result); */
/* } */

/* static ATermList PARlistToPar2gen(ATermList pars) { */
/*   ATermList result=ATempty; */
/*   ATerm name, sort; */
/*   while (ATmatch((ATerm)pars,"[par(<term>,<term>,<term>),<list>]" */
/* 		 ,                 &name, &sort,  NULL,   &pars)) */
/*     result = ATinsert(result,ATmake("v(<term>,<term>)",name,sort)); */
/*   assert(ATisEmpty(pars)); */
/*   return ATreverse(result); */
/* } */

/* static ATermList PARlistToInit2gen(ATermList pars) { */
/*   ATermList result=ATempty; */
/*   ATerm init; */
/*   while (ATmatch((ATerm)pars,"[par(<term>,<term>,<term>),<list>]" */
/* 		 ,                  NULL, NULL  , &init , &pars)) */
/*     result = ATinsert(result,init); */
/*   assert(ATisEmpty(pars)); */
/*   return ATreverse(result); */
/* } */

