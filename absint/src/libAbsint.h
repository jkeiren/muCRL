/* $Id: libAbsint.h,v 1.1 2004/05/28 08:18:02 bertl Exp $ */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "rw.h"

#define P(msg)  fprintf(stderr,"%s\n",msg)
#define PP(msg)  fprintf(stderr,"%s ",msg)
#define NAME_LENGTH 500
#define MAX_NUM_PARS 1000
#define pTerm(term)  fprintf(stderr,"%s\n", ATwriteToString(term));
#define ppTerm(term)  fprintf(stderr,"%s ", ATwriteToString(term));
 
static ATbool MONITOR = ATfalse;
static char *absPrefix="abs_";

static char *setPrefix="setOf_";
static char *liftPrefix="lift_";
static char *auxVarPrefix = "auxVar_";
static char *maySufix = "_may";
static char *mustSufix = "_must";

static char *emptyPrefix = "empty_";
static char *fullPrefix = "full_";
static char *inSym = "in_setOf";
static char *orderedInSym = "in_order_setOf";
static char *ltSym = "abs_lt";
static char *eqSym = "eq";  
static char *eqSym1 = "eq#";
static char *absEqSym = "abs_eq";
static char *ifSym = "if";
static char *absIfSym = "absIf";  
static char *orSym = "or";
static char *andSym = "and"; 
static char *unionSym = "U";
static char *memberSym = "member";
static char *subsetSym = "subset";
static char *singletonSym = "singleton";  
static char *singSym = "sing";
static char *notSym = "not"; 
static char *headSym = "head_setOf";
  
static char *absH = "H";
static char *absHinv = "Hinv";
static char *absAlpha = "alpha";
static char *absGamma = "gamma";

static char *constructorPrefix="A_";

AFun createAbstractH(ATerm absSort);
ATerm createEmptyCons(ATerm setSort); 
ATerm createFullSetOfBool();
ATerm createFullCons(ATerm setSort);
AFun createInCons(ATerm sort, ATerm setSort);
AFun createOrderedInFunc(ATerm sort, ATerm setSort, AFun inFun, AFun ifFun,
							ATerm emptyTerm, ATerm fullTerm);
AFun createSingCons(ATerm sort, ATerm setSort, 
					ATerm emptyTerm, AFun inFun);
AFun createEqFunc(ATerm sort);
AFun createUnionFunc(ATerm sort, ATerm setSort, ATerm emptyTerm, ATerm 
	fullTerm, AFun inFun, AFun ifFun, AFun memberFun);
AFun createIfFunc(ATerm sort);
AFun createMemberFunc(ATerm sort, ATerm setSort, AFun eqFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun);
						
AFun createHeadFunc(ATerm sort, ATerm setSort, AFun inFun);
AFun createSubsetFunc(ATerm sort, ATerm setSort, AFun memberFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun);
AFun createSingletonFunc(ATerm sort, ATerm setSort, AFun eqFun,
					   AFun inFun, ATerm emptyTerm, ATerm fullTerm, AFun ifFun);

void createSetFuncs(ATerm sort, ATerm setSort);

void createNewEquations(AFun tag, ATermList sorts, int i, ATerm targetSort, 
			ATermList listLeft, ATerm right, ATermList rl1, ATermList rl2, 
			ATermList vars, ATbool done);


ATerm liftSort(ATerm sort);
ATerm abstractSort(ATerm sort);
ATerm getConcrete(ATerm sort);
ATbool isAbstracted(ATerm sort);
ATerm getUnLifted(ATerm sort);
ATbool isLifted(ATerm sort);
ATbool matchesSort(ATerm s1, ATerm s2);

ATbool abstractedArgs(ATermList sorts);
ATbool abstractedOrLiftedSorts(ATermList sorts);

ATerm createAlphaTerm(ATerm term, ATerm termSort);
ATerm createGammaTerm(ATerm term, ATerm termSort);

ATerm createSingTerm(ATerm term, ATerm setSort);

void appendString(char *head, char *tail, char *newString);
ATbool hasPrefix(char *string, char *prefix);

AFun createNewFunc(AFun fun, ATermList argSorts, ATerm fSort);
AFun createNewFuncSym (char *funcName, ATermList sorts);
ATerm createNewFuncTerm(ATerm func, ATermList argSorts, ATerm fSort);


ATermList getFuncSortList(ATerm func);
void getFuncName(AFun fun, char *sym);
ATbool reservedFunc(AFun fun);

ATermList getListOfSorts(ATerm adt);
ATermList getConstructors(ATerm adt);
ATermList getFunctions(ATerm adt);
ATermList getEquations(ATerm adt);

void setOrder();
