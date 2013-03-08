/* $Id: libmcrl.c,v 1.17 2007/11/07 09:48:26 bertl Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "aterm2.h"
#include "mcrl.h"

#define INITSIZE 300 
#define MAX_ARITY 256

#define RULE(a, b, c)  (ATmake("e(<term>,<term>,<term>)",a, b, c))
   
static FILE *input_add = NULL, *input_remove = NULL;

MCRL_OUTPUTFORMAT MCRLformat = MCRLundefined;
ATbool MCRLoldTbf = ATfalse;
static ATbool first = ATtrue, reorder_rules = ATfalse,
       flagTest = ATtrue, extend_adt = ATfalse, may_extend_adt = ATtrue;

static ATermList  
       add_eqs = NULL,
       add_sorts = NULL, add_cons = NULL, add_maps = NULL;

static ATerm xVar = NULL , yVar = NULL , zVar = NULL;

ATerm MCRLterm_bool, MCRLterm_state, MCRLterm_false,
MCRLterm_true, MCRLterm_delta, MCRLterm_tau, MCRLterm_tau_c,
MCRLterm_terminated, MCRLterm_empty_tree, MCRLterm_i;

AFun MCRLsym_i, MCRLsym_v, MCRLsym_pair, MCRLsym_and, MCRLsym_or,
MCRLsym_not, MCRLsym_ite, MCRLsym_one, MCRLsym_x2p0, MCRLsym_x2p1;

ATerm MCRLtag = NULL;

typedef struct {
    ATerm f; /* if (type==sort) list of constructors 
                if (type >= function) fname(sorts of function arguments,
                annotated by projections) */
    ATermList l; /* if (type==MCRLconstructorsort) list of case functions  */
    } SYMTERM;
    
typedef struct {
   MCRLsymtype type; 
   long sort; /* used as auxilary variable in case sort */
   unsigned short nr; /* order number of sort or order number of 
   casefunction per sort  */ 
   } SYMINT;
   
typedef struct {
    int size;
    AFun *e, *n; 
    } ENUMSORTS; 
    
static ENUMSORTS enumsorts;
     
static int size, maxsym = 0;
static SYMTERM *symterm = NULL;
static SYMINT *symint = NULL;
      
static ATerm currentAdt=NULL, currentProc=NULL, currentSpec=NULL;

static ATbool mcrl_report = ATfalse, verbose = ATfalse,  o_flag = ATfalse;

static ATerm projTag=NULL, depthTag=NULL; 

static char fileName[MCRLsize], *filterName = NULL, *outputFile = NULL;

static ATermTable db_term_print = NULL;

static char vname[] = "v";
static AFun vTag;

static AFun CexxxIsxEquation(AFun c, ATerm esort, ATerm sort, ATbool *new);
static int CaseEquations(AFun c,  ATermList cs, ATerm sort, ATbool *new); 
static void UpdateSpecs(void);
static int ClosedEqualRules(AFun srt, ATbool *new);
static void ReadExtraAdt(FILE *f);
static ATerm TranslateEq(ATerm e);
/* Not added to the API. Reasons:
   Not yet documented
   The name doesn't cover the load
   Not important enough
*/
static char *MCRLextendNameString(ATermList sorts, char *format,...);
static AFun MCRLextendNameSymbol(ATermList sorts, char *format,...);
static char *MCRLgetNameSymbol(AFun s);
static char *MCRLgetNameTerm(ATerm t);
static char *MCRLgetNameString(char *s);
static AFun MCRLnextSymbol(AFun s);
static ATerm MCRLuniqueTermF(ATermList sorts, char *format,...);
static ATermList MCRLgetMapsIfNotConstructors(AFun fsort);
static AFun MCRLputReflexivity(ATerm sort, ATbool *new);
static ATbool RWisRewriterNeeded(void);
static ATermList MCRLgenerateElementsOfConstructorSort(AFun s);
static ATermList occurringVars(ATerm t);
static ATerm BuildRHS(ATermTable db, ATerm t);
static ATerm NormalEq(ATerm eq);
      
static void EnlargeTables(AFun sym) {
      if (sym> maxsym) maxsym = sym;
      if (size > sym) return;
      { long old=size;
      ATunprotect((ATerm*) symterm); 
      while (size <= sym) size *= 2;  
      if (!(symint = (SYMINT*) realloc(symint, 
             size*sizeof(SYMINT))))
        ATerror("Cannot reallocate symint array (%d)", size);
      if (!(symterm = (SYMTERM*) realloc(symterm, 
             size*sizeof(SYMTERM))))
        ATerror("Cannot reallocate term array (%d)", size);
      /* ATwarning("QQQ test %d %d", sizeof(ATerm), sizeof(SYMTERM)); */
      /* ATwarning("Reallocation (sym %d) new size %d", sym, size); */
      for (;old<size;old++) {
           symint[old].type=0;
           symint[old].sort=0;
           symterm[old].f=NULL;
           symterm[old].l=NULL;
           }
      ATprotectArray((ATerm*) symterm, 2*size);
      }     
}

void EnlargeEnumeratedsorts(int arity) {
    int size0 = enumsorts.size;
    if (size0 == 0) {
        size0 = INITSIZE;
        while (size0<=arity) size0 *= 2;
        if (!(enumsorts.e = (AFun*) calloc(size0, sizeof(AFun)))) {
           ATerror("Cannot malloc enumerated sorts (%d)",size0);
           }
        if (!(enumsorts.n = (AFun*) calloc(size0, sizeof(AFun)))) {
           ATerror("Cannot malloc enumerated sorts (%d)",size0);
           }
        }
        else {
           int i;
           if (size0>arity) return;
           while (size0<=arity) size0 *= 2;
           if (!(enumsorts.e =
                   (AFun*) realloc(enumsorts.e, size0*sizeof(AFun)))) {
           ATerror("Cannot realloc enumerated sorts (%d)",size0);
           }
           if (!(enumsorts.n =
                   (AFun*) realloc(enumsorts.n, size0*sizeof(AFun)))) {
           ATerror("Cannot realloc enumerated sorts (%d)",size0);
           }
           for (i=enumsorts.size;i<size0;i++) {
		enumsorts.e[i] = 0;
	        enumsorts.n[i] = 0;
                }
        }
    enumsorts.size = size0;
    }
     
static void initConstants(void) {
#include "mcrl_sig.h"
    ATprotect(&MCRLterm_bool); MCRLterm_bool = ATmake("<str>",bool_term);
    ATprotect(&MCRLterm_state); MCRLterm_state = ATmake("<str>",state_term);
    ATprotect(&MCRLterm_false); MCRLterm_false = ATmake("<str>",false_term);
    ATprotect(&MCRLterm_true);  MCRLterm_true = ATmake("<str>",true_term);
    ATprotect(&MCRLterm_delta); MCRLterm_delta = ATmake("<str>",delta_term);
    ATprotect(&MCRLterm_tau); MCRLterm_tau = ATmake("<str>",tau_term);
    ATprotect(&MCRLterm_tau_c); MCRLterm_tau_c = ATmake("<str>",tau_c_term);
    ATprotect(&MCRLterm_terminated); MCRLterm_terminated = ATmake("<appl>",
                                     terminated_term);
    ATprotect(&MCRLterm_empty_tree); MCRLterm_empty_tree = ATmake("<appl>",
                                     empty_tree_term);
    ATprotect(&MCRLterm_i);  MCRLterm_i = ATmake("<appl>", i_term);
	MCRLsym_i = ATmakeSymbol(i_sym,1, ATfalse);
	ATprotectSymbol(MCRLsym_i);
	MCRLsym_v = ATmakeSymbol(v_sym,2, ATfalse);
	ATprotectSymbol(MCRLsym_v);
	MCRLsym_pair = ATmakeSymbol(pair_sym, 2, ATfalse);
      	ATprotectSymbol(MCRLsym_pair);
	MCRLsym_and = ATmakeSymbol(and_sym, 2, ATtrue);
    	ATprotectSymbol(MCRLsym_and);
     	MCRLsym_or = ATmakeSymbol(or_sym, 2, ATtrue);
	ATprotectSymbol(MCRLsym_or);
        MCRLsym_not = ATmakeSymbol(not_sym,1,ATtrue); 
    	ATprotectSymbol(MCRLsym_not); 
        MCRLsym_ite = ATmakeSymbol(if_sym,3,ATtrue); 
    	ATprotectSymbol(MCRLsym_ite); 
        MCRLsym_one = ATmakeSymbol(one_sym,0,ATtrue); 
    	ATprotectSymbol(MCRLsym_one);
        MCRLsym_x2p0 = ATmakeSymbol(x2p0_sym,1,ATtrue); 
    	ATprotectSymbol(MCRLsym_x2p0);
        MCRLsym_x2p1 = ATmakeSymbol(x2p1_sym,1,ATtrue); 
    	ATprotectSymbol(MCRLsym_x2p1);
        ATprotect(&xVar);ATprotect(&yVar);ATprotect(&zVar);
        xVar = ATmake("<str>","x");yVar = ATmake("<str>","y");
        zVar = ATmake("<str>","z");                                                                                                                                       
  }
  
static void PrintEqu(AFun sym, ATerm eq, char *s) {
     if (verbose) 
        ATwarning("Equation  %t = %t is %s added", 
        ATmakeApplList(sym, ATgetArguments((ATermAppl) ATgetArgument((ATermAppl) eq, 1))),
        ATgetArgument((ATermAppl)eq, 2), s);
     }

static ATbool CheckTrueAndFalse(ATerm adt) {
 ATermList funcs = (ATermList) ATgetArgument((ATermAppl) 
     ATgetArgument((ATermAppl) adt,0),1);
 ATbool truePresent = ATfalse, falsePresent = ATfalse;
 ATerm oldTrue = ATmake("<str>","T"), oldFalse = ATmake("<str>","F");
 for (;!ATisEmpty(funcs);
       funcs=ATgetNext(funcs))
     {ATerm func = ATgetFirst(funcs);
     if (ATisEqual(ATgetArgument((ATermAppl) func, 0), MCRLterm_false))
          falsePresent = ATtrue;
     else
     if (ATisEqual(ATgetArgument((ATermAppl) func, 0), MCRLterm_true))
          truePresent = ATtrue;
     else
     if (ATisEqual(ATgetArgument((ATermAppl) func, 2), MCRLterm_bool))
          ATwarning("WARNING: Constructor %t has result type %t",
          ATgetArgument((ATermAppl) func, 0), MCRLterm_bool);
     }
 if (falsePresent && truePresent) return ATtrue;
 funcs = (ATermList) ATgetArgument((ATermAppl) 
     ATgetArgument(adt,0),1);
 truePresent = ATfalse; falsePresent = ATfalse;
 for (;!ATisEmpty(funcs)&&(!truePresent||!falsePresent);
       funcs=ATgetNext(funcs))
     {ATerm func = ATgetFirst(funcs);
     if (ATisEqual(ATgetArgument((ATermAppl) func, 0), oldFalse))
          falsePresent = ATtrue;
     if (ATisEqual(ATgetArgument((ATermAppl) func, 0), oldTrue))
          truePresent = ATtrue;
     }
 if  (falsePresent && truePresent) {
     MCRLterm_false = oldFalse;
     MCRLterm_true = oldTrue;
     ATwarning("Old 2th generation .tbf file format\n");
     MCRLoldTbf = ATtrue;
     return ATtrue;
     }
 ATwarning("No %t and %t present", MCRLterm_false, MCRLterm_true);
 return ATfalse;
}

static void fillFilename(char *filename) {
    strncpy(filename, fileName, MCRLsize); {
    char *lastdot = strrchr(filename,'.');
    if (lastdot && !strcmp(lastdot,".tbf")) *lastdot ='\0';
    }
    }

void MCRLsetOutputFile(char *filename) {
    outputFile = filename;
}

char *MCRLgetOutputFile(void) {
    return outputFile;
}
                   
/* IF these two functions are called before MCRLinit, then they  
   will be compiled */
              
void MCRLsetArguments(int *argc, char ***argv) {
     int i, j=0;
     char **newargv = (char**) calloc(*argc + 1, sizeof(char*)),
     *suffix = NULL;
     if (!newargv) ATerror("Cannot allocate array argv");
     fileName[0]='\0';
     newargv[j++] = (*argv)[0];
     for(i=1;i<*argc;i++) {
       if (!outputFile) {
       if (!strcmp((*argv)[i],"-ascii")) {
	    MCRLformat = MCRLtext;
	    continue;
	    }
       if (!strcmp((*argv)[i],"-taf")) {
	    MCRLformat = MCRLsharedText;
	    continue;
	    }
       if (!strcmp((*argv)[i],"-baf")) {
	    MCRLformat = MCRLbinary;
	    continue;
	    }
       if (!strcmp((*argv)[i],"-saf")) {
	    MCRLformat = MCRLserializedBinary;
	    continue;
            }
       }
       if (!strcmp((*argv)[i],"-mcrl-hash")) {
	    if (db_term_print) ATtableDestroy(db_term_print);
	    db_term_print = ATtableCreate(100,75);
	    continue;
	    }
       if (!strcmp((*argv)[i],"-mcrl-report")) {
	    mcrl_report = ATtrue;
            verbose = ATtrue;
	    continue;
	    }
      if (!strcmp((*argv)[i],"-verbose")) {
	    verbose = ATtrue;
	    continue;
	    }
      if (!strcmp((*argv)[i],"-reorder-rules")) {
	    reorder_rules = ATtrue;
	    continue;
	    }
      if (!strcmp((*argv)[i],"-extra-rules") || !strcmp((*argv)[i],"-extend-adt")) {
	    extend_adt = ATtrue; may_extend_adt = ATtrue; 
	    continue;
            }
      if (!strcmp((*argv)[i],"-may-extend-adt")) {
	    may_extend_adt = ATtrue; extend_adt = ATfalse;
	    continue;
            }
      if (!strcmp((*argv)[i],"-no-extra-rules") ||
      !strcmp((*argv)[i],"-no-extend-adt"))  {
	    may_extend_adt = ATfalse; extend_adt = ATfalse;
	    continue;
            }
      if (!strcmp((*argv)[i],"-add")) {
            if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i];
                if (input_add) ATerror("flag -add already present");
                input_add = fopen(name,"r");
                if (!input_add) ATerror("Cannot open file %s", name);
                continue;
                }
            ATerror("Option %s needs argument.\n",(*argv)[i-1]);
            }
      if (!strcmp((*argv)[i],"-rem")) {
            if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
                char *name = (*argv)[i];
                if (input_remove) ATerror("flag -rem already present");
                input_remove = fopen(name,"r");
                if (!input_remove) ATerror("Cannot open file %s", name); 
                continue;
                }
            ATerror("Option %s needs argument.\n",(*argv)[i-1]);
            }
       if (outputFile && !strcmp((*argv)[i],"-o")) {
            if ((++i)<*argc && strncmp((*argv)[i],"-",1)) {
                char *file = (*argv)[i];
                strncpy(outputFile, file, MCRLsize);
                o_flag = ATtrue; 
                continue;
                }
            else
               ATerror("After flag -o filename expected");
            }
      if (i == *argc -1 && (!((*argv)[i][0]) || (*argv)[i][0]!='-')) {
      /* File name can start from argv[i][1]. argv[i][0] is then '\0' */
         strncpy(fileName, (char*) (((*argv)[i])+
               (((*argv)[i][0])?0:1)), MCRLsize-5);
	 suffix = strrchr(fileName,'.');
	 if (!suffix || strcmp(suffix,".tbf")) strncat(fileName,".tbf", 
             MCRLsize);
         if (outputFile && !o_flag) fillFilename(outputFile); 
         } else           
         newargv[j++] = (*argv)[i];
      }
      *argc = j; *argv = newargv;
     }

int MCRLcopyOption(char **newargv, char **argv, int argc, int i, int j) { 
 if (argv[i][0] && argv[i][0]!='-' && strcmp(newargv[j-1],argv[i-1])) {
         if (i==(argc-1)) {
            char *s = (char*) malloc(strlen(argv[i])+2);
            s[0]='\0';
            strcpy(s+1, argv[i]);
            newargv[j++]= s;
            }
         else 
         ATerror("Illegal argument \"%s\" encountered (after \"%s\")", 
                argv[i], argv[i-1]);
         } else
	   newargv[j++] = argv[i];
   return j;
   }  
	      
static ATbool check_enumerated_sort(AFun sort) {
  ATbool new=ATtrue;
  AFun sym;
  if (MCRLgetType(sort)!=MCRLconstructorsort) return ATfalse; 
  {
  ATermList cs = ATreverse((ATermList) symterm[sort].f);
  symterm[sort].f = (ATerm) cs;
  if (ATisEmpty(cs)) return ATfalse; /* A not constructed sort */
  for (;!ATisEmpty(cs); cs=ATgetNext(cs)) {
  if (ATgetArity(ATgetAFun(ATgetFirst(cs)))>0) return ATfalse;
    if (!ATisEmpty(MCRLgetRewriteRules(ATgetAFun(ATgetFirst(cs)))))
        return ATfalse;
    }
  }                           
  sym=MCRLputEqFunction((ATerm) ATmakeAppl0(sort), extend_adt?&new:NULL);  
  if (sym) {
      /* Check */
      if (!extend_adt || !new) {
         ATermList eqs = MCRLgetRewriteRules(sym);
         for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
            ATerm lhs = ATgetArgument(ATgetFirst(eqs),1),
                  rhs = ATgetArgument(ATgetFirst(eqs),2);
            if (ATisEqual(ATgetArgument(lhs,0),ATgetArgument(lhs,1)) &&
               !ATisEqual(rhs, MCRLterm_true)) {
               if (mcrl_report) ATwarning("Rejected %t", ATgetFirst(eqs)); 
               return ATfalse;
               }
            if (MCRLgetTypeTerm(ATgetArgument(lhs,0)) == MCRLconstructor &&
               MCRLgetTypeTerm(ATgetArgument(lhs,1)) == MCRLconstructor)
               if (!ATisEqual(ATgetArgument(lhs,0),ATgetArgument(lhs,1)) &&
                  !ATisEqual(rhs, MCRLterm_false)) {
                   if (mcrl_report) ATwarning("Rejected %t", ATgetFirst(eqs));
                   return ATfalse;
                   } 
             }
          }
       else
         if (extend_adt) ClosedEqualRules(sort, &new);
       }
  if (verbose) ATwarning("%a is an enumerated sort", sort);
  {
  int n = MCRLgetNumberOfConstructors(sort);
  char buf[80];
  sprintf(buf,"Enum%d", n);
  EnlargeEnumeratedsorts(n);
  if (enumsorts.n[n]==0) enumsorts.n[n] = ATmakeAFun(buf,0, ATtrue);
  if (enumsorts.e[n]==0 || enumsorts.n[n]==sort || sort == ATgetAFun(MCRLterm_bool)) 
                    enumsorts.e[n]=sort;
  }
  return ATtrue;
  }

static void check_enumerated_sorts(void) {
  int i;
  for(i=0; i<=maxsym; i++) { 
    if (check_enumerated_sort(i)) 
    symint[i].type=MCRLenumeratedsort;    
    }
  }
     
static ATermList check_whether_case_function(AFun fsym) {
/* Returns NULL if fsym not case function and the list of its belonging 
   enumerators if yes */
   if (MCRLgetType(fsym) != MCRLfunction && 
      MCRLgetType(fsym) != MCRLcasefunction) return NULL;
   if (ATgetArity(fsym)<2) return NULL;
   {
   int n = ATgetArity(fsym), i;
   ATerm sig = MCRLgetFunction(fsym), *selectors = NULL;
   ATermList eqs = MCRLgetRewriteRules(fsym),  cs = ATempty;
   AFun fsort = MCRLgetSortSymbol(fsym), 
        enumsort = ATgetAFun(ATgetArgument((ATermAppl) sig, 0));
   /* if (n==4) ATwarning("%a: %a  (%a)", fsym, enumsort, MCRLgetEnumSort(3));*/
   if (MCRLgetType(enumsort)!= MCRLenumeratedsort  || 
      MCRLgetEnumSort(n-1) != enumsort ||
       MCRLgetNumberOfConstructors(enumsort) != n-1) return (ATermList) NULL; 
   for (i=1;i<n;i++) 
      if (ATgetAFun(ATgetArgument((ATermAppl) sig, i)) != fsort) 
              return (ATermList) NULL;
   if (mcrl_report) ATwarning("Candidate for case function: %a", fsym);
   /* Check the rewrite rules */
   selectors = (ATerm*) calloc(n-1, sizeof(ATerm));
   ATprotectArray(selectors, n-1);
   for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
        ATerm eq = ATgetFirst(eqs),
              lhs = ATgetArgument((ATermAppl) eq, 1), 
              rhs = ATgetArgument((ATermAppl) eq, 2),
              arg0= ATgetArgument((ATermAppl) lhs, 0);
      
        if (MCRLgetTypeTerm(arg0)==MCRLconstructor && 
            MCRLgetTypeTerm(rhs)==MCRLvariable) {
            ATermList args = ATgetNext(ATgetArguments((ATermAppl) lhs));
            int x = ATindexOf(args, rhs, 0);
            if (selectors[x]==NULL) selectors[x]=arg0; 
            else if (!ATisEqual(selectors[x], arg0))
            {ATunprotect(selectors); free(selectors); return NULL;} 
            }
      } 
    for (i=n-2;i>=0;i--)
      if (selectors[i]==NULL) {
       ATunprotect(selectors); free(selectors); return NULL;
       }
      else cs = ATinsert(cs, selectors[i]);
    ATunprotect(selectors); free(selectors); 
    if (mcrl_report) ATwarning("Strong candidate for case function %a selectors %t", 
            fsym, cs);
    if (CaseEquations(fsym,  cs, (ATerm) ATmakeAppl0(fsort), (ATbool*) NULL) 
              != n-1) return (ATermList) NULL;
    return cs; /* Returns selectors in right order */
    }
    }
  
static int PosInList(ATermList l, AFun f) {
     int r = 0;
     for (;!ATisEmpty(l); l = ATgetNext(l), r++)
         if (ATgetAFun(ATgetFirst(l))==f) return r; 
     return -1; 
     }
     
static int CreateExtraProjectionEquations(AFun fsym, ATermList cs, int n, 
   int *aux, ATerm dummy) {
   /* Pi(f(x1...xn))=dummy */
   int i = 0, r = 0;
   char buf[MCRLsize];
   for (;!ATisEmpty(cs)&&i<n;i++, cs = ATgetNext(cs))
   if (aux[i]==0) {
      AFun a = ATgetAFun(ATgetFirst(cs));
      int m = ATgetArity(a), j;
      ATermList vs = ATempty, as = ATempty;
      ATerm eq = NULL;
      ATbool new;
      for (j=0;j<m;j++) {
          ATerm fsort = ATremoveAllAnnotations((ATerm)
                        ATgetArgument(ATgetFirst(cs),j)); 
          ATerm name = NULL;
          sprintf(buf,"%s%d",vname, j);
          name = ATmake("<str>", buf);
          vs = ATinsert(vs, (ATerm) ATmakeAppl2(vTag, name, fsort));
          as = ATinsert(as, name);
          }
      eq = ATmake("e(<term>, <term>, <term>)", ATreverse(vs),
           (ATerm) ATmakeAppl1(fsym, 
                    (ATerm) ATmakeApplList(a, ATreverse(as))), dummy);
      MCRLputEquation(eq, &new);
      r++;
      if (mcrl_report) ATwarning("Equation %t = %t: added",
      ATgetArgument((ATermAppl) eq, 1), ATgetArgument((ATermAppl) eq, 2));    
      }
   return r;
   }
    
static int check_whether_projection(AFun fsym, AFun *farg, int *new) {
/* Returns -1 if fsym not a projection function and the position of the 
   argument if yes */
   int n = ATgetArity(fsym), r = -1, i; 
   
   if (n!=1) return -1 /* No projection */;
      {
      ATermList eqs = MCRLgetRewriteRules(fsym);
      int *aux = NULL;
      AFun asort = ATgetAFun(ATgetArgument((ATermAppl) symterm[fsym].f, 0)),
      rsort = MCRLgetSortSym(fsym);
      ATermList cs = NULL;
      ATerm dummy = NULL;
      /* if (rsort != MCRLconstructorsort) return -1; */
      dummy = MCRLdummyVal(rsort); 
      if (!dummy) return -1; 
      if (new) *new = 0;
      if (MCRLgetType(asort)!=MCRLconstructorsort) return -1;
      cs = MCRLgetConstructors(asort);
      n = ATgetLength(cs);
      if (!(aux = (int*) calloc(n, sizeof(int)))) 
            ATerror("Cannot allocate aux. array (size %d)", n);
      for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
           ATerm eq = ATgetFirst(eqs);
           ATerm lhs = ATgetArgument((ATermAppl) eq, 1),
                 rhs = ATgetArgument((ATermAppl) eq, 2),
                 arg = ATgetArgument((ATermAppl) lhs, 0);
           AFun fun = ATgetAFun(arg);
           int pos = -1;
           if (MCRLgetTypeTerm(arg)!=MCRLconstructor) {free(aux);return -1;}
           pos = PosInList(cs, ATgetAFun(symterm[fun].f));
           if (MCRLgetTypeTerm(rhs)==MCRLvariable) {
               ATermList vs = ATempty;
               int k = ATgetArity(ATgetAFun(arg));
               for (i=0;i<k;i++) {
                  ATerm x = (ATerm) ATgetArgument((ATermAppl) arg, i);
                  if (MCRLgetTypeTerm(x)!=MCRLvariable) { 
                       free(aux);return -1;}
                  if (ATindexOf(vs, x, 0)>=0) {
                       free(aux);return -1;}
                  vs = ATinsert(vs, x);
                  }
               for (i=0;i<k;i++) {
                  ATerm x = (ATerm) ATgetArgument((ATermAppl) arg, i);
                  if (ATisEqual(x, rhs)) { 
                       if (r<0) {
                           r = i;
                           *farg = ATgetAFun(arg);
                           aux[pos] = 1;
                           } else {free(aux);return -1;}
                       }
                  }
               } else {
                 if (!ATisEqual(rhs, dummy)) {free(aux);return -1;}  
                 }
           aux[pos] = 1;
           }
       if (r<0) {free(aux);return r;}
       if (!may_extend_adt || !new) {
           for (i=0;i<n;i++)
           if (aux[i]==0)  {free(aux);return -1;} 
           }
       else
           *new = CreateExtraProjectionEquations(fsym, cs, n, aux, dummy);
       if (mcrl_report) ATwarning("%s is a projection function: argument %d of %s", 
            ATgetName(fsym), r, ATgetName(*farg));
       free(aux);
       return r;
      }
  }
 
static ATbool check_whether_det(AFun fsym) {
   if (MCRLgetType(fsym)!=MCRLfunction) return ATfalse;
   {
   int n = ATgetArity(fsym), i =0;
   AFun fsort = MCRLgetSortSym(fsym);
   if (n!=1 || MCRLgetType(fsort)!=MCRLenumeratedsort) return ATfalse 
         /* Determination function */;
      {
      ATermList eqs = MCRLgetRewriteRules(fsym), cs = NULL, es = NULL;
      AFun asort = ATgetAFun(ATgetArgument((ATermAppl) symterm[fsym].f, 0));
      int *aux = NULL, m = -1;
      if (MCRLgetType(asort)!=MCRLconstructorsort) return ATfalse;
      cs = MCRLgetConstructors(asort);
      es = MCRLgetConstructors(fsort);
      n = ATgetLength(cs); m = ATgetLength(es);
      if (n!=m) return ATfalse;
      if (!(aux = (int*) calloc(n, sizeof(int)))) 
            ATerror("Cannot allocate aux. array (size %d)", n); 
      for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
       ATerm eq = ATgetFirst(eqs);
       ATerm lhs = ATgetArgument((ATermAppl) eq, 1),
             rhs = ATgetArgument((ATermAppl) eq, 2),
             arg = ATgetArgument((ATermAppl) lhs, 0);
       int pos = -1, i, k = ATgetArity(ATgetAFun(arg));
       ATermList vs = ATempty;
       if (MCRLgetTypeTerm(arg)!=MCRLconstructor ||
           MCRLgetTypeTerm(rhs)!=MCRLconstructor) 
               {free(aux);return ATfalse;}
       for (i=0;i<k;i++) {
          ATerm x = (ATerm) ATgetArgument((ATermAppl) arg, i);
          if (MCRLgetTypeTerm(x)!=MCRLvariable) { 
               free(aux);return ATfalse;}
          if (ATindexOf(vs, x, 0)>=0) {
               free(aux);return ATfalse;}
          vs = ATinsert(vs, x);
          }
       pos = ATindexOf(es, rhs, 0);
       if (MCRLgetType(ATgetAFun(arg))!=MCRLconstructor) {
          free(aux); return ATfalse;} 
       if (PosInList(cs, ATgetAFun(symterm[ATgetAFun(arg)].f)) !=pos) {
               free(aux);return ATfalse;}
       aux[pos]=1;
       }
       for (i=0;i<n;i++) 
       if (aux[i]==0) {free(aux);return ATfalse;}
       if (mcrl_report) 
            ATwarning("%s is a determination function", ATgetName(fsym));
       free(aux); 
       return ATtrue;
       }
  }
  }
    
static ATbool PresentInSort(AFun f) {
  AFun fsort = symint[f].sort;
  int m = ATgetArity(f);
  ATermList cs = MCRLgetCaseFunctions(fsort);
  for (;!ATisEmpty(cs);cs=ATgetNext(cs)) { 
      ATerm c = ATgetFirst(cs);
      if (ATgetArity(ATgetAFun(c))==m) {
        /* if (f != ATgetAFun(c) && MCRLgetType(f)==MCRLcasefunction) 
             MCRLsetType(f, MCRLunknown); */
        return ATtrue;
        }
      }    
  return ATfalse;    
  }
  
static void ForceCaseFunction(AFun f) { 
   AFun fsort = symint[f].sort;
   ATerm t = symterm[f].f;
   ATermList cs = symterm[fsort].l;
   long n = MCRLgetNumberOfConstructors(fsort), m = ATgetArity(f)-1;
   /* ATwarning("QQQ MCRLsetCaseF %s",ATgetName(f)); */
   
   if (ATisEmpty(cs)) cs =ATinsert(cs, t);
   else { 
       if (n==m) {
          cs =ATinsert(cs, t);
          }
       else { 
          cs = ATinsert(ATinsert(ATgetNext(cs), t), ATgetFirst(cs));
          }
       }
   symterm[fsort].l = cs;
   symint[f].type = MCRLcasefunction;
   }
     
ATbool MCRLsetCaseFunction(AFun f) {
if (PresentInSort(f)) {
       return ATfalse;
       }
   ForceCaseFunction(f);
   return ATtrue;
   }
     
static AFun AlreadyPresentSymbol(AFun sort, int n) {
  if (MCRLgetType(sort)==MCRLunknown || MCRLgetType(sort)>=MCRLvariable) 
       return 0;
  {
  ATermList cs = MCRLgetCaseFunctions(sort);
  for (;!ATisEmpty(cs);cs=ATgetNext(cs)) { 
      ATerm c = ATgetFirst(cs);
      /* ATwarning("QQ sort = %a c = %t arity = %d n = %d", 
      sort, c, ATgetArity(ATgetAFun(c)), n); */
      if (ATgetArity(ATgetAFun(c))==n+1) {
        return ATgetAFun(c);
        }
      }    
  return 0;    
  }
  }
               
AFun MCRLputIfFunction(ATerm sort, ATbool *new) { 
  AFun result = AlreadyPresentSymbol(ATgetAFun(sort), 2);
  ATbool extendEqu = (new && *new);
  ATermList cs = ATmakeList2(MCRLterm_true, MCRLterm_false);
  if (result==0 || CaseEquations(result, cs, sort, (ATbool*) NULL) != 2) {
     AFun sym =  MCRLsym_ite;
     result = MCRLputMap(
         (ATerm) ATmakeAppl3(sym, MCRLterm_bool, sort, sort), sort, new);   
     if (result != 0) {
        if (new && *new) CaseEquations(result, cs, sort, new); 
        else return 0;  
        }
     else {if (new) *new = ATfalse; return 0;}
     }
/* ATwarning("QQ %a  <-> %a",result, MCRLsym_ite); */
    else if (result != MCRLsym_ite) {
        ATprotectSymbol(result);
        MCRLsym_ite = result;
        }
  if ((new && *new) || extendEqu) {
     CexxxIsxEquation(result, MCRLterm_bool, sort, new);
     } 
  return result; 
  }

static AFun CexxxIsxEquation(AFun c, ATerm esort, ATerm sort, ATbool *new) {
  int n = ATgetArity(c)-1, i;
  AFun result;
  ATermList vars = ATmakeList2(ATmake("v(<str>,<term>)", "e", esort),
                               ATmake("v(<str>,<term>)", "x", sort));
  ATerm *aux = (ATerm*) calloc(n+1, sizeof(ATerm)), lhs, eq;
  aux[0] = ATgetArgument((ATermAppl) ATelementAt(vars, 0), 0);
  for (i=1;i<=n;i++) aux[i] = ATgetArgument((ATermAppl) ATelementAt(vars, 1), 0);
  lhs = (ATerm) ATmakeApplArray(c, aux);
  eq = RULE(vars, lhs,  aux[1]);
  result = MCRLputEquation(eq, new); 
  if (new && *new) PrintEqu(c, eq, "");
  return result;                            
  }
    
static int CaseEquations(AFun c,  ATermList cs, ATerm sort, ATbool *new) {
    int n = ATgetArity(c)-1, i, cnt = 0;
    ATermList vars = ATempty;
    ATerm *aux = (ATerm*) calloc(n+1, sizeof(ATerm)), lhs;
    char buf[80];
    ATprotectArray(aux,n+1);
    for (i=n;i>=1;i--) {
         sprintf(buf,"%s%d", "v", i-1);
         {
         ATerm v = ATmake("v(<str>,<term>)", buf , sort);
         vars = ATinsert(vars, v);
         aux[i] = ATmake("<str>", buf);
         }
         }
     aux[0] = (ATerm) ATempty;
     lhs = (ATerm) ATmakeApplArray(c, aux);
     for (i=0;i<n; (i++, cs = ATgetNext(cs))) {
        if (MCRLputEquation(
          RULE(vars, ATsetArgument((ATermAppl) lhs , ATgetFirst(cs), 0), 
                 aux[i+1]), new) && (!new || (new && *new))) cnt++;
        }
    ATunprotect(aux);free(aux);
    if (new) *new = (cnt>0?ATtrue:ATfalse); 
    if (verbose &&  new && cnt>0) 
        ATwarning("There %s %d \"case\"-equation%s %s", 
           cnt>1?"are":"is", cnt, cnt>1?"s":"",new?"added":"found");
    return cnt;
    }
           
AFun MCRLputCaseFunction(int n, ATerm sort, ATbool *new) {
     int i;
     ATbool extendEqu = (new && *new);
     ATermList sorts = ATempty; 
     AFun c = AlreadyPresentSymbol(ATgetAFun(sort), n);
     ATerm e,  ct;
     if (n<=0) return 0;
     if (c) {
        if (new) {
           if (*new) CexxxIsxEquation(c,
                 (ATerm) ATmakeAppl0(enumsorts.e[n]),sort, new);
           } 
           return c;
           }
     EnlargeEnumeratedsorts(n);
     /* if (enumsorts.e[n]>0) ATwarning("%a", enumsorts.e[n]); */
     if (enumsorts.e[n]==0) {
         /* Enumerated sort with cardinality <n> is not present */
         e = MCRLuniqueTermF((ATermList) NULL, "Enum%d", n);
         if (MCRLputSort(e, new)==0) {if (new) *new = ATfalse; return 0;};
         for (i=n-1;i>=0;i--) {
              ATerm constructor = MCRLuniqueTermF(ATempty, "u-%d-%d", i, n);
              if (MCRLputConstructor(constructor, e, new)==0)
                       {if (new) *new = ATfalse; return 0;}
              /* ATwarning("Add Constructor %t:%t", constructor, e); */
              }
         enumsorts.e[n] = ATgetAFun(e);
         }
     else {
          e = (ATerm) ATmakeAppl0(enumsorts.e[n]);
          }
     for (i=0;i<n;i++) sorts = ATinsert(sorts, sort);
     sorts = ATinsert(sorts, e);
     ct = MCRLuniqueTermF(sorts, "%s%d-%s", "C", n, ATgetName(ATgetAFun(sort)));
     c = ATgetAFun(ct);
     MCRLputMap(ct, sort, new);
     CaseEquations(c,  MCRLgetConstructors(ATgetAFun(e)), sort, new);
     if (extendEqu) CexxxIsxEquation(c, e, sort,  new);
     MCRLsetCaseFunction(c);
     return c;         
     }
      
AFun MCRLgetEnumSort(int n) {
     if (n>=enumsorts.size) return 0;
     return enumsorts.e[n];
     } 
             
static int ClosedEqualRules(AFun srt, ATbool *new) {
    int cnt = 0, i, j;
    ATermList cs = MCRLgetConstructors(srt);
    int n = ATgetLength(cs);
    for (;!ATisEmpty(cs);cs = ATgetNext(cs)) {
        if (ATgetArity(ATgetAFun(ATgetFirst(cs)))>0) return 0;
        if (!ATisEmpty(MCRLgetRewriteRules(ATgetAFun(ATgetFirst(cs))))) return 0;
        }
     cs = MCRLgetConstructors(srt);
     for (i=0;i<n;i++)
         for (j=0;j<n;j++) 
             if (i!=j) {
             ATerm e =  ATmake("e(<term>,<term>,<term>)", 
                                 ATempty, 
             ATmake("<str(<term>,<term>)>", 
                   "eq", ATelementAt(cs,i), ATelementAt(cs,j)),
                      MCRLterm_false);               
            MCRLputEquation(e, new);
            if (new && *new) cnt++; 
            }
    if (new) *new = cnt>0?ATtrue:ATfalse;
    if (verbose &&  cnt>0) 
       ATwarning("There %s %d \"eq\"-equation%s on closed terms of sort %a added", 
          cnt>1?"are":"is", cnt, cnt>1?"s":"", srt);
    return cnt;       
    }
 
ATbool MCRLisPureConstructorSort(AFun srt) {
    ATermList l = MCRLgetConstructors(srt);
    for (;!ATisEmpty(l);l=ATgetNext(l)) 
    if (!ATisEmpty(MCRLgetRewriteRules(ATgetAFun(ATgetFirst(l))))) {
         if (verbose) 
            ATwarning("Constructor%t of sort %a is lhs of a rewrite rule",
            ATgetFirst(l), srt);
         return ATfalse;
         }
    return ATtrue;
    }

static ATerm NormalizeLhs(ATerm cons) {
     ATermList vars = occurringVars(cons), varpt = vars, newvars = ATempty; 
     ATerm newcons, eq;
     int i, n = ATgetLength(vars);
     ATermTable db = ATtableCreate(50,70);
     for (i=0, varpt = vars;i<n;i++, varpt = ATgetNext(varpt)) {
         ATerm newval1 = ATmake("v(<term>, <term>)", ATgetFirst(varpt), 
              (ATerm) ATmakeAppl0(MCRLgetSort(ATgetFirst(varpt))));
         newvars = ATinsert(newvars, (ATerm) newval1);
         }
     for (i=0, varpt = vars;i<n;i++, varpt = ATgetNext(varpt)) {
          ATerm newval = (ATerm)
                ATmakeAppl0(MCRLextendNameSymbol(ATempty,"||%d", i)),
          newval2 = ATmake("v(<term>, <term>)", newval, 
              (ATerm) ATmakeAppl0(MCRLgetSort(ATgetFirst(varpt))));
          ATtablePut(db, ATgetFirst(varpt), newval);
          MCRLdeclareVar(newval2);
          newvars = ATinsert(newvars, (ATerm) newval2);
          }
     newcons = BuildRHS(db, cons);
     eq = RULE(ATreverse(newvars), ATmake("<str(<term>,<term>)>", "eq", cons, newcons),
         MCRLterm_true);
     ATtableDestroy(db);
     return ATgetArgument((ATermAppl)
          ATgetArgument((ATermAppl) NormalEq(eq), 1), 0);
     }
              
static ATbool check_whether_eq_function(AFun fsym);

static ATbool CheckEqRules(AFun fsym, ATerm arg0, ATermList cs) {
    ATermList eqs = MCRLgetRewriteRules(fsym), seleqs = ATempty;
    for (;!ATisEmpty(eqs);eqs = ATgetNext(eqs)) {
        ATerm left = ATgetArgument((ATermAppl) ATgetFirst(eqs), 1),
        arg0 = ATgetArgument((ATermAppl) left, 0),
        arg1 = ATgetArgument((ATermAppl) left, 1);
        if (ATgetAFun(arg0)!= ATgetAFun(arg1)) continue;
        seleqs = ATinsert(seleqs, arg0);
        }
     for (;!ATisEmpty(cs);cs = ATgetNext(cs)) {
        ATerm c = NormalizeLhs(ATgetFirst(cs));
        if (ATindexOf(seleqs, c ,0)<0) break;
        }
     if (!ATisEmpty(cs)) {
     if (extend_adt) {
            ATbool new = ATtrue;
            if (MCRLputReflexivity(arg0, &new)==0) return ATfalse;
            } 
        else if (MCRLputReflexivity(arg0, NULL)==0) {
            if (verbose)
       ATwarning("%t is no eq-function. Add rule eq(x,x)=T to specification",
                MCRLprint(MCRLgetFunction(fsym)));
                return ATfalse;
                }
       } 
    return ATtrue;
    }
              
static ATbool check_whether_eq_function(AFun fsym) {
   /* assumed that "eq" is a reserved word for equality function */
   if (MCRLgetSortSym(fsym) != ATgetAFun(MCRLterm_bool)) return ATfalse;
   if (MCRLgetType(fsym)<MCRLconstructor) return ATfalse;
   if (strncmp(ATgetName(fsym),"eq#",3) ||
       ATgetArity(fsym)!=2) return ATfalse;
   if (MCRLgetType(fsym)!=MCRLfunction) { 
           if (MCRLgetType(fsym)==MCRLconstructor)
               ATwarning("\"%t\" is a constructor",
               MCRLprint(MCRLgetFunction(fsym)));
           return MCRLgetType(fsym)==MCRLeqfunction;
           } 
   {
   ATerm f = MCRLgetFunction(fsym);
   ATerm arg0 = ATgetArgument((ATermAppl) f, 0); 
   ATerm arg1 = ATgetArgument((ATermAppl) f, 1);
   ATermList cs = NULL;
   /* Check sorts of both arguments are equal */
   if (!ATisEqual(arg0, arg1)) return ATfalse;
   /* Check sorts are constructor (enumerated) sorts */ 
   if (MCRLgetType(ATgetAFun(arg0)==MCRLsort)) return ATfalse;
   cs = MCRLgenerateElementsOfConstructorSort(ATgetAFun(arg0));
   if (!cs || !CheckEqRules(fsym, arg0, cs)) {
   
       if (verbose && !extend_adt) 
          ATwarning("%t is no eq-function. Add rule eq(x,x)=T to specification",
            MCRLprint(MCRLgetFunction(fsym)));
            return ATfalse;
            } 
   if (verbose) ATwarning("%t is  eq-function",  
         MCRLprint(MCRLgetFunction(fsym)));
   return ATtrue;
   }
   }
   
static ATbool ClosedBoolTerm(ATerm t) {
     return ATisEqual(t, MCRLterm_true) || ATisEqual(t, MCRLterm_false);
     }
             
static ATerm  MakeBoolFun2Equ(AFun sym, ATerm x, ATerm y, ATerm right) {
     ATerm left = NULL, result = NULL; 
     ATermList vars = NULL;
     if (ClosedBoolTerm(x))
         vars = ATmakeList1(ATmake("v(<term>,<term>)",y, MCRLterm_bool));
     else
     /* if (ClosedBoolTerm(y)) */
        vars = ATmakeList1(ATmake("v(<term>,<term>)",x, MCRLterm_bool));
     left = (ATerm) ATmakeAppl2(sym, x, y);
     result = ATmake("<appl(<term>,<term>,<term>)>","e",vars, left, right);    
     return result;
     }
     
static ATerm  MakeBoolFun1Equ(AFun sym, ATerm x, ATerm f, ATerm right) {
     ATerm left = NULL, result = NULL; 
     ATermList vars = NULL;
     if (x)
     vars = ATmakeList1(ATmake("v(<term>,<term>)",x, MCRLterm_bool));
     else vars = ATempty;
     left = (ATerm) ATmakeAppl1(sym, f);
     result = ATmake("<appl(<term>,<term>,<term>)>","e",vars, left, right);    
     return result;
     } 

static int AndEquations(ATbool *new) {
    ATerm x = (ATerm) ATmakeAppl0(ATmakeAFun("x",0, ATtrue));
    int cnt = 0;
    if (MCRLputEquation(
           MakeBoolFun2Equ(MCRLsym_and, MCRLterm_false, x, MCRLterm_false), new) && new && *new) cnt++;
    if (MCRLputEquation(
       MakeBoolFun2Equ(MCRLsym_and,  x, MCRLterm_false, MCRLterm_false), new) && new && *new) cnt++;
    if (MCRLputEquation(   
       MakeBoolFun2Equ(MCRLsym_and,  x, MCRLterm_true, x), new) && new && *new) cnt++;
    if (MCRLputEquation(
        MakeBoolFun2Equ(MCRLsym_and,  MCRLterm_true, x, x), new) && new && *new) cnt++;
    if (verbose &&  cnt>0) 
        ATwarning("There %s %d \"and\"-equation%s added", 
           cnt>1?"are":"is", cnt, cnt>1?"s":"");
    if (new) *new = (cnt>0?ATtrue:ATfalse); 
    return cnt;  
    }
    
static int OrEquations(ATbool *new) {
    int cnt = 0;
    ATerm x = (ATerm) ATmakeAppl0(ATmakeAFun("x",0, ATtrue));
    if (MCRLputEquation( 
            MakeBoolFun2Equ(MCRLsym_or, MCRLterm_false, x, x), new) && new && *new) cnt++;
    if (MCRLputEquation( 
        MakeBoolFun2Equ(MCRLsym_or,  x, MCRLterm_false, x), new) && new && *new) cnt++;
    if (MCRLputEquation( 
        MakeBoolFun2Equ(MCRLsym_or,  x, MCRLterm_true, MCRLterm_true), new) && new && *new) cnt++;
    if (MCRLputEquation( 
        MakeBoolFun2Equ(MCRLsym_or,  MCRLterm_true, x, MCRLterm_true), new) && new && *new) cnt++;
    if (verbose &&  cnt>0) 
    ATwarning("There %s %d \"or\"-equation%s added", 
           cnt>1?"are":"is", cnt, cnt>1?"s":""); 
    if (new) *new = (cnt>0?ATtrue:ATfalse);
    return cnt;
    }
    
static int NotEquations(ATbool *new) {
     int cnt = 0;
     ATerm x = (ATerm) ATmakeAppl0(ATmakeAFun("x",0, ATtrue));
     ATerm f = (ATerm) ATmakeAppl1(MCRLsym_not, x);
     if (MCRLputEquation( 
         MakeBoolFun1Equ(MCRLsym_not, NULL, MCRLterm_true, MCRLterm_false), new) && new && *new) cnt++;
     if (MCRLputEquation( 
         MakeBoolFun1Equ(MCRLsym_not, NULL, MCRLterm_false, MCRLterm_true), new) && new && *new) cnt++;
     if (MCRLputEquation(
         MakeBoolFun1Equ(MCRLsym_not, x , f, x), new) && new && *new) cnt++;
     if (verbose &&  cnt>0) 
     ATwarning("There %s %d \"not\"-equation%s added", 
           cnt>1?"are":"is", cnt, cnt>1?"s":"");
     if (new) *new = (cnt>0?ATtrue:ATfalse);  
     return cnt;             
     }

static AFun MCRLputReflexivity(ATerm sort, ATbool *new) {
     ATerm  eq = RULE(ATmakeList1(ATmake("v(<str>,<term>)", "v", sort)),
         ATmake("<str(<str>,<str>)>", "eq","v","v"), MCRLterm_true);
     AFun sym = MCRLputEquation(eq, new);
     if (sym && new && *new) PrintEqu(sym, eq, "");
     return sym;
     }
     

              
AFun MCRLputAndFunction(ATbool *new)  {
     ATbool extendEqu = (new && *new); 
     AFun s = MCRLputMap((ATerm) ATmakeAppl2(MCRLsym_and, MCRLterm_bool, MCRLterm_bool),
                          MCRLterm_bool, new);
     if (s  && ((new && *new) || extendEqu)) AndEquations(new);
     return s; 
     }
     
AFun MCRLputOrFunction(ATbool *new) {
     ATbool extendEqu = (new && *new); 
     AFun s = MCRLputMap((ATerm) ATmakeAppl2(MCRLsym_or, MCRLterm_bool, MCRLterm_bool),
      MCRLterm_bool, new);
     if (s  && ((new && *new) || extendEqu)) OrEquations(new);
     return s; 
     }
     
AFun MCRLputNotFunction(ATbool *new) {
     ATbool extendEqu = (new && *new);
     AFun s = MCRLputMap((ATerm) ATmakeAppl1(MCRLsym_not, MCRLterm_bool),
      MCRLterm_bool, new);
     if (s  && ((new && *new) || extendEqu)) NotEquations(new);
     return s; 
     }
     
AFun MCRLputEqFunction(ATerm sort, ATbool *new) {
     ATbool extendEqu = (new && *new);
     AFun s = MCRLputMap((ATerm) ATmakeAppl2(
            ATmakeAFun("eq",2, ATtrue) , sort, sort),
     MCRLterm_bool, new);
     if (s  && ((new && *new) || extendEqu)) MCRLputReflexivity(sort, new);
     return s; 
     }
                                             
static void ExtraAndOrNotRules(void) {
     ATbool new = ATtrue;
     MCRLputAndFunction(&new);
     new = ATtrue;
     MCRLputOrFunction(&new);
     new = ATtrue;
     MCRLputNotFunction(&new);     
     }
                 

/* -------- Utility functions to build terms -------- */

static ATerm SortAsTerm(ATerm t){
	return (ATerm) ATmakeAppl0(MCRLgetSort(t));
}

/* eq : <sort> # <sort> -> Bool */
ATerm MCRLmakeEq(ATerm t1,ATerm t2){
	ATerm s1=SortAsTerm(t1);
	ATerm s2=SortAsTerm(t2);
	AFun eq_sym=MCRLputEqFunction(s1,NULL);
	if (t1 && t2 && eq_sym && s1==s2) {
		return (ATerm) ATmakeAppl2(eq_sym,t1,t2);
	} else return NULL;
}

/* if : Bool # <sort> # <sort> -> <sort> */
ATerm MCRLmakeIfThenElse(ATerm b,ATerm t1,ATerm t2){
	ATerm s1=SortAsTerm(t1);
	ATerm s2=SortAsTerm(t2);
	AFun if_sym=MCRLputIfFunction(s1,NULL);
	if (b && t1 && t2 && if_sym && s1==s2 && SortAsTerm(b)==MCRLterm_bool) {
		return (ATerm) ATmakeAppl3(if_sym,b,t1,t2);
	} else return NULL;
}

/* and : Bool # Bool -> Bool */
ATerm MCRLmakeAnd(ATerm t1,ATerm t2){
	if (MCRLsym_and && t1 && SortAsTerm(t1)==MCRLterm_bool
			&& t2 && SortAsTerm(t2)==MCRLterm_bool){
		return (ATerm) ATmakeAppl2(MCRLsym_and,t1,t2);
	} else return NULL;
}

/* or : Bool # Bool -> Bool */
ATerm MCRLmakeOr(ATerm t1,ATerm t2){
	if (MCRLsym_or && t1 && SortAsTerm(t1)==MCRLterm_bool
			&& t2 && SortAsTerm(t2)==MCRLterm_bool){
		return (ATerm) ATmakeAppl2(MCRLsym_or,t1,t2);
	} else return NULL;
}

/* not : Bool -> Bool */
ATerm MCRLmakeNot(ATerm t){
	if (MCRLsym_not && t && SortAsTerm(t)==MCRLterm_bool) {
		return (ATerm) ATmakeAppl1(MCRLsym_not,t);
	} else return NULL;
}

/* T : -> Bool */
ATerm MCRLmakeTrue(){
	return MCRLterm_true;
}

/* F : -> Bool */
ATerm MCRLmakeFalse(){
	return MCRLterm_false;
}

/* -------- End of utility functions -------- */



   
/* Modification: More case functions with the same arity must be possible */
          
static void check_case_functions(void) {
  int i;
  ATbool new;
  for(i=0; i<=maxsym; i++) {  
    ATermList enums = check_whether_case_function(i);
    if (enums) {
        ATerm f = MCRLgetFunction(i);
        AFun fsort = ATgetAFun(ATgetArgument((ATermAppl) f,0)); 
        if (MCRLgetNumberOfConstructors(fsort) != ATgetLength(enums))
            ATerror("System error %s <-> %t",ATgetName(fsort), enums);
        /* Constructors of enumerated type */
        if (symint[fsort].sort==0) { 
              // ATwarning("Assignment enums %t CaseFunction %t",
              // enums, f); 
              symterm[fsort].f = (ATerm) enums;
              symint[fsort].sort=1; /* Auxilary flag */
              } 
        else {
             if (!ATisEqual(MCRLgetConstructors(fsort), (ATerm) enums)) {
            ATwarning("Function %t is rejected as case function (inconsistent)",
                      MCRLprint(MCRLgetFunction(i)));
                 return ;
                 }
             }
        if (verbose) ATwarning("%a is a case function(%t)", i, enums);
        if (fsort==ATgetAFun(MCRLterm_bool) && 
            !ATisEqual(ATelementAt(enums,0), MCRLterm_true) &&
            !ATisEqual(ATelementAt(enums,1), MCRLterm_false)) {
  ATwarning("%a has unexpected order of boolean selectors [F,T]", i); 
           ATwarning("May be cause of performance penalty");
           }
        ForceCaseFunction(i);
        if (extend_adt) CexxxIsxEquation(i, (ATerm) ATmakeAppl0(fsort), 
                            (ATerm) ATmakeAppl0(MCRLgetSortSym(i)), 
                            &new);     
        /*
        if (verbose) ATwarning("Function %t is marked as casefunction",
                     MCRLprint(MCRLgetFunction(i)));
        */
        }    
    }
  }
  
static int check_projections(int *new) {
  int i, n=0, r = 0;
  AFun f;
  if (new) *new = 0;
  for(i=0; i<=maxsym; i++) {
  /* ATwarning("QQQ %s %d", ATgetName(i), MCRLgetType(i)); */
    if (symint[i].type==MCRLfunction && ATgetArity(i)==1) { 
       int arg = check_whether_projection(i, &f, new?(&n):NULL);
       if (arg>=0) {
           MCRLsetProjection(f, arg, symterm[i].f);
           if (new) *new += n;
           r++;
           }
    }
  }
  return r;
  }
   
static int check_determinationfunctions(void) {
  int i, n = 0;
  for(i=0; i<=maxsym; i++) {
    if (symint[i].type==MCRLfunction && ATgetArity(i)==1) { 
       ATbool r = check_whether_det(i);
       if (r) {
           ATerm f = MCRLgetFunction(i);
           MCRLsetDetFunction(ATgetAFun(ATgetArgument((ATermAppl)f, 0)), i);
           n++;
           }
    }
  }
  return n;
  }
  
int MCRLregistrateExistingProjections(int *new) {
  check_determinationfunctions();
  return check_projections(new);
  }
    
static void check_eq_functions(void) {
  int i;
  for(i=0; i<=maxsym; i++) 
  if (check_whether_eq_function(i)) 
     MCRLsetType(i, MCRLeqfunction);       
  }
  
              
static AFun CreateSymFromFunc(ATerm f) {
     char *name = ATgetName(ATgetAFun(ATgetArgument((ATermAppl) f, 0))); 
     int n = ATgetLength((ATermList) ATgetArgument((ATermAppl) f, 1));
     return ATmakeAFun(name, n, ATtrue);
     }
 
ATermList Reorder(ATermList eqs) {
     /* Equs with closed rhs's must be placed in from of the rest */
     int n = ATgetLength(eqs), i;
     ATerm *a = (ATerm*) calloc(n, sizeof(ATerm));
     ATbool *c = (ATbool*) calloc(n, sizeof(ATbool));
     ATbool closed = ATfalse;
     ATermList r = ATempty;
     if (!a || !c) ATerror("Cannot allocate array a or c (%d)",n);
     ATprotectArray(a, n);
     for (i=0;!ATisEmpty(eqs);eqs=ATgetNext(eqs),i++) { 
        ATerm eq = ATgetFirst(eqs);
        ATerm rhs = ATgetArgument((ATermAppl) eq, 2);
        ATermList vs = (ATermList) ATgetArgument((ATermAppl) eq, 0);
        closed = ATisEqual(MCRLremainingVars(rhs, vs), vs);
        if (!closed) {a[i] = eq; c[i] = ATfalse;}
        else {
           int j = i-1;
           for (;j>=0 && c[j]==ATfalse;j--) {
              c[j+1] =c[j]; a[j+1] = a[j];
              }
           a[j+1] = eq; c[j+1] = ATtrue;
           }     
        }
     for (i=n-1;i>=0;i--) r = ATinsert(r, a[i]);
     ATunprotect(a); free(a); free(c);
     return r;
     } 
             
static ATerm BuildLHS(ATermTable db, ATerm t, int *varno) {
  int n = ATgetArity(ATgetSymbol(t));
  if (n==0) {
       ATerm u = ATtableGet(db, t);
       if (u) {
         if (ATgetType(u)==AT_INT) return u;
         u = (ATerm) ATmakeInt(*varno);
         ATtablePut(db, t, u);
         (*varno)++;
         return u;
         }
       else return t;
       }
     {
     int i;
     ATerm result;
     DECLA(ATerm, aux, n);
     for (i=0;i<n;i++) 
             aux[i] = BuildLHS(db, ATgetArgument((ATermAppl)t, i), varno);
     result = (ATerm) ATmakeApplArray(ATgetAFun(t), aux);         
     return result;
     }   
 }
 
 static ATerm BuildRHS(ATermTable db, ATerm t) {
  int n = ATgetArity(ATgetSymbol(t));
  if (n==0) {
       ATerm u = ATtableGet(db, t);
       if (u) return u;
       else return t;
       }
     {
     int i;
     ATerm result;
     DECLA(ATerm, aux, n);
     for (i=0;i<n;i++) 
        if ((aux[i] = 
          BuildRHS(db, ATgetArgument((ATermAppl)t, i)))==NULL) 
                 return NULL;
     result = (ATerm) ATmakeApplArray(ATgetAFun(t), aux);         
     return result;
     }   
 }
 
static ATermList BuildVars(ATermTable db, ATermList vs, int varno) {
   ATermList  rs = ATempty;
   int i;
   DECLA(ATerm, a, varno);
   // ATwarning("Buildvars vs=%t", vs);
   for (;!ATisEmpty(vs);vs = ATgetNext(vs)) {
     ATerm v = ATgetFirst(vs);
     ATerm u = ATtableGet(db, ATgetArgument((ATermAppl) v, 0));
     if (u && ATgetType(u)==AT_INT) {
        int n = ATgetInt((ATermInt) u);
        a[n] = v;
        }
     }
   for (i=varno-1;i>=0;i--)  
   if (a[i]) rs = ATinsert(rs, a[i]);   
   return rs;
   }
   
static ATerm NormalEq(ATerm eq) {
   int varno = 0;
   ATermList vs = (ATermList) ATgetArgument((ATermAppl) eq, 0), vs0 = vs;
   ATerm lhs0 = ATgetArgument((ATermAppl) eq, 1),
         rhs0 = ATgetArgument((ATermAppl) eq, 2),
         r = NULL, rhs = NULL, lhs = NULL;
   ATermTable db = ATtableCreate(100,70); 
   for (;!ATisEmpty(vs);vs = ATgetNext(vs)) {
     ATerm v = ATgetFirst(vs);
     ATtablePut(db, ATgetArgument((ATermAppl) v, 0), (ATerm) ATempty);
     }
   lhs = BuildLHS(db, lhs0, &varno);
   rhs = BuildRHS(db, rhs0);
   if (rhs==NULL) {
      if (RWisRewriterNeeded()) 
      ATerror("of equation \"%t = %t\"", MCRLprint(lhs0), MCRLprint(rhs0));
      else {
      ATwarning("of equation \"%t = %t\"", MCRLprint(lhs0), MCRLprint(rhs0));
      return NULL;
      }
      }
   r  = ATmake ("e(<term>,<term>,<term>)", (ATerm) BuildVars(db, vs0, varno), 
   lhs, rhs);
   ATtableDestroy(db);
   /* ATwarning("QQ:Normal form %t", r); */
   return r;
   }
             
static void AddSortsToSymtab(ATermList sorts) {
  for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts)) {
      ATerm sort = ATgetFirst(sorts);
      AFun sym = ATgetAFun(sort);
      EnlargeTables(sym);
      symint[sym].type = MCRLsort;
      symterm[sym].f = (ATerm) ATmakeList0();
      symterm[sym].l = ATmakeList0();
      add_sorts = ATinsert(add_sorts, sort);
     }
  }

AFun MCRLputSort(ATerm sort, ATbool *new) { 
    AFun sym = ATgetAFun(sort);
    if (MCRLgetType(sym)!=MCRLunknown) {
      if (mcrl_report) 
          ATwarning("Sort %a is not added (already present)", sym);
      if (new) *new = ATfalse;
      return sym;
      }
    if (!may_extend_adt || !new) return 0;
    if (mcrl_report)
    ATwarning("Sort %a is added", sym);
    EnlargeTables(sym);
    symint[sym].type = MCRLsort;
    symterm[sym].f = (ATerm) ATmakeList0();
    symterm[sym].l = ATmakeList0();
    add_sorts = ATinsert(add_sorts, sort);
    *new = ATtrue;
    return ATgetAFun(sort);
    }

static ATerm RightFormat(ATerm sig, ATerm *sort) {
    if (sort==NULL) return sig;
    {
    ATerm name = ATgetArgument((ATermAppl) sig, 0);
    ATermList sorts = (ATermList) ATgetArgument((ATermAppl) sig, 1);
    *sort = ATgetArgument((ATermAppl) sig, 2);
    sig = (ATerm) ATmakeApplList(ATmakeAFun(ATgetName(ATgetAFun(name)),
          ATgetLength(sorts), ATtrue), sorts);
    return sig;
    }
    }
    
AFun MCRLputConstructor(ATerm sig, ATerm sort, ATbool *new) {
    if (sort == NULL) sig = RightFormat(sig,  &sort);
    {
    ATermList sortcons = NULL;
    AFun sym = ATmakeAFun(MCRLextendName(ATgetName(ATgetAFun(sig)),
    ATgetArguments((ATermAppl) sig)),ATgetArity(ATgetAFun(sig)), ATtrue),
    sortsym = ATgetAFun(sort);
    if (MCRLgetType(sortsym)==MCRLunknown) 
          ATerror("Sort \"%a\" of constructor: \"%t\" is unknown",
          sortsym, MCRLprint(sig));
    if (MCRLgetType(sym)>=MCRLconstructor) {
      if (MCRLgetType(sym)!=MCRLconstructor) {
          ATwarning("Added constructor %a already exists and is a map", sym);
          if (new) *new = ATfalse; return 0;
          }
      if (MCRLgetSortSym(sym) != ATgetAFun(sort)) {
          ATwarning(
          "Result type differs from existing constructor (%t:%a<->%t)",
           MCRLprint(MCRLgetFunction(sym)), MCRLgetSortSym(sym), sort);
           if (new) *new = ATfalse; return 0;
           }
      if (mcrl_report) 
          ATwarning("Constructor %a is not added (already present)", sym);
      if (new) *new = ATfalse; return sym;
      }
    if (!may_extend_adt || !new) {
        if (mcrl_report) 
        ATwarning("Constructor %a is not added (not permitted)", sym);
        if (new) *new = ATfalse; return 0;
        }
    if (verbose) 
          ATwarning("Constructor %a is added", sym);
    if (MCRLgetType(sortsym)==MCRLunknown) { 
        ATwarning("Sort %a of constructor: \"%t\" is unknown", sortsym, MCRLprint(sig));
        abort();
        }
    sortcons = (ATermList) symterm[sortsym].f;
    sig = (ATerm) ATmakeApplList(sym, ATgetArguments((ATermAppl) sig));
    MCRLsetFunction(sig, MCRLconstructor, sortsym); 
    add_cons = ATinsert(add_cons, ATmake("f(<str>,<term>,<term>)",
         ATgetName(sym), ATgetArguments((ATermAppl) sig), sort));
    if (ATindexOf(sortcons, sig,0)<0) {
         if (symint[sortsym].type == MCRLconstructorsort)
               symterm[sortsym].f = (ATerm) ATinsert(sortcons, sig);
         else {
              symint[sortsym].type = MCRLconstructorsort;
              symterm[sortsym].f = (ATerm) ATmakeList1(sig);
              }
         }
    *new = ATtrue;
    return sym;
    } 
    }    

                     
static void AddConsToSymtab(ATermList cons) {
  ATbool new; 
  for (;!ATisEmpty(cons);cons=ATgetNext(cons)) {
      ATerm con = ATgetFirst(cons);
      AFun sym = CreateSymFromFunc(con);
      ATerm f = (ATerm) ATmakeApplList(sym, 
                 (ATermList) ATgetArgument((ATermAppl) con, 1)),
            sort = ATgetArgument((ATermAppl) con, 2);
      if (!MCRLputConstructor(f, sort, &new)) ATerror("System error %t:%t", f, sort);
      }
  }
      
AFun MCRLputMap(ATerm sig, ATerm sort, ATbool *new) {
     if (sort == NULL) sig = RightFormat(sig,  &sort);
      {
      AFun sym = ATmakeAFun(MCRLextendName(ATgetName(ATgetAFun(sig)),
      ATgetArguments((ATermAppl) sig)),ATgetArity(ATgetAFun(sig)), ATtrue),
      sortsym = ATgetAFun(sort);
      if (MCRLgetType(sortsym)==MCRLunknown) 
          ATerror("Sort %a of map: \"%t\" is unknown", 
          sortsym, MCRLprint(sig));
      {
      ATermList sortmaps = (ATermList) symterm[sortsym].f;
      if (MCRLgetType(sym)>=MCRLconstructor) {
        if (MCRLgetType(sym)==MCRLconstructor) {
          ATwarning("Added map %a already exists and is a constructor", sym);
          return 0;
          }
        if (MCRLgetSortSym(sym) != ATgetAFun(sort)) {
          ATwarning(
          "Result type differs from existing map (%t:%a<->%t)",
           MCRLprint(MCRLgetFunction(sym)), MCRLgetSortSym(sym), sort);
           if (new) *new = ATfalse; return 0;
           }
        if (mcrl_report) 
        ATwarning("Map %a is not added (already present)", sym);
        if (new) *new = ATfalse;
        return sym;
        }
      if (!may_extend_adt || !new) {
        if (mcrl_report) 
        ATwarning("Map %a is not added (not permitted)", sym);
        if (new) *new = ATfalse;
        return 0;
        }
      if (verbose) 
            ATwarning("Map %a is added", sym);
      sig = (ATerm) ATmakeApplList(sym, ATgetArguments((ATermAppl) sig));
      MCRLsetFunction(sig, MCRLfunction, sortsym);
      if (MCRLgetType(sortsym) == MCRLsort) { 
         if (ATindexOf(sortmaps, sig,0)<0) 
               symterm[sortsym].f = (ATerm) ATinsert(sortmaps, sig);
         }
     add_maps = ATinsert(add_maps, ATmake("f(<str>,<term>,<term>)",
           ATgetName(sym), ATgetArguments((ATermAppl) sig), sort));
    *new = ATtrue;
    return sym;
    }
    }
    }
               
static void AddMapsToSymtab(ATermList maps) {
  ATbool new;  
  for (;!ATisEmpty(maps);maps=ATgetNext(maps)) {
      ATerm map = ATgetFirst(maps);
      AFun sym = CreateSymFromFunc(map);
      ATerm f = (ATerm) ATmakeApplList(sym, 
                 (ATermList) ATgetArgument((ATermAppl) map, 1)),
            sort = ATgetArgument((ATermAppl) map, 2);
      if (!MCRLputMap(f, sort, &new)) ATerror("System error %t:%t", f, sort);
      }
  }

static ATermList Unique(ATerm eq) {
  return ATmakeList2(ATgetArgument((ATermAppl) eq, 1),
                     ATgetArgument((ATermAppl) eq, 2));
  }
  
static int IndexOf(ATermList l, ATerm e) {
  int i;
  ATerm e1 = ATgetArgument((ATermAppl) e, 1),
        e2 = ATgetArgument((ATermAppl) e, 2);
  for (i=ATgetLength(l)-1;i>=0;i--, l=ATgetNext(l))
  if (ATisEqual(ATgetArgument((ATermAppl) ATgetFirst(l),1), e1) && 
      ATisEqual(ATgetArgument((ATermAppl) ATgetFirst(l),2), e2)) 
      return ATgetLength(l)-1-i;
  return i;
  }
        
AFun MCRLputEquation(ATerm eq, ATbool *new) {
    if (!(eq=TranslateEq(eq))) 
                ATerror("Undefined equation");              
    {
    ATerm e = NormalEq(eq),
    arg1 = ATgetArgument((ATermAppl) eq, 1),
    arg2 = ATgetArgument((ATermAppl) eq, 2);
    AFun sym = ATgetSymbol(arg1);
    if (e==NULL) return 0;
    if (IndexOf(symterm[sym].l, e)<0) {
         if (!may_extend_adt || !new) {
            if (new) *new = ATfalse;
            if (mcrl_report) PrintEqu(sym, eq,"not"); 
              return 0;
             } else {
            add_eqs = ATinsert(add_eqs, eq);
            symterm[sym].l = ATinsert(symterm[sym].l, e);
            if (mcrl_report) {
               ATwarning("Equation %t = %t is absent",
                    arg1, arg2);
               ATwarning("Equation %t = %t is added",
                    arg1, arg2);
                    }
            *new = ATtrue;
            /* PrintEqu(sym, eq,"");  */      
            return ATgetAFun(arg1);
            }
         }
         else {
            if (mcrl_report)
            ATwarning("Equation %t = %t already present", arg1, arg2);
            /* PrintEqu(sym, eq,"not"); */
            if (new) *new = ATfalse;
            return ATgetAFun(arg1);
        }
    }
    } 

static ATermList RemoveEquations(ATermList eqs, ATermList  reqs) {
    ATermIndexedSet  db = ATindexedSetCreate(1000,80);
    ATermList r = ATempty; ATbool new;
    for (;!ATisEmpty(reqs);reqs=ATgetNext(reqs)) {
         ATerm eq = ATgetFirst(reqs), e;
         if (!(eq=TranslateEq(eq))) 
               ATerror("Undefined equation");
           e = NormalEq(eq); 
           if (e==NULL) continue;
            ATindexedSetPut(db, (ATerm) Unique(e), &new);
            }
    for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
         ATerm eq = ATgetFirst(eqs), e;
         e = NormalEq(eq);
         if (e==NULL) continue;
         if (ATindexedSetGetIndex(db, (ATerm) Unique(e))<0) r = ATinsert(r, eq);
         else {
             AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
             ATermList l = symterm[sym].l;
             int k = IndexOf(l, e);
             symterm[sym].l = ATremoveElementAt(l, k);
             if (verbose) 
              ATwarning("Equation %t = %t is removed", 
              MCRLprint(ATgetArgument((ATermAppl) eq, 1)),
              MCRLprint(ATgetArgument((ATermAppl) eq, 2)));
             }
         }
    ATindexedSetDestroy(db);
    return ATreverse(r);
    }   
               
static void AddEqsToSymtab(ATermList eqs0) {
     ATermList eqs;int i;
     for (eqs=eqs0;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
         ATerm eq = ATgetFirst(eqs), e;
         AFun sym = ATgetSymbol(ATgetArgument((ATermAppl) eq, 1));
         // ATwarning("QQQ %t", eq);
         add_eqs = ATinsert(add_eqs, eq); 
         e = NormalEq(eq);
         if (e==NULL) continue;      
         if (IndexOf(symterm[sym].l, e)<0) {
               symterm[sym].l = ATinsert(symterm[sym].l, e);
               }
         } 
     for (i=0;i<=maxsym;i++)
     if (symint[i].type>=MCRLconstructor)
         symterm[i].l=ATreverse(symterm[i].l);
     }
                                          
static void AllocateSymbolTable(ATerm adt) {
     ATbool new = ATtrue, may_extend_adt0 = may_extend_adt,
     verbose0 = verbose;
     ATermList eqs = (ATermList) ATgetArgument((ATermAppl) adt,1),
     sig = (ATermList) ATgetArgument((ATermAppl) adt ,0);
     ATermList sorts = (ATermList) ATgetArgument(sig,0),
     funcs = (ATermList) ATgetArgument(sig,1),
     maps = (ATermList) ATgetArgument(sig,2);
     may_extend_adt = ATtrue; verbose = ATfalse;
     size = INITSIZE;
     enumsorts.size = 0;
     EnlargeEnumeratedsorts(0);
     if (symint) {
         ATunprotect((ATerm*) symterm);
	 free(symterm); free(symint);
         maxsym  = 0;
         }         
     symint = (SYMINT*) calloc(size, sizeof(SYMINT));
     symterm = (SYMTERM*) calloc(size, sizeof(SYMTERM));
     if (sizeof(SYMTERM)!=2*sizeof(ATerm)) 
         ATwarning("Protection error. Perhaps a portability problem");
     ATprotectArray((ATerm*) symterm, 2*size);
     AddSortsToSymtab(sorts);
     AddConsToSymtab(funcs);
     AddMapsToSymtab(maps);
     AddEqsToSymtab(eqs);
     verbose = verbose0;
     may_extend_adt = may_extend_adt0;
     if (reorder_rules) add_eqs = Reorder(add_eqs);
     if (input_remove) {
       add_eqs = RemoveEquations(add_eqs, MCRLparseEquations(input_remove));
       fclose(input_remove); input_remove = NULL;
       } 
     if (input_add) {
        ReadExtraAdt(input_add);
        fclose(input_add); input_add = NULL;
        }
     MCRLsetAdt(ATmake("d(<term>,<term>)", ATmake("s(<term>,<term>,<term>)",
       ATreverse(add_sorts), ATreverse(add_cons), ATreverse(add_maps)), 
       ATreverse(add_eqs)));
     add_sorts = add_cons = add_maps = add_eqs = ATempty;
     check_eq_functions();
     check_enumerated_sorts();
     check_case_functions();
     /* MCRLsym_ite= */
     if (MCRLputIfFunction(MCRLterm_bool, extend_adt?&new:NULL)==0)
         {if (verbose) ATwarning("No \"if-then-else\" function present");}
     else
         {if (verbose) 
           ATwarning("The map %a is \"if-then-else\" function", MCRLsym_ite);} 
     if (extend_adt) ExtraAndOrNotRules(); 
     }          
     
ATbool MCRLinitialize(void) {
     ATbool r = ATfalse;
     if (filterName && filterName[0]) {
        FILE *fp = NULL;
        if (fileName[0]!='\0') {
            strncat(filterName," ", MCRLsize); 
            strncat(filterName, fileName, MCRLsize);
            }
        fp = Popen(filterName, "r");
        if (verbose) ATwarning("Input filter %s is used", filterName);
        if (!fp) ATerror("Filter %s cannot be invoked");
        r = MCRLinitFile(fp);
        Pclose(fp);
        return r;
        }
     return MCRLinitNamedFile(fileName);
     }
                      
                                      
ATbool MCRLinitializeAdt(ATerm adt) {
   if (first) {
	 initConstants();
         ATprotect(&MCRLtag);
	 MCRLtag = ATmake("<appl>","tag");
	 ATprotect(&projTag);
	 projTag = ATmake("<appl>","projection");
         ATprotect(&depthTag);
	 depthTag = ATmake("<appl>","depth");
	 ATprotect(&currentAdt);
	 vTag  = ATmakeSymbol("v",2, ATfalse);
         ATprotectSymbol(vTag);
	 first = ATfalse;
         add_cons = add_maps = add_sorts = add_eqs = ATempty;
         ATprotect((ATerm*) &add_eqs);
         ATprotect((ATerm*) &add_sorts);
         ATprotect((ATerm*) &add_cons);
         ATprotect((ATerm*) &add_maps);
	 }
    if (!CheckTrueAndFalse(adt)) return ATfalse;
    AllocateSymbolTable(adt);
    return ATtrue;
    }
    
ATbool MCRLisInitialized(void) {return !first;} 
     
ATbool MCRLinitFile(FILE *input) {
    if (first) {ATprotect(&currentProc);ATprotect(&currentSpec);}
    currentSpec = ATreadFromFile(input);
     
    if (!currentSpec || strcmp(ATgetName(ATgetSymbol(currentSpec)),"spec2gen")) {
         ATwarning("Illegal \".tbf\" file format");
	 return ATfalse;
	 }
    currentProc = ATgetArgument((ATermAppl) currentSpec,1);
    return MCRLinitializeAdt(ATgetArgument((ATermAppl) currentSpec,0));
} 

ATbool MCRLinitNamedFile(char *inputFile) {
    if (inputFile && inputFile[0]!='\0') {
      FILE *input = NULL;
      ATbool r = ATfalse;
      if (!(input = fopen(inputFile,"r"))) {
         ATwarning("File %s cannot be opened", inputFile);
	 return ATfalse;
	 }
      r = MCRLinitFile(input);
      fclose(input); return r;
      }
    return MCRLinitFile(stdin);
} 

static void UpdateSpecs(void) {
  if (!ATisEmpty(add_sorts)) {
    ATermList maps, sorts, cons, eqs;
    if (!ATmatch(currentAdt,"d(s(<term>,<term>,<term>),<term>)", 
            &sorts, &cons, &maps, &eqs))
        ATerror("System Match d.. expected: found %t", currentAdt);
    MCRLsetAdt(ATmake("d(<term>,<term>)", ATmake("s(<term>,<term>,<term>)",
       ATconcat(sorts, ATreverse(add_sorts)), cons, maps), eqs)); add_sorts = ATempty;
    }
  if (!ATisEmpty(add_cons)) {
    ATermList maps, sorts, cons, eqs;
    if (!ATmatch(currentAdt,"d(s(<term>,<term>,<term>),<term>)", 
            &sorts, &cons, &maps, &eqs))
        ATerror("System Match d.. expected: found %t", currentAdt);
    MCRLsetAdt(ATmake("d(<term>,<term>)", ATmake("s(<term>,<term>,<term>)",
       sorts,  ATconcat(cons, ATreverse(add_cons)), maps), eqs)); 
       add_cons = ATempty;
    }
  if (!ATisEmpty(add_maps)) {
    ATermList maps, sorts, cons, eqs;
    if (!ATmatch(currentAdt,"d(s(<term>,<term>,<term>),<term>)", 
            &sorts, &cons, &maps, &eqs))
        ATerror("System Match d.. expected: found %t", currentAdt);
    MCRLsetAdt(ATmake("d(<term>,<term>)", ATmake("s(<term>,<term>,<term>)",
       sorts, cons, ATconcat(maps, ATreverse(add_maps))), eqs)); 
       add_maps = ATempty;
    }
  if (!ATisEmpty(add_eqs)) {
    ATerm sig; ATermList eqs;
    if (!ATmatch(currentAdt,"d(<term>,<term>)",&sig, &eqs))
        ATerror("System Match d.. expected: found %t", currentAdt);
    MCRLsetAdt(ATmake("d(<term>,<term>)", sig, 
       ATconcat(ATreverse(add_eqs), eqs))); 
    add_eqs = ATempty;
    }
  }
  
ATerm MCRLgetSpec(void) {
    UpdateSpecs();
    return currentSpec;
}

void MCRLsetSpec(ATerm spec) {
    currentSpec = spec;
    currentProc = (ATerm) ATgetArgument((ATermAppl) spec, 1);
    currentAdt = (ATerm) ATgetArgument((ATermAppl) spec, 0);   
}

ATerm MCRLgetProc(void) {
    return currentProc;
}

void MCRLsetProc(ATerm proc) {
   currentProc = proc;
   if (MCRLgetAdt()) currentSpec = (ATerm) ATmakeAppl2(ATgetAFun(currentSpec), MCRLgetAdt(), proc);
}

ATerm MCRLgetAdt(void) {
  UpdateSpecs();
  return currentAdt;
}

void MCRLsetAdt(ATerm adt) {
   currentAdt = adt;
   if (MCRLgetProc()) currentSpec = (ATerm) ATmakeAppl2(ATgetAFun(currentSpec) , adt, MCRLgetProc());
}

void MCRLwrite(char *outputfile, MCRL_OUTPUTFORMAT format) {
  FILE *output;
  if (outputfile) {
      if (!(output = fopen(outputfile,"w")))
         ATerror("File %s cannot be opened for write", outputfile);
      }
  else output = stdout;
  switch (format) {
    case MCRLtext: ATwriteToTextFile(MCRLgetSpec(), output); break;
    case MCRLbinary: ATwriteToBinaryFile(MCRLgetSpec(), output); break;
    case MCRLundefined: 
    case MCRLsharedText: ATwriteToSharedTextFile(MCRLgetSpec(), output); break;
    case MCRLserializedBinary: ATwriteToSAFFile(MCRLgetSpec(), output); break;
  }
}

void MCRLoutput(void) {
     MCRLwrite(NULL, MCRLformat);
     }
     
ATermList MCRLgetListOfPars(void) {
    return (ATermList) ATgetArgument((ATermAppl) currentProc,1);
}

void MCRLsetListOfSummands(ATermList summands) {
   ATerm proc = currentProc;
   currentProc = (ATerm) ATmakeAppl3(
          ATgetAFun(proc), ATgetArgument((ATermAppl) proc, 0),
          ATgetArgument((ATermAppl) proc, 1), (ATerm) summands);
   currentSpec = (ATerm) ATmakeAppl2(ATgetAFun(currentSpec), MCRLgetAdt(), 
   currentProc);
   }

ATermList MCRLgetListOfVars(ATerm summand) {
    return (ATermList) ATgetArgument((ATermAppl) summand, 0);
    }

ATermList MCRLgetListOfInitValues(void) {
    return (ATermList) ATgetArgument((ATermAppl) currentProc,0);
    }

int MCRLgetNumberOfPars(void) {
    return ATgetLength(ATgetArgument((ATermAppl) currentProc,1));
    }

int MCRLgetNumberOfVars(ATerm summand) {
    return ATgetLength((ATermList) ATgetArgument((ATermAppl) summand, 0));
    }

int MCRLgetNumberOfSummands(void) {
    return ATgetLength((ATermList) ATgetArgument((ATermAppl) currentProc,2));
    }
    
ATermList  MCRLgetListOfSummands(void) {
    return (ATermList) ATgetArgument((ATermAppl) currentProc,2);
    } 

static int _MCRLstate2Number(ATerm v) {
    if (ATgetSymbol(v)==MCRLsym_one) return 1;
    if (ATgetSymbol(v)==MCRLsym_x2p0) return 
       2*_MCRLstate2Number(ATgetArgument(v,0));
    if (ATgetSymbol(v)==MCRLsym_x2p1) return
       2*_MCRLstate2Number(ATgetArgument(v,0)) + 1;
    return 0;
}

int MCRLstate2Number(ATerm v) {
    return _MCRLstate2Number(v);
    }

static ATbool Insert(ATerm *a, int i, ATerm t)  {
    a[i] = NULL;
    if (i==0 || ATgetAFun(a[--i])<ATgetAFun(t)) return ATfalse; 
    /* ATwarning("Insert %d %t", i, t); */
    for (;i>=0 && ATgetAFun(a[i])>=ATgetAFun(t); i--) {
       a[i+1] = a[i];
       }
    /* i<0 || (a[i]<t && a[i+2]==a[i+1] && a[i+2]>=t */ 
    i++;
    a[i] = (ATisEqual(a[i],t))?NULL:t;
    return ATtrue;    
    }
    
static ATermList Union(ATermList s1, ATermList s2) {
    int n1 = ATgetLength(s1), n2 = ATgetLength(s2);
    if (n1 == 0) return s2;
    if (n2 == 0) return s1;
    if (ATisEqual(s1,s2)) return s1;
         {
         int i, pt =0;
         DECLA(ATerm, a, n1+n2);
         ATermList r = ATempty;
         for (;!ATisEmpty(s1);s1 = ATgetNext(s1), pt++) a[pt] = ATgetFirst(s1);
         for (;!ATisEmpty(s2) && Insert(a, pt, ATgetFirst(s2));
             s2 = ATgetNext(s2), pt++);
         for (i=pt-1;i>=0;i--) 
               if (a[i]) r = ATinsert(r, a[i]);
         return ATconcat(r, s2);
         } 
    }
    
static ATermList occurringVars(ATerm t) {
    AFun s = ATgetSymbol((ATermAppl) t);
    int n = ATgetArity(s);
    static ATermTable occ_db = NULL;
    if (n == 0) {
        return MCRLgetType(s)==MCRLvariable?symterm[s].l:ATempty;
        }
    if (!occ_db) occ_db = ATtableCreate(10,70); 
    {
    int i;
    ATermList r;
    if (n<5) {
       r = (ATermList) ATtableGet(occ_db , t) /* NULL */;
       if (r) return r;
       }  
    for (r=ATempty, i=0;i<n;i++) 
       r = Union(r, occurringVars(ATgetArgument((ATermAppl) t, i)));
    if (n<5) ATtablePut(occ_db, t,(ATerm) r); 
    return r;
    }
    }

static ATbool NotFound(AFun *a,AFun s, int lb, int ub) {
    int i;
    for (i=lb;i<ub && s>a[i];i++);
    return i>=ub || s<a[i];
    }
    
ATbool MCRLisClosedTerm(ATerm t) {
    return ATisEmpty(occurringVars(t));
    }
            
ATermList MCRLremainingVars(ATerm t, ATermList vars) {
    int len = ATgetLength(vars);
    if (len==0) return vars;
       {
       ATermList r = occurringVars(t);
       if (!ATisEmpty(r)) {
          int i, n = ATgetLength(r), n1 = n-1;
          DECLA(AFun, ra, n);
          for (i=0;i<n;i++, r = ATgetNext(r)) { 
                 ra[i] = ATgetAFun(ATgetFirst(r));
                 /* fprintf(stderr,"%d ",ra[i]); */
                 }
          /* ATwarning("r = %t", r); */
          for (r= ATempty, i=0;!ATisEmpty(vars);vars = ATgetNext(vars)) { 
             ATerm var = ATgetFirst(vars), 
             varname = (ATgetArity(ATgetAFun(var))==2?
                 ATgetArgument((ATermAppl)var, 0): var);
             AFun varsym = ATgetAFun(varname);
             /* ATwarning("QQ r = %t varname = %t", r, varname); */
             if (varsym<ra[0] || varsym>ra[n1] ||  
                  NotFound(ra, varsym, 0, n))
                  r = ATinsert(r, var);   
             }
          r = ATreverse(r);
          } else r = vars; 
       return r;
       }   
    }
     
static int GetDepth(ATerm t) {         
     return ATgetInt((ATermInt) ATgetAnnotation(t, depthTag));
     }
     
static ATerm SetDepth(ATerm t, int d) { 
     return ATsetAnnotation(t, depthTag, (ATerm) ATmakeInt(d));
     }
             
static ATermIndexedSet sortdb = NULL;

static double NumberOfElements(ATerm sort) {
     ATbool new;
     double result = 0; 
     ATermList cs = MCRLgetMapsIfNotConstructors(ATgetAFun(sort));
     ATindexedSetPut(sortdb, sort, &new);
     if (!new) return -1;
     for (;!ATisEmpty(cs);cs=ATgetNext(cs)) {
         ATermAppl c = (ATermAppl) ATgetFirst(cs);
         int i, n = ATgetArity(ATgetAFun(c));
         double r;
         for (r=1, i=0;i<n;i++) {
           double v = NumberOfElements(ATgetArgument(c, i));
           if (v<0) return -1;
           r *= v;
           }
         result += r;
         }
     ATindexedSetRemove(sortdb, sort);
     return result;
     }
     
double MCRLgetNumberOfElements(AFun sort) {
     double result;
     sortdb = ATindexedSetCreate(100,50);
     result= NumberOfElements((ATerm) ATmakeAppl0(sort));
     /* ATwarning("QQQ %t", ts); */
     ATindexedSetDestroy(sortdb);
     return result;
     } 
/* expand(sort) = [f_0(expand(sort_0^0),...,expand(sort_n^0)),...,
                   f_m(expand(sort_0^m),...,expand(sort_k^m))]
*/ 
#define RECURSIVE 10000000  
 
static ATermList Expand(ATerm sort, int *depth) {
/* Expand(s) -> [c1(Expand(s1)...Expand(sn)),c2(Expand(z1)...Expand(zm))] */
     ATermList cs = MCRLgetMapsIfNotConstructors(ATgetAFun(sort)), r = ATempty;
     ATbool new; int m = ATgetLength(cs), k=0;
     DECLA(ATerm, d, m);
     ATindexedSetPut(sortdb, sort, &new);
     if (!new) { 
          *depth = RECURSIVE;
          return ATempty;
          }
     for (;!ATisEmpty(cs);cs=ATgetNext(cs)) {
         ATerm c =  ATgetFirst(cs);
         int i, n = ATgetArity(ATgetAFun((ATermAppl)c)), recursive;
         DECLA(ATerm, a, n);
         *depth = 0;
         for (recursive=ATfalse,i=0;i<n;i++) {
           int val;
           ATbool recdef = ATfalse;
           ATermList es = Expand(ATgetArgument(c, i), &val);
           if (ATisEmpty(es)) recursive = ATtrue;
           a[i] = (ATerm) es;
           *depth = val+1>*depth?val+1:*depth;
           }
         c = SetDepth((ATerm) ATmakeApplArray(ATgetAFun(c), a), *depth);
         if (! recursive) {
           for (i=k-1;i>=0 && GetDepth(d[i])>*depth;i--) 
                       d[i+1]=d[i];
           d[i+1] = c;
           k++;
           }
         }
       for (k--;k>=0;k--)  r = ATinsert(r, d[k]); 
       *depth = ATisEmpty(r)?RECURSIVE:GetDepth(d[0]);
       ATindexedSetRemove(sortdb, sort);
       return r;
     }
          
static ATerm FirstPath(ATermList expand) {
     ATerm t = ATgetFirst(expand);
     int n = ATgetArity(ATgetAFun(t));
     if (n==0) return t;
     {
     int i;
     DECLA(ATerm, a, n);
     for (i=0;i<n;i++) {
         a[i] = FirstPath((ATermList) ATgetArgument(t,i));
         }
     return (ATerm) ATmakeApplArray(ATgetAFun(t), a);
     }
     }
                            
ATerm MCRLdummyVal(AFun sort) {
     ATermList ts = NULL; ATerm r = NULL;
     int depth; 
     ATerm sortterm = (ATerm) ATmakeAppl0(sort);
     static ATermTable sorthash = NULL;
/* ATwarning("MCRLdummyVal %a", sort); */
     if (!sorthash) sorthash = ATtableCreate(30,70);
     if ((r=ATtableGet(sorthash, sortterm))!=NULL) return r;
     // ATwarning("Number of elements of %a: %f", sort, d);
     sortdb = ATindexedSetCreate(100,50);
     ts = Expand(sortterm, &depth);
     /* ATwarning("After expand ts = %t depth = %d", ts, depth); */
     if (ATisEmpty(ts)) {ATindexedSetDestroy(sortdb);return NULL;}
     r = FirstPath(ts);
     // ATwarning("Dummy = %t remainder %t", r, ts);
     ATindexedSetDestroy(sortdb);
     r = ATremoveAllAnnotations(r);
     /* ATwarning("MCRLdummyVal return %a %t", sort,r); */
     ATtablePut(sorthash, sortterm, r);
     return r;
     }

static int isFiniteSort_rec(AFun s, ATermIndexedSet a)
{ int i=0; 
  ATbool new=0;
  { ATermList l=MCRLgetConstructors(s);
    if (ATisEmpty(l))
    { /* sort is not a constructorsort, so it may have
       * an infinite number of elements */
      return 0; 
    }

    ATindexedSetPut(a,(ATerm)ATmakeAppl0(s),&new);
    if (new==0)
    { /* s was in a, meaning that we have detected a loop.
	 s in not necesarily finite */
      return 0;
    }

    for( ; !ATisEmpty(l) ; l=ATgetNext(l) )
    { AFun f=ATgetAFun(ATgetFirst(l));
      ATerm t=MCRLgetFunction(f);
      for(i=0 ; i<ATgetArity(f) ; i++)  
      { if (isFiniteSort_rec(ATgetAFun(ATgetArgument(t,i)),a)==0)
	return 0;
      }
    }
    ATindexedSetRemove(a,(ATerm)ATmakeAppl0(s));
    return 1;
} }
     
int MCRLisFiniteSort(AFun s)
{ /* This function returns 1 if the sort s is `finite' otherwise
     a 0 is returned. We inductively define that a sort s is finite
     iff 
     1 there is at least one constructor function with target sort
       s. In other words s is a constructorsort (s is an MCRLconstructorsort
       or an MCRLenumeratedsort) and
     2 all argument sorts of each constructor with target sort s are finite.
  */
  int r;
  ATermIndexedSet a=ATindexedSetCreate(10,50);
  if (verbose) ATfprintf(stderr,"Is %s a finite sort?: ",ATgetName(s));
  r=isFiniteSort_rec(s,a);
  ATindexedSetDestroy(a);
  if (verbose)
  { if (r) ATfprintf(stderr,"yes\n");
         else  ATfprintf(stderr,"no\n");
  }
  return r;
}

static int increase(ATermList *argloper, ATermList *allargs, int index)
{ /* find the lexicographic next element in 
     argloper, where allargs contain all elements. Deliver 1 if
     a next element could be found. Otherwise deliver 0.
  */
  int i;

  for(i=index ; i>=0 ; i--)
  { if (ATisEmpty(ATgetNext(argloper[i])))
    { argloper[i]=allargs[i];
    }
    else 
    { argloper[i]=ATgetNext(argloper[i]);
      return 1;
    }
  }
  return 0;
}
 
static ATermList ReturnVariable(AFun s, int idx) {
    /* Return Variable  */
    ATerm v = 
      (ATerm)ATmakeAppl0(MCRLextendNameSymbol(ATempty,"|%d", idx));
    MCRLdeclareVar(ATmake("v(<term>, <term>)", v, 
           (ATerm) ATmakeAppl0(MCRLgetSortSym(s))));
    return ATmakeList1(v);
    }
         
static ATermList generateElementsOfConstructorSort_rec(AFun s, ATerm occ, 
     ATermIndexedSet a, ATbool finite)
{ int i=0;
  ATbool new;
  ATermList l=MCRLgetConstructors(s);
  ATermList r=ATempty;
  int max=0;
  ATermList l1;
  long idx;
  if (ATisEmpty(l))
  { /* sort is not a constructorsort, so it may have
     * an infinite number of elements */
    return NULL; 
  }
  if (finite || occ) {
  idx = ATindexedSetPut(a, finite?(ATerm) ATmakeAppl0(s):occ ,&new);
  if (new==0) {
     if (finite)
          { /* s was in a, meaning that we have detected a loop.
               s in not necesarily finite */
            return NULL;
          }
     else  return ReturnVariable(s, idx);     
     } if (!finite) return ReturnVariable(s, idx);  
   }
 
  /* First determine the largest arity of any constructor
   * of sort s */

  for(l1=l ; !ATisEmpty(l1) ; l1=ATgetNext(l1) )
  { if (max<ATgetArity(ATgetAFun(ATgetFirst(l1))))
    { max=ATgetArity(ATgetAFun(ATgetFirst(l1)));
    }
  }
  { 
  DECLA(ATermList, allargs, max); 
  DECLA(ATerm, args, max);
  DECLA(ATermList, argloper, max);
  for( ; !ATisEmpty(l) ; l=ATgetNext(l) )
  { AFun f=ATgetAFun(ATgetFirst(l));
    ATerm t=MCRLgetFunction(f);
    for(i=0 ; i<ATgetArity(f) ; i++)  
    { allargs[i]=generateElementsOfConstructorSort_rec(
         ATgetAFun(ATgetArgument((ATermAppl) t, i)),
	 (ATerm) (finite?NULL:ATmakeAppl1(
             ATmakeAFun(ATgetName(f),1, ATfalse),(ATerm) ATmakeInt(i))),
      a, finite);
      if (allargs[i]==NULL) return NULL;
    }
    /* all lists of elements to be used as arguments are given
     * in arg. The only thing to be done is to transform the arguments
     * in a total list of elements */

    for(i=0 ; i<ATgetArity(f) ; i++)
    { argloper[i]=allargs[i];
    }

    do
    { for(i=0 ; i<ATgetArity(f) ; i++)
      { args[i]=ATgetFirst(argloper[i]);
      }
      r=ATinsert(r,(ATerm)ATmakeApplArray(f,args));
    }
    while (increase(argloper,allargs,ATgetArity(f)-1));
  }
  if (finite) 
      ATindexedSetRemove(a, (ATerm)ATmakeAppl0(s));
  return r;
  }
} 

static ATermList MCRLgenerateElementsOfConstructorSort(AFun s)
{ /* This function returns a list of all elements of a sort s. 
     The order in which the terms is generated is deterministic
     and ought to be the same when this routine in invoked more
     often, except if new sorts or constructor functions have been
     added to the adt database.
  */
  
   ATermList r;
   ATermIndexedSet a=ATindexedSetCreate(10,50);
   r=generateElementsOfConstructorSort_rec(s,NULL,a, ATfalse);
   /* ATwarning("QQQ r=%t", r); */
   ATindexedSetDestroy(a);
   return r;
}

ATermList MCRLgenerateElementsOfFiniteSort(AFun s)
{ /* This function returns a list of all elements of a sort s. 
     In case the list is not finite, it will not terminate.
     If sort s is not finite, this function yields NULL.
     See also MCRLisFinitSort which contains the definition when
     a sort is considered finite.
     The order in which the terms is generated is deterministic
     and ought to be the same when this routine in invoked more
     often, except if new sorts or constructor functions have been
     added to the adt database.
  */
  
   ATermList r;
   ATermIndexedSet a=ATindexedSetCreate(10,50);
   r=generateElementsOfConstructorSort_rec(s,NULL,a, ATtrue);
   ATindexedSetDestroy(a);
   return r;
}
                     
char *MCRLextendName(char *n, ATermList sorts)
{ unsigned int resultlength;
  char *sort;
  ATermList sorts1;
  static char *buffer=NULL;
  static unsigned int buffer_length=0;

  /* first determine length of result */
  sorts1=sorts;
  if (!MCRLoldTbf && strchr(n,'#')) return n;
  if (!MCRLoldTbf && ATisEmpty(sorts1)) resultlength = strlen(n)+2;
  else
  for( resultlength=strlen(n)+1; (!ATisEmpty(sorts1)); sorts1=ATgetNext(sorts1))
  { if (!ATmatch(ATgetFirst(sorts1),"<str>",&sort))
      {ATwarning("Expect string %t",ATgetFirst(sorts1));abort();}
    resultlength=resultlength+strlen(sort)+1;
  }
  if (resultlength>buffer_length)
  { if (buffer==NULL)
    { buffer=malloc(resultlength+64);
      buffer_length=resultlength+64;
    }
    else 
     { buffer=realloc(buffer,resultlength*2);
       buffer_length=resultlength*2;
     }
    if (buffer==NULL) ATerror("Cannot extend string buffer");
  }
  sorts1=sorts;
  if (!MCRLoldTbf && ATisEmpty(sorts1)) {
      strcpy(buffer,n);
      strcat(buffer,"#");
      }
  else
  for( strcpy(buffer,n); (!ATisEmpty(sorts1)); sorts1=ATgetNext(sorts1))
  { if (!ATmatch(ATgetFirst(sorts1),"<str>",&sort))
        ATerror("Expect string %t",ATgetFirst(sorts1));
    strcat(buffer,"#");
    strcat(buffer,sort);
  }
  return buffer;
}


static char *make_message(const char *fmt, va_list ap) {
     /* Guess we need no more than 30 bytes. */
     int n; 
     static int size = 0;
     static char *p = NULL;
     if (size==0) {
        size = 30;
        if ((p = malloc (size)) == NULL)
            ATerror("make_message: Out of memory size=%d", size);
        }
     /* Try to print in the allocated space. */
     n = vsnprintf (p, size, fmt, ap);
     /* If that worked, return the string. */
     if (n > -1 && n < size)
        return p;
     /* Else try again with more space. */
     if (n > -1)    /* glibc 2.1 */
        size *= 2;
     else           /* glibc 2.0 */
        size *= 2;  /* twice the old size */
     if ((p = realloc (p, size)) == NULL)
       ATerror("make_message: Out of memory size=%d", size);
     /* ATwarning("size = %d", size); */ 
     return NULL;
   }
   
AFun MCRLextendSymbol(AFun *sorts, int len, char *format, ...) { 
  int resultlength, i;
  char *s;
  va_list ap;
  do {
     va_start(ap, format);
     s = make_message(format, ap);
     va_end(ap);
     } while (s==NULL);
  /* first determine length of result */
  if (strchr(s,'#')) return ATmakeAFun(s, len, ATtrue);
  for(i=0,resultlength=strlen(s)+2; i<len; i++) resultlength+=
         (strlen(ATgetName(sorts[i]))+1);
  {
  DECLA(char, buffer,resultlength);
  for(i=0,strcpy(buffer,s); i<len; i++) { 
    strcat(buffer,"#");
    strcat(buffer,ATgetName(sorts[i]));
    }
  if (!MCRLoldTbf && len==0) strcat(buffer,"#");
  return ATmakeAFun(buffer, len, ATtrue);
  }
  }

static char *MCRLextendNameString(ATermList sorts, char *format,...) {
  va_list ap;
  char *s;
  do {
     va_start(ap, format);
     s = make_message(format, ap);
     va_end(ap);
     } while (s==NULL);
  return MCRLextendName(s, sorts?sorts:ATempty);
  }
    
static AFun MCRLextendNameSymbol(ATermList sorts, char *format,...) {
  va_list ap;
  char *s;
  do {
     va_start(ap, format);
     s = make_message(format, ap);
     va_end(ap);
     } while (s==NULL);
  return
  ATmakeAFun(MCRLextendName(s, sorts?sorts:ATempty), sorts?ATgetLength(sorts):0, ATtrue);   
  }
  
static AFun MCRLnextSymbol(AFun s) {
  /* name#sort#... -> name'<n>#sort#... -> name'<n+1>'#sort#... */
  char *c = ATgetName(s);
  char *buf = calloc(strlen(c)+20, sizeof(char)), 
       *tail = calloc(strlen(c), sizeof(char)), *suffix;
  int cnt;
  AFun result;
  if (!buf) ATerror("Cannot allocate buf (%d)", strlen(c));
  strcpy(buf, c);
  strtok(buf,"#");
  strcpy(tail, buf + strlen(buf)+1);
  suffix = strrchr(buf,'\'');
  if (suffix== NULL || sscanf(suffix+1, "%d", &cnt)<1) strcat(buf,"'1");
  else
       sprintf(suffix+1,"%d", cnt+1);
  strcat(buf,"#");strcat(buf, tail);
  result = ATmakeAFun(buf, ATgetArity(s), ATtrue);
  free(tail); free(buf);
  return result;
  }
  
ATerm MCRLuniqueTerm(char *n, ATermList sorts) {
   ATerm t = ATmake("<str(<list>)>",MCRLextendName(n, sorts), sorts);
   int cnt = 1;
   for (;MCRLgetType(ATgetAFun(t))!=MCRLunknown;cnt++) {
      AFun s = MCRLnextSymbol(ATgetAFun(t));
      t = (ATerm) ATmakeApplList(s, sorts);   
      }
   return t;
   }
       
static ATerm MCRLuniqueTermF(ATermList sorts, char *format,...) {
   va_list ap;
   char *s;
   do {
     va_start(ap, format);
     s = make_message(format, ap);
     va_end(ap);
     } while (s==NULL);
   {
   AFun sym = 
   ATmakeAFun(MCRLextendName(s, sorts?sorts:ATempty), sorts?ATgetLength(sorts):0, ATtrue);
   while (MCRLgetType(sym)!=MCRLunknown) sym = MCRLnextSymbol(sym);
   if (!sorts) return (ATerm) ATmakeAppl0(sym);
   return (ATerm) ATmakeApplList(sym, sorts);  
   } 
   }
  
void MCRLhelp(void) {
     Pr("General options of the MCRL library are:");
     if (!outputFile) {
     Pr("-ascii:\t\t\twrites .tbf file in ascii code");
     Pr("-taf:\t\t\tas -ascii, however in shared representation");
     Pr("-baf:\t\t\twrites .tbf file in binary format");
     Pr("-saf:\t\t\twrites .tbf file in serialized binary format");
     }
     Pr("-no-extend-adt:\t\tabsolutely forbidden to extend the adt");
     Pr("-may-extend-adt:\tonly if it is strict necessary (default)");
     Pr("-extend-adt:\t\textend with standard function and its equations");
     Pr("-mcrl-hash:\t\tuses hash table during printing");
     Pr("-reorder-rules:\t\trewrite rules will be reordered such");
     Pr("\t\t\tthat the rules with closed rhs's occur first");
     Pr("-verbose:\t\tprints information messages during run");
     Pr("-add <file name>:\treads extra rewrite rules (in .mcrl format)");
     Pr("-rem <file name>:\tdeletes rewrite rules (in .mcrl format)");
     }

void MCRLdeclareVar(ATerm varterm) { 
     AFun var = ATgetAFun(ATgetArgument(varterm,0)),
     srt = ATgetAFun(ATgetArgument(varterm,1));
     EnlargeTables(var);
     symint[var].type = MCRLvariable;
     symint[var].sort = srt;
     symterm[var].f = (ATerm) ATmakeAppl0(var);
     symterm[var].l = ATmakeList1(symterm[var].f);
     }
     
void MCRLdeclareVars(ATermList vars) {
     for (;!ATisEmpty(vars);vars = ATgetNext(vars)) 
       MCRLdeclareVar(ATgetFirst(vars)); 
     }
     
void MCRLdeclareVarName(ATerm varterm) { 
     AFun var = ATgetAFun(varterm);
     EnlargeTables(var);
     symint[var].type = MCRLvariable;
     symterm[var].f = (ATerm) ATmakeAppl0(var);
     symterm[var].l = ATmakeList1(symterm[var].f);
     }
     
void MCRLdeclareVarNames(ATermList vars) {
     for (;!ATisEmpty(vars);vars = ATgetNext(vars))
      MCRLdeclareVarName(ATgetFirst(vars));
     }
     
void MCRLundeclareVar(ATerm varterm) { 
     AFun var = ATgetAFun(ATgetArgument(varterm,0));
        if (var<size && symint[var].type != MCRLunknown) {
          if (symint[var].type==MCRLvariable) {
             symint[var].type = MCRLunknown;
             symterm[var].f = NULL;
             symterm[var].l = NULL;
             }
          else ATerror("Not permitted to undeclare symbol %a", var);
          }
     }
     
void MCRLundeclareVars(ATermList vars) {
     for (;!ATisEmpty(vars);vars = ATgetNext(vars)) 
       MCRLundeclareVar(ATgetFirst(vars)); 
     }
     
void MCRLundeclareVarName(ATerm varterm) { 
     AFun var = ATgetAFun(varterm);
     if (var<size && symint[var].type != MCRLunknown) {
       if (symint[var].type==MCRLvariable) {
          symint[var].type = MCRLunknown;
          symterm[var].f = NULL;
          symterm[var].l = NULL; 
          }
        else ATerror("Not permitted to undeclare symbol %a", var);
       }
     }
     
void MCRLundeclareVarNames(ATermList vars) {
     for (;!ATisEmpty(vars);vars = ATgetNext(vars))
      MCRLundeclareVarName(ATgetFirst(vars));
     } 
         
void MCRLdeclareSort(AFun nsort, MCRLsymtype type, ATermList constructors) {
     EnlargeTables(nsort);
     symint[nsort].type = type;
     symterm[nsort].f = (ATerm) constructors;
     symterm[nsort].l = ATempty;
     }
     
void MCRLsetFunction(ATerm f, MCRLsymtype type, AFun fsort) {
     AFun fsym = ATgetAFun(f);
     EnlargeTables(fsym);
     symint[fsym].type = type;
     symint[fsym].sort = fsort;
     symterm[fsym].f = f;
     symterm[fsym].l = ATempty;
     }
     
ATerm MCRLgetFunction(AFun fsym) {
     return symterm[fsym].f;
     }
     
void MCRLdeclareFunction(ATerm f, MCRLsymtype type, AFun fsort) {
     MCRLsetFunction(f, type, fsort);
     }
                    
void MCRLassignSort(AFun var, AFun vsort) {
     symint[var].sort = vsort;
     }
           
MCRLsymtype MCRLgetType(AFun s) {
   if (s<=maxsym)
      return symint[s].type;
   return MCRLunknown;
   }
   
MCRLsymtype MCRLgetTypeTerm(ATerm t) {
   if (ATgetType(t)==AT_INT) return MCRLvariable;
   return MCRLgetType(ATgetAFun(t));
   }
      
void MCRLsetType(AFun s, MCRLsymtype type) {
   EnlargeTables(s);
   symint[s].type = type;
   }
    
ATermList MCRLgetConstructors(AFun fsort) {
     if (MCRLgetType(fsort) == MCRLconstructorsort || 
         MCRLgetType(fsort) == MCRLenumeratedsort)
        return (ATermList) symterm[fsort].f;
     return ATempty;
     }

void MCRLsetConstructors(AFun fsort, ATermList cons) {
     symterm[fsort].f = (ATerm) cons;
     }
     
ATermList  MCRLgetAllFunctions(void) {
     int i;
     ATermList r = ATempty;
     for (i=0;i<=maxsym;i++)
     if (symint[i].type>=MCRLconstructor)
        r = ATinsert(r,  symterm[i].f);
     return ATreverse(r);
     }
     
ATermList  MCRLgetAllSorts(void) {
     int i;
     ATermList r = ATempty;
     for (i=0;i<=maxsym;i++)
     if (symint[i].type>=MCRLsort && symint[i].type<=MCRLenumeratedsort)
        r = ATinsert(r,  (ATerm) ATmakeAppl0(i));
     return ATreverse(r);
     }
              
static ATermList MCRLgetMapsIfNotConstructors(AFun fsort) {
     return (ATermList) symterm[fsort].f;
     }
          
ATermList MCRLgetRewriteRules(AFun fsym) {
     if (MCRLgetType(fsym)==MCRLunknown) return NULL;
     return symterm[fsym].l;
     } 
         
int MCRLgetNumberOfConstructors(AFun fsort) {
     return ATgetLength(MCRLgetConstructors(fsort));
     }
                   
ATermList MCRLgetCaseFunctions(AFun fsort) {
     return symterm[fsort].l;
     }
              
ATermList MCRLgetCaseSelectors(AFun casesym) {
     return (ATermList)
     symterm[ATgetAFun(ATgetArgument((ATermAppl) symterm[casesym].f, 0))].f;
     }
                  
AFun MCRLgetSort(ATerm t) {
     return MCRLgetSortSym(ATgetAFun(t));
     }
     
AFun MCRLgetSortSym(AFun s) {
     if (s>maxsym) return 0;
     if (MCRLgetType(s)==MCRLunknown) return 0;
     return symint[s].sort;
     }
     
AFun MCRLgetSortSymbol(AFun s) {return MCRLgetSortSym(s);}
          
char *MCRLgetName(ATerm t) {
     return MCRLgetNameSymbol(ATgetAFun(t));
     }
     
static char *MCRLgetNameTerm(ATerm t) {
     return MCRLgetNameSymbol(ATgetAFun(t));
     }
          
static char *MCRLgetNameSymbol(AFun s) {
     return MCRLgetNameString(ATgetName(s));
     }
          
static char *MCRLgetNameString(char *s) {
     static char name[MCRLsize];
     strncpy(name, s, MCRLsize);
     s=strtok(name,"#");
     return s?s:"";
     }

static ATerm ApplHeader(ATerm t) {
     if (ATgetType(t)==AT_INT) {
         char buf[10];
         sprintf(buf,"#v%d", ATgetInt((ATermInt) t));
         return (ATerm) ATmakeAppl0(ATmakeAFun(buf, 0, ATtrue));
         }
     return t; 
     }
       
ATerm MCRLprint(ATerm t) {
    ATerm result = (db_term_print
      && ATgetType(t)==AT_APPL && ATgetArity(ATgetAFun(t))>0)?
          ATtableGet(db_term_print, t): NULL;
    if (result!=(ATerm) NULL) return result;
    /* ATprotectSymbol(s); */
    t = ApplHeader(t);
    {
    int n = ATgetArity(ATgetSymbol(t)), i;
    AFun s = ATmakeSymbol(MCRLgetName(t), n, ATfalse);
    DECLA(ATerm, aux, n);
    for (i=0;i<n;i++) 
            aux[i] = MCRLprint(ATgetArgument((ATermAppl)t, i));
    result = (ATerm) ATmakeApplArray(s, aux);
    if (db_term_print)
        ATtablePut(db_term_print, t, result);   
   return result; 
   }  
   }
   
ATermList MCRLprintList(ATermList args) {
     ATermList result = ATmakeList0();
     for (;!ATisEmpty(args);args=ATgetNext(args))
          result = ATinsert(result, MCRLprint(ATgetFirst(args)));
     return ATreverse(result);
     }
   
void MCRLsetFilter(char *name) { 
     if (!filterName) {
         filterName= (char*) 
         calloc(MCRLsize, sizeof(char));
         }  
     strncpy(filterName, BINDIR, MCRLsize);
     strncat(filterName, "/", MCRLsize);
     strncat(filterName, name, MCRLsize);
     }
     
void MCRLsetProjection(AFun f, int arg, ATerm proj) {
     AFun fsort = MCRLgetSortSym(f);
     ATermList cs = MCRLgetMapsIfNotConstructors(fsort);
     ATerm t = NULL, a = NULL, p = NULL;
     int pos = PosInList(cs, f);
     ATerm ann = ATgetAnnotation((ATerm) cs, projTag);
     if (pos<0) ATerror("Something wrong with %t %s", cs, ATgetName(f));
     t = ATelementAt(cs, pos);
     a = ATgetArgument((ATermAppl) t, arg);
     p = ATgetAnnotation(a, projTag);
     if (!p) {
          a = ATsetAnnotation(a, projTag, proj);
          t = (ATerm) ATsetArgument((ATermAppl) t, a, arg);
          /* ATwarning("Set projection %t",t); */
          }
     cs = ATreplace(cs, t, pos);
     if (ann) cs = (ATermList) ATsetAnnotation((ATerm) cs, projTag, ann);
     symterm[fsort].f = (ATerm) cs;
     } 
     
ATerm MCRLgetProjection(AFun f, int arg) {
     ATermList cs = MCRLgetMapsIfNotConstructors(MCRLgetSortSym(f));
     ATerm t = NULL, a = NULL;
     int pos = PosInList(cs, f);
     if (pos<0) ATerror("Something wrong with %t %s", cs, ATgetName(f));
     t = ATelementAt(cs, pos);
     a = ATgetArgument((ATermAppl) t, arg); 
     return ATgetAnnotation(a, projTag); 
     }
     
void MCRLsetDetFunction(AFun fsort, AFun det) {
     ATermList cs = MCRLgetConstructors(fsort);
     ATermList dets = (ATermList) ATgetAnnotation((ATerm) cs, projTag);
     if (!dets) dets = ATmakeList0();
     if (det>0) dets = ATappend(dets, MCRLgetFunction(det));
     symterm[fsort].f = (ATerm) ATsetAnnotation((ATerm) cs, projTag, 
                        (ATerm) dets);
     }
     
void MCRLsetDetFunctions(AFun fsort, ATermList dets) {
     if (MCRLgetDetFunctions(fsort)) {
         symterm[fsort].f = 
	    ATremoveAllAnnotations((ATerm) symterm[fsort].f);
         };
     MCRLsetDetFunction(fsort, 0);
     for (;!ATisEmpty(dets);dets=ATgetNext(dets))
         {ATerm det = ATgetFirst(dets);
          MCRLsetDetFunction(fsort, ATgetAFun(det));
         }
     }
         
ATermList MCRLgetDetFunctions(AFun fsort) {
     ATermList cs = MCRLgetConstructors(fsort);
     ATermList dets = (ATermList) ATgetAnnotation((ATerm) cs, projTag);
     return dets;
     }
     
ATermList MCRLgetProjections(AFun fsort) {
     ATermList r = MCRLgetDetFunctions(fsort), cs = NULL;
     if (!r) return NULL;
     r = ATreverse(r),
     cs = MCRLgetConstructors(fsort);
     for (;!ATisEmpty(cs);cs=ATgetNext(cs)) {
         ATerm c = ATgetFirst(cs);
         int i, n = ATgetArity(ATgetAFun(c));
         for (i=0;i<n;i++) {
             ATerm a = ATgetAnnotation(ATgetArgument((ATermAppl) c, i),projTag);
             if (!a) return NULL;
             r = ATinsert(r, a);
         }
     }
     return ATreverse(r);
     }     

/* -------------------------- Interface to rewriters --------------------- */
#include "tasks.h"
#include "rw.c"
/* -------------------------- End Interface to rewriters ----------------- */
                             
ATbool MCRLcheckRemainingFlags(int argc, char *argv[]) {
    int i; 
    for (i=1;i<argc;i++) { 
        if (argv[i][0] =='-' && strncmp(argv[i],"-at-",4) && 
           strcmp(argv[i],"-verbose")) {
           ATwarning("\"%s\" is unknown flag\n", argv[i]);
           return ATfalse; 
           }
        }
	return ATtrue;
    }

ATbool MCRLinitializeYY(int *argc, char ***argv) {    
     MCRLsetArguments(argc, argv);
     if (outputFile && fileName[0]=='\0') {
            ATwarning("File name expected as last argument");
	    return ATfalse;
            }
     if (flagTest && !MCRLcheckRemainingFlags(*argc, *argv)) return ATfalse;
     if (!MCRLinitialize()) return ATfalse;
     return ATtrue;
     }
     
ATbool MCRLinitializeXX(int *argc, char ***argv) {
     flagTest = ATfalse;
     if (!MCRLinitializeYY(argc, argv)) return ATfalse;
     flagTest = ATtrue;
     return ATtrue;
     }
              
ATbool MCRLinitializeRW(int *argc, char ***argv) {
     RWsetArguments(argc, argv);
     if (!MCRLinitializeYY(argc, argv)) return ATfalse;
     if (caseFlag && !MCRLinitCaseDistribution()) exit(1);
     if (!RWinitialize(MCRLgetAdt())) return ATfalse;
     return ATtrue;
     }

ATbool MCRLinitializeSU(int *argc, char ***argv) {
     SUsetArguments(argc, argv);
     if (!MCRLinitializeYY(argc, argv)) return ATfalse;
     if (!SUinitialize(MCRLgetAdt())) return ATfalse;
     return ATtrue;
     }
     
ATbool MCRLinitRW(int argc, char **argv) {
     return MCRLinitializeRW(&argc, &argv);
     }
     
ATbool MCRLinitSU(int argc, char **argv) {
     return MCRLinitializeSU(&argc, &argv);
     }
     
ATbool MCRLinit(int *argc, char ***argv) {
     return MCRLinitializeXX(argc, argv);
     }
     
ATbool MCRLinitOnly(int argc, char **argv) {
     return MCRLinitializeYY(&argc, &argv);
     }
                           
/* Library bolonging to simulater the routines are included in librw.a */

/* Library belonging to parsing MCRL terms */
    
static ATerm Translate(ATerm e) {
     int i, n = ATgetArity(ATgetSymbol(e));
     DECLA(ATerm, a, n);
     ATermList sorts = ATmakeList0();
     for (i=0;i<n;i++) {
          if (!(a[i]=Translate(ATgetArgument((ATermAppl) e, i)))) return NULL;
          sorts = ATinsert(sorts, (ATerm) ATmakeAppl0(MCRLgetSort(a[i])));
          }
       {
       AFun sym = ATmakeSymbol(MCRLextendName(ATgetName(ATgetSymbol(e)), 
                         ATreverse(sorts)), n, ATtrue);
       ATerm result = (ATerm) (n>0?ATmakeApplArray(sym, a):ATmakeAppl0(sym));
       if (MCRLgetType(ATgetAFun(result))<MCRLvariable) {
             ATwarning("Symbol %a is not declared", sym);
             return NULL;
             }
       return result;
       }
     }
     
ATerm MCRLtranslate(ATerm e) {
     return Translate(e);
     }
          
static ATerm TranslateDB(ATermTable db, ATermTable srt, ATerm t) {
  int i, n = ATgetArity(ATgetSymbol(t));
  if (n==0) {
       ATerm u = ATtableGet(db, t);
       if (u) return u;
       u = ATmake("<str>", MCRLextendName(ATgetName(ATgetSymbol(t)),ATempty));
       if (!MCRLgetSort(u) && !ATtableGet(srt, u)) 
               ATerror("Symbol %a is not declared", ATgetAFun(u));
       return u;      
       }
     {
     DECLA(ATerm, a, n);
     ATermList sorts = ATempty;
     for (i=0;i<n;i++) { 
             ATerm u = ATgetArgument((ATermAppl)t, i), t;
             AFun s;
             if (!(a[i] = TranslateDB(db, srt, u)))
                    return NULL;
             s = MCRLgetSort(a[i]);
             if (s>0) t = (ATerm) ATmakeAppl0(s);
             else
                t = ATtableGet(srt, a[i]);
             sorts = ATinsert(sorts, t);
             }
       {
       ATerm result = (ATerm) ATmakeApplArray(
       MCRLextendNameSymbol(ATreverse(sorts), "%s", ATgetName(ATgetAFun(t))) 
       ,a);
       if (!MCRLgetSort(result) && !ATtableGet(srt, result)) 
               ATerror("Symbol %a is not declared", ATgetAFun(result));        
       return result;
       }
     }   
 }     
     
static void ExtendVars(ATermList vars, ATermList *newvars, ATermTable *db,
     ATermTable *srt) {
     ATermList result = ATempty; 
     *db = ATtableCreate(100,80),
     *srt = ATtableCreate(100,80); 
     if (!db) ATerror("Extendvars cannot open db");
     for (;!ATisEmpty(vars);vars=ATgetNext(vars)) {
         ATerm var = ATgetFirst(vars);
         AFun a = MCRLextendNameSymbol(ATempty, "%s",
                  ATgetName(ATgetAFun(ApplHeader(
                  ATgetArgument((ATermAppl) var,  0)))));
         ATerm t;
         while (MCRLgetType(a)>=MCRLconstructor) a= MCRLnextSymbol(a);
         t =  (ATerm) ATmakeAppl0(a);
         result = ATinsert(result, ATmake("v(<term>, <term>)",
                  t , ATgetArgument((ATermAppl) var, 1)));
         /* ATwarning("Extendvars %t=%t", ATgetArgument((ATermAppl) var,  0),
         t); */      
         ATtablePut(*db, ATgetArgument((ATermAppl) var,  0), t);
         ATtablePut(*srt, t, ATgetArgument((ATermAppl) var,  1));           
         }
     *newvars =  ATreverse(result);
     // MCRLdeclareVars(*newvars);
     }
          
static ATerm TranslateEq(ATerm eq) { 
     ATermList vars;   
     ATermTable db, srt;
     ExtendVars((ATermList) ATgetArgument((ATermAppl) eq, 0), &vars,
         &db, &srt);
     MCRLdeclareVars(vars);
     {
     ATerm arg1 = TranslateDB(db, srt, ATgetArgument((ATermAppl) eq, 1)),
           arg2 = TranslateDB(db, srt, ATgetArgument((ATermAppl) eq, 2));
     AFun s1, s2;
    if (!arg1 || !arg2 || 
       (MCRLgetSort(arg1)==0 && ATtableGet(srt, arg1)== NULL) || 
       (MCRLgetSort(arg2)==0 && ATtableGet(srt, arg2)== NULL)) 
              {ATwarning("Illegal %s %t=%t",  arg1?"rhs":"lhs",
               arg1?arg1:ATgetArgument((ATermAppl) eq, 1),
               arg2?arg2:ATgetArgument((ATermAppl) eq, 2));
               ATtableDestroy(db); ATtableDestroy(srt);
               return NULL;
               }
    s1 = MCRLgetSort(arg1)?MCRLgetSort(arg1):ATgetAFun(ATtableGet(srt, arg1));
    s2 = MCRLgetSort(arg2)?MCRLgetSort(arg2):ATgetAFun(ATtableGet(srt, arg2));
    if (s1!=s2) {
       ATwarning("Sort lhs %a != sort rhs %a: Equation: %t=%t",
       s1, s2, MCRLprint(arg1), MCRLprint(arg2));
       ATtableDestroy(db); ATtableDestroy(srt);
       return NULL;
       }
     ATtableDestroy(db); ATtableDestroy(srt);
     MCRLundeclareVars(vars);
     return ATmake("e(<term>,<term>, <term>)", (ATerm) vars, arg1, arg2);
     }
     }
           

          
/* ---------- Part Belonging to CASE DISTRIBUTION ------------------------------*/

typedef struct {
    AFun *d;
    int n;
} CASEROW;

static CASEROW *caseTable = NULL; /* sortnr # casenr  -> CaseFunction */

/* Computes the set of case functions belonging to arity n */
        
ATbool MCRLinitCaseDistribution(void) {
     int i = 0, pt = 0, sort_id = 0, cnt = 0;
     ATermList rs = ATempty;
     int pos[MAX_ARITY], arity[MAX_ARITY];
     memset(pos, 0, MAX_ARITY*sizeof(int));
     for (i=0;i<=maxsym;i++) 
     if (MCRLgetType(i)>=MCRLconstructor) {
        ATerm t = (ATerm) ATmakeAppl0(MCRLgetSortSym(i));
        if (ATindexOf(rs, t, 0)<0) { 
               rs = ATinsert(rs,t);
               symint[ATgetAFun(t)].nr = (sort_id++);
               }
        }
     for (i=0;i<=maxsym;i++) 
     if (MCRLgetType(i)==MCRLcasefunction) { 
        ATerm e = ATgetArgument((ATermAppl) MCRLgetFunction(i), 0);
        if (pos[ATgetArity(i)]==0) {
            arity[pt] = ATgetArity(i);
            pos[ATgetArity(i)]=(pt++);
            }
        if (ATindexOf(rs, e, 0)<0) { 
            rs = ATinsert(rs, e);
            symint[ATgetAFun(e)].nr = (sort_id++);
            }
        symint[i].nr = pos[ATgetArity(i)]; 
        }
    /*rs:  List of sorts of the case functions */ 
    /* ATwarning("MCRLinitCaseDistribution QQQ sorts = %t (%d)", rs, sort_id);
    */ 
     if (!(caseTable = (CASEROW*) calloc(sort_id, sizeof(CASEROW))))
        ATerror("Cannot allocate caseTable (%d)", sizeof(CASEROW));
     for (rs=ATreverse(rs);!ATisEmpty(rs);rs=ATgetNext(rs)) {
        int k = symint[ATgetAFun(ATgetFirst(rs))].nr;
        if (!(caseTable[k].d = (AFun*) calloc(pt, sizeof(AFun))))
             ATerror("Cannot allocate caseTable[%d] (%d)", k, pt);
        caseTable[k].n = pt;
        for (i=0;i<pt;i++)  {
             ATbool new = extend_adt;
             if ((
               caseTable[k].d[i] = MCRLputCaseFunction(arity[i]-1, ATgetFirst(rs), &new))
                ==0) return ATfalse;
             if (new) {symint[caseTable[k].d[i]].nr = pos[arity[i]]; cnt++;}
             }
        }
     if (verbose && cnt>0) ATwarning("There are %d case function%s updated", cnt, cnt>1?"s":"");
     return ATtrue;
     } 

AFun MCRLsimilarCasefunction(AFun srt, AFun casef) {
/* ATwarning("srt = %s nr = %d",ATgetName(srt), symint[srt].nr);
ATwarning("casef = %s nr = %d",ATgetName(casef), symint[casef].nr);
ATwarning("%s",ATgetName(caseTable[symint[srt].nr].d[symint[casef].nr]));
*/
     return caseTable[symint[srt].nr].d[symint[casef].nr];
     }
     
/* Belonging to case distribution */ 
   
static ATerm Context(ATerm f, ATerm e, int s) {
     int n = ATgetArity(ATgetAFun(f)), i;
     if (n!=0 && MCRLgetType(ATgetAFun(f))==MCRLcasefunction) {
         if (ATisEqual(ATgetArgument((ATermAppl) f, 0), e) 
               && MCRLgetType(ATgetAFun(e))==MCRLvariable) {
	       f = ATgetArgument((ATermAppl) f, s);
	       n = ATgetArity(ATgetAFun(f));
	       }
	  {
          ATerm *a = calloc(n, sizeof(ATerm)); ATprotectArray(a, n);
          for (i=0;i<n;i++) a[i] = ATgetArgument((ATermAppl) f, i); 
          for (i=1;i<n;i++) {
              ATerm arg = ATgetArgument((ATermAppl) f, i);
              if (MCRLgetType(ATgetAFun(arg))==MCRLcasefunction /* &&
             ATgetArity(ATgetAFun(arg)) == n */) {
                 a[i] = Context(arg, e, s);  
              }
           }
           f = (ATerm) ATmakeApplArray(ATgetAFun(f), a);
           ATunprotect(a); free(a);
           }
	   }
     return f;   
     }

static ATerm ContextLoop(ATerm f) {
     if (MCRLgetType(ATgetAFun(f))==MCRLcasefunction) {
        int n = ATgetArity(ATgetAFun(f)), i;
	ATerm *a = calloc(n, sizeof(ATerm)); ATprotectArray(a, n);
	a[0] = ATgetArgument((ATermAppl) f, 0);
        for (i=1;i<n;i++) {
           a[i] = Context(ATgetArgument((ATermAppl) f, i), 
	          ATgetArgument((ATermAppl) f, 0), i); 
        }
	f = (ATerm) ATmakeApplArray(ATgetAFun(f), a);
        ATunprotect(a); free(a);
     }
     return f;
     }
                 
    
static ATerm T(MCRLREWRITE rewr, ATerm f, int p) {
     /* f(p) must be case function */
     ATerm result = NULL, casef = ATgetArgument((ATermAppl) f, p);
     AFun casefsym = ATgetAFun(casef), fsym = ATgetAFun(f), varsym;
     int m = ATgetArity(casefsym), i;
     ATermList sels = MCRLgetCaseSelectors(casefsym);
     ATerm *a = calloc(m, sizeof(ATerm)); ATprotectArray(a, m);
    /* ATwarning("QQ %s %d",ATgetName(fsym),p); */
     a[0] = ATgetArgument(casef, 0); varsym = ATgetAFun(a[0]);
     /* if (MCRLgetType(varsym)!=MCRLvariable ||
         !ATisEqual((val = RWgetAssignedVariable(varsym)), a[0])
         ) val = NULL; */
     for (i=1;i<m && !ATisEmpty(sels);i++, sels = ATgetNext(sels)) {
         /* a[i] = lookup[fsym] */ 
         if (!rewr || ATisEmpty(MCRLgetRewriteRules(fsym)))
           a[i] = (ATerm) ATsetArgument((ATermAppl) f,  ATgetArgument(casef, i), p); 
         else {
           /* if (val) RWassignVariable(ATgetAFun(val), ATgetFirst(sels) , NULL, 1); */
           a[i] =  
               rewr((ATerm) ATsetArgument((ATermAppl) f, ATgetArgument(casef, i), p));
           /* if (val) {RWresetVariables(1);} */
           }
         }
     result = (ATerm) ATmakeApplArray(
              MCRLsimilarCasefunction(MCRLgetSort(f), casefsym), a);
     /* C(e,q,C(g,C(e,a,b,c...),...)...) -> C(e,q, C(g,b,....)...) */
     result = ContextLoop(result);
     ATunprotect(a); free(a);
     if (ATgetArity(ATgetAFun(result))!= m) ATerror("System error %t %d %t",
                  result, m, casef);
    /* ATwarning("QQ: T result = %s",ATgetName(ATgetAFun(result))); */
    /* ATwarning("QQ: T result = %t",result); */
     return result;
     }
      
ATerm MCRLcaseDistribution(MCRLREWRITE rewr, ATerm f) {
     int n = ATgetArity(ATgetAFun(f)), i;
     ATerm result =f;
     if (MCRLgetType(ATgetAFun(f))==MCRLcasefunction) {
    /* ATwarning("QQQ %d %t",rewr, f); */
         for (i=1;i<n &&
        (MCRLgetType(ATgetAFun(ATgetArgument((ATermAppl) f, i)))!= MCRLcasefunction
        || ATgetArity(ATgetAFun(ATgetArgument((ATermAppl) f, i)))>=n);i++);
         }
     else {        
         for (i=0;i<n &&
         MCRLgetType(ATgetAFun(ATgetArgument((ATermAppl) f, i)))!= MCRLcasefunction;
         i++);
         } 
     if (i<n) result = T(rewr, f, i); 
     return result;     
     }

/* -------------------------End part belonging to Case Dist ---------------- */
     
#include "mcrlparse.h"

ATerm MCRLparse(char *e) {
     ATerm result = Parse(e);
     if (!result) return NULL;
     result = Translate(result);
     if (!result) return NULL; 
     return result;
     }
     
static ATerm Action(ATerm actname, ATermList  actargs) {
      return (ATerm) ATmakeAppl0(ATmakeSymbol(ATwriteToString(MCRLprint(
      (ATerm) ATmakeApplList(
      ATmakeSymbol(ATgetName(ATgetSymbol(actname)),ATgetLength(actargs), ATtrue),
      actargs))),0, ATtrue));
      }
      
static ATermIndexedSet ActionsInSpecs(void) {
     ATermIndexedSet db = ATindexedSetCreate(100,80);
     ATbool new;
     ATermList sums = MCRLgetListOfSummands();
     MCRLdeclareVars(MCRLgetListOfPars());
     for (;!ATisEmpty(sums);sums=ATgetNext(sums))
          {ATerm sum = ATgetFirst(sums);
          ATerm actname = ATgetArgument((ATermAppl) sum, 1);
          ATermList actargs = (ATermList) ATgetArgument((ATermAppl) sum,2);
          int i, n = ATgetLength(actargs);
          MCRLdeclareVars(MCRLgetListOfVars(sum));
          if (n>0) {
             AFun actsym = ATmakeAFun(ATgetName(ATgetAFun(actname)), n, ATtrue);
             DECLA(ATerm, a, n);
             for (i=0;i<n&&!ATisEmpty(actargs);i++,actargs=ATgetNext(actargs)) 
                  a[i] = (ATerm)
                  ATmakeAppl0(MCRLgetSort(ATgetFirst(actargs)));
             ATindexedSetPut(db, (ATerm) ATmakeApplArray(actsym, a), &new);
             }
          else
             ATindexedSetPut(db, actname, &new);   
          }    
     return db;
     } 
              
ATermList MCRLparseActions(char *e) {
     ATermList ts = Parse2(e), result = ATempty;
     ATermIndexedSet db = ActionsInSpecs();
     if (!ts) return NULL;
     for (;!ATisEmpty(ts);ts = ATgetNext(ts)) {
       ATermAppl action = (ATermAppl) ATgetFirst(ts);
       AFun sym = ATgetAFun(action);
       int n = ATgetArity(sym), i;
       if (n>0) {
          DECLA(ATerm, a, n);
          DECLA(ATerm, b, n);     
          for (i=0;i<n;i++) {
                  a[i] = Translate(ATgetArgument(action, i));
                  if (!a[i]) return NULL;
                  if (!MCRLisClosedTerm(a[i])) {
                       ATwarning("Term %t in action \"%t\" is not closed", 
                       MCRLprint(a[i]), MCRLprint((ATerm) action));
                       return NULL;
                       };
                  }
          for (i=0;i<n;i++) b[i] = (ATerm) ATmakeAppl0(MCRLgetSort(a[i]));
          /* ATwarning("%t  %t", ATindexedSetElements(db), 
              (ATerm) ATmakeApplArray(sym, b)); */
          if (ATindexedSetGetIndex(db, (ATerm) ATmakeApplArray(sym, b))<0) {
               ATwarning("Illegal action on commandline: %t", 
                   MCRLprint((ATerm) ATmakeApplArray(sym, a)));
               return NULL;
               }
          result = ATinsert(result,
          (ATerm) ATmakeAppl0(ATmakeSymbol(ATwriteToString(MCRLprint(
          (ATerm) ATmakeApplArray(sym, a))),0, ATtrue)));
          }
          else {
             if (ATindexedSetGetIndex(db, (ATerm) action)<0) {
             ATwarning("Illegal action on commandline: %t", 
                 action);
             return NULL;
             }
             result = ATinsert(result, (ATerm) action);
             }
       }
     if (!result) return NULL; 
     return ATreverse(result);
     }
          
ATerm MCRLparseFile(FILE *fp) {
     ATerm result = ParseFile(fp);
     if (!result) return NULL;
     result = Translate(result);
     if (!result) return NULL; 
     return result;
     }

static ATerm *inv_ar = NULL;
static int inv_size;
     
ATermList MCRLparseEquations(FILE *fp) {
     return ParseEqs(fp);
     }

ATermList MCRLparseTrace(FILE *fp, int *current) {
     int npars = MCRLgetNumberOfPars(), i;
     ATermList ts = Parse2File(fp), r = ATempty;
     /* ATfprintf(stdout,"QQQ %t\n", ts); */
     if (!ts) return NULL;
     while (ATgetLength(ts)>npars) {
         r = ATinsert(r, ATgetFirst(ts));
         ts = ATgetNext(ts);
         for (i=0;i<npars;i++, ts = ATgetNext(ts)) { 
              ATerm t = Translate(ATgetFirst(ts));
              if (t) r = ATinsert(r, t); else return NULL;
              }
         }
     sscanf(ATwriteToString(MCRLprint(ATgetFirst(ts))), "%d", current);
     /* ATfprintf(stdout,"QQQ current %d\n", *current);  */
     return ATreverse(r);
     } 
              
int MCRLparseInvariants(FILE *fp) {
     int n, i;
     ATermList invariants = Parse2File(fp);
     /* ATwarning("QQQ %t", invariants); */
     if (!invariants) ATerror("Syntax error");
     n = ATgetLength(invariants); inv_size = n;
     if (n==0) ATerror("No invariants defined");
     inv_ar = (ATerm*) calloc(n, sizeof(ATerm));
     ATprotectArray(inv_ar, n);
     for (i= 0;!ATisEmpty(invariants);invariants=ATgetNext(invariants), i++) {
         ATerm t = Translate(ATgetFirst(invariants));
         if (!t) exit(1);
         inv_ar[i] = t;
         }
     return n;
     }
     
ATerm MCRLgetInvariant(int invariant) {
     if (!inv_ar) ATerror("No invariants available");
     if (invariant<0 || invariant >= inv_size) 
        ATerror("Invariant number %d out of range (%d,%d)",
        invariant, 0, inv_size);
     return inv_ar[invariant];
     }

ATerm MCRLparseAdt(FILE *f) {
  return (ATerm) ParseAdt(f);
  }
                             
static void ReadExtraAdt(FILE *f) {
     ATbool new = ATfalse;
     ATermAppl extra = (ATermAppl) ParseAdt(f);
     ATermAppl  sig = (ATermAppl) ATgetArgument(extra, 0);
     ATermList eqs = (ATermList) ATgetArgument(extra, 1),
               sorts = (ATermList) ATgetArgument(sig, 0),
               funcs = (ATermList) ATgetArgument(sig, 1),
               maps = (ATermList) ATgetArgument(sig, 2);
     ATermList addedSorts = ATempty;
     for (;!ATisEmpty(sorts);sorts=ATgetNext(sorts)) {
        ATerm sortstring = ATgetFirst(sorts);
        AFun sym = MCRLputSort(sortstring, &new);
        if (sym == 0) ATerror("Error in added ADT");
        if (new) addedSorts = ATinsert(addedSorts, sortstring);
        }
     for (;!ATisEmpty(funcs);funcs=ATgetNext(funcs)) {
        ATerm funcstring = ATgetFirst(funcs);
        AFun sym = MCRLputConstructor(funcstring, NULL, &new);
        if (sym == 0) ATerror("Error in added ADT");
        {
        ATerm sortterm = (ATerm) ATmakeAppl0(MCRLgetSortSym(sym));
        if (new && ATindexOf(addedSorts, sortterm, 0)<0)
        ATwarning(
          "Existing sort %t will be extended by constructor %t",
          sortterm, MCRLprint(MCRLgetFunction(sym)));
        } 
      }    
     for (;!ATisEmpty(maps);maps=ATgetNext(maps)) {
        ATerm mapstring = ATgetFirst(maps);
        AFun sym = MCRLputMap(mapstring, NULL, &new);
        if (sym == 0) ATerror("Error in added ADT"); 
     }
     for (;!ATisEmpty(eqs);eqs=ATgetNext(eqs)) {
       AFun sym = MCRLputEquation(ATgetFirst(eqs), &new);
       if (sym == 0) ATerror("Error in added ADT");
       } 
  }


