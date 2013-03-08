/* $Id: prover.c,v 1.5 2005/04/20 14:25:55 vdpol Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "aterm2.h"
#include "prover.h"
#include <assert.h>
#include "signature.h"

#ifdef MCRLLIB
#include "rw.h"
#endif


/* Author: Jaco.van.de.Pol@CWI.nl

   main function: BDD build_BDD(FORM)

   Input: equational FORMula (see typedefs below)
   Output: ordered EQ-BDD

   programmed along the lines of the algorithm described in
   J.F. Groote and J.C. van de Pol
   "Equational Binary Decision Diagrams"
   CWI-report SEN-R0006

   Switches: 
   * VERBOSE, STATISTICS - define the level of information on stderr
   * PERSISTENT          - preserves the hash-table across various calls
                           to smallest
*/

/* 18/8/2004: JCP added -pr-reverse: sorting on rhs node first
   -pr-reverse implies -pr-full

   19/8/2004: JCP added -pr-lpo: use lpo to order terms.
 */

static char TEST=0,STATISTICS=0,PERSISTENT=1;
static char FULL=0, PRINT=0, VERBOSE=0, DOT=0, REVERSE=0, LPO=0;

#define MAXBDD 1000      /* initial size only */

int calls_TD, lookups_TD, hits_TD; /* top down */
int calls_SM, lookups_SM, hits_SM; /* smallest */
int calls_tot_TD, lookups_tot_TD, hits_tot_TD; /* top down */
int calls_tot_SM, lookups_tot_SM, hits_tot_SM; /* smallest */

static ATerm make(ATerm e, ATerm high, ATerm low) {
  /* returns a reduced BDD */
  
  if (high == low) return low;
  return prITE(e,high,low);
}

static ATermTable visited; /* used to avoid printing nodes twice */
static int N; /* number of next node */

static void aux_print_BDD(ATerm node, FILE* fp) {
  ATerm low, high;
  int lownum, highnum;

  if (ATtableGet(visited,node))
    return;

  /* a new node */

  if (node==prFALSE)
    fprintf(fp,"(%d): F\n",N);
  else if (node==prTRUE)
    fprintf(fp,"(%d): T\n",N);
  else if (Is_ite(node)) {
    high=ATgetArgument(node,1);
    low=ATgetArgument(node,2);
    aux_print_BDD(high,fp);
    aux_print_BDD(low,fp);
    highnum = ATgetInt((ATermInt)ATtableGet(visited,high));
    lownum = ATgetInt((ATermInt)ATtableGet(visited,low));
    ATfprintf(fp,"(%d): %t --> (%d) , (%d)\n", N, 
	      prettyprint(ATgetArgument(node,0)), highnum, lownum);
  }
  else 
    ATfprintf(fp,"(%d): %t\n",N,prettyprint(node));
  ATtablePut(visited,node,(ATerm)ATmakeInt(N++));
}

void print_BDD(ATerm root,FILE* fp) {
  visited = ATtableCreate(MAXBDD*2,75);
  N=0;
  fprintf(fp,"  \nBDD: (node): atom --> (high) , (low)\n");
  fprintf(fp,"------------------------------------\n");
  aux_print_BDD(root,fp);
  fprintf(fp,"------------------------------------\n");
  fprintf(fp,"Total number of nodes: %d\n\n",N);
  ATtableDestroy(visited);
}

static void aux_dot_BDD(ATerm node, FILE* fp) {
  ATerm low, high;
  int lownum, highnum;

  if (ATtableGet(visited,node))
    return;

  /* a new node */

  if (node==prFALSE)
    fprintf(fp,"  %d [shape=box,label=\"F\"];\n",N);
  else if (node==prTRUE)
    fprintf(fp,"  %d [shape=box,label=\"T\"];\n",N);
  else if (Is_ite(node)) {
    high=ATgetArgument(node,1);
    low=ATgetArgument(node,2);
    aux_dot_BDD(high,fp);
    aux_dot_BDD(low,fp);
    highnum = ATgetInt((ATermInt)ATtableGet(visited,high));
    lownum = ATgetInt((ATermInt)ATtableGet(visited,low));
    ATfprintf(fp,"  %d [label=\"%t\"];\n",N,prettyprint(ATgetArgument(node,0)));
    ATfprintf(fp,"  %d -> %d;\n",N,highnum);
    ATfprintf(fp,"  %d -> %d [style=dashed];\n",N,lownum);
  }
  else 
    ATfprintf(fp,"  %d [shape=box,label=\"%t\"\n",N,prettyprint(node));
  ATtablePut(visited,node,(ATerm)ATmakeInt(N++));
}

void dot_BDD(ATerm root,FILE* fp) {
  visited = ATtableCreate(MAXBDD*2,75);
  N=0;
  fprintf(fp,"digraph BDD {\n");
  aux_dot_BDD(root,fp);
  fprintf(fp,"}\n");
  ATtableDestroy(visited);
}

ATermIndexedSet Bool_Count,Dom_Count,Intern_Count;

static void aux_count_BDD(ATerm b) {
  Symbol f;
  ATbool new;

  f=ATgetSymbol(b);
  if (Is_var(b))
    if (Sort_of(b)==prBOOL) 
      ATindexedSetPut(Bool_Count,b,&new);
    else 
      ATindexedSetPut(Dom_Count,b,&new);
  else {
    ATindexedSetPut(Intern_Count,b,&new);
    if (new) {
      int i, n=ATgetArity(f);
      for (i=0; i<n; i++)
	aux_count_BDD(ATgetArgument(b,i));
    }
  }
}

void count_BDD(ATerm root, FILE* fp) {
  int dc,bc,ic;
  Dom_Count = ATindexedSetCreate(127,75);
  Bool_Count = ATindexedSetCreate(127,75);
  Intern_Count = ATindexedSetCreate(127,75);
  Intern_Count = ATindexedSetCreate(127,75);
  aux_count_BDD(root);
  dc = ATgetLength(ATindexedSetElements(Dom_Count));
  bc = ATgetLength(ATindexedSetElements(Bool_Count));
  ic = ATgetLength(ATindexedSetElements(Intern_Count));
  ATfprintf(fp,"%d domain and %d boolean variables\n",dc,bc);
  ATfprintf(fp,"%d internal nodes\n",ic);
  ATindexedSetDestroy(Dom_Count);
  ATindexedSetDestroy(Bool_Count);
  ATindexedSetDestroy(Intern_Count);
}

/* ******************************************************************** */


static int occurs(ATerm x, ATerm y) { /* y occurs in x */
  if (x==y) return 1;
  if (ATmatch(x,"<int>",NULL)) return 0;
  // else branch:
  { 
    int i, n = ATgetArity(ATgetSymbol(x));
    for (i=0; i<n; i++)
      if (occurs(ATgetArgument(x,i),y))
	return 1;
  }
  return 0;
}

static int compare_term(ATerm x, ATerm y);

static ATermTable Orient;

static ATerm orient(ATerm g) {
  ATerm  result = ATtableGet(Orient,g);
  if (result) return result;
  else  { 
    Symbol f=ATgetSymbol(g);
    int i, m=ATgetArity(f);
    ATerm h;
    DECLA(ATerm,x,m);
    // ATerm *x = (ATerm*)alloca(m*sizeof(ATerm));
    
    for (i=0;i<m;i++)
      x[i]=orient(ATgetArgument(g,i));
    h = (ATerm)ATmakeApplArray(f,x);
  
    if (Is_eq(h)) {
      ATerm s,t;
      s=ATgetArgument(h,0);
      t=ATgetArgument(h,1);
      if (compare_term(s,t)==1)
	h=(ATerm)ATmakeAppl2(f,t,s);
    }
    ATtablePut(Orient,g,h);
    return h;
  }
}

static ATermTable SetTF;
static ATermTable Smallest; 

static ATerm Settrue(ATerm e1, ATerm e2) {
  ATerm result;
  char ISEQ;
  if (e1==prTRUE || e1==prFALSE) return e1;

  if (e1==e2) return prTRUE;

  ISEQ = Is_eq(e2);
  if (ISEQ && ATgetArgument(e2,1)==e1)
    return ATgetArgument(e2,0);

  if (Is_var(e1)) return e1;
  
  result = ATtableGet(SetTF,e1);
  if (result) return result;
  
  if (!ISEQ) {
    result = ATtableGet(Smallest,e1);
    if (!result)
      /* this means that e1 has no atoms, i.e. no boolean subterms */
      return e1;
    if (result != e2) {
      /* e2 cannot occur within e1 */
      //    ATtablePut(SetTF,e1,e1);
      return e1;
    } // Note that this is not possible for equations, because if e2= (x=y) and
  }   // e2 doesn't occur in e1, still all y's in e1 must be replaced by x.
  
  {
    Symbol f = ATgetSymbol(e1);
    int m = ATgetArity(f);
    DECLA(ATerm,x,m);
    // ATerm* x = (ATerm*)alloca(m*sizeof(ATerm));
    int i;
    for (i=0;i<m;i++)
      x[i]=Settrue(ATgetArgument(e1,i),e2);
    result = (ATerm)ATmakeApplArray(f,x);
    ATtablePut(SetTF,e1,result);
    return result;
  }
}

static ATerm settrue(ATerm e1, ATerm e2) {
  ATerm result;
  SetTF = ATtableCreate(2047,50);
  result = Settrue(e1,e2);
  ATtableDestroy(SetTF);
  return result;
}

static ATerm Setfalse(ATerm e1, ATerm e2) {
  ATerm result;

  if (e1==prTRUE || e1==prFALSE) return e1;

  if (e1==e2) return prFALSE;
  
  if (Is_var(e1)) return e1;

  result = ATtableGet(SetTF,e1);
  if (result) return result;

  result = ATtableGet(Smallest,e1);
  if (!result)
    /* This means that e1 has no atoms, i.e. no boolean subterms */
    return e1;

  if (result != e2) {
    /* e2 cannot occur within e1 */
    //    ATtablePut(SetTF,e1,e1);
    return e1;
  }
  else {
    Symbol f = ATgetSymbol(e1);
    int m = ATgetArity(f);
    DECLA(ATerm,x,m);
    // ATerm* x = (ATerm*)alloca(m*sizeof(ATerm));
    int i;
    //    ATtableRemove(Smallest,e1);
    for (i=0;i<m;i++)
      x[i]=Setfalse(ATgetArgument(e1,i),e2);
    result = (ATerm)ATmakeApplArray(f,x);
    ATtablePut(SetTF,e1,result);
    return result;
  }
}

static ATerm setfalse(ATerm e1, ATerm e2) {
  ATerm result;
  SetTF = ATtableCreate(2047,50);
  result = Setfalse(e1,e2);
  ATtableDestroy(SetTF);
  return result;
}

/* ***************************************************************** */
/* code for lpo */

static char symbol_type(Symbol f) {
  switch (MCRLgetType(f)) {
  case MCRLconstructor: return 0;
  case MCRLfunction:
  case MCRLcasefunction: return 1;
  default: return 2;
  }
}

static int compare_symbol(Symbol f, Symbol g) {
  char fcons,gcons;
  if (f==g) return 0;

  /* funcs are smaller than maps are smaller than variables */

  fcons = symbol_type(f);
  gcons = symbol_type(g);
  if (fcons < gcons) return -1;
  if (fcons > gcons) return 1;

  /* otherwise: use symbol index of ATerm library */

  return (f<g ? -1 : 1);
}

static int lpo(ATerm s, ATerm t);

static char lpo_eq_vector(ATerm s, ATerm t, int n) {
  /* returns: Exists i . i<n . s_i >= lpo t */
  int i=0;
  while (i<n) {
    if (lpo(ATgetArgument(s,i),t) >= 0) return 1;
    i++;
  }
  return 0;
}

static int lpo(ATerm s, ATerm t) {
  Symbol sf = ATgetSymbol(s);
  Symbol tf = ATgetSymbol(t);
  int sn = ATgetArity(sf);
  int tn = ATgetArity(tf);
  int i=0,comp;

  if (s==t) return 0;

  if (lpo_eq_vector(s,t,sn)) return 1;
  if (lpo_eq_vector(t,s,tn)) return -1;

  comp = compare_symbol(sf,tf);
  if (comp!=0) return comp;

  assert(sn==tn);
  while (i<sn) {
    comp = lpo(ATgetArgument(s,i),ATgetArgument(t,i));
    if (comp != 0) return comp;
    i++;
  }
  assert(0);
  /* here s=t would hold, which was excluded already */
  
}

static int compare_lpo(ATerm s, ATerm t) {
  int comp;
  comp = lpo(s,t);
  if (TEST) {
    char c = ( (comp==-1) ? '<' : ((comp==1) ? '>' : '='));
    ATfprintf(stderr,"%t %c %t\n",MCRLprint(s),c,MCRLprint(t));
  }
  return comp;
}

/* **** */

static int compare_address(ATerm x, ATerm y) {
  long i,j;
  i= (long)x;
  j= (long)y;
  if (i<j) return -1;
  if (i>j) return 1;
  return 0;
}

static int give_type(ATerm x) {
  /* assume: x is of type bool */
  if (Is_var(x)) return 0;
  if (Is_eq(x)) {
    if (Is_var(ATgetArgument(x,0)) && Is_var(ATgetArgument(x,1)))
      return 1;
    else
      return 2;
  }
  return 3;
}

static int compare_type(ATerm x,ATerm y) {
  int i,j;
  i=give_type(x);
  j=give_type(y);
  if (i<j) return -1;
  if (i>j) return 1;
  return 0;
}

static int compare_occurs(ATerm x, ATerm y) {
  if (x==y) return 0;
  if (occurs(x,y)) return 1;
  if (occurs(y,x)) return -1;
  return 0;
}

static int term_type(ATerm x) {
  /* assume: x is not of type bool */
  if (Is_var(x)) return 2;
  if (Is_func(x)) return 0;
  return 1;
}

static int compare_termtype(ATerm x, ATerm y) {
  int i,j;
  i=term_type(x);
  j=term_type(y);
  if (i<j) return -1;
  if (i>j) return 1;
  return 0;
}

static int lexico(int i,int j) {
  if (i) return i;
  return j;
}

static int compare_term(ATerm x, ATerm y) {
  if (LPO) return compare_lpo(x,y);
  else
  return lexico(lexico(compare_occurs(x,y),
		       compare_termtype(x,y)),
		compare_address(x,y));
}

static int compare_eq(ATerm x, ATerm y) {

  // For completeness in the case of equalities only, FULL==1 is required.
  // However, this has disastrous consequences
  // on some examples, especially of the form 
  // (0=x \/ 1=x) /\ (0=y \/ 1=y) /\ (0=z \/ 1=z) /\ ...
  // which lead to exponential blowup.
  // Therefore, by default FULL==0. This is changed with the option -pr-full

  if (!FULL) return 0; 
  if (Is_eq(x) && Is_eq(y)) {
    if (REVERSE)
      return lexico(compare_term(ATgetArgument(x,1),ATgetArgument(y,1)),
		    compare_term(ATgetArgument(x,0),ATgetArgument(y,0)));
    else
      return lexico(compare_term(ATgetArgument(x,0),ATgetArgument(y,0)),
		    compare_term(ATgetArgument(x,1),ATgetArgument(y,1)));
  }
  else
    return 0;
}

static int compare_guard(ATerm g1, ATerm g2) {
  return lexico(lexico(compare_type(g1,g2),compare_eq(g1,g2)),
		compare_address(g1,g2));
}

static ATerm minn(ATerm g1, ATerm g2) {
  /* Pre: g1 and g2 either undefined or oriented guards */

  if (!g1) return g2;
  if (!g2) return g1;

  if (compare_guard(g1,g2) == -1) 
    return g1;
  else
    return g2;
}

static ATerm smallest_rec(ATerm f) {
  /* return the smallest equation from f if it exists, else NULL */
  
  ATerm s;
  int i;
  
  calls_SM++;
  
  if (Is_var(f)) {
    if (Sort_of(f)==prBOOL)
      return f;
    else {
      return NULL;
      }
  }
  if (f==prFALSE) return NULL;
  if (f==prTRUE) return NULL;
  

  lookups_SM++;
  s=ATtableGet(Smallest,f);
  if (s) {
    hits_SM++; 
    return s;
  }

  /* s==NULL */

  for (i=0;i<ATgetArity(ATgetSymbol(f));i++)
    s = minn(s,smallest_rec(ATgetArgument(f,i)));
  
  if (!s && (Sort_of(f)==prBOOL))
    s=f;

  if (s) ATtablePut(Smallest,f,s); 
  
  return s;
}
  
static ATerm smallest(ATerm f) {
  ATerm result;

  result = smallest_rec(f);
  if (!PERSISTENT) {
    ATfprintf(stderr,"Not persistent\n");
    ATtableDestroy(Smallest);
    Smallest=ATtableCreate(2047,50);
  }

  return result;
}

static ATermTable FormBdd; /* dynamic programming: FORM -> BDD */
static int DEPTH=0; // only used for debugging with -pr-test (if (TEST) ...)

static ATerm BDD_down(ATerm f) {

  ATerm g;
  ATerm f1,f2;
  ATerm B;

  calls_TD++;
  if (f==prFALSE) {
    if (TEST) ATfprintf(stderr,"Level %4d: Leaf: F\n",DEPTH);
    return f;
  }
  if (f==prTRUE) {
    if (TEST) ATfprintf(stderr,"Level %4d: Leaf: T\n",DEPTH);
    return f;
  }
  
  lookups_TD++;
  B=ATtableGet(FormBdd,f);
  if (B) {
    if (TEST) ATfprintf(stderr,"Level %4d: Hit hashtable\n",DEPTH);
    hits_TD++; 
    return B;}
  
  /* not yet constructed */

  g=smallest(f);
  
  if (!g) {
    ATwarning("Unexpected situation: formula has no guard\n");
    return f;
  }
  
  if (TEST) ATfprintf(stderr,"Level %4d: Splitting on %t\n",
		      DEPTH,prettyprint(g));

  /* now split on g: */

  DEPTH++;
  f1=BDD_down(orient(RWrewrite(settrue(f,g))));
  f2=BDD_down(orient(RWrewrite(setfalse(f,g))));
  DEPTH--;
  // WHY NOT: B=RWrewrite(make(g,f1,f2));
  B=make(g,f1,f2);
  ATtablePut(FormBdd,f,B);
  return B;
}

static ATerm build_BDD(ATerm formula) {
  ATerm prev;
  int i;
  
  prev = NULL;
  i=1;
  calls_tot_TD = lookups_tot_TD = hits_tot_TD = 0;
    

  while (prev != formula) {
    if (VERBOSE) fprintf(stderr,"\nStarting iteration %d\n",i);
    
    if (STATISTICS) {
      count_BDD(formula,stderr);
      calls_TD = lookups_TD = hits_TD = 0;
      calls_SM = lookups_SM = hits_SM = 0;
    }
    
    prev=formula;
    // WHY NOT: formula=RWrewrite(BDD_down(formula));
    //    if (TEST) ATfprintf(stderr,"in : %t\n",formula);
    formula=BDD_down(formula);
    //    if (TEST) ATfprintf(stderr,"out: %t\n",formula);
    i++;
    if (PRINT) print_BDD(formula,stderr);
    if (DOT) dot_BDD(formula,stderr);
    if (STATISTICS) {
      fprintf(stderr, "TOP DOWN :  calls: %d, lookups: %d, hits: %d\n",
	      calls_TD,lookups_TD,hits_TD);
      fprintf(stderr, "SMALLEST :  calls: %d, lookups: %d, hits: %d\n",
	      calls_SM,lookups_SM,hits_SM);
      
      calls_tot_TD += calls_TD;
      lookups_tot_TD += lookups_TD;
      hits_tot_TD += hits_TD;
      calls_tot_SM += calls_SM;
      lookups_tot_SM += lookups_SM;
      hits_tot_SM += hits_SM;
    }
  }
  
  if (STATISTICS) {
    fprintf(stderr,"\nG R A N D   T O T A L S\n");
    fprintf(stderr, "Fixed point reached after %d iterations\n",i-2);
    fprintf(stderr, "TOP DOWN :  calls: %d, lookups: %d, hits: %d\n",
	    calls_tot_TD,lookups_tot_TD,hits_tot_TD);
    fprintf(stderr, "SMALLEST :  calls: %d, lookups: %d, hits: %d\n",
	    calls_tot_SM,lookups_tot_SM,hits_tot_SM);
  }  

  return formula;
}

ATerm Prove(ATerm formula) {
  FormBdd = ATtableCreate(65535,25);
  Smallest=ATtableCreate(2047,50);
  Orient=ATtableCreate(2047,50);

  formula = RWrewrite(formula);
  formula = (ATerm)orient(formula);
  formula = build_BDD(formula);

  RWflush();  
  ATtableDestroy(FormBdd);
  ATtableDestroy(Smallest);
  ATtableDestroy(Orient);

  return formula;
}

static ATermList example(ATerm BDD, ATerm polarity) {
  ATerm x,y,z;
  ATermList l;
  if (Is_ite(BDD)) {
    x=ATgetArgument(BDD,0);
    y=ATgetArgument(BDD,1);
    z=ATgetArgument(BDD,2);
    l=example(y,polarity);
    if (ATisEmpty(l)) {
      l = example(z,polarity);
      if (ATisEmpty(l))
	return ATempty;
      else 
	return ATinsert(l,prNOT(x));
    }
    else
      return ATinsert(l,x);
  }
  if (BDD==polarity) 
    return ATmakeList1(BDD);
  return ATempty;
}

void print_example(ATerm bdd, ATerm polarity, FILE* fp) {
  ATermList q;
  
  if (polarity==prFALSE)
    ATfprintf(fp,"\nFALSE SITUATION:\n");
  else if (polarity==prTRUE)
    ATfprintf(fp,"\nTRUE SITUATION:\n");
  else
    ATerror("Polarity of print_example should be TRUE/FALSE\n");
  
  q = example(bdd,polarity);
  while (!ATisEmpty(q)) {
    ATfprintf(fp,"%t\n",prettyprint(ATgetFirst(q)));
    q = ATgetNext(q);
  }
}



ATerm Simplify(ATerm term) {
  // Todo: apply 'simplifying' rules from TRS only.
  return RWrewrite(term);
}

static void parse_argument_line(int *argc,char ***argv) {
  int i, j=0;
  char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
  if (!newargv) ATerror("Cannot allocate array argv"); 
  newargv[j++] = (*argv)[0];
  for (i=1;i<*argc;i++) {
    if (!strcmp((*argv)[i],"-pr-test")) {
      TEST=1;
      continue;
      } 
    if (!strcmp((*argv)[i],"-pr-statistics")) {
      STATISTICS=1;
      continue; 
      }
    if (!strcmp((*argv)[i],"-pr-verbose")) {
      VERBOSE=1;
      continue;
      } 
    if (!strcmp((*argv)[i],"-pr-print")) {
      PRINT=1; 
      continue;
      }
    if (!strcmp((*argv)[i],"-pr-dot")) {
      DOT=1; 
      continue;
      }
    if (!strcmp((*argv)[i],"-pr-full")) {
      FULL=1; 
      continue;
    }
    if (!strcmp((*argv)[i],"-pr-reverse")) {
      FULL=1; 
      REVERSE=1; 
      continue;
    }
    if (!strcmp((*argv)[i],"-pr-lpo")) {
      LPO=1; 
      continue;
    }
    newargv[j++] = (*argv)[i];
  }
  *argc = j;  *argv = newargv;
}

static int ExitWrongArgument(int argc, char *argv[]) {
     if (argc>1) {
         ATwarning("Illegal option %s", argv[1]);
         return 0;
         }
     return 1;
     }
     
int Init_prover(ATerm datatype,int argc, char *argv[]) {
  ATerm signature;
  ATermList equations;

  parse_argument_line(&argc,&argv);

  if (!ATmatch(datatype,"d(<term>,<term>)",&signature,&equations))
    ATerror("Data specification expected.\n");

  Init_signature(signature,argc,argv);
  /* equations = ATconcat(equations,generate_reflexivities());
  datatype = ATmake("d(<term>,<term>)",signature,equations); */
  RWsetArguments(&argc, &argv);
  if (!ExitWrongArgument(argc, argv)) return 0;
  RWinitialize(datatype);
  if (VERBOSE) ATfprintf(stderr,"Prover initialized (version " VERSION ")\n");
  return 1;
}

#if MCRLLIB

void ProverSetArguments(int *argc, char ***argv) {
     parse_argument_line(argc,argv);
     SignatureSetArguments(argc, argv);  
     RWsetArguments(argc, argv);
     }

void ProverInitialize(void) {
/* Must be invoked instead of RWinitialiseRewriter after 
   ProverSetArguments() */
  SignatureInitialize();
  RWinitialize(MCRLgetAdt());

  if (VERBOSE) ATfprintf(stderr,"Prover initialized (version " VERSION ")\n");
  }
#endif

/**********************************************************/
/* later addition: bottom up construction of BDD
 */

static ATermTable CombineTable;
static Symbol iteF, orF, andF, notF;

static ATerm combine0(Symbol f) {
  ATerm result;

  assert(ATgetArity(f)==0);

  result = RWrewrite((ATerm)ATmakeAppl0(f));
  if (result != prTRUE && result != prFALSE && Sort_of(result)==prBOOL)
      result = make(result,prTRUE,prFALSE);
  return result;
}


static ATerm combine1(Symbol f, ATerm arg0) {
  ATerm result;
  
  assert(ATgetArity(f)==1);

  if (result=ATtableGet(CombineTable,arg0))
    return result;

  if (f==notF) {
    if (arg0==prTRUE) return prFALSE;
    if (arg0==prFALSE) return prTRUE;
    // test on NOT NOT?
  }

  if (arg0==prTRUE || arg0==prFALSE || Sort_of(arg0)!=prBOOL)
  { result = RWrewrite((ATerm)ATmakeAppl1(f,arg0));
    if (result != prTRUE && result != prFALSE && Sort_of(result)==prBOOL)
      result = make(result,prTRUE,prFALSE);
    return result;
  }
  
  assert(Sort_of(arg0)==prBOOL);
  if (!Is_ite(arg0))
     ATerror("Expected BDD: %t\n",arg0);

  result = make(ATgetArgument(arg0,0),
                combine1(f,ATgetArgument(arg0,1)),
                combine1(f,ATgetArgument(arg0,2)));

  ATtablePut(CombineTable,arg0,result);
  return result;
}

static ATerm combine2(Symbol f, ATerm arg0, ATerm arg1) {
  ATerm result;
  ATerm fullterm;
  ATerm smallest=NULL;

  assert(ATgetArity(f)==2);

  fullterm=(ATerm)ATmakeAppl2(f,arg0,arg1);
  if (result=ATtableGet(CombineTable,fullterm))
    return result;
  
  if (f==andF) {
    if (arg0==prTRUE) return arg1;
    if (arg0==prFALSE) return prFALSE;
    if (arg1==prTRUE) return arg0;
    if (arg1==prFALSE) return prFALSE;
    // test on idempotence?
  }
  else if (f==orF) {
    if (arg0==prTRUE) return prTRUE;
    if (arg0==prFALSE) return arg1;
    if (arg1==prTRUE) return prTRUE;
    if (arg1==prFALSE) return arg0;
    // test on idempotence?
  }

  if (arg0!=prTRUE && arg0!=prFALSE && Sort_of(arg0)==prBOOL)
  { if (!Is_ite(arg0))
      ATerror("Expected BDD: %t\n",arg0);
    smallest=ATgetArgument(arg0,0);
  }

  if (arg1!=prTRUE && arg1!=prFALSE && Sort_of(arg1)==prBOOL)
  { if (!Is_ite(arg1))
      ATerror("Expected BDD: %t\n",arg1);
    smallest=minn(smallest, ATgetArgument(arg1,0));
  }
 
  if (!smallest) {
    result = RWrewrite(fullterm);
    if (result != prTRUE && result != prFALSE && Sort_of(result)==prBOOL)
      result = make(result,prTRUE,prFALSE);
    return result;
  }

  if (arg0==prTRUE || arg0==prFALSE || Sort_of(arg0)!=prBOOL
          || ATgetArgument(arg0,0)!=smallest) 
  { result = make(smallest,
                  combine2(f,arg0,ATgetArgument(arg1,1)),
                  combine2(f,arg0,ATgetArgument(arg1,2)));
  }
  else  
  if (arg1==prTRUE || arg1==prFALSE || Sort_of(arg1)!=prBOOL   
          || ATgetArgument(arg1,0)!=smallest)   
  { result = make(smallest,
                  combine2(f,ATgetArgument(arg0,1),arg1),
                  combine2(f,ATgetArgument(arg0,2),arg1));
  }  
  else
   result = make(smallest,
                 combine2(f,ATgetArgument(arg0,1),ATgetArgument(arg1,1)),
                 combine2(f,ATgetArgument(arg0,2),ATgetArgument(arg1,2)));

  ATtablePut(CombineTable,fullterm,result);
  return result;
}

static ATerm combine3(Symbol f, ATerm arg0, ATerm arg1,ATerm arg2) {
  ATerm result;
  ATerm fullterm;
  ATerm smallest=NULL;

  assert(ATgetArity(f)==3);

  fullterm=(ATerm)ATmakeAppl3(f,arg0,arg1,arg2);
  if (result=ATtableGet(CombineTable,fullterm))
    return result;

  if (f==iteF) {
    if (arg0==prTRUE) return arg1;
    if (arg0==prFALSE) return arg2;
    // test on idempotence?
  }

  if (arg0!=prTRUE && arg0!=prFALSE && Sort_of(arg0)==prBOOL)
  { if (!Is_ite(arg0))
      ATerror("Expected BDD: %t\n",arg0);
    smallest=ATgetArgument(arg0,0);
  }

  if (arg1!=prTRUE && arg1!=prFALSE && Sort_of(arg1)==prBOOL)
  { if (!Is_ite(arg1))
      ATerror("Expected BDD: %t\n",arg1);
    smallest=minn(smallest, ATgetArgument(arg1,0));
  }

  if (arg2!=prTRUE && arg2!=prFALSE && Sort_of(arg2)==prBOOL)
  { if (!Is_ite(arg2))
      ATerror("Expected BDD: %t\n",arg2);
    smallest=minn(smallest, ATgetArgument(arg2,0));
  }

  if (!smallest) {
    result = RWrewrite(fullterm);
    if (result != prTRUE && result != prFALSE && Sort_of(result)==prBOOL)
      result = make(result,prTRUE,prFALSE);
    return result;
  }

  if (arg0==prTRUE || arg0==prFALSE || Sort_of(arg0)!=prBOOL
          || ATgetArgument(arg0,0)!=smallest)
  { if (arg1==prTRUE || arg1==prFALSE || Sort_of(arg1)!=prBOOL
          || ATgetArgument(arg1,0)!=smallest)
    { result = make(smallest,
                  combine3(f,arg0,arg1,ATgetArgument(arg2,1)),
                  combine3(f,arg0,arg1,ATgetArgument(arg2,2)));
    }
    else
    if (arg2==prTRUE || arg2==prFALSE || Sort_of(arg2)!=prBOOL
          || ATgetArgument(arg2,0)!=smallest)
    { result = make(smallest,
                  combine3(f,arg0,ATgetArgument(arg1,1),arg2),
                  combine3(f,arg0,ATgetArgument(arg1,2),arg2));
    }
    else
    { result = make(smallest,
                  combine3(f,arg0,ATgetArgument(arg1,1),ATgetArgument(arg2,1)),
                  combine3(f,arg0,ATgetArgument(arg1,2),ATgetArgument(arg2,2)));
    }
  }
  else
  { if (arg1==prTRUE || arg1==prFALSE || Sort_of(arg1)!=prBOOL
          || ATgetArgument(arg1,0)!=smallest)
    { if (arg2==prTRUE || arg2==prFALSE || Sort_of(arg2)!=prBOOL 
            || ATgetArgument(arg2,0)!=smallest)
	{ result = make(smallest,
			combine3(f,ATgetArgument(arg0,1),arg1,arg2),
			combine3(f,ATgetArgument(arg0,2),arg1,arg2));
	}

      else
	{ result = make(smallest,
			combine3(f,ATgetArgument(arg0,1),arg1,ATgetArgument(arg2,1)),
			combine3(f,ATgetArgument(arg0,2),arg1,ATgetArgument(arg2,2)));
	}
    }
    else
    if (arg2==prTRUE || arg2==prFALSE || Sort_of(arg2)!=prBOOL 
          || ATgetArgument(arg2,0)!=smallest)
    { result = make(smallest,
                  combine3(f,ATgetArgument(arg0,1),ATgetArgument(arg1,1),arg2),
                  combine3(f,ATgetArgument(arg0,2),ATgetArgument(arg1,2),arg2));
    }
    else
    { result = make(smallest,
                  combine3(f,ATgetArgument(arg0,1),
                             ATgetArgument(arg1,1),
                             ATgetArgument(arg2,1)),
                  combine3(f,ATgetArgument(arg0,2),
                             ATgetArgument(arg1,2),
                             ATgetArgument(arg2,2)));
    }
  }

  ATtablePut(CombineTable,fullterm,result);
  return result;
}

static ATerm combine(Symbol f, ATermList args) {
  ATerm result;
  ATerm smallest=NULL;
  ATermList l;

  if (result=ATtableGet(CombineTable,(ATerm)args))
    return result;
  
  
  for (l=args;!ATisEmpty(l);l=ATgetNext(l)) {
    ATerm first = ATgetFirst(l);
    if (first==prTRUE || first==prFALSE || Sort_of(first)!=prBOOL)
      continue;
    if (!Is_ite(first))
      ATerror("Expected BDD: %t\n",first);
    smallest=minn(smallest, ATgetArgument(first,0));
  }
  if (!smallest) {
    ATerm result = RWrewrite((ATerm)ATmakeApplList(f,args));
    if (result != prTRUE && result != prFALSE && Sort_of(result)==prBOOL)
      result = make(result,prTRUE,prFALSE);
    return result;
  }
  else {
    ATermList args1 = ATempty;
    ATermList args2 = ATempty;
    for (l=ATreverse(args);!ATisEmpty(l);l=ATgetNext(l)) {
      ATerm first = ATgetFirst(l);
      if (first==prTRUE || first==prFALSE || Sort_of(first)!=prBOOL
	  || ATgetArgument(first,0)!=smallest) {
	args1 = ATinsert(args1,first);
	args2 = ATinsert(args2,first);
      }
      else {
	args1 = ATinsert(args1,ATgetArgument(first,1));
	args2 = ATinsert(args2,ATgetArgument(first,2));
      }
    }
    result = make(smallest,combine(f,args1),combine(f,args2));
    ATtablePut(CombineTable,(ATerm)args,result);
    return result;
  }
}

ATerm Combine(Symbol f, ATermList args) {
/* static has been removed by jfg, 3/1/3 */
  ATerm result;
  int n=ATgetArity(f);
  if (n==0) return combine0(f);

  CombineTable = ATtableCreate(1024,75);
  switch (ATgetArity(f)) 
  { case 1: result=combine1(f,ATgetFirst(args));
            break;
    case 2: result=combine2(f,ATgetFirst(args),ATgetFirst(ATgetNext(args)));
            break;
    case 3: result=combine3(f,
                            ATgetFirst(args),
                            ATgetFirst(ATgetNext(args)),
                            ATgetFirst(ATgetNext(ATgetNext(args))));
            break;
    default: result=combine(f,args);
  }
  ATtableDestroy(CombineTable);
  return result;
}

static ATermTable BottomupTable;

static ATerm bottomup(ATerm formula) {
  ATerm result;
  if (formula==prTRUE) return formula;
  if (formula==prFALSE) return formula;
  if (result=ATtableGet(BottomupTable,formula))
    return result;

  // ATfprintf(stderr,"bu: %t\n",formula);
  {
    Symbol s = ATgetSymbol(formula);
    int i, n=ATgetArity(s);
    ATermList news = ATempty;
    for (i=n-1; i>=0; i--) { // processing arguments this way avoids ATreverse
      ATerm arg = ATgetArgument(formula,i);
      //      if (Sort_of(arg)==prBOOL)
      arg = bottomup(arg);
      news = ATinsert(news,arg);
    }
    result = Combine(s,news);
    ATtablePut(BottomupTable,formula,result);
    return result;
  }
}

static ATerm Bottomup(ATerm formula) {
  ATerm result;
  BottomupTable=ATtableCreate(1024,75);
  result = bottomup(formula);
  ATtableDestroy(BottomupTable);
  return result;
}

static ATermTable EqbddTable;

static ATerm eqbdd(ATerm formula) {
  ATerm result;
  if (formula==prTRUE || formula==prFALSE)
    return formula;
  if (result=ATtableGet(EqbddTable,formula))
    return result;
  if (Is_eq(ATgetArgument(formula,0)))
    result = Prove(formula);
  else
    result = make(ATgetArgument(formula,0),
		  eqbdd(ATgetArgument(formula,1)),
		  eqbdd(ATgetArgument(formula,2)));
  ATtablePut(EqbddTable,formula,result);
  return result;
}

static ATerm Eqbdd(ATerm formula) {
  ATerm result;
  EqbddTable=ATtableCreate(1024,75);
  result = eqbdd(formula);
  ATtableDestroy(EqbddTable);
  return result;
}

ATerm Prove2(ATerm formula) { 
  iteF = ATgetSymbol(prITE(prTRUE,prTRUE,prTRUE));
  andF = ATgetSymbol(prAND(prTRUE,prTRUE));
  orF  = ATgetSymbol(prOR(prTRUE,prTRUE));
  notF = ATgetSymbol(prNOT(prTRUE));

  if (TEST) fprintf(stderr,"\nRewriting... ");
  formula = RWrewrite(formula);
  RWflush();

  if (TEST) fprintf(stderr,"Orienting... ");
  Orient=ATtableCreate(2047,50);
  formula = orient(formula);
  ATtableDestroy(Orient);
  
  if (TEST) fprintf(stderr,"Bottoming... ");
  formula = Bottomup(formula);

  if (TEST) fprintf(stderr,"Eqbdding... ");
  formula = Eqbdd(formula); 
  
  if (TEST) fprintf(stderr,"Ready\n");
  return formula;
}

/* **************************** */

/* Experimental part: dealing wiht inequalities */

/* Floyd-Warshall All-Pairs-Shortest-Path algorithm 
   Input: adjacency matrix P, with filled part 0..n-1
   Output: 1 if P contains negative cycles, 0 otherwise.
   If no negative cycles exist, P will be the table with 
   shortest paths. Matrix N is an auxiliary matrix.
 */

#include <limits.h>

#define MAX 50
static int P[MAX][MAX];
static int NN[MAX][MAX];

static void print_matrix(int A[MAX][MAX],int n) {
  int i,j;
  for (i=0;i<n;i++) {
    for (j=0;j<n;j++) 
      if (A[i][j]==INT_MAX)
	fprintf(stderr,"#\t");
      else
	fprintf(stderr,"%d\t",A[i][j]);
    fprintf(stderr,"\n");
  }
  fprintf(stderr,"\n");
}

static char check_negative_cycle(int n) {
  int x,k,i,j;

  /* Start adding reflexive closure */

  for (i=0;i<n;i++)
    if (P[i][i]<0) return 1;
    else P[i][i]=0;

  /* Floyd-Warshall: 
     P(k+1)[i][j] = minn(P(k)[i][j] , P(k)[i][k]+P(k)[k][j]
  */
  for (k=0;k<n;k++) {
    for (i=0;i<n;i++)
      for (j=0;j<n;j++) {
	if (P[i][k]==INT_MAX) x=INT_MAX;
	else if (P[k][j]==INT_MAX) x=INT_MAX;
	else x = P[i][k] + P[k][j];
	NN[i][j] = (x<P[i][j] ? x : P[i][j]);
	if (i==j && NN[i][j]<0) return 1;
      }
    
    for (i=0;i<n;i++)
      for (j=0;j<n;j++)
	P[i][j]=NN[i][j];
    
    /* print_matrix(P,n); */
  }
  return 0;
}

char UNSAT_INEQ(ATermList List) {
  Symbol zeroSym = ATmakeSymbol("0#",0,1);
  Symbol succSym = ATmakeSymbol("s#Nat",1,1);
  Symbol leSym   = ATmakeSymbol("le#Nat#Nat",2,1);
  Symbol eqSym   = ATmakeSymbol("eq#Nat#Nat",2,1);
  ATermIndexedSet Vartable = ATindexedSetCreate(64,50);
  long zero=ATindexedSetPut(Vartable,(ATerm)ATmakeAppl0(zeroSym),NULL);
  int i,j,k=zero; /* highest index in Vartable */
  ATbool b;

  for (i=0;i<MAX;i++)
    for (j=0;j<MAX;j++)
      P[i][j]=INT_MAX;

  while (!ATisEmpty(List)) {
    ATerm guard = ATgetFirst(List);
    Symbol p = ATgetSymbol(guard);
    List = ATgetNext(List);
    if (p==leSym || p==eqSym) {
      ATerm left = ATgetArgument(guard,0);
      ATerm right = ATgetArgument(guard,1);
      long i,j;
      int n=0;
      while (ATgetSymbol(left)==succSym) {
	n--;
	left = ATgetArgument(left,0);
      }
      while (ATgetSymbol(right)==succSym) {
	n++;
	right = ATgetArgument(right,0);
      }
      i = ATindexedSetPut(Vartable,left,&b);
      if (b) k++;
      j = ATindexedSetPut(Vartable,right,&b);
      if (b) k++;
      /* we now have that guard is of the form x_i ~p~ x_j + n */
      P[i][j]=n;
      if (VERBOSE) fprintf(stderr,"x%ld <= x%ld + %d\n",i,j,n);
      if (p==eqSym) {
	P[j][i]= -n;
	if (VERBOSE) fprintf(stderr,"x%ld <== x%ld + %d\n",j,i,-n);
      }
    }
    else if (guard==MCRLterm_false) {
      ATindexedSetDestroy(Vartable);
      return 1;
    }
    /* next make sure 0 <= x_i for all i in table */
    for (i=0;i<=k;i++)
      if (P[zero][i]>0) P[zero][i]=0;
  }
  if (VERBOSE) print_matrix(P,k+1);
  b=check_negative_cycle(k+1);
  if (!b && VERBOSE) print_matrix(P,k+1);
  ATindexedSetDestroy(Vartable);
  return b;
}

static ATermIndexedSet PathTable;

static void paths_rec(ATerm BDD, ATermList path) {
  if (Is_ite(BDD)) {
    ATerm guard = ATgetArgument(BDD,0);
    Symbol p = ATgetSymbol(guard);
    ATermList L1,L2;

    if (p==ATmakeSymbol("eq#Nat#Nat",2,1)
	|| p==ATmakeSymbol("ge#Nat#Nat",2,1)) {
      L1 = ATinsert(path,MCRLprint(guard));
      L2 = ATinsert(path,MCRLprint(prNOT(guard)));
      ATindexedSetPut(PathTable,(ATerm)L1,NULL);
      ATindexedSetPut(PathTable,(ATerm)L2,NULL);
    }
    else
      L1 = L2 = path;
    paths_rec(ATgetArgument(BDD,1),L1);
    paths_rec(ATgetArgument(BDD,2),L2);
  }
}

void Paths(ATerm BDD) {
  ATermList List;
  PathTable = ATindexedSetCreate(64,50);
  paths_rec(BDD,ATempty);
  List = ATindexedSetElements(PathTable);
  while (!ATisEmpty(List)) {
    ATfprintf(stderr,"%t\n",ATgetFirst(List));
    List = ATgetNext(List);
  }
  ATindexedSetDestroy(PathTable);
}

static ATerm simpIneq(ATerm BDD, ATermList path) {
  if (Is_ite(BDD)) {
    ATerm guard = ATgetArgument(BDD,0);
    Symbol p = ATgetSymbol(guard);
    if (p==ATmakeSymbol("eq#Nat#Nat",2,1)
	|| p==ATmakeSymbol("le#Nat#Nat",2,1)) {
      ATermList L1 = ATinsert(path,RWrewrite(guard));
      ATermList L2 = ATinsert(path,RWrewrite(prNOT(guard)));
      if (UNSAT_INEQ(L1))
	return simpIneq(ATgetArgument(BDD,2),path);
      else if (UNSAT_INEQ(L2))
	return simpIneq(ATgetArgument(BDD,1),path);
      else
	return make(guard,
		   simpIneq(ATgetArgument(BDD,1),L1),
		   simpIneq(ATgetArgument(BDD,2),L2));
    }
    else
      return make(guard,
		 simpIneq(ATgetArgument(BDD,1),path),
		 simpIneq(ATgetArgument(BDD,2),path));
  }
  else
    return BDD;
}

ATerm SimpIneq(ATerm BDD) {
  return simpIneq(BDD,ATempty);
}

void starttest(void){TEST=1;}
