/* Jaco.van.de.Pol@cwi.nl

   This program tries to prove the negation of each guard
   to be an invariant. If this succeeds, the summand can
   be removed.

   Given parameters x, and summands
     sum(y,.. <| b1(x,y) |> delta)
     sum(z,. X(g(x,z)) <| b2(x,z) |> delta)

   we should prove:
    FORALL x,z. ((FORALL y. NOT b1(x,y)) & b2(x,z))
                IMPLIES (FORALL y. NOT b1(g(x,z),y))

   Instead, we prove the weaker (and easier):
    FORALL x,y,z. ((NOT b1(x,y)) & b2(x,z)) IMPLIES NOT b1(g(x,z),y)
		
   6/6/2001, Jaco van de Pol (Jaco.van.de.Pol@cwi.nl)

   Later improvement: we start from the initial state, and see which
   summands can be reached, using the above formulae. This is stronger,
   in case a number of unreachable summands enable each other.

   We use breadth first search, to report the shortest path from
   init to summand.
   1/1/2002
*/

#include "aterm2.h"
#include "mcrl.h"
#include "prover.h"
#include "usechange.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#define MY_NAME "Reachelm"
// VERSION assumed to be defined with -DVERSION=\"...\"

char PRINT=0;
char COUNTER=0;
static char VERBOSE=1;
static int REM=0; // number of removed summands.
static int KEPT=0; // number of kept summands.

static void WarningHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     }
     
static void ErrorHandler(const char *format, va_list args)
     {
     fprintf(stderr,"%s: ", MY_NAME);
     ATvfprintf(stderr, format, args);
     fprintf(stderr,"\n");
     exit(-1);
     }

void version() {
  fprintf(stderr,"%s (version %s)\n",MY_NAME, VERSION);
  exit(0);
}

void help() {
  ATfprintf(stderr,"%s",
	    "Usage: reachelm [options] [lpo.tbf]\n"
	    "Reads LPO from lpo.tbf or stdin and writes LPO to stdout.\n"
	    "Removes summands by proving that they are not reachable\n\n"
	    "Reachelm marks in a breadth-first search all summands that\n"
	    "might be enabled in the initial state or by enabled summands.\n"
	    "All unmarked summands are removed. The output reflects a minimal\n"
	    "execution from the initial state to the preserved summands.\n\n"
	    );
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-silent        : "
	    "suppress information per summand");
  ATfprintf(stderr,"%s\n",
	    "-print         : "
	    "prints resulting BDDs (use for small examples only)");
  ATfprintf(stderr,"%s\n",
	    "-counter       : "
	    "prints counter-examples");
  ATfprintf(stderr,"%s\n",
	    "-version       : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-help          : "
	    "prints this message");
  ATfprintf(stderr,"%s\n","");
  MCRLhelp();
  exit(0);
}

void parse_argument_line(int argc,char *argv[]) {
  int i;
  
  for (i=1;i<argc;i++) {
    if (!strcmp(argv[i],"-counter"))
      COUNTER=1; 
    if (!strcmp(argv[i],"-print"))
      PRINT=1; 
    if (!strcmp(argv[i],"-silent"))
      VERBOSE=0; 
    if (!strcmp(argv[i],"-help"))
      help(); 
    if (!strcmp(argv[i],"-version"))
      version();
  }
}

static ATermList create_variables_rec(ATermList sum, char* suffix)
{ /* TODO check that new variable names have not been 
     used elsewhere */

  char *var;
  char buffer[100];
  ATerm sort;
  if (ATmatch((ATerm)sum,"[v(<str>,<term>),<list>]",
              &var, &sort, &sum))
   { if (strlen(var)+strlen(suffix)>=100)
        ATerror("String too long: %s",var);

   // assumption: var is of the form "....#...." 
   // result: "..._suffix#..."

     var = strtok(var,"#");
     sprintf(buffer,"%s%s%s",var,suffix,"#");
     return ATinsert(create_variables_rec(sum,suffix),
		     ATmake("v(<str>,<term>)]",buffer,sort));
   }
  if (!ATmatch((ATerm)sum,"[]"))
     ATerror("Expect variablelist: %t",sum);
  return sum;   
}

static ATermList make_termlist(ATermList vars) { 
  char *var, *sort;
  if (ATmatch((ATerm)vars,"[v(<str>,<str>),<list>])",
	      &var,&sort,&vars))
    return ATinsert(make_termlist(vars),
		    ATmake("<str>",var));
  if (!ATmatch((ATerm)vars,"[]"))
     ATerror("Expect variable list: %t",vars);
  return ATmakeList0();
}


static ATerm substitute_const(ATermList termlist, ATermList varlist,ATerm v)
{ ATerm var;
  while (!ATisEmpty(termlist)) {
    assert(!ATisEmpty(varlist));
    var=ATgetFirst(varlist); 
    // var is of the form v(name,sort)
    if (v==ATgetArgument(var,0)) 
      return ATgetFirst(termlist);
    termlist=ATgetNext(termlist);
    varlist=ATgetNext(varlist);
  }
  assert(ATisEmpty(varlist));
  return v;
}

static ATerm substitute(ATermList termlist, ATermList varlist,ATerm t);

static ATermList substitute_list(ATermList termlist, ATermList varlist,ATermList tl) {
  ATerm t1;
  if (ATisEmpty(tl)) return tl;
  
  t1 = substitute(termlist,varlist,ATgetFirst(tl));
  tl = substitute_list(termlist,varlist,ATgetNext(tl));
  return ATinsert(tl,t1);
}

static ATerm substitute(ATermList termlist, ATermList varlist,ATerm t)
{ 
  Symbol f;
  f = ATgetSymbol(t);
  if (ATgetArity(f)==0)
    { return substitute_const(termlist,varlist,t);
    }
  return (ATerm)ATmakeApplList(f,
			       substitute_list(termlist,varlist,
					       ATgetArguments((ATermAppl)t)));
}

int *s;
ATerm *b, *notb;
ATermList *v, *ev, *g;
int *queue;
int start=0,stop=0;

/*
 * v[i] the variables of summand i
 * ev[i] fresh names for summand i
 * b[i] the guard of summand i
 * notb[i] the negation of summand i with fresh names
 * g[i] the next state of summand i
 * s[i]: status of summand i:
 *   0: not visited
 *   1: visited during BFS
 * queue[] the queue used for breadth-first search.
 * start,stop = begin and end pointers in the queue
 *  (stop = first empty position, start = first unexplored position)
 */

int main(int argc, char *argv[])
{ ATerm bottomOfStack=NULL;
  ATerm LPO=NULL, formula=NULL;
  ATermList init=NULL,sums=NULL,finsums=NULL,parameters=NULL;
  int i,j,N;
  LPO_t lpo;

  parse_argument_line(argc,argv);
 
  ATinit(argc,argv,&bottomOfStack);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);

  ATprotect(&LPO);
  ATprotect((ATerm*)&sums);
  ATprotect((ATerm*)&finsums);
  ATprotect((ATerm*)&parameters);
  ATprotect((ATerm*)&init);
  ATprotect(&formula);
  
  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");

  LPO=MCRLgetProc();

  if (!ATmatch(LPO,"initprocspec(<term>,<term>,<term>)",
	       &init,&parameters,&sums))
    ATerror("Expect LPO");

  lpo = LPOfrom2gen(LPO);
  UCinitialize(lpo);
  
  ProverSetArguments(&argc,&argv);
  ProverInitialize();

  Declare_vars(parameters);

  N = ATgetLength(sums);
  s = (int*)calloc(N,sizeof(int));
  b = (ATerm*)calloc(N,sizeof(ATerm));
  notb = (ATerm*)calloc(N,sizeof(ATerm));
  v = (ATermList*)calloc(N,sizeof(ATerm));
  ev = (ATermList*)calloc(N,sizeof(ATerm));
  g = (ATermList*)calloc(N,sizeof(ATerm));
  queue=(int*)calloc(N,sizeof(int));

  ATprotectArray(b,N);
  ATprotectArray(notb,N);
  ATprotectArray((ATerm*)v,N);
  ATprotectArray((ATerm*)ev,N);
  ATprotectArray((ATerm*)g,N);

  for (i=0;i<N;i++) {
    ATermList vt=NULL;
    if (!ATmatch(ATelementAt(sums,i),
		 "smd(<term>,<str>,<term>,i(<term>),<term>)",
		 &(v[i]),NULL,NULL,&(g[i]),&(b[i])))
      ATerror("Summand expected");
    ev[i] = create_variables_rec(v[i],"_a1");
    vt = make_termlist(ev[i]);
    notb[i] = substitute(vt,v[i],prNOT(b[i]));


    formula = substitute(init,parameters,notb[i]);
    Declare_vars(ev[i]);
    formula = Prove(formula);
    if (formula!=prTRUE) {
      KEPT++;
      if (VERBOSE)
	ATwarning("%d: Summand %d might be enabled initially",KEPT,i+1);
      s[i]=1;
      queue[stop++]=i;
      if (PRINT) print_BDD(formula,stderr);
      if (COUNTER) print_example(formula,prFALSE,stderr);
    }
    else s[i]=0;
  }
  
  while (start<stop) {
    i = queue[start++];
    Declare_vars(v[i]);
    
    for (j=0;j<N;j++) {

      if (s[j] != 0)
	continue; // j has been visited already
      
      if (disjoint(Used_in_guard_set(lpo,j),Changed_set(lpo,i)))
      	continue; // need not check with independent summand
      
      // fprintf(stderr,"i,j=%d,%d\n",i+1,j+1);
      
      Declare_vars(ev[j]);
      formula = prIMPLIES(prAND(b[i],notb[j]),
			substitute(g[i],parameters,notb[j]));

      formula = Prove(formula);
      if (formula!=prTRUE) {
	  KEPT++;
	  if (VERBOSE)
	    ATwarning("%d: Summand %d might be enabled by %d",KEPT,j+1,i+1);
	  s[j]=1;
	  queue[stop++]=j;
	  if (PRINT) print_BDD(formula,stderr);
	  if (COUNTER) print_example(formula,prFALSE,stderr);
	}
    }
  }
  if (VERBOSE) ATwarning("-------------------------");
  
  finsums=ATmakeList0();
  for (i=0;i<N;i++) {
    if (s[i]==0) {
      REM++;
      if (VERBOSE)
	ATwarning("Summand %d is removed",i+1);
    }
    else
      finsums = ATinsert(finsums,ATgetFirst(sums));
    sums = ATgetNext(sums);
  }
  finsums = ATreverse(finsums);

  MCRLsetProc(ATmake("initprocspec(<term>,<term>,<term>)",
		     init,parameters,finsums));
  MCRLoutput();

  ATwarning("Removed %d out of %d summands.",REM,N);
  return 0;
}
