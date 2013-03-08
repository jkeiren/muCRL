#include "aterm2.h"
#include "prover.h"
#include "mcrl.h"
#include "usechange.h"

#include <string.h>
#include <assert.h>
#include <stdlib.h>

#define MY_NAME "Confelm"
// VERSION assumed to be defined with -DVERSION=\"...\"

#define BUFFERLENGTH 1000

static char QUICK=1;
static char VERBOSE=1;
static char COUNTER=0;
static char PRINT=0;
static int SUMMAND=-1;
static int TOTAL = 0;

static char* Inv_file=0;

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
  ATfprintf(stderr,"%s\n",
	    "Usage: confelm [options] [lpo.tbf]\n"
            "Reads LPO from lpo.tbf or from stdin and writes to stdout.\n\n"
	    "Confelm applies a symbolic reduction on LPOs. This\n"
            "reduction preserves branching bisimulation, but not\n"
            "strong bisimulation, in general. Intermediate states\n"
	    "are eliminated by concatenating ctau-steps immediately\n"
	    "after non-ctau-steps. These ctau-steps are assumed to be\n"
	    "confluent, and are typically generated with 'confcheck -mark'."
	    );
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-invariant <file>: "
	    "uses the invariant in <file>. The invariant is not checked!\n"
	    "                   "           
	    "<file> contains a term of type Bool; parameters may occur.");
  ATfprintf(stderr,"%s\n",
	    "-summand <n>   : "
	    "applies to n'th summand only (should not be a ctau)\n"
	    "                 "           
	    "if n=0, then it applies only to the intial state");
  ATfprintf(stderr,"%s\n",
	    "-quick        : "
	    "a quicker variant, which is less complete");
  ATfprintf(stderr,"%s\n",
	    "-silent        : "
	    "suppresses information on stderr");
  ATfprintf(stderr,"%s\n",
	    "-print         : "
	    "prints resulting BDDs (use for small examples only)");
  ATfprintf(stderr,"%s\n",
	    "-counter       : "
	    "prints counter-examples when ctau steps are not enabled");
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
    if (!strcmp(argv[i],"-quick"))
      QUICK=1; 
    if (!strcmp(argv[i],"-summand")) {
      SUMMAND=atoi(argv[++i]); 
      argv[i]="-"; // needed because otherwise MCRLsetArguments might take it as filename.
    }
    if (!strcmp(argv[i],"-invariant")) {
      Inv_file=argv[++i]; 
      argv[i]="-"; // needed because otherwise MCRLsetArguments might take it as filename.
    }
    if (!strcmp(argv[i],"-help"))
      help(); 
    if (!strcmp(argv[i],"-version"))
      version();
  }
}

static ATermList make_termlist(ATermList vars) { 
  char *var, *sort;
  if (ATmatch((ATerm)vars,"[v(<str>,<str>),<list>])",
	      &var,&sort,&vars))
    return ATinsert(make_termlist(vars),
		    ATmake("<str>",var));
  if (!ATmatch((ATerm)vars,"[]"))
     ATerror("Expect variable list: %t\n",vars);
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

static ATerm check_guard(ATermList parameters, ATermList sum1,
                   ATermList g1, ATerm b1, ATerm b2, ATerm Inv) {
  ATerm formula;
  formula = substitute(g1,parameters,b2);
  // ATfprintf(stderr,"\n%t\n",prettyprint(formula));

  if (QUICK) b1=prTRUE;
  formula = prIMPLIES(prAND(Inv,b1),formula);
  //  ATfprintf(stderr,"\n%t\n",prettyprint(formula));
  return Prove(formula);
}

static ATermList find_successor(ATermList Sums, ATermList parameters, 
	        ATermList sum1, ATerm b1, ATermList g1, ATerm Inv,
	        int acount, LPO_t lpo) { 
  ATerm summand, b2, result;
  ATermList sum2, f2, g2, current_state=g1;
  char *a, *loop, iteration=1;
  FINSET_t changeset = emptyset(LPOnPars(lpo));
  
  // special case: acount = 0: initial state!
  // variable changeset is only defined when acount>0
  
  if (acount>0) merge(changeset,Changed_set(lpo,acount-1));
  
  loop = (char*)calloc(ATgetLength(Sums),sizeof(char));
  if (!loop) ATerror("out of memory!\n");
  
  while (iteration) {
    int count=0;
    ATermList sums=Sums;
    iteration=0;
    while (!ATisEmpty(sums)) {
      count++;
      summand = ATgetFirst(sums);
      sums = ATgetNext(sums);
      if (!ATmatch(summand,"smd(<term>,<str>,<term>,i(<term>),<term>)",
		   &sum2,&a,&f2,&g2,&b2))
	ATerror("Expect summand %t",summand);
      
      if (!strcmp(a,"ctau") && ATisEmpty(sum2) && !loop[count-1]) {
	// fprintf(stderr,"(%d)",count);
	if (acount>0 && disjoint(Used_in_guard_set(lpo,count-1),changeset)) {
	  // fprintf(stderr,"no");
	  continue; // no parameters used in condition of this summand changed: try next one.
	}
	result = check_guard(parameters,sum1,current_state,b1,b2,Inv);
	if (result==prTRUE) {
	  if (VERBOSE) 
	    fprintf(stderr," %d",count);
	  current_state = substitute_list(current_state,parameters,g2);
	  loop[count-1]=1;
	  if (acount>0) merge(changeset,Changed_set(lpo,count-1));
	  iteration=1;
	  break; // try to find the next ctau successor
	}
	else {
	  if (PRINT) print_BDD(result,stderr);
	  if (COUNTER) print_example(result,prFALSE,stderr);
	}
      }
    }
  }
  if (VERBOSE)
    fprintf(stderr,"\n");
  if (current_state!=g1)
    TOTAL++;
  return current_state;
}

static ATerm process_summands(ATerm LPO,ATerm Inv)
{
  ATermList parameters=NULL, sums=NULL, init=NULL; 
  ATermList sum=NULL, f=NULL, g=NULL;
  ATerm b=NULL;
  ATerm summand=NULL;
  ATermList Sums=NULL;
  ATermList todo=NULL;
  LPO_t lpo;
  int count=0;
  char *a;

  if (!ATmatch(LPO,"initprocspec(<term>,<term>,<term>))",
	       &init,&parameters,&sums))
    ATerror("Expect process specification\n");

  lpo=LPOfrom2gen(LPO);
  UCinitialize(lpo);
    
  Declare_vars(parameters);
  
  if (!Inv) 
    Inv=prTRUE;

  if (SUMMAND<=0) {
    if (VERBOSE) ATfprintf(stderr,"init has successor:");
    init=find_successor(sums,parameters,ATmakeList0(),prTRUE,init,Inv,0,lpo);
  }

  Sums=ATmakeList0();
  todo=sums;

  while (!ATisEmpty(todo)) {
    summand = ATgetFirst(todo);
    todo = ATgetNext(todo);
    count++;
    if (!ATmatch(summand,"smd(<term>,<str>,<term>,i(<term>),<term>)",
		 &sum,&a,&f,&g,&b))
      ATerror("Summand expected\n");

    if (strcmp(a,"ctau") && ((SUMMAND<0) || (count==SUMMAND))) {
      // this is a non-tau summand that the user wants to process: 

      if (VERBOSE) ATfprintf(stderr,"summand %d has successor:",count);

      Declare_vars(sum);
      g = find_successor(sums,parameters,sum,b,g,Inv,count,lpo);
      summand = ATmake("smd(<term>,<str>,<term>,i(<term>),<term>)",
		       sum,a,f,g,b);
    }
    else
      if (count==SUMMAND)
	ATerror("Summand %d should not be a ctau-summand",SUMMAND);
    
    Sums = ATinsert(Sums,summand);
  }
  LPO = ATmake("initprocspec(<term>,<term>,<term>)",
	       init,parameters,ATreverse(Sums));
  return LPO;
}

int main(int argc, char *argv[]) { 
  ATerm bottomOfStack=NULL;
  ATerm LPO=NULL, Inv=NULL;
  FILE *fp;

  ATinit(argc,argv,&bottomOfStack);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);

  ATprotect(&LPO);
  ATprotect(&Inv);

  parse_argument_line(argc,argv);

  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize\n");
  
  LPO=MCRLgetProc();

  ProverSetArguments(&argc,&argv);
  ProverInitialize();

  MCRLdeclareVars(MCRLgetListOfPars());

  if (Inv_file) {
    fp = fopen(Inv_file,"r");
    if (!fp) {
      perror(Inv_file);
      exit(1);
    }
    Inv=read_formula(fp);
    if (Inv==NULL) 
     ATerror("Invariant file %s is wrong\n",Inv_file);
  }

  MCRLsetProc(process_summands(LPO,Inv));
  
  MCRLoutput();
  ATwarning("Priorized %d summands (or init)\n",TOTAL);
  return 0;
}
