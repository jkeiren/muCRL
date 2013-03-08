/*  $Id: invcheck.c,v 1.3 2005/03/11 16:55:15 bertl Exp $
This program generates the invariance conditions for an LPO,

   12/07/2000 Jaco van de Pol
   - hold in initial state
   - are preserved for each summand
    
   8/12/2000  and also checks them.

*/
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "aterm2.h"
#include "mcrl.h"
#include "prover.h"
#include <assert.h>

#define MY_NAME "Invcheck"
// VERSION assumed to be defined with -DVERSION=\"...\"

char PRINT=0;
char DOT=0;
char COUNTER=0;
static char VERBOSE=0;
char GENERATE=0;
static char ALL=0;

char* Inv_file=0;

void version() {
  fprintf(stderr,"%s (version %s)\n",MY_NAME, VERSION);
  exit(0);
}

void help() {
  ATfprintf(stderr,"%s\n",
	    "invcheck -invariant file1 [options] [file2]\n"
	    "-- checks whether the invariant holds");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","Reads LPO from [file2[.tbf]] or stdin and invariant from file1");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-generate      : "
	    "generates formulae without checking to stdout");
  ATfprintf(stderr,"%s\n",
	    "-all           : "
	    "doesn't terminate as soon as an invariant-violation is found");
  ATfprintf(stderr,"%s\n",
	    "-verbose       : "
	    "indicates for which summands the invariant holds");
  ATfprintf(stderr,"%s\n",
	    "-print         : "
	    "prints BDDs for failed summands in ASCII on stderr");
  ATfprintf(stderr,"%s\n",
	    "-print-dot     : "
	    "prints BDDs for failed summands in dot-format on stdout");
  ATfprintf(stderr,"%s\n",
	    "-counter       : "
	    "prints counter-examples for failed summands on stderr");
  ATfprintf(stderr,"%s\n",
	    "-version       : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-help          : "
	    "prints this message");
  ATfprintf(stderr,"%s\n",
	    "-help-mcrl     : "
	    "prints standard options of mcrl toolset");

  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","If -generate is absent, -verbose is on automatically");
  ATfprintf(stderr,"%s\n","Don't use '-generate' together with '-counter/print'");
  exit(0);
}

void parse_argument_line(int *argc,char **argv[]) {
  int i;
  int newargc=1;
  char** newargv=(char**)calloc(*argc,sizeof(char*));
  newargv[0]=(*argv)[0];
  
  for (i=1;i<*argc;i++) {
    if (!strcmp((*argv)[i],"-counter"))
      COUNTER=1; 
    else if (!strcmp((*argv)[i],"-all"))
      ALL=1;
    else if (!strcmp((*argv)[i],"-print-dot"))
      DOT=1; 
    else if (!strcmp((*argv)[i],"-print"))
      PRINT=1; 
    else if (!strcmp((*argv)[i],"-verbose"))
      VERBOSE=1; 
    else if (!strcmp((*argv)[i],"-generate"))
      GENERATE=1; 
    else if (!strcmp((*argv)[i],"-invariant"))
      Inv_file=(*argv)[++i]; 
    else if (!strcmp((*argv)[i],"-help"))
      help(); 
    else if (!strcmp((*argv)[i],"-help-mcrl")) {
      MCRLhelp();
      exit(0);
    }
    else if (!strcmp((*argv)[i],"-version"))
      version();
    else 
      newargv[newargc++]=(*argv)[i];
  }
  *argv=newargv;
  *argc=newargc;

  if (!Inv_file) ATerror("Invariant file required '-invariant file'\n");
  if (!GENERATE) VERBOSE=1;
  if (GENERATE && (DOT || PRINT || COUNTER))
    fprintf(stderr,"'-print/-print-dot/-counter' is ignored with '-generate'\n");
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

static int check_init(ATermList init,ATermList parameters, ATerm I) {
  ATerm formula;
  formula = substitute(init,parameters,I);

  if (GENERATE) {
    ATfprintf(stdout,"%t,\n", prettyprint_decls(parameters));
    ATfprintf(stdout,"%t" , prettyprint(Simplify(formula)));
    return 1;
  }
  
  formula = Prove(formula);
  if (formula==prTRUE) {
    if (VERBOSE) fprintf(stderr,"Init OK ");
    return 1;
  }
  else {
    fprintf(stderr,"Invariant doesn't hold in initial state!\n");
    if (PRINT) print_BDD(formula,stderr);
    if (DOT) dot_BDD(formula,stdout);
    if (COUNTER) print_example(formula,prFALSE,stderr);
    return 0;
  }
}

static void traverse_sums(ATermList sums, ATermList parameters, ATerm I) { 
  ATerm summand;
  ATerm b_a;
  ATerm formula;
  ATermList sum_a, f_a, g_a;
  char *a;
  int wrong=0,count=0;
  
  for( ; (!ATisEmpty(sums)) ; ) {
    summand = ATgetFirst(sums);
    sums = ATgetNext(sums);
    count++;
    if (!ATmatch(summand,"smd(<term>,<str>,<term>,i(<term>),<term>)",
		 &sum_a,&a,&f_a,&g_a,&b_a)) 
      ATerror("Expect summand %t",summand);
    
    // ATfprintf(stderr,"Action: %s\n",a);
    
    Declare_vars(sum_a);
    formula = prIMPLIES(prAND(b_a,I),substitute(g_a,parameters,I));

    if (GENERATE) {
      if (VERBOSE) ATfprintf(stderr,".");
      ATfprintf(stdout,",\n\n%t,\n",
		prettyprint_decls(ATconcat(parameters,sum_a)));
      ATfprintf(stdout,"%t",prettyprint(Simplify(formula)));
    }
    else {
      formula = Prove(formula);
      if (formula == prTRUE)
	ATfprintf(stderr,".");
      else {
	ATfprintf(stderr,"X");
	if (!ALL) {
	  sums=ATmakeList0();
	  ATfprintf(stderr,"\nNo! (summand %d violates invariant)\n",count);
	}
	if (PRINT) print_BDD(formula,stderr);
	if (DOT) dot_BDD(formula,stdout);
	if (COUNTER) print_example(formula,prFALSE,stderr);
	wrong=1;
      }
    }
  }
  if ((!GENERATE) && VERBOSE && !wrong)
    fprintf(stderr,"\nYes! invariant holds for all summands!");
  if (VERBOSE) fprintf(stderr,"\n");
}

static void check_invariance_conditions(ATerm LPO,ATerm I)
{
  ATerm init=NULL;
  ATermList parameters=NULL, sums=NULL; 

  if (!ATmatch(LPO,"initprocspec(<term>,<term>,<term>)",
	       &init,&parameters,&sums))
    ATerror("Expect LPO\n");
  
  Declare_vars(parameters);
  
  if (GENERATE) fprintf(stdout,"[");
  if (check_init((ATermList)init,parameters,I) || ALL)
    traverse_sums(sums,parameters,I);  
  if (GENERATE) fprintf(stdout,"]\n");
}

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
     
static void ExitWrongArgument(int argc, char *argv[]) {
     if (argc>1) {
         ATwarning("Illegal option %s", argv[1]);
         help();
         exit(1);
         }
     }
     
int main(int argc, char *argv[])
{ ATerm bottomOfStack=NULL;
  ATerm LPO=NULL, I=NULL;
  FILE *fp;
  ATinit(argc,argv,&bottomOfStack);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);
  ATprotect(&LPO);
  ATprotect(&I);

  parse_argument_line(&argc,&argv);
 
  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");

  LPO=MCRLgetProc();
  ProverSetArguments(&argc,&argv);
  ExitWrongArgument(argc, argv);
  ProverInitialize();

  MCRLdeclareVars(MCRLgetListOfPars());
  
  fp = fopen(Inv_file,"r");
  if (!fp) {
    perror(Inv_file);
    exit(1);
  }
  
  I = read_formula(fp);
  if (!I) 
    ATerror("Invariant file %s is wrong\n",Inv_file);
  
  check_invariance_conditions(LPO,I);
  
  return 0;
}
