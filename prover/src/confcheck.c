/* This program generates the confluence conditions for an LPO,
   according to Groote & Sellink, Confluence for Process Verification,
   TCS 170, 1996.

   Adapted 10/07/2000 by Jaco van de Pol:
   - spec2gen format
   - separate  formulae per summand
   - no assumption on clustering
   - weaker approximation without existential quantifiers

   5/06/01:
   - takes symmetry into account
*/

#include "aterm2.h"
#include "mcrl.h"
#include "prover.h"
#include "rw.h"
#include "usechange.h"
#include <string.h>
#include <assert.h>
#include <stdlib.h>

#define MY_NAME "Confcheck"
// VERSION assumed to be defined with -DVERSION=\"...\"

#define BUFFERLENGTH 1000

static char VERBOSE=1;
static char COUNTER=0;
static char PRINT=0;
static char DOT=0;
static char MARK=0;
static char GENERATE=0;
static int SUMMAND=0;
static char ALL=0;

static int SUM=0, TAU=0, CONF=0; // count statistics

static char* Inv_file=0;

int N;        // number of summands
int* A;       // A[i,j] 0:?    1: i commutes with j
int* S;       // S[i]   0:?    j: i not confluent with j

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

static void version(void) {
  fprintf(stderr,"%s (version %s)\n",MY_NAME, VERSION);
  exit(0);
}

static void help(void) {
  ATfprintf(stderr,"%s\n",
	    "confcheck [options] -- "
	    "checks which tau-summands are confluent");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","Reads LPO from stdin");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-mark          : "
	    "marks confluent tau-summands as ctau; writes LPO to stdout");
  ATfprintf(stderr,"%s\n",
	    "-generate      : "
	    "writes confluence formulae to stdout, without checking them");
  ATfprintf(stderr,"%s\n",
	    "-invariant file: "
	    "uses this invariant; it is not checked!");
  ATfprintf(stderr,"%s\n",
	    "-summand <n>   : "
	    "checks confluence of n'th summand only (should be a tau)");
  ATfprintf(stderr,"%s\n",
	    "-all           : "
	    "doesn't terminate on detection of the first non-confluence");
  ATfprintf(stderr,"%s\n",
	    "-silent        : "
	    "suppresses information on confluent taus to stderr");
  ATfprintf(stderr,"%s\n",
	    "-print         : "
	    "prints resulting BDDs in ASCII to stderr");
  ATfprintf(stderr,"%s\n",
	    "-print-dot     : "
	    "prints resulting BDDs as graphs in dot-format to stdout");
  ATfprintf(stderr,"%s\n",
	    "-counter       : "
	    "prints counter-examples to the confluence formulae");
  ATfprintf(stderr,"%s\n",
	    "-version       : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-help          : "
	    "prints this message");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n",
	    "Don't use '-generate' together with "
	    "'-mark/counter/print'");

  ATfprintf(stderr,"%s\n\n",
	    "-silent is only useful in combination "
	    "with '-mark/generate/counter/print'");
  ATfprintf(stderr,"%s\n",
	    "The report on stderr can be understood as follows: ");
  ATfprintf(stderr,"%s\n",
	    " . confluent by symmetry (previous case).\n"
	    " : confluent by syntactic disjointness.\n"
	    " + confluent by consulting the prover.\n"
	    " - not confluent after consulting prover (check why with -counter or -print(-dot)).\n");

  exit(0);
}

static void parse_argument_line(int *argc,char **argv[]) {
  int i;
  int newargc=1;
  char** newargv=(char**)calloc(*argc,sizeof(char*));
  newargv[0]=(*argv)[0];
  for (i=1;i< *argc;i++) {
    if (!strcmp((*argv)[i],"-counter"))
      COUNTER=1; 
    else if (!strcmp((*argv)[i],"-print-dot"))
      DOT=1; 
    else if (!strcmp((*argv)[i],"-print"))
      PRINT=1; 
    else if (!strcmp((*argv)[i],"-mark"))
      MARK=1; 
    else if (!strcmp((*argv)[i],"-silent"))
      VERBOSE=0; 
    else if (!strcmp((*argv)[i],"-generate"))
      GENERATE=1; 
    else if (!strcmp((*argv)[i],"-all"))
      ALL=1;
    else if (!strcmp((*argv)[i],"-summand"))
      SUMMAND=atoi((*argv)[++i]); 
    else if (!strcmp((*argv)[i],"-invariant"))
      Inv_file=(*argv)[++i]; 
    else if (!strcmp((*argv)[i],"-help"))
      help(); 
    else if (!strcmp((*argv)[i],"-version"))
      version();
    else 
      newargv[newargc++]=(*argv)[i];
  }
  if (MARK && GENERATE) ATerror("'-generate' and '-mark' are incompatible\n");
  if (MARK && DOT) ATerror("'-mark' and '-dot' are incompatible\n");
  if (DOT && GENERATE) ATerror("'-generate' and '-dot' are incompatible\n");
  if (!(VERBOSE || MARK || GENERATE || COUNTER || PRINT || DOT))
    ATwarning("No output: -silent without "
	      "-mark, -generate, -counter or -print(-dot)");
  if (GENERATE && (PRINT || COUNTER || DOT))
    ATwarning("'-print/counter' is ignored with '-generate'");
*argv=newargv;
*argc=newargc;
}

static ATermList create_variables_rec(ATermList sum, char* suffix)
{ /* TODO check that new variable names have not been 
     used elsewhere */

  char *var;
  char buffer[BUFFERLENGTH];
  ATerm sort;
  if (ATmatch((ATerm)sum,"[v(<str>,<term>),<list>]",
              &var, &sort, &sum))
   { if (strlen(var)+strlen(suffix)>=BUFFERLENGTH)
        ATerror("String too long: %s\n",var);

   // assumption: var is of the form "....#...." 
   // result: "..._suffix#..."

     var = strtok(var,"#");
     sprintf(buffer,"%s%s%s",var,suffix,"#");
     return ATinsert(create_variables_rec(sum,suffix),
		     ATmake("v(<str>,<term>)]",buffer,sort));
   }
  if (!ATmatch((ATerm)sum,"[]"))
     ATerror("Expect variablelist: %t\n",sum);
  return sum;   
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

static ATerm equal(ATermList t1, ATermList t2) { 
  ATerm term1, term2;
  if (ATmatch((ATerm)t1,"[<term>,<list>]",
	      &term1,&t1)) {
    if (!ATmatch((ATerm)t2,"[<term>,<list>]",
		 &term2,&t2))
      ATerror("Termlists must have the same length:\n%t\n%t\n",t1,t2);
    return prAND(prEQ(term1,term2), equal(t1,t2));
  }
  if (!ATmatch((ATerm)t2,"[]"))
    ATerror("Expect empty termlist: %t\n",t2);
  return prTRUE;
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

static void set_subst(ATermList termlist, ATermList varlist) {
  while (!ATisEmpty(varlist)) {
    Symbol v = ATgetSymbol(ATgetArgument(ATgetFirst(varlist),0));
    ATerm t = ATgetFirst(termlist);
    RWassignVariable(v,t,NULL,1);
    varlist = ATgetNext(varlist);
    termlist = ATgetNext(termlist);
  }
}

static ATerm check_a_confluence_condition(ATermList parameters,
          ATermList sum_a,char *a, ATermList f_a, ATermList g_a, ATerm b_a,
          ATermList sum_tau, ATermList f_tau, ATermList g_tau,ATerm b_tau,
          ATerm Inv)
     // WARNING: returns TRUE if GENERATE is set
{ ATermList e1,e2;
  ATermList e1terms, e2terms;
  ATerm result, b_a_e1, b_tau_e2, b_a_g, b_tau_g;
  ATermList g_a_e1, g_tau_e2, f_a_e1, f_a_g, g_a_g, g_tau_g;

  // ATfprintf(stderr,"CONFLUENCE FORMULA for action `%s'\n",a);

  if (!ATmatch((ATerm)g_a,"i(<term>)",&g_a))
     ATerror("g_a must start with i: %t\n",g_a);

  if (!ATmatch((ATerm)g_tau,"i(<term>)",&g_tau))
     ATerror("g_tau must start with i: %t\n",g_tau);

  e1=create_variables_rec(sum_a,"_a1");
  e1terms=make_termlist(e1);
  e2=create_variables_rec(sum_tau,"_tau1");
  e2terms=make_termlist(e2);

  Declare_vars(e1);
  Declare_vars(e2);

  if (GENERATE)
    ATfprintf(stdout,"%t,\n",
	      prettyprint_decls(ATconcat(parameters,ATconcat(e1,e2))));
  
  /* The formula to be generated used to be:

     forall(d:D,
     forall(e1:E_a, forall(e2:E_tau,exists(e3:E_a,exists(e4:E_tau,
         eq(g_a(d,e1),g_tau(d,e2)) or [ ONLY IF a=tau]
         not(b_a(d,e1)) or
         not(b_tau(d,e2)) or
         ( eq(f_a(d,e1),f_a(g_tau(d,e2),e3) and
           b_a(g_tau(d,e2),e3) and
           b_tau(g_a(d,e1),e4) and
           eq(g_a(g_tau(d,e2),e3),g_tau(g_a(d,e1),e4))))))))) 

     We now
      - avoid existential quantifiers
      - relativize this by an invariant

     forall(d:D,
     forall(e1:E_a, forall(e2:E_tau,
       Inv implies
         eq(g_a(d,e1),g_tau(d,e2)) or [ ONLY IF a=tau]
         not(b_a(d,e1)) or
         not(b_tau(d,e2)) or
         ( eq(f_a(d,e1),f_a(g_tau(d,e2),e1) and
           b_a(g_tau(d,e2),e1) and
           b_tau(g_a(d,e1),e2) and
           eq(g_a(g_tau(d,e2),e1),g_tau(g_a(d,e1),e2)))))))


  */
  
  /* make substitution sum_a -> e1terms */

  set_subst(e1terms,sum_a);
  g_a_e1 = RWrewriteList(g_a);
  f_a_e1 = RWrewriteList(f_a);
  b_a_e1 = RWrewrite(b_a);

  set_subst(e2terms,sum_tau);
  g_tau_e2 = RWrewriteList(g_tau);
  b_tau_e2 = RWrewrite(b_tau);

  set_subst(g_tau_e2,parameters);
  f_a_g = RWrewriteList(f_a_e1);
  b_a_g = RWrewrite(b_a_e1);
  g_a_g = RWrewriteList(g_a_e1);

  set_subst(g_a_e1,parameters);
  b_tau_g = RWrewrite(b_tau_e2);
  g_tau_g = RWrewriteList(g_tau_e2);
    
  RWresetVariables(1);

  result= prAND( equal(f_a_e1, f_a_g),
          prAND( b_a_g,
          prAND( b_tau_g,
	       equal(g_a_g,g_tau_g))));
  
  if (strcmp(a,"tau")==0)
    result= prOR(equal(g_a_e1,g_tau_e2),result);
  
  result=prIMPLIES(prAND(prAND(b_a_e1,b_tau_e2),Inv),result);
  
  if (GENERATE) {
    ATfprintf(stdout,"%t",prettyprint(Simplify(result)));
    return prTRUE;
  }
  
  return Prove(result);
}

static int traverse_sums(int tau_count, ATermList sums, ATermList parameters, 
        ATermList sum_tau, ATermList f_tau, ATermList g_tau, ATerm b_tau,
        ATerm Inv,LPO_t lpo)  
     // WARNING: returns 1 if GENERATE is set
{ ATerm summand;
  ATerm b_a;
  ATermList sum_a, f_a, g_a;
  ATerm result;
  char *a;
  int count=0;
  char confluent=1;

  if (S[tau_count]>0 && !ALL) {
    confluent=0;
    if (VERBOSE)
      fprintf(stderr,"Was not confluent with summand %d\n",S[tau_count]);
  }
  
  while ((ALL || confluent) && !ATisEmpty(sums)) {
    count++;
    summand = ATgetFirst(sums);
    sums = ATgetNext(sums);
    
    if ((!GENERATE) && (!ALL) && A[N*tau_count+count]==1) {
      if (VERBOSE) fprintf(stderr,".");
      continue; //next iteration: dealt with already
    }

    if (   (!GENERATE)
        && disjoint(Used_set(lpo,count-1),Changed_set(lpo,tau_count-1))
	&& disjoint(Changed_set(lpo,count-1),Used_set(lpo,tau_count-1))
	&& disjoint(Changed_set(lpo,count-1),Changed_set(lpo,tau_count-1))
	) {
      if (VERBOSE) fprintf(stderr,":");
      A[N*count+tau_count]=1;
      continue; //next iteration: disjoint summands
    }
    
    if (!ATmatch(summand,"smd(<term>,<str>,<term>,<term>,<term>)",
		 &sum_a,&a,&f_a,&g_a,&b_a))
      ATerror("Expect summand %t",summand);
    
    result = check_a_confluence_condition(parameters,
               sum_a,a,f_a,g_a,b_a,sum_tau,f_tau,g_tau,b_tau,Inv);
    if (result==prTRUE) {
      A[N*count+tau_count]=1;
      if (VERBOSE) 
	fprintf(stderr,"+");
      if (GENERATE && !ATisEmpty(sums))
	ATfprintf(stdout,",\n\n");
      // continue with next summand
    }
    else {
      confluent=0;
      S[count]=tau_count;
      if (VERBOSE) {
	if (ALL)
	  fprintf(stderr,"-");
	else
	  fprintf(stderr,"Not confluent with summand %d\n",count);
      }
      if (PRINT) print_BDD(result,stderr);
      if (DOT) dot_BDD(result,stdout);
      if (COUNTER) print_example(result,prFALSE,stderr);
      // continue with next summand (in case ALL is set)
    }
  }
  if (confluent && VERBOSE && !GENERATE) 
    fprintf(stderr,"Confluent with all summands!");
  if (VERBOSE && (confluent || ALL))
    fprintf(stderr,"\n");
  return confluent;
}

static ATerm check_confluence_and_mark(ATerm LPO,ATerm Inv)
{
  ATerm init=NULL;
  ATermList parameters=NULL, sums=NULL; 
  ATermList sum_tau=NULL, f_tau=NULL, g_tau=NULL;
  ATerm b_tau=NULL;
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
  
  N = ATgetLength(sums);
  A = (int*)calloc((N+1)*(N+1),sizeof(int));
  S = (int*)calloc(N+1,sizeof(int));
  
  Sums=ATmakeList0();
  todo=sums;
  if (GENERATE)
    fprintf(stdout,"[");
  while (!ATisEmpty(todo)) {
    SUM++;
    summand = ATgetFirst(todo);
    todo = ATgetNext(todo);
    count++;
    if (!ATmatch(summand,"smd(<term>,<str>,<term>,<term>,<term>)",
		 &sum_tau,&a,&f_tau,&g_tau,&b_tau))
      ATerror("Summand expected\n");
    if (strcmp(a,"tau")==0) {
      TAU++;
      if ((!SUMMAND) || count==SUMMAND) {
	// this is a tau-summand that the user wants to do: 
	// check it and if confluent, mark it as ctau
	if (VERBOSE) ATfprintf(stderr,"tau summand %2d:",count);
	if (traverse_sums(count,sums,parameters,sum_tau,f_tau,g_tau,b_tau,Inv,lpo)) {
	  CONF++;
	  summand = ATmake("smd(<term>,\"ctau\",<term>,<term>,<term>)",
			   sum_tau,f_tau,g_tau,b_tau);
	  if (GENERATE && !ATisEmpty(todo))
	    fprintf(stdout,",\n\n");
	}
      }
    }
    else
      if (SUMMAND && (SUMMAND==count))
	ATfprintf(stderr,"Summand %d is not a tau-summand\n",count);
    Sums = ATinsert(Sums,summand);
  }
  if (GENERATE)
    fprintf(stdout,"]\n");
  LPO = ATmake("initprocspec(<term>,<term>,<term>)",
	       init,parameters,ATreverse(Sums));
  return LPO;
}

static void ExitWrongArgument(int argc, char *argv[]) {
     if (argc>1) {
         ATwarning("Illegal option %s", argv[1]);
         help();
         exit(1);
         }
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
  
  parse_argument_line(&argc,&argv);
  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");

  LPO=MCRLgetProc();

  ProverSetArguments(&argc,&argv);
  ExitWrongArgument(argc, argv);
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
  
  LPO = check_confluence_and_mark(LPO,Inv);
  if (MARK) {
    MCRLsetProc(LPO);
    MCRLoutput();
  }
  
  if (!GENERATE)
    ATwarning(
	      "%s %d confluent out of %d tau-summands, "
	      "out of %d summands in total.",
	      (MARK ? "Marked" : "Detected"),CONF,TAU,SUM);
  return 0;
}
