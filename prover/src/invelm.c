/* $Id: invelm.c,v 1.5 2005/04/20 14:25:55 vdpol Exp $ */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif
#include "aterm2.h"
#include "prover.h"
#include "rw.h"
#include <stdlib.h>
#include <string.h>
#define MY_NAME "Invelm"
// VERSION assumed to be defined with -DVERSION=\"...\"

static char SILENT;
static char SIMPLIFY=0;
static char REWRITE=0;
static char SUMMAND=0;
static char WITNESS=0;
static char SPLITSUMS=0;
static char PRINT=0;
static char DOT=0;
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

#define P(x) fprintf(stderr,"  %s\n",x);

void moresimplify() {
 P("If -simplify is present, then every guard g is transformed into a")
 P("BDD which is equivalent to and(inv,g), where inv is the invariant.")
 P("The user is responsible for checking that inv is an invariant indeed")
 P("(see invcheck). A BDD is a nested if-then-else term, with certain")
 P("properties (however, uniqueness is not guaranteed in non-propositional")
 P("cases).")
 P("")
 P("The effect of -simplify is to make global knowledge (provided by the ")
 P("invariant) locally available in each guard. This may be helpful for other ")
 P("tools that use the prover, such as confcheck. However, static analysis")
 P("tools (e.g. constelm, parelm, sumelm) may perform worse, because BDDs ")
 P("are syntactically harder, and all variables of the invariant tend to occur ")
 P("in all summands.")
 P("")
 P("Use -rewrite in order to eliminate variables from summands.")
 exit(0);
}

void morerewrite() {
  P("If -rewrite is present, then the rewrite system is modified as follows:")
  P("- parameters of the LPO are viewed as constants (maps)")
  P("- certain facts from the invariant are viewed as rewrite rules")
  P("These rewrite rules are added to the existing rew's, and applied")
  P("to all summands. The abstract datatype is not changed. The user is")
  P("responsible for ensuring termination, and for checking correctness")
  P("(see invcheck).")
  P("The new rules are displayed on stderr (except with -silent)")
  P("")
  P("As an example, if the invariant is of the form:")
  P("  and(eq(x,plus(y,z)),")
  P("  and(c,")
  P("  and(not(b),")
  P("  and(eq(length(l),S(0))")
  P("  and(or(a,d),")
  P("      not(or(gt(x,y),e)))))))")
  P("Then the following rules are generated:")
  P("  x -> plus(y,z)")
  P("  c -> T")
  P("  b -> F")
  P("  length(l) -> S(0)")
  P("  gt(y,z) -> F")
  P("  e -> F")
  P("Typically, applying parelm subsequently, will eliminate x,c,b and e.")
  P("")
  P("Summarizing, the rules for generating rules from an invariant are as follows:")
  P("first, not-symbols are pushed inside. Next, terms with or() and ite()")
  P("are skipped. Terms with and() are split. At the atom level, a positive")
  P("atom eq(l,r) is read as l->r; other positive atoms b are turned to b->T; ")
  P("negative atoms not(b) (including equations) are turned into b->F.")
  exit(0);
}

void help() {
  ATfprintf(stderr,"%s\n",
	    "\ninvelm [options] -- "
	    "eliminates summands with guards contradicting");
  ATfprintf(stderr,"%s\n",
            "                     "
	    "an invariant; other summands may be simplified");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","Reads LPO from stdin; writes LPO to stdout");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","OPTIONS:");
  ATfprintf(stderr,"%s\n",
	    "-invariant file:"
	    " invariant is used, NOT checked!");
  ATfprintf(stderr,"%s\n",
	    "-simplify      :"
	    " rewrites conjunction of guard and invariant to BDD");
  ATfprintf(stderr,"%s\n",
	    "-rewrite       :"
	    " rewrites summands, using ADT + equations in invariant");
  ATfprintf(stderr,"%s\n",
	    "-splitsums     :"
	    " splits summands with guard or( , ) in multiple summands");
  ATfprintf(stderr,"%s\n",
	    "-summand <n>   : "
	    "only eliminates/simplifies the n'th summand");
  ATfprintf(stderr,"%s\n",
	    "-witness       : "
	    "provides a witness for summands that seem to be reachable");
  ATfprintf(stderr,"%s\n",
	    "-silent        :"
	    " no output on stderr");
  ATfprintf(stderr,"%s\n",
	    "-print         : "
	    "prints guards as BDDs in ASCII to stderr");
  ATfprintf(stderr,"%s\n",
	    "-print-dot     : "
	    "prints guards as BDDs in dot-format to stdout (instead of LPO)");
  ATfprintf(stderr,"%s\n",
	    "-version       : "
	    "prints the version number");
  ATfprintf(stderr,"%s\n",
	    "-help          :"
	    " prints this message");
  ATfprintf(stderr,"%s\n",
	    "-help-rewrite  :"
	    " prints more help on -rewrite flag");
  ATfprintf(stderr,"%s\n",
	    "-help-simplify  :"
	    " prints more help on -simplify flag");
  ATfprintf(stderr,"%s\n","");
  ATfprintf(stderr,"%s\n","If -invariant is missing, T(rue) is taken;");
  ATfprintf(stderr,"%s\n","this is especially useful with -simplify.");
  exit(0);
}

void parse_argument_line(int *argc,char ***argv) {
  int i, j = 0;
  char **newargv = (char**) calloc(*argc + 1, sizeof(char*));
  if (!newargv) ATerror("Cannot allocate array argv");
  newargv[j++] = (*argv)[0];
  for (i=1;i<*argc;i++) {
    if (!strcmp((*argv)[i],"-silent")) {
      SILENT=1; continue;}
    if (!strcmp((*argv)[i],"-invariant")) {
      Inv_file=(*argv)[++i]; continue;} 
    if (!strcmp((*argv)[i],"-summand")) {
      SUMMAND=atoi((*argv)[++i]); continue;}
    if (!strcmp((*argv)[i],"-simplify")) {
      SIMPLIFY=1; continue;}
    if (!strcmp((*argv)[i],"-rewrite")) {
      REWRITE=1; continue;}
    if (!strcmp((*argv)[i],"-splitsums")) {
      SPLITSUMS=1; continue;}
    if (!strcmp((*argv)[i],"-witness")) {
      WITNESS=1; continue;}
    if (!strcmp((*argv)[i],"-print-dot")) {
      DOT=1; continue;}
    if (!strcmp((*argv)[i],"-print")) {
      PRINT=1; continue;}
    if (!strcmp((*argv)[i],"-version")) 
      version();
    if (!strcmp((*argv)[i],"-help"))
      help(); 
    if (!strcmp((*argv)[i],"-help-rewrite"))
      morerewrite(); 
    if (!strcmp((*argv)[i],"-help-simplify"))
      moresimplify(); 
    j=MCRLcopyOption(newargv, *argv, *argc, i, j);
  }
  if (DOT && SPLITSUMS) ATwarning("-splitsums ignored due to -print-dot");
  if (!(Inv_file||SIMPLIFY))
    ATwarning("invelm without -invariant or -simplify?");
  if (REWRITE && !Inv_file)
    ATwarning("invelm with -rewrite but without -invariant?");
  *argc = j; *argv = newargv;
}

ATermList orlist(ATerm guard) {
  if (ATgetSymbol(guard)==MCRLsym_or)
    return ATconcat(orlist(ATgetArgument(guard,0)),
		    orlist(ATgetArgument(guard,1)));
  else
    return ATmakeList1(guard);
}

ATermList NewRules(ATerm Inv) {
  /* rules for generating invariants: 
     and    -> split
     or/ite -> skip
     eq(l,r)-> make rule l->r
     not(not())     -> simplify, continue
     not(and/ite()) -> skip
     not(or())      -> treat as and(not(),not())
     not(other)     -> make rule other -> F
     other          -> make rule other -> T
  */

  Symbol f = ATgetSymbol(Inv);
  if (Inv == MCRLterm_true) return ATempty;
  else if (f == MCRLsym_and)
    return ATconcat(NewRules(ATgetArgument(Inv,0)),
		    NewRules(ATgetArgument(Inv,1)));
  else if (Is_eq(Inv))
    return ATmakeList1(Inv);
  else if (f == MCRLsym_or) return ATempty;
  else if (MCRLgetType(f) == MCRLcasefunction) return ATempty;
  else if (f == MCRLsym_not) {
    ATerm notInv = ATgetArgument(Inv,0);
    Symbol g = ATgetSymbol(notInv);
    if (notInv == MCRLterm_false) return ATempty;
    if (g==MCRLsym_not) return NewRules(ATgetArgument(notInv,0));
    else if (g==MCRLsym_and) return ATempty;
    else if (g==MCRLsym_or) 
      return ATconcat(NewRules(prNOT(ATgetArgument(notInv,0))),
		      NewRules(prNOT(ATgetArgument(notInv,1))));
    else if (MCRLgetType(f) == MCRLcasefunction) return ATempty;
    return ATmakeList1(MCRLmakeEq(notInv,prFALSE));
  }
  else return ATmakeList1(MCRLmakeEq(Inv,prTRUE));
}

void ProverExtendTRS(ATermList parameters,ATermList rules) {
  // (Re)initializes prover and rewriter, with 
  // - parameters added as constants
  // - rules added as rewrite rules
  // The current ADT is not changed
  ATbool new;
  ATerm adt = MCRLgetAdt();

  while (!ATisEmpty(parameters)) {
    ATerm t,s;
    ATmatch((ATerm)parameters,"[v(<term>,<term>),<list>]",&t,&s,&parameters);
    MCRLputMap(t,s,&new);
  }
  while (!ATisEmpty(rules)) {
    ATerm l,r,eq;
    l=ATgetArgument(ATgetFirst(rules),0);
    r=ATgetArgument(ATgetFirst(rules),1);
    if (!SILENT)
      ATwarning("Added TRS-rule: %t -> %t",MCRLprint(l),MCRLprint(r));
    rules = ATgetNext(rules);
    eq = ATmake("e([],<term>,<term>)",l,r);
    MCRLputEquation(eq,&new);
  }
  ProverInitialize();
  MCRLsetAdt(adt);
}

int main(int argc, char *argv[])
{ ATerm bottomOfStack=NULL;
  ATerm LPO=NULL;
  ATerm init=NULL;
  ATermList parameters=NULL,sums=NULL,todo=NULL;
  ATerm Inv=NULL;
  FILE *fp;
  int count=0;
  int REM=0; // number of removed summands
  ATinit(argc,argv,&bottomOfStack);
  ATsetWarningHandler(WarningHandler);
  ATsetErrorHandler(ErrorHandler);

  ATprotect(&LPO);
  ATprotect(&init);
  ATprotect((ATerm*)&parameters);
  ATprotect((ATerm*)&sums);
  ATprotect((ATerm*)&todo);
  ATprotect(&Inv);

  parse_argument_line(&argc,&argv);

  MCRLsetArguments(&argc,&argv);
  if (!MCRLinitialize()) ATerror("Error with MCRLinitialize");
  ProverSetArguments(&argc,&argv);
  ProverInitialize();                // done to ensure and/eq functions
  MCRLdeclareVars(MCRLgetListOfPars()); // needed for parsing invariant
 
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

  LPO=MCRLgetProc();
  if (!ATmatch(LPO,"initprocspec(<term>,<term>,<term>)",
	       &init,&parameters,&sums))
    ATerror("Expect LPO\n");


  if (!Inv) 
    Inv=prTRUE;
  
  if (REWRITE) {
    ATermList rules = NewRules(Inv);
    ProverExtendTRS(parameters,rules);
  }
  else
    Declare_vars(parameters);

  Inv = RWrewrite(Inv);

  todo = sums;
  sums = ATempty;
  while (!ATisEmpty(todo)) {
    ATermList vars, args;
    ATerm act,next,guard,result;
    ATerm sum = ATgetFirst(todo);

    todo = ATgetNext(todo);
    count++;
    if (!ATmatch(sum,"smd(<term>,<term>,<term>,<term>,<term>)",
		 &vars,&act,&args,&next,&guard))
      ATerror("Sum expected: %t\n",sum);

    if (SUMMAND && (SUMMAND != count))
      sums = ATinsert(sums,sum);
    else {
      Declare_vars(vars);
      guard = RWrewrite(guard);
      result = Prove(prAND(guard,Inv));
      if (result==prFALSE) {
	if (!SILENT) fprintf(stderr, "\nsummand %d removed",count);
	REM++;
      }
      else {
	if (!SILENT) fprintf(stderr,".");
	if (WITNESS) print_example(result,prTRUE,stderr);
	if (REWRITE) {
	  if (!SIMPLIFY) result=guard; // it has been rewritten before
	  next = ATmake("i(<term>)",
			RWrewriteList((ATermList)ATgetArgument(next,0)));
	  args = RWrewriteList(args);
	}
	if (PRINT) print_BDD(result,stderr);
	if (DOT)
	  dot_BDD(result,stdout);
	else {
	  if (REWRITE || SIMPLIFY)
	    sum = ATmake("smd(<term>,<term>,<term>,<term>,<term>)",
			 vars,act,args,next,result);  
	  if (SPLITSUMS) {
	    ATermList newguards = orlist(ATgetArgument(sum,4));
	    while (!ATisEmpty(newguards)) {
	      sums = ATinsert(sums,(ATerm)ATsetArgument((ATermAppl)sum,ATgetFirst(newguards),4));
	      newguards = ATgetNext(newguards);
	    }
	  }
	  else
	    sums = ATinsert(sums,sum);
	}
      }
    }
  }
  if (!SILENT) fprintf(stderr,"\n");
  
  sums = ATreverse(sums);
  MCRLsetProc(ATmake("initprocspec(<term>,<term>,<term>)",
		     init,parameters,sums));
  if (!DOT) MCRLoutput();
	      
  ATwarning("Removed %d out of %d summands",REM,count);
  return 0;
}
